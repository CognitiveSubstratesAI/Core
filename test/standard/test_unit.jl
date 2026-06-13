# UNIT conformance matrix — the primitive layer the 26 integration scripts (test_conformance.jl)
# never gated. Each test/standard/unit/<module>.metta vendors hyperon's OWN #[test] cases (extracted
# + translated VERBATIM from lib/src/metta/runner/stdlib/<module>.rs and metta/<module>.rs), one
# self-checking !(assertEqual …) / !(assertAlphaEqualToResult …) per case.
#
# Same honesty discipline as test_conformance.jl: an explicit per-file baseline of EXPECTED failures
# (known divergences + bugs-to-fix + known-missing ops). A regression (fails go up) OR an unrecorded
# improvement (a fix lands, fails go down) BOTH fail this test, forcing the baseline to stay truthful.
# The matrix prints every run so the incomplete state is always visible.
using MeTTaCore.Minimal, MeTTaCore.Minimal.StandardMeTTa, Test
const SM = MeTTaCore.Minimal
const UNIT_DIR = joinpath(@__DIR__, "unit")

# baseline = expected number of FAILING directives per module file (0 = fully green vs hyperon).
# Each non-zero entry is a recorded gap; lowering it requires updating this baseline (keep it honest).
const BASELINE = Dict(
    # Each non-zero entry is a CONFIRMED-REAL divergence (classified by spot-check, not an
    # unvalidated agent fail). Lowering one requires updating this baseline (keep it honest).
    #
    # atom: min-atom + max-atom (unimplemented) + index-atom error-form (IndexOutOfBounds symbol vs
    #   "Index is out of bounds" string) + 2 Core-added bare-predicate filter-atom regressions (chain bug).
    "atom.metta" => 5,
    # math: the ENTIRE math library (sqrt-math/pow-math/sin-math/log-math/abs-math/ceil-math/…) is
    #   unimplemented in Minimal — all 48 are clean "op missing".
    "math.metta" => 48,
    # core: pragma! unimplemented (~5) + case-on-Empty / unify-in-case divergence (~3).
    "core.metta" => 8,
    # space: state-op behaviour (change-state! / get-state).
    "space.metta" => 2,
    "text.metta" => 0,        # clean — comment-handling cases all pass
    "types.metta" => 0,       # residue-only (no MeTTa directives; gated by test_types.jl)
    # interpreter: PROVISIONAL — NOT yet validated-real. 43→41 after error_atom→grounded-String (only 2
    #   were pure error-format, NOT the ~16 first estimated from a since-known-buggy classifier). The bulk
    #   of the 41 are the chain bare-computed-operand bug (symptom: a free var $X where a value is expected)
    #   — that fix is the real lever here, not error representation. Needs the corrected $X-symptom classifier
    #   + the chain fix before this is an honest real count.
    "interpreter.metta" => 41,
)

"Run one unit .metta file; return (npass, nfail, fails::Vector{String})."
function run_unit_file(path)
    s = SM.Space(); SM.load_core_stdlib!(s)
    npass = 0; fails = String[]
    for (d, a) in SM.parse_program(read(path, String))
        d || (SM.add_atom!(s, a); continue)
        r = try SM.metta_run(a, s) catch e; [SM.Sym("EXC:$(typeof(e))")] end
        ok = !isempty(r) && all(x -> x isa SM.Expression && isempty(x.children), r)   # () = assert passed
        if ok; npass += 1
        else
            q = a isa SM.Expression && length(a.children) >= 2 ? a.children[2] : a
            push!(fails, first(string(SM.subst(q, SM.Bindings())), 70))
        end
    end
    (npass, length(fails), fails)
end

@testset "UNIT conformance — hyperon stdlib #[test] corpus" begin
    files = sort(filter(f -> endswith(f, ".metta"), readdir(UNIT_DIR)))
    isempty(files) && @warn "no unit/*.metta files found"
    printstyled("\n  module                 pass  fail  baseline\n"; bold=true)
    for f in files
        np, nf, fails = run_unit_file(joinpath(UNIT_DIR, f))
        base = get(BASELINE, f, 0)
        mark = nf == base ? "✓" : (nf > base ? "✗ REGRESSION" : "✗ IMPROVED→update baseline")
        printstyled("  $(rpad(f,22)) $(lpad(np,4))  $(lpad(nf,4))  $(lpad(base,4))  $mark\n";
                    color = nf == base ? :green : :red)
        @testset "$f" begin
            @test nf == base
        end
    end
end
