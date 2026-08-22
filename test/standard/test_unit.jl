# UNIT conformance matrix — the primitive layer the 26 integration scripts (test_conformance.jl)
# never gated. Each test/standard/unit/<module>.metta vendors hyperon's OWN #[test] cases (extracted
# + translated VERBATIM from lib/src/metta/runner/stdlib/<module>.rs and metta/<module>.rs), one
# self-checking !(assertEqual …) / !(assertAlphaEqualToResult …) per case.
#
# Same honesty discipline as test_conformance.jl: an explicit per-file baseline of EXPECTED failures
# (known divergences + bugs-to-fix + known-missing ops). A regression (fails go up) OR an unrecorded
# improvement (a fix lands, fails go down) BOTH fail this test, forcing the baseline to stay truthful.
# The matrix prints every run so the incomplete state is always visible.
using MeTTaCore.Eval, MeTTaCore.StandardMeTTa, Test
const SM = MeTTaCore.Eval
const UNIT_DIR = joinpath(@__DIR__, "unit")

# baseline = expected number of FAILING directives per module file (0 = fully green vs hyperon).
# Each non-zero entry is a recorded gap; lowering it requires updating this baseline (keep it honest).
const BASELINE = Dict(
    # Each non-zero entry is a CONFIRMED-REAL divergence (classified by spot-check, not an
    # unvalidated agent fail). Lowering one requires updating this baseline (keep it honest).
    #
    # atom: min-atom + max-atom (unimplemented) + index-atom error-form (IndexOutOfBounds symbol vs
    #   "Index is out of bounds" string) + 2 Core-added bare-predicate filter-atom regressions (chain bug).
    "atom.metta" => 3,
    # math: full hyperon math library now implemented as grounded ops (src/standard/CoreMathOps.jl) —
    #   sqrt/pow/log/trig always Float, abs/trunc/ceil/floor/round preserve type, isnan/isinf → Bool.
    #   48/48 green. (Was 48 missing.)
    "math.metta" => 0,
    # core: 8 → 2, LOWERED 2026-08-16, and the old comment ("pragma! unimplemented (~5) +
    # case-on-Empty / unify-in-case divergence (~3)") was ALREADY WRONG when it was lowered.
    # ⚠️ THIS FILE HAD NEVER RUN. It is reached by no `include` in the suite and by nothing in `bin/`
    # or `tools/` — adopted at `0c51e87`, then touched only by three mechanical module renames. So six
    # gaps closed and the ratchet never noticed. `test_suite_reachability.jl` now exists so that a test
    # nothing runs fails the suite. The 6 fixes are UNATTRIBUTED — nothing recorded which commits
    # earned them, which is the cost of a gate that does not run.
    # THE 2 THAT REMAIN, measured (`unit/core.metta` unchanged since adoption, 24 directives, 22 pass):
    #   1. `(pragma! max-stack-depth -12)` — and pragma! is NOT "unimplemented": the file has ELEVEN
    #      pragma! directives and only this one fails, i.e. only the negative-value case.
    #   2. `(case (fac 6) ((Error $a StackOverflow) …))` — expects a StackOverflow error we never raise.
    # Both are the SAME cause class — depth/stack limits. `_METTA_MAX` defaults to 0 = unlimited
    # (deliberately, mirroring hyperon's `max_stack_depth` default), so there is no depth to exceed and
    # no StackOverflow to report. Sibling of interpreter.metta's recorded "1 step-limit" entry.
    "core.metta" => 2,
    # space: state-op behaviour (change-state! / get-state).
    "space.metta" => 1,
    "text.metta" => 0,        # clean — comment-handling cases all pass
    "types.metta" => 0,       # residue-only (no MeTTa directives; gated by test_types.jl)
    # stdlib_space_sugar: add-reduct/add-reducts/add-atoms (ported from hyperon stdlib.metta:567-683)
    "stdlib_space_sugar.metta" => 0,
    # control: noeval (hyperon stdlib.metta:270 / CeTTa:360) + empty (hyperon:622 / CeTTa:462) — both upstreams
    #   agree; additive stdlib rules, hang-safe. 4/4 green.
    "control.metta" => 0,
    # asserts: assertIncludes (hyperon stdlib.metta:691 verbatim). Additive stdlib rule. 3/3 green.
    #   (assertAlphaEqual/*Msg/=alpha deferred to the assert-family grounded-vs-rules decision.)
    "asserts.metta" => 0,
    # debug: hyperon debug.rs assert-family OWN-behavior cases (the harness verbs tested at their edges).
    #   3/5 pass; 2 EXPECTED-FAIL = the grounded-assert `.jl` fix-target, CONFIRMED by discriminating probe.
    #   The 2 fails are DIFFERENT KINDS (don't conflate at fix-time — they can land separately):
    #   (#5) MULTIPLICITY = CORRECTNESS (load-bearing): Core compare is set-equality (multiplicity-insensitive),
    #        hyperon is multiset. This is the half that justifies touching the `.jl`. (`collapse (mult)`→`(D D D)`
    #        so collapse is faithful; gap is contained to the grounded assert ops.)
    #   (#4) error-message form = COSMETIC: Core bare `AssertionFailed` vs hyperon `Expected/Got/Missed/Excessive`.
    #        No program's BEHAVIOR depends on the message text; exact-whitespace match is fiddly — don't let it block #5.
    #   STATUS: the multiplicity gap is LATENT, not live — grep of the live suite (conformance/unit/lib) found NO
    #   assert over multiset results (all distinct; no superpose-repeats / same-RHS; MOSES/MetaMo assert via Julia ==).
    #   So no spurious pass today; this gate protects the FUTURE. Lower to 0 when the grounded fix lands (post-hang).
    "debug.metta" => 2,
    # interpreter: 15 (was 41). The 26 bare-variable-atom CONTAMINATION cases were FIXED 2026-06-14 by the
    #   resolve-filter at the three rewrite-query sites in Eval.jl: drop a query match where the rewrite-RHS X
    #   is TRULY unbound (`!haskey(mb.var_to_slot, X)`) — a bare-var space atom binds itself to the whole `(= …)`
    #   query, leaving X free; hyperon's `query` filters the same via `resolve(&var_x)→None` (interpreter.rs:619).
    #   Verified FAITHFUL not symptom-suppressing: control.metta's `rvid` id-guard (X equated to a var → KEPT)
    #   stays green and conformance holds 234/234. (First attempt used `resolve===nothing` — over-filtered, broke
    #   the id-guard + b1 + debug; corrected to `haskey` since Core's resolve returns nothing for var-equivalence.)
    #   See memory project_core_bare_var_atom_bug. Remaining 15, MEASURED (all confirmed real/benign — NOT the
    #   contamination, NOT the chain bug):
    #     12 format-only      — benign error-message text divergence (Core `AssertionFailed` vs hyperon detail);
    #      2 NoReturn-subject — `function` reports subject `(function X)` vs hyperon `(X)`;
    #      1 step-limit       — busy-beaver hits Core's step cap where hyperon completes.
    "interpreter.metta" => 15
)

"Run one unit .metta file; return (npass, nfail, fails::Vector{String})."
function run_unit_file(path)
    s = SM.Space()
    SM.load_core_stdlib!(s)
    get!(s.tokens, "&self", SM.Grounded(s))
    npass = 0
    fails = String[]
    # TOKEN-AWARE incremental parse-eval (mirrors load_metta!): parse each atom against s.tokens so a
    # `bind!`-bound space token (&stateAB, &ns, …) substitutes to its Grounded value before the next atom
    # is parsed. (parse_program does NOT substitute tokens, so custom bound spaces fell through to &self.)
    toks = SM.tokenize(read(path, String))
    i = Ref(1)
    while i[] <= length(toks)
        directive = false
        toks[i[]] == "!" && (directive=true; i[] += 1)
        i[] > length(toks) && break
        a = SM.parse_from(toks, i, s.tokens)
        directive || (SM.add_atom!(s, a); continue)
        r = try
            SM.metta_run(a, s)
        catch e
            [SM.Sym("EXC:$(typeof(e))")]
        end
        ok = !isempty(r) && all(x -> x isa SM.Expression && isempty(x.children), r)   # () = assert passed
        if ok
            npass += 1
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
        mark =
            nf == base ? "✓" : (nf > base ? "✗ REGRESSION" : "✗ IMPROVED→update baseline")
        printstyled(
            "  $(rpad(f,22)) $(lpad(np,4))  $(lpad(nf,4))  $(lpad(base,4))  $mark\n";
            color=nf == base ? :green : :red)
        @testset "$f" begin
            @test nf == base
        end
    end
end
