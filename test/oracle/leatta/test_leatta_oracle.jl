# ============================================================================================
# LeaTTa PROVED-ORACLE differential — the strongest conformance oracle in the fleet by provenance.
#
# LeaTTa (~/JuliaAGI/dev-zone/LeaTTa) is a Lean-4 MACHINE-PROVED MeTTa/Hyperon interpreter (the spec
# MeTTa-TS ports from): its `interpretAtom`/`mettaEval` come with machine-checked TypeSoundness /
# Preservation / Confluence / MatcherCorrect proofs. So "Core ≠ LeaTTa ⇒ Core erred" — a deviation is
# OUR bug, not a difference of opinion.
#
# DESIGN — golden-snapshot, renderer-independent, no toolchain at CI time:
#   * The vendored corpus (test/oracle/leatta/corpus/, copied verbatim from LeaTTa's tests/corpus/ — which
#     is Hyperon's own UNMODIFIED test corpus, MIT, upstream commit 3f76dc4) is
#     SELF-CHECKING: every `!`-directive is an assertEqual-family call that returns the UNIT atom `()` on
#     pass and `(Error <call> AssertionFailed)` on fail. LeaTTa PROVES all 270 directives pass (FAIL=0 —
#     see corpus/EXPECTED.txt). So "Core PASSES directive d" ≡ "Core computes the proved-correct value
#     for d" — transitive agreement with LeaTTa's values with NO string-diffing (hence immune to the
#     render-format false-positives — quote/Float-vs-Int/var-alpha — that a freeze-LeaTTa-output-and-diff
#     oracle would suffer). CI therefore needs neither Lean/elan nor the LeaTTa binary; only Core + the
#     frozen corpus + EXPECTED.txt. Regenerate the corpus/golden offline with ./RUN.sh.
#
# GATE (per the LeaTTa-oracle CI contract):
#   * CORE_BUG (HARD gate, must be 0): a directive that does NOT pass and does NOT reference a known-
#     unimplemented op — Core computed a WRONG answer (or crashed) for something LeaTTa proved correct.
#   * MISSING_OP (LEDGER, honest-kept baseline): a directive fails only because Core has no impl for its
#     head op (assert-variant, sort-strings, help!, pragma!) — this is CORRECT MeTTa (an undefined head
#     returns the call unreduced), NOT a bug. Tracked as a live conformance-COVERAGE ledger: when Core
#     grows one of these ops the count DROPS, the baseline mismatches, and this test fails to force the
#     baseline update (celebrating the coverage gain). A RISE means a regression or a new unimplemented op.
#   * LEATTA_SPECIFIC (FILTERED): ops LeaTTa/hyperon have that hyperon-experimental (and thus Core) do
#     not — hyperpose, fork-spaces. Not a Core gap; excluded from the gate, tracked separately.
#
# History: this oracle's first differential (2026-07-08) found exactly ONE real CORE_BUG — `case` on an
# empty result set (fixed, commit 1ee0356, locked by test_interpreter.jl). Everything else was MISSING_OP
# / LEATTA_SPECIFIC / import!-path (the last fixed here by seeding _MODULE_PATH with the corpus dir).
# ============================================================================================
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa
using Test
const _LI = Interpreter

const LEATTA_CORPUS = joinpath(@__DIR__, "corpus")

# Ops Core does not (yet) implement — a call with one of these heads returns UNREDUCED (correct MeTTa for
# an undefined head), so its self-checking directive can't pass. NOT bugs; this is the coverage ledger.
const LEATTA_KNOWN_MISSING = Set([
    "assert", "assertEqualMsg", "assertEqualToResultMsg",
    "assertAlphaEqualMsg", "assertAlphaEqualToResult", "assertAlphaEqualToResultMsg",
    "assertIncludes", "sort-strings", "help!", "pragma!",
])
# Space/parallel-model ops present in the corpus (LeaTTa passes them: c2_spaces 25/25) that Core does not
# implement — `fork-space` (forked named spaces) and `hyperpose` (parallel superpose). Tracked separately
# from the plain missing stdlib ops above; both are non-gated ledger items, not CORE_BUGs.
const LEATTA_ONLY = Set(["hyperpose", "fork-space", "fork-spaces", "new-space-forked"])

# Frozen ledger: per file, the (MISSING_OP, LEATTA_SPECIFIC) directive counts Core currently exhibits.
# EVERY other directive must PASS; any deviation from these exact counts (or any CORE_BUG) fails the gate.
# Derived from the 2026-07-08 differential; total = 246 pass + 19 missing + 5 leatta = 270 (== EXPECTED.txt).
const LEATTA_LEDGER_BASELINE = Dict{String,Tuple{Int,Int}}(
    "a1_symbols.metta"       => (0, 0), "a2_opencoggy.metta"     => (0, 0),
    "a3_twoside.metta"       => (0, 0), "b0_chaining_prelim.metta" => (0, 0),
    "b1_equal_chain.metta"   => (0, 0), "b2_backchain.metta"     => (0, 0),
    "b3_direct.metta"        => (0, 0), "b4_nondeterm.metta"     => (0, 0),
    "b5_types_prelim.metta"  => (0, 0), "c1_grounded_basic.metta" => (0, 0),
    "c2_spaces.metta"        => (0, 3), "c3_pln_stv.metta"       => (0, 0),
    "d1_gadt.metta"          => (0, 0), "d2_higherfunc.metta"    => (0, 0),
    "d3_deptypes.metta"      => (0, 0), "d4_type_prop.metta"     => (0, 0),
    "d5_auto_types.metta"    => (1, 0), "e1_kb_write.metta"      => (0, 0),
    "e2_states.metta"        => (0, 0), "e3_match_states.metta"  => (0, 0),
    "g1_docs.metta"          => (5, 0), "test_stdlib.metta"      => (13, 2),
)

# ---- per-directive runner: mirrors load_metta!'s incremental parse-eval loop (Interpreter.jl:2190),
# but captures ONE result set per `!`-directive instead of flat-concatenating them. Non-directive atoms
# are add_atom!'d exactly as load_metta! does, so state (defs / bind! tokens / add-atom) threads across
# directives identically.
function _leatta_run_directives(space::_LI.Space, text::AbstractString)
    get!(space.tokens, "&self", _LI.Grounded(space))
    toks = _LI.tokenize(text); i = Ref(1)
    out = Tuple{_LI.Atom, Vector{_LI.Atom}}[]
    while i[] <= length(toks)
        directive = false
        toks[i[]] == "!" && (directive = true; i[] += 1)
        i[] > length(toks) && break
        atom = _LI.parse_from(toks, i, space.tokens)
        if directive
            res = _LI.metta_run(atom, space)
            push!(out, (atom, res))
        else
            _LI.add_atom!(space, atom)
        end
    end
    out
end

_leatta_is_error(a) = a isa _LI.Expression && !isempty(a.children) && a.children[1] == _LI.Sym("Error")
_leatta_is_unit(rs) = length(rs) == 1 && rs[1] isa _LI.Expression && isempty(rs[1].children)

# collect every Sym head appearing anywhere in an atom tree (to spot unimplemented / LeaTTa-only ops)
function _leatta_heads!(a, acc)
    if a isa _LI.Expression && !isempty(a.children)
        h = a.children[1]; h isa _LI.Sym && push!(acc, string(h))
        for c in a.children; _leatta_heads!(c, acc); end
    end
    acc
end
_leatta_heads(a) = _leatta_heads!(a, Set{String}())

# Parse EXPECTED.txt (LeaTTa's proved golden: `<file> <PASS> <FAIL> <TOTAL>`, all FAIL=0) → file => TOTAL.
function _leatta_expected_totals()
    d = Dict{String,Int}()
    for ln in eachline(joinpath(LEATTA_CORPUS, "EXPECTED.txt"))
        s = strip(ln); (isempty(s) || startswith(s, "#")) && continue
        parts = split(s)
        length(parts) >= 4 && (d[parts[1]] = parse(Int, parts[4]))
    end
    d
end

@testset "LeaTTa proved-oracle — Core vs machine-proved MeTTa (CORE_BUG gate + coverage ledger)" begin
    expected = _leatta_expected_totals()
    files = sort(filter(f -> endswith(f, ".metta") && f != "c2_spaces_kb.metta", readdir(LEATTA_CORPUS)))

    # seed the import! search path with the corpus dir so `!(import! &kb c2_spaces_kb)` resolves the
    # module file (the former FORMAT_ARTIFACT). Prepend + restore so nothing leaks into other tests.
    added = !(LEATTA_CORPUS in _LI._MODULE_PATH[])
    added && push!(_LI._MODULE_PATH[], LEATTA_CORPUS)
    try
        println("\n  ── LeaTTa proved-oracle matrix (Core vs Lean-4-proved semantics) ──")
        tot_pass = tot_miss = tot_leatta = tot_bug = 0
        bug_detail = String[]
        for f in files
            sp = _LI.Space(); _LI.load_core_stdlib!(sp)
            dirs = try
                _leatta_run_directives(sp, read(joinpath(LEATTA_CORPUS, f), String))
            catch e   # a crash loading/evaluating the proved corpus is itself a CORE_BUG
                push!(bug_detail, "$f: LOAD CRASH $(typeof(e))")
                tot_bug += 1
                Tuple{_LI.Atom,Vector{_LI.Atom}}[]
            end
            fp = fm = fl = fb = 0
            for (atom, rs) in dirs
                if _leatta_is_unit(rs); fp += 1; continue; end
                hs = _leatta_heads(atom)
                if !isdisjoint(hs, LEATTA_ONLY)
                    fl += 1
                elseif !isdisjoint(hs, LEATTA_KNOWN_MISSING)
                    fm += 1
                else                                    # non-pass with no unimplemented head ⇒ CORE_BUG
                    fb += 1
                    push!(bug_detail, "$f: $(string(atom))  ⇒  $(isempty(rs) ? "<empty>" : join(string.(rs), " | "))")
                end
            end
            tot_pass += fp; tot_miss += fm; tot_leatta += fl; tot_bug += fb
            base = get(LEATTA_LEDGER_BASELINE, f, (0, 0))
            flag = fb > 0 ? "‼ CORE_BUG=$fb" :
                   (fm, fl) == base ? (fm + fl == 0 ? "✓" : "· ($(fm) miss, $(fl) leatta)") :
                   "‼ LEDGER $(base)→$((fm, fl))"
            et = get(expected, f, -1)
            println("    ", rpad(f, 26), "pass=", rpad(fp, 4), "miss=", rpad(fm, 3),
                    "leatta=", rpad(fl, 3), "total=", rpad(fp + fm + fl, 4),
                    et >= 0 && et != fp + fm + fl ? "‼ EXPECTED=$et" : "", "  ", flag)

            # honest ledger: exact (miss, leatta) per file. A DROP = coverage gain (implement op → update
            # baseline); a RISE = regression or a newly-unimplemented op. Either way, update deliberately.
            @test (fm, fl) == base
            # corpus-integrity: Core must see exactly as many directives as LeaTTa's proved golden counts.
            et >= 0 && @test fp + fm + fl == et
        end
        println("    TOTAL: pass=$tot_pass  missing_op=$tot_miss  leatta_specific=$tot_leatta  ",
                "CORE_BUG=$tot_bug   (proved corpus = $(sum(values(expected); init=0)) directives)")
        if tot_bug > 0
            println("\n    ‼‼ CORE_BUG detail (Core diverged from the machine-proved semantics):")
            for d in bug_detail; println("      • ", d); end
        end

        # THE gate: zero real divergences from the proved semantics.
        @testset "CORE_BUG gate (must be 0 — a divergence from proved semantics is OUR bug)" begin
            @test tot_bug == 0
        end
    finally
        added && filter!(!=(LEATTA_CORPUS), _LI._MODULE_PATH[])
    end
end
