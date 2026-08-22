# test_pln_base_rate.jl
# ─────────────────────────────────────────────────────────────────────────────
# Core-side coverage for `lib/pln/base_rate.metta` — the node BASE-RATE formulas
# (BaseRateTv / EvidenceConfidence / BaseRateAdmits).
#
# The file shipped with NO Core-side test and OUTSIDE `pln.metta`'s import chain: its only loader in
# the whole tree was Julia (`WorldModel/src/PLNCore.jl`), so an agent doing `!(import! &self "pln.metta")`
# got the PLN library *without* the base-rate formulas — the library's own entry point disagreeing with
# what the world model runs. A reflective multi-agent audit of the changed surface then found two live
# defects in it that no test could have caught, both locked below:
#
#   (1) `BaseRateAdmits`'s `(> $sA 0)` guard was INOPERATIVE. `and` is a grounded EAGER op (no
#       short-circuit) and `/safe` returns `(empty)` on a non-positive denominator, so at sA=0 the
#       empty ANNIHILATED the conjunction: the call evaluated to nothing at all instead of to False.
#       A decision procedure that vanishes rather than answering is the fail-OPEN shape this project
#       bans. Fixed by delegating to the canonical `conditional-probability-consistency`, which was
#       already in the same library and the same Space — so this also removed a second copy of the
#       interval test (the copies had already diverged: max/min vs clamp, /safe vs /).
#
#   (2) `stv-strength`/`stv-confidence` were PARTIAL over the library's own majority constructor.
#       They matched only uppercase `(STV $s $c)`, while every truth formula — Truth_Deduction,
#       Truth_Revision, BaseRateTv, … — emits lowercase `(stv $s $c)`. An accessor call on a formula
#       result silently failed to reduce and marshalled out as 0.0; that is how `(0,0)` beliefs got
#       written (commit 11fbc0c). Fixed by widening the accessors (lowercase is the majority form —
#       the formulas were NOT switched to uppercase).
#
# Oracle for the arithmetic: `Truth_w2c` (k = 1) and `conditional-probability-consistency`, both
# already pinned by the wider PLN suite — every assertion here is either a canonical-agreement check
# or a boundary case, never a hand-computed constant standing in for the library.

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa

const _LIBPLN = joinpath(@__DIR__, "..", "..", "lib", "pln")

@testset "PLN base rates — reachable from pln.metta, total accessors, decidable guard" begin

    # ── (0) M1: the LIBRARY ENTRY POINT carries the base-rate formulas ────────────────────────────
    # Load `pln.metta` and nothing else — exactly what an agent does. Before the fix this testset
    # failed at the first call with an unreduced `(BaseRateTv 3 7)`.
    entry = Space()
    load_core_stdlib!(entry)
    load_metta!(entry, "!(import! &self \"$(abspath(joinpath(_LIBPLN, "pln.metta")))\")")
    ent(expr) = strip(join(string.(load_metta!(entry, "!$expr")), " | "))

    @test ent("(BaseRateTv 3 7)") == "(stv 0.42857142857142855 0.75)"
    @test ent("(EvidenceConfidence 3)") == "0.75"
    @test ent("(BaseRateAdmits 0.5 0.9 0.9)") == "True"

    # ── the rest against a directly-loaded space (matches the idiom of the sibling PLN tests) ─────
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(_LIBPLN, "stv.metta"), String))
    load_metta!(sp, read(joinpath(_LIBPLN, "pln_core_logic.metta"), String))
    load_metta!(sp, read(joinpath(_LIBPLN, "base_rate.metta"), String))
    load_metta!(sp, read(joinpath(_LIBPLN, "decay.metta"), String))    # EvidenceConfidence + decay law
    res(expr) = strip(join(string.(load_metta!(sp, "!$expr")), " | "))

    # ── (1) BaseRateTv — the extensional prior s = |ext|/|universe|, c = Truth_w2c(|ext|) ──────────
    @test res("(BaseRateTv 3 7)") == "(stv 0.42857142857142855 0.75)"
    @test res("(BaseRateTv 1 2)") == "(stv 0.5 0.5)"
    # confidence rides the CANONICAL map, it is not a private copy — agreement, not a constant
    @test res("(BaseRateTv 3 7)") == "(stv $(3/7) $(res("(Truth_w2c 3)")))"

    # ABSENCE IS NOT A TRUTH VALUE: neither branch may yield (0,0), which would pass PLN's
    # `as > 0` precondition check as a real belief and force the (stv 1 0) ignorance fallback.
    @test res("(BaseRateTv 0 7)") == "no-evidence"     # concept with no instances
    @test res("(BaseRateTv 3 0)") == "no-evidence"     # empty universe
    @test res("(BaseRateTv 0 0)") == "no-evidence"

    # ── (2) EvidenceConfidence IS Truth_w2c — one definition, referenced ──────────────────────────
    for n in ("0", "1", "3", "7", "100")
        @test res("(EvidenceConfidence $n)") == res("(Truth_w2c $n)")
    end
    @test res("(EvidenceConfidence 1)") == "0.5"       # k = 1 (NOT PeTTaChainer's k = 800)
    @test res("(EvidenceConfidence 3)") == "0.75"

    # ── (3) BaseRateAdmits — REGRESSION LOCK on the inoperative guard ──────────────────────────────
    # P(B|A) must lie in [max(0,(sA+sB-1)/sA), min(1, sB/sA)].
    @test res("(BaseRateAdmits 0.5 0.9 0.9)") == "True"    # 0.9 <= 0.9/0.5 capped at 1 ✓
    @test res("(BaseRateAdmits 0.5 0.9 0.1)") == "False"   # below (0.5+0.9-1)/0.5 = 0.8
    @test res("(BaseRateAdmits 0.8 0.7 0.7)") == "True"    # canonical doctest (pln_core_logic.jl:173)
    @test res("(BaseRateAdmits 0.8 0.7 0.95)") == "False"  # canonical doctest (:174)

    # THE BUG: sA = 0 returned NOTHING AT ALL (empty annihilated the eager `and`), so a caller
    # branching on the result took neither branch. It must DECIDE.
    @test res("(BaseRateAdmits 0.0 0.5 0.5)") == "False"
    @test res("(BaseRateAdmits 0.0 0.0 0.0)") == "False"

    # and it must be the canonical rule, not a second copy that can drift from it
    for (a, b, ab) in (("0.0", "0.5", "0.5"), ("0.5", "0.9", "0.1"), ("0.5", "0.9", "0.9"),
        ("0.8", "0.7", "0.7"), ("0.8", "0.7", "0.95"), ("1.0", "1.0", "1.0"))
        @test res("(BaseRateAdmits $a $b $ab)") ==
            res("(conditional-probability-consistency $a $b $ab)")
    end

    # ── (4) M3 REGRESSION LOCK: the accessors are TOTAL over both constructors ────────────────────
    # Each of these matched no rule before the fix, so it reduced to itself and marshalled as 0.0.
    @test res("(stv-strength (stv 0.25 0.75))") == "0.25"
    @test res("(stv-confidence (stv 0.25 0.75))") == "0.75"
    @test res("(stv-strength (STV 0.25 0.75))") == "0.25"      # uppercase still works
    @test res("(stv-confidence (STV 0.25 0.75))") == "0.75"

    # applied to what the formulas ACTUALLY emit — the case that wrote (0,0) beliefs
    @test res("(stv-strength (BaseRateTv 3 7))") == "$(3/7)"
    @test res("(stv-confidence (BaseRateTv 3 7))") == "0.75"
    @test res(
        "(stv-confidence (Truth_Deduction (stv 0.8 0.9) (stv 0.7 0.85) (stv 0.6 0.8) (stv 0.7 0.9) (stv 0.6 0.85)))"
    ) == "0.3213"

    # a NON-truth-value argument must still not match — the accessors stayed shape-guarded, they
    # were not widened to `$x` (which would return garbage for anything at all).
    @test res("(stv-strength no-evidence)") == "(stv-strength no-evidence)"

    # ── (5) the R10 DECAY LAW (decay.metta) ───────────────────────────────────────────────────────
    # c(t) = c₀·exp(−λ(t−t₀)) (§6.1.3). This lived only as a Julia expression in WorldModel/src/Beliefs.jl
    # with `lambda = 0.1` as a keyword default, while the ECAN side of the same tree already had its
    # decay factor as a named atom. Both the curve and the rate are policy an evolutionary search should
    # be free to vary, so both are atoms now.
    @test res("(BeliefDecayRate)") == "0.1"
    @test parse(Float64, res("(DecayedConfidence 1.0 0.0 0.0 (BeliefDecayRate))")) ≈ 1.0          # t = t₀
    @test parse(Float64, res("(DecayedConfidence 1.0 0.0 10.0 (BeliefDecayRate))")) ≈
        exp(-1.0)
    @test parse(Float64, res("(DecayedConfidence 0.9 5.0 25.0 (BeliefDecayRate))")) ≈
        0.9 * exp(-2.0)
    @test parse(Float64, res("(DecayedConfidence 1.0 0.0 10.0 0.0)")) ≈ 1.0                       # λ=0 ⇒ no decay
    # monotone non-increasing in t, and it never reaches zero (a decayed belief is weak, never refuted)
    let ds = [
            parse(
                Float64, res("(DecayedConfidence 1.0 0.0 $(float(t)) (BeliefDecayRate))")
            ) for t in 0:5:40
        ]
        @test issorted(ds; rev=true)
        @test all(>(0.0), ds)
    end
end
