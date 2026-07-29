# test_pln_lc4_domain_guard.jl
# ─────────────────────────────────────────────────────────────────────────────
# L-C4 regression lock: four PLN truth formulas (Induction, Abduction,
# equivalenceToImplication, TransitiveSimilarityStrength) emitted OUT-OF-DOMAIN strengths
# (s ∉ [0,1]) when fed probabilistically-inconsistent input TVs — the strength ran through the
# division-by-margin terms with no domain precondition (only Truth_Deduction carried
# `conditional-probability-consistency`). The out-of-domain value was then SILENTLY LAUNDERED by
# Truth_Revision's downstream `(min 1.0 $f)` clamp into a confident belief.
#
# THE FIX (guard-coverage, NOT a formula change — the four bodies are byte-identical to canonical
# trueagi-io/PLN + PeTTa): a `valid-strength` [0,1] predicate wraps each formula AT ORIGIN, rejecting
# the out-of-domain inference (→ (stv 1 0), confidence-0 ⇒ zero weight in revision; → (empty) prune
# for the strength helper). The opposite of clamping: the poison value is DISCARDED, not kept.
#
# Found by a reflective (understand→design→adversarially-verify) audit of our PLN against Goertzel's
# ωPLN law catalogue; the ωPLN law realized here = "durable strength is a probability in [0,1];
# reject-not-promote." (The ωPLN status-as-TYPE contract is orthogonal + deferred — its seam is
# welded to patham9's kernel.) NOTE: hyperon-experimental has no upstream test on these four rules,
# so the oracle is the [0,1] invariant + the in-file doctest values as the regression baseline.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.StandardMeTTa

@testset "PLN L-C4 — out-of-domain truth strengths rejected at origin (not clamped)" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_core_logic.metta"), String))
    res(expr) = strip(join(string.(load_metta!(sp, "!$expr")), " | "))

    # (0) the guard predicate itself
    @test res("(valid-strength 0.5)")  == "True"
    @test res("(valid-strength 3.7)")  == "False"
    @test res("(valid-strength -0.8)") == "False"    # catches s<0, which the asymmetric (min 1.0 …) clamp misses

    # (1) OUT-OF-DOMAIN — must now be REJECTED at origin (was (stv 10.0 …)/(stv 3.667 …)/(stv 6.5 …)/(stv -0.8 …))
    @test res("(Truth_Abduction (stv 0.5 0.5) (stv 0.1 0.5) (stv 1.0 0.5) (stv 1.0 0.5) (stv 1.0 0.5))") == "(stv 1 0)"  # s=10 (term1 diverges as sB→0)
    @test res("(Truth_equivalenceToImplication (stv 0.1 0.5) (stv 1.0 0.5) (stv 0.5 0.5))") == "(stv 1 0)"              # s=3.667 (sim2inh factor explodes for small As)
    @test res("(Truth_Induction (stv 0.1 0.5) (stv 0.5 0.5) (stv 0.1 0.5) (stv 0.9 0.5) (stv 0.9 0.5))") == "(stv 1 0)" # s=6.5
    @test res("(Truth_Induction (stv 0.9 0.5) (stv 0.5 0.5) (stv 0.0 0.5) (stv 0.1 0.5) (stv 0.9 0.5))") == "(stv 1 0)" # s<0

    # (2) TransitiveSimilarityStrength — out-of-domain / div-by-zero → PRUNED (empty), no Inf/NaN leak
    @test res("(TransitiveSimilarityStrength 0.1 0.9 0.9 0.9 0.9)") == ""   # >1
    @test res("(TransitiveSimilarityStrength 0.0 0.9 0.9 0.9 0.9)") == ""   # div-by-zero (was Inf/NaN via bare `/`, now /safe-hardened)
    @test res("(Truth_transitiveSimilarity (stv 0.1 0.5) (stv 0.9 0.5) (stv 0.9 0.5) (stv 0.9 0.5) (stv 0.9 0.5))") == ""

    # (3) VALID inputs PRESERVED — no over-rejection; /safe is a no-op on non-zero denominators
    @test startswith(res("(Truth_Deduction (stv 0.8 0.9) (stv 0.7 0.85) (stv 0.6 0.8) (stv 0.7 0.9) (stv 0.6 0.85))"), "(stv 0.6")       # deduction untouched
    @test startswith(res("(Truth_transitiveSimilarity (stv 0.6 0.7) (stv 0.5 0.8) (stv 0.7 0.9) (stv 0.8 0.85) (stv 0.6 0.8))"), "(stv 0.669")  # KEY: /safe no-op → doctest 0.6694 unchanged
    @test startswith(res("(Truth_equivalenceToImplication (stv 0.8 0.9) (stv 0.6 0.9) (stv 0.5 0.9))"), "(stv 0.583")
    @test startswith(res("(Truth_Induction (stv 0.8 0.5) (stv 0.5 0.5) (stv 0.6 0.5) (stv 0.5 0.5) (stv 0.5 0.5))"), "(stv 0.63")         # proper stv, NOT (stv 1 0)
    @test startswith(res("(Truth_Abduction (stv 0.5 0.5) (stv 0.6 0.5) (stv 0.5 0.5) (stv 0.5 0.5) (stv 0.5 0.5))"), "(stv 0.52")        # proper stv, NOT (stv 1 0)
end
