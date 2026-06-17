# test_pln_indabd.jl
# ─────────────────────────────────────────────────────────────────────────────
# The two hardest rules: induction + abduction (5-premise, rows-only), whose strength
# sensitivities are chain-rule compositions through an inversion intermediate
# (ind: sAB=sBA·sB/sA; abd: sBC=sCB·sC/sB), reusing the deduction strength partials.
# Differentially validated vs the Julia oracle; goldens GENERATED (fwd_*/sens_*/demand_adjoint),
# and every term hand-derived first so a match is understood, not reverse-engineered.
#
# DISCRIMINATING TESTS FIRST (where a 5-premise transcription error hides, and a friendly
# mid-range input would not catch it):
#  - Abduction sens_A = 0 (premise A is absent from the formula) ⇒ dem_A is EXACTLY 0, at
#    mid-range AND at the sB→0 singularity. A sign error or transposed term almost certainly
#    produces a nonzero A-demand, so this is the strongest catch.
#  - Singularity caps: ind sA→0 and abd sB→0 blow up the inversion intermediate; the cap
#    reshapes the NORMALIZER, so the whole distribution (not just one magnitude) changes —
#    these exact goldens fail under a missing/misplaced cap in the chain-rule composition.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

@testset "PLN rows-only — induction + abduction (5-premise chain-rule + singularities + sens_A=0) vs oracle" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    load_metta!(sp, """
    (message nA (stv 0.6 0.8))
    (message nB (stv 0.4 0.85))
    (message nC (stv 0.6 0.9))
    (message nBA (stv 0.5 0.85))
    (message nBC (stv 0.5 0.8))
    (factor indf induction (premises nA nB nC nBA nBC) (conclusion ACi))
    (produces ACi indf)
    (factor abdf abduction (premises nA nB nC nBA nBC) (conclusion ACa))
    (produces ACa abdf)
    (message nAs (stv 0.0001 0.8))
    (factor inds induction (premises nAs nB nC nBA nBC) (conclusion ACis))
    (produces ACis inds)
    (message nBs (stv 0.0001 0.85))
    (factor abds abduction (premises nA nBs nC nBA nBC) (conclusion ACas))
    (produces ACas abds)
    """)

    asserts = """
    !(assertEqual (factor-demand-abduction ACa 1.0) (dquint 0 0.08812800000000003 0.09999999999999998 0.08812800000000003 0.12484799999999996))
    !(assertEqual (factor-demand-abduction ACas 1.0) (dquint 0 0.15000000000000002 0.0002500250025002499 0.00044995499549954995 0.0005999399939993997))
    !(assertEqual (fwd-induction (stv 0.6 0.8) (stv 0.4 0.85) (stv 0.6 0.9) (stv 0.5 0.85) (stv 0.5 0.8)) (stv 0.611111111111111 0.5202000000000001))
    !(assertEqual (fwd-abduction (stv 0.6 0.8) (stv 0.4 0.85) (stv 0.6 0.9) (stv 0.5 0.85) (stv 0.5 0.8)) (stv 0.625 0.5202000000000001))
    !(assertEqual (factor-demand-induction ACi 1.0) (dquint 0.01666666666666666 0.08262000000000003 0.09999999999999998 0.08262000000000003 0.11704499999999997))
    !(assertEqual (factor-demand-induction ACis 1.0) (dquint 0.19999999999999996 0.0002082916666666666 0.0003331666666666666 9.999999999999999e-5 0.0006665333333333332))
    """
    rs = load_metta!(sp, asserts)
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    @test isempty(errs)
    @test length(rs) == 6
end
