# test_pln_dtv.jl
# ─────────────────────────────────────────────────────────────────────────────
# §5 Layer-2 Distributional Truth Values (Beta DTVs in (μ,n) coords). Validated against
# the paper's §6.2 worked example (the Mammal/Lassie chain re-run with Beta DTVs):
#   p_A=Beta(19,2)=(μ,n)=(0.905,21), p_AB=(0.8,10), p_B=Beta(1,1)=(0.5,2), p_BC=(0.882,17).
# §6.2 exact intermediate values are the oracle:
#   need: A=0.047, AB=0.175, B=1.0, BC=0.069   (eq31)
#   forward μ_B = μ_A·μ_AB = 0.724              (the n_B the paper quotes as "≈12.3" is loose;
#                                                the moment-matched formula gives 12.815)
#   sensitivity at f2: ∂μ_C/∂μ_B=0.882, ∂μ_C/∂μ_BC=0.5
#   demand at f1 (boundary leaves, no threading divergence): dem_A=0.042, dem_AB=0.175
# Plus §5.7 STV-recovery: embedding an STV into a Beta and growing nc → μ→s, need→0.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

_derrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

@testset "§5 Layer-2 DTV — Beta truth values vs §6.2 worked example" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    rs = load_metta!(sp, """
    ;; §5.3 need (eq31) — all four match §6.2
    !(assertEqual (need-dtv (dtv 0.9047619047619048 21.0)) 0.04700061842918985)
    !(assertEqual (need-dtv (dtv 0.8 10.0)) 0.17454545454545453)
    !(assertEqual (need-dtv (dtv 0.5 2.0)) 1.0)
    !(assertEqual (need-dtv (dtv 0.8823529411764706 17.0)) 0.06920415224913495)
    ;; §5.6 forward product (f1): μ_B = μ_A·μ_AB = 0.724 (exact); n_B moment-matched
    !(assertEqual (dtv-mu (fwd-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))) 0.7238095238095239)
    !(assertEqual (dtv-n  (fwd-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))) 12.814960629921467)
    ;; §5.4 sensitivity at f2: (spair μ_BC μ_B) = (0.882, 0.5)
    !(assertEqual (sens2-hmp-dtv (dtv 0.5 2.0) (dtv 0.8823529411764706 17.0)) (spair 0.8823529411764706 0.5))
    ;; §5.5 demand adjoint at f1 (dv=dem_B=1.0; A,AB boundary leaves) → dem_A=0.042, dem_AB=0.175
    !(assertEqual
       (adjoint2-dtv 1.0 (sens2-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0)) (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))
       (dpair 0.04155844155844156 0.17454545454545453))
    """)
    @test isempty(_derrs(rs)); @test length(rs) == 8

    # §5.7 STV-recovery limit: high nc ⇒ μ→s, need→~0 (DTV reduces to STV semantics)
    rs2 = load_metta!(sp, """
    !(assertEqual (> (dtv-mu (stv->dtv 0.9 0.999 1000.0)) 0.8999) True)
    !(assertEqual (< (dtv-mu (stv->dtv 0.9 0.999 1000.0)) 0.9001) True)
    !(assertEqual (< (need-dtv (stv->dtv 0.9 0.999 1000.0)) 0.001) True)
    """)
    @test isempty(_derrs(rs2)); @test length(rs2) == 3
end
