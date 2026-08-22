# test_pln_demand_adjoint.jl
# ─────────────────────────────────────────────────────────────────────────────
# Substrate-native PLN demand adjoint (§3.3 Eq 1), single-HMP-factor case,
# differentially validated against the Julia oracle (PLNDemand.jl) at
# test/mgfw/test_pln_demand.jl:252:
#     demand_adjoint(1.0, sens_hmp(0.8,0.9,0.7,0.85), (0.9,0.85)) = (0.09444…, 0.15)
#
# ADVERSARIAL DESIGN (the point of this piece): the adjoint is the transpose of the
# forward sensitivity, where a transposed index gives a plausible-but-wrong number.
# The inputs are deliberately ASYMMETRIC (sens (0.85,0.9) ≠, need (0.1,0.15) ≠), so a
# transposed adjoint yields (0.1, 0.14167) — DIFFERENT from the golden. The first
# assert therefore FAILS under a transpose; the second makes that discrimination
# explicit (a transposed computation is asserted NOT equal to the golden), so the
# test can never silently pass a transpose-invariant (i.e. broken) implementation.

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa

@testset "PLN demand adjoint — single HMP factor (§3.3 Eq1 vs oracle) + transpose discrimination" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(
        sp,
        read(
            joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_factor_graph.metta"), String
        )
    )

    # :252 single-factor graph: A=(0.8,0.9), AB=(0.7,0.85) → B (demanded 1.0).
    load_metta!(
        sp,
        """
(message A  (stv 0.8 0.9))
(message AB (stv 0.7 0.85))
(factor mp hmp (premises A AB) (conclusion B))
(produces B mp)
"""
    )

    # Adversarial negative control: the TRANSPOSED adjoint (each sens paired with the OTHER
    # premise's need). Test-only; proves the golden is not transpose-invariant.
    load_metta!(
        sp,
        """
(= (hmp-demand-T \$dv (stv \$sA \$cA) (stv \$sAB \$cAB))
   (let* ((\$senA (max \$sAB \$cAB)) (\$senAB (max \$sA \$cA)) (\$S (max \$senA \$senAB))
          (\$pA  (clampu (* (* \$dv (/ \$senAB \$S)) (- 1.0 \$cA))))
          (\$pAB (clampu (* (* \$dv (/ \$senA  \$S)) (- 1.0 \$cAB)))))
     (dpair \$pA \$pAB)))
"""
    )

    asserts = """
    !(assertEqual (factor-demand-pair B 1.0) (dpair 0.09444444444444441 0.15000000000000002))
    !(assertEqual (== (hmp-demand-T 1.0 (stv 0.8 0.9) (stv 0.7 0.85)) (dpair 0.09444444444444441 0.15000000000000002)) False)
    """
    rs = load_metta!(sp, asserts)
    errs = filter(
        r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs
    )
    @test isempty(errs)
    @test length(rs) == 2
end
