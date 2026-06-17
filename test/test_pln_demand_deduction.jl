# test_pln_demand_deduction.jl
# ─────────────────────────────────────────────────────────────────────────────
# Substrate-native PLN demand adjoint for the 4-premise DEDUCTION rule (§3.3 Eq 1 on
# the §3.4 rows-only sens_deduction, eqs 8-11), differentially validated against the
# Julia oracle (PLNDemand.jl) at test/mgfw/test_pln_demand.jl:213.
#
# Graph: B,C,AB,BC (deliberately ASYMMETRIC) →[ded] AC (demanded 1.0).
# Oracle goldens: dem[B]=0.2, dem[C]=0.14118, dem[AB]=0.08889, dem[BC]=0.14118.
#
# THE ADVERSARIAL BITE (why this is the boundary case, not a value check):
# deduction is asymmetric, so the LINK demand dem[AB] must DIFFER from the TERM demand
# dem[B] — a circular/symmetric implementation, or a premise transposition in extraction,
# would land equal demand on them and pass a friendlier test. The second assert verifies
# NON-CIRCULARITY as an explicit PROPERTY: (== dem[AB] dem[B]) is False. The first assert
# (exact goldens) additionally fails under ANY premise transposition, since every value is
# position-specific.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

@testset "PLN demand adjoint — deduction (4-premise, §3.3 Eq1 vs oracle :213) + non-circular property" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    # :213 graph — premises in semantic role order (B C AB BC = premise_1..4).
    load_metta!(sp, """
    (message B  (stv 0.4 0.8))
    (message C  (stv 0.6 0.85))
    (message AB (stv 0.7 0.9))
    (message BC (stv 0.5 0.85))
    (factor ded deduction (premises B C AB BC) (conclusion AC))
    (produces AC ded)
    """)
    # accessors for the explicit non-circular property check
    load_metta!(sp, """
    (= (q-B  (dquad \$b \$c \$ab \$bc)) \$b)
    (= (q-AB (dquad \$b \$c \$ab \$bc)) \$ab)
    """)

    asserts = """
    !(assertEqual (factor-demand-quad AC 1.0) (dquad 0.19999999999999996 0.14117647058823535 0.08888888888888888 0.14117647058823535))
    !(assertEqual (== (q-AB (factor-demand-quad AC 1.0)) (q-B (factor-demand-quad AC 1.0))) False)
    """
    rs = load_metta!(sp, asserts)
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    @test isempty(errs)
    @test length(rs) == 2
end
