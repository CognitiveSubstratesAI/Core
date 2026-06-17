# test_pln_demand_sweep.jl
# ─────────────────────────────────────────────────────────────────────────────
# Substrate-native PLN multi-factor demand SWEEP (§4.4 compute_demand_field): top-down
# BFS from the query via the conclusion-first `produces` index, demand threaded down
# across factors, the field materialised as `(dem node val)` atoms in the space.
#
# Validated against an INDEPENDENTLY GENERATED oracle golden — produced by running the
# Julia oracle's `forward_supply` then `compute_demand_field` on the §6.1 Mammal/Lassie
# graph (Collie→Dog→Mammal, 2 HMP factors). The golden is NOT hand-computed: a hand
# computation would share the implementation's forward-marginal-threading assumption and
# could agree on a wrong answer, so the bar is the oracle's own output:
#     dem[C]=1.0, dem[B]=0.24, dem[BC]=0.3960000000000001,
#     dem[A]=0.01200000000000001, dem[AB]=0.046060606060606045
#
# THREADING CONTROL (the multi-factor failure mode): the upstream factor f1's premises'
# demand must use dem[B]=0.24 (threaded from f2), NOT a fresh d_v=1.0. With threading,
# dem[A]=0.012; WITHOUT it, dem[A] would be 0.05. The last assert checks that the
# un-threaded recompute (factor-demand-pair on B with d_v=1.0 → 0.05) is NOT equal to the
# stored, threaded dem[A] — so the test fails if propagation drops the threading.
# (Confirmed independently: the oracle's demand-WITHOUT-forward gives dem[B]=1.0 vs 0.24 —
# the forward-marginal threading is load-bearing, and `supply` provides it here.)

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

@testset "PLN demand sweep — multi-factor (§4.4 vs generated oracle golden) + threading control" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    load_metta!(sp, """
    (message A  (stv 0.95 0.95))
    (message AB (stv 0.99 0.80))
    (message BC (stv 0.95 0.60))
    (factor f1 hmp (premises A AB) (conclusion B))
    (factor f2 hmp (premises B BC) (conclusion C))
    (produces B f1)
    (produces C f2)
    """)
    load_metta!(sp, "!(compute-demand-field! C)")   # materialise the field as (dem node val) atoms

    asserts = """
    !(assertEqual (match &self (dem C \$d) \$d) 1.0)
    !(assertEqual (match &self (dem B \$d) \$d) 0.24)
    !(assertEqual (match &self (dem BC \$d) \$d) 0.3960000000000001)
    !(assertEqual (match &self (dem A \$d) \$d) 0.01200000000000001)
    !(assertEqual (match &self (dem AB \$d) \$d) 0.046060606060606045)
    !(assertEqual (== (dp-1 (factor-demand-pair B 1.0)) (match &self (dem A \$d) \$d)) False)
    """
    rs = load_metta!(sp, asserts)
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    @test isempty(errs)
    @test length(rs) == 6
end
