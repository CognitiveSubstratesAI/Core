# test_pln_factor_graph.jl
# ─────────────────────────────────────────────────────────────────────────────
# Substrate-native PLN factor-graph forward chain (lib/pln/pln_factor_graph.metta),
# differentially validated against the Julia oracle (MorkSupercompiler PLNDemand.jl
# `forward_supply`) on the §6.1 Mammal/Lassie worked example.
#
# Graph: Collie(A) →[f1:hmp] Dog(B) →[f2:hmp] Mammal(C), with conclusion-first `produces`
# adjacency. Oracle goldens: B=(0.9405, 0.76), C=(0.893475, 0.456).

using Test
using MeTTaCore.Minimal
using MeTTaCore.Minimal.StandardMeTTa

@testset "PLN factor graph — forward supply (§6.1 Mammal/Lassie vs oracle)" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    # The Mammal/Lassie graph as atoms (conclusion-first schema). Leaves carry messages;
    # B and C are computed.
    graph = """
    (message A  (stv 0.95 0.95))
    (message AB (stv 0.99 0.80))
    (message BC (stv 0.95 0.60))
    (factor f1 hmp (premises A AB) (conclusion B))
    (factor f2 hmp (premises B BC) (conclusion C))
    (produces B f1)
    (produces C f2)
    """
    load_metta!(sp, graph)

    # Differential goldens vs the oracle (exact Core arithmetic; deterministic products).
    asserts = """
    !(assertEqual (supply A) (stv 0.95 0.95))
    !(assertEqual (supply B) (stv 0.9405 0.76))
    !(assertEqual (supply C) (stv 0.8934749999999999 0.45599999999999996))
    """
    rs = load_metta!(sp, asserts)
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    @test isempty(errs)
    @test length(rs) == 3
end
