# test_pln_gated.jl
# ─────────────────────────────────────────────────────────────────────────────
# §4.7 gated demand expansion: the demand sweep + a gate that HALTS recursion past a premise
# whose demand < tau, but RETAINS it in the `active` set (Design Commitment #2) unless
# retain_boundary is off — a high-confidence boundary has tiny demand yet still SEEDS forward
# supply, so dropping it would starve the marginal.
#
# This test asserts the ACTIVE-SET behavior, which is the actual content of §4.7 (gate + DC#2),
# rather than exact demand values: the substrate-native walk threads forward marginals via
# `supply`, so its dem values differ from the oracle's gated test (which reads placeholder
# messages) — but the gate DECISION is identical (a sub-tau boundary halts either way), and the
# active-set membership is the load-bearing property. Verified against the Julia oracle's
# gated_demand_expansion scenarios (test_pln_demand.jl:439/450/490).
#
# Scenarios:
#  T1  tau=0    — nothing halts ⇒ every node active (no-op gate).
#  T3  tau=0.20 — Mammal/Lassie: A and A→B have sub-tau demand and HALT, but DC#2 RETAINS them.
#  T3* retain=False — the same halt now DROPS them (DC#2 is load-bearing).
#  T2  tau=0.20 — Q←conj(X,Y): X high-conf⇒low demand PRUNED (Xn/fx out), Y low-conf⇒high demand
#                 KEPT (Yn in). Mixes conjunction (2-premise) + negation (1-premise) ⇒ arity dispatch.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

const _GFG = joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta")
const _GML = "(message A (stv 0.95 0.95)) (message AB (stv 0.99 0.80)) (message BC (stv 0.95 0.60)) (factor f1 hmp (premises A AB) (conclusion B)) (factor f2 hmp (premises B BC) (conclusion C)) (produces B f1) (produces C f2)"
const _GG2 = "(message X (stv 0.9 0.95)) (message Y (stv 0.6 0.3)) (message Xn (stv 0.1 0.95)) (message Yn (stv 0.4 0.3)) (factor f1 conjunction (premises X Y) (conclusion Q)) (factor fx negation (premises Xn) (conclusion X)) (factor fy negation (premises Yn) (conclusion Y)) (produces Q f1) (produces X fx) (produces Y fy)"

_gerrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
function _gscen(graph, call, asserts)
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(_GFG, String)); load_metta!(sp, graph)
    load_metta!(sp, call); load_metta!(sp, asserts)
end

@testset "§4.7 gated demand expansion — active-set semantics vs oracle" begin
    @testset "T1 no-op (tau=0 ⇒ all active)" begin
        rs = _gscen(_GML, "!(gated-demand-field! C 0.0 True)",
            "!(assertEqual (is-active A) True)\n!(assertEqual (is-active BC) True)\n!(assertEqual (is-active f1) True)")
        @test isempty(_gerrs(rs)); @test length(rs) == 3
    end
    @testset "T3 DC#2 retains halted boundaries" begin
        rs = _gscen(_GML, "!(gated-demand-field! C 0.20 True)",
            "!(assertEqual (is-active A) True)\n!(assertEqual (is-active AB) True)")
        @test isempty(_gerrs(rs)); @test length(rs) == 2
    end
    @testset "T3-off retain=False drops them (DC#2 load-bearing)" begin
        rs = _gscen(_GML, "!(gated-demand-field! C 0.20 False)",
            "!(assertEqual (is-active A) False)\n!(assertEqual (is-active AB) False)")
        @test isempty(_gerrs(rs)); @test length(rs) == 2
    end
    @testset "T2 prune low branch, keep high (+ arity dispatch)" begin
        rs = _gscen(_GG2, "!(gated-demand-field! Q 0.20 True)",
            "!(assertEqual (is-active Y) True)\n!(assertEqual (is-active Yn) True)\n!(assertEqual (is-active Xn) False)\n!(assertEqual (is-active fx) False)")
        @test isempty(_gerrs(rs)); @test length(rs) == 4
    end
    # T-DAG  §4.4 max-join under gating: diamond C<-f0(P,Q); P<-f1(S,X); Q<-f2(S,Y); S shared.
    # S reached via 2 paths must keep ONE (dem S _) atom = max over paths, and the gated walk
    # must TERMINATE (monotone-increase recursion guard). tau=0 ⇒ full expansion, S active.
    _GDIA = "(message S (stv 0.9 0.5)) (message X (stv 0.8 0.9)) (message Y (stv 0.7 0.3)) (factor f1 hmp (premises S X) (conclusion P)) (factor f2 hmp (premises S Y) (conclusion Q)) (factor f0 hmp (premises P Q) (conclusion C)) (produces P f1) (produces Q f2) (produces C f0)"
    @testset "T-DAG max-join under gating: dedup + max + terminates" begin
        rs = _gscen(_GDIA, "!(gated-demand-field! C 0.0 True)",
            "!(assertEqual (size-atom (collapse (match &self (dem S \$d) \$d))) 1)\n" *
            "!(assertEqual (is-active S) True)\n" *
            "!(assertEqual (match &self (dem S \$d) \$d) (max (dp-1 (factor-demand-pair P (match &self (dem P \$e) \$e))) (dp-1 (factor-demand-pair Q (match &self (dem Q \$g) \$g)))))")
        @test isempty(_gerrs(rs)); @test length(rs) == 3
    end
    # T-ARITY  §4.1 arity-complete gated path: a deduction (4-premise) factor must expand in
    # the GATED walk too (premises get demand + active), and recursion must reach a premise's
    # producer past the deduction. Demand cross-checked against factor-demand-quad.
    @testset "T-ARITY gated path threads deduction (4-premise) + multi-hop" begin
        gded = "(message B (stv 0.8 0.8)) (message C (stv 0.7 0.7)) (message AB (stv 0.9 0.9)) (message BC (stv 0.85 0.85)) (factor fd deduction (premises B C AB BC) (conclusion G)) (produces G fd)"
        rs = _gscen(gded, "!(gated-demand-field! G 0.0 True)",
            "!(assertEqual (match &self (dem B \$d) \$d) (dq-1 (factor-demand-quad G 1.0)))\n" *
            "!(assertEqual (is-active C) True)\n!(assertEqual (is-active BC) True)")
        @test isempty(_gerrs(rs)); @test length(rs) == 3
        gmh = "(message C (stv 0.7 0.7)) (message AB (stv 0.9 0.9)) (message BC (stv 0.85 0.85)) (message x1 (stv 0.9 0.9)) (message x2 (stv 0.8 0.8)) (factor fd deduction (premises B C AB BC) (conclusion G)) (factor fb hmp (premises x1 x2) (conclusion B)) (produces G fd) (produces B fb)"
        rs2 = _gscen(gmh, "!(gated-demand-field! G 0.0 True)", "!(assertEqual (is-active x1) True)")
        @test isempty(_gerrs(rs2)); @test length(rs2) == 1
    end
end
