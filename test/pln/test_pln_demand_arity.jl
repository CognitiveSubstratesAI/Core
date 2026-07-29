# test_pln_demand_arity.jl
# ─────────────────────────────────────────────────────────────────────────────
# §4.1 ARITY-COMPLETE demand sweep: compute-demand-field! must thread demand through ALL 8
# rule families, not just the 2-premise ones (hmp/conj/disj). Before this, a backward chain
# through deduction/inversion/induction/abduction/negation stopped dead — the per-rule demand
# math existed (factor-demand-quad/triple/induction/abduction/single) but was never wired into
# the recursive sweep.
#
# Oracle = the per-rule factor-demand-* functions themselves (already unit-tested elsewhere):
# the sweep's materialised (dem premise _) must equal the tuple slot the standalone function
# returns. This is internal-consistency, not a hardcoded float — if the sweep mis-routes a
# premise or drops an arity, the cross-check fails.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.StandardMeTTa

_aerrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
function _ascen(graph, query, asserts)
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_factor_graph.metta"), String))
    load_metta!(sp, graph)
    load_metta!(sp, "!(compute-demand-field! $query)")
    load_metta!(sp, asserts)
end

@testset "§4.1 arity-complete demand sweep — all 8 rules thread through the sweep" begin
    @testset "deduction (4-premise) → premises match factor-demand-quad" begin
        g = "(message B (stv 0.8 0.8)) (message C (stv 0.7 0.7)) (message AB (stv 0.9 0.9)) (message BC (stv 0.85 0.85)) (factor fd deduction (premises B C AB BC) (conclusion G)) (produces G fd)"
        rs = _ascen(g, "G", """
        !(assertEqual (match &self (dem B \$d) \$d)  (dq-1 (factor-demand-quad G 1.0)))
        !(assertEqual (match &self (dem C \$d) \$d)  (dq-2 (factor-demand-quad G 1.0)))
        !(assertEqual (match &self (dem AB \$d) \$d) (dq-3 (factor-demand-quad G 1.0)))
        !(assertEqual (match &self (dem BC \$d) \$d) (dq-4 (factor-demand-quad G 1.0)))""")
        @test isempty(_aerrs(rs)); @test length(rs) == 4
    end
    @testset "inversion (3-premise) → premises match factor-demand-triple" begin
        g = "(message iA (stv 0.6 0.7)) (message iB (stv 0.8 0.7)) (message iBA (stv 0.9 0.7)) (factor fi inversion (premises iA iB iBA) (conclusion GI)) (produces GI fi)"
        rs = _ascen(g, "GI", """
        !(assertEqual (match &self (dem iA \$d) \$d)  (dt-1 (factor-demand-triple GI 1.0)))
        !(assertEqual (match &self (dem iB \$d) \$d)  (dt-2 (factor-demand-triple GI 1.0)))
        !(assertEqual (match &self (dem iBA \$d) \$d) (dt-3 (factor-demand-triple GI 1.0)))""")
        @test isempty(_aerrs(rs)); @test length(rs) == 3
    end
    @testset "induction (5-premise) → premises match factor-demand-induction" begin
        g = "(message uA (stv 0.7 0.7)) (message uB (stv 0.6 0.7)) (message uC (stv 0.65 0.7)) (message uBA (stv 0.8 0.7)) (message uBC (stv 0.75 0.7)) (factor fu induction (premises uA uB uC uBA uBC) (conclusion GU)) (produces GU fu)"
        rs = _ascen(g, "GU", """
        !(assertEqual (match &self (dem uA \$d) \$d)  (dn-1 (factor-demand-induction GU 1.0)))
        !(assertEqual (match &self (dem uBC \$d) \$d) (dn-5 (factor-demand-induction GU 1.0)))""")
        @test isempty(_aerrs(rs)); @test length(rs) == 2
    end
    @testset "abduction (5-premise) → premises match factor-demand-abduction (sens_A=0)" begin
        g = "(message aA (stv 0.7 0.7)) (message aB (stv 0.6 0.7)) (message aC (stv 0.65 0.7)) (message aAB (stv 0.8 0.7)) (message aCB (stv 0.75 0.7)) (factor fa abduction (premises aA aB aC aAB aCB) (conclusion GA)) (produces GA fa)"
        rs = _ascen(g, "GA", """
        !(assertEqual (match &self (dem aA \$d) \$d)  0.0)
        !(assertEqual (match &self (dem aB \$d) \$d)  (dn-2 (factor-demand-abduction GA 1.0)))
        !(assertEqual (match &self (dem aCB \$d) \$d) (dn-5 (factor-demand-abduction GA 1.0)))""")
        @test isempty(_aerrs(rs)); @test length(rs) == 3
    end
    @testset "negation (1-premise) in PLAIN sweep → premise matches factor-demand-single" begin
        g = "(message np (stv 0.4 0.5)) (factor fn negation (premises np) (conclusion GN)) (produces GN fn)"
        rs = _ascen(g, "GN", "!(assertEqual (match &self (dem np \$d) \$d) (ds-1 (factor-demand-single GN 1.0)))")
        @test isempty(_aerrs(rs)); @test length(rs) == 1
    end
    @testset "multi-hop: sweep recurses THROUGH a deduction factor into a premise's producer" begin
        # G <- deduction(B,C,AB,BC); B <- hmp(x1,x2). Demand must reach x1/x2 past deduction.
        g = "(message C (stv 0.7 0.7)) (message AB (stv 0.9 0.9)) (message BC (stv 0.85 0.85)) (message x1 (stv 0.9 0.9)) (message x2 (stv 0.8 0.8)) (factor fd deduction (premises B C AB BC) (conclusion G)) (factor fb hmp (premises x1 x2) (conclusion B)) (produces G fd) (produces B fb)"
        rs = _ascen(g, "G", """
        !(assertEqual (> (match &self (dem x1 \$d) \$d) 0.0) True)
        !(assertEqual (> (match &self (dem x2 \$d) \$d) 0.0) True)""")
        @test isempty(_aerrs(rs)); @test length(rs) == 2
    end
end
