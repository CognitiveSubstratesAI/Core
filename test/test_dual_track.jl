# Dual-track unified entry (src/standard/DualTrack.jl) — mc_run auto-dispatches to the right lane.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "dual-track unified entry (mc_run)" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"

    @testset "auto-dispatch by program form" begin
        # (~> …) → rewrite lane
        r = mc_run(MC.new_core_space(), facts, raw"(~> (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        @test r.lane == :rewrite
        @test r.results == ["(trans 0 2)", "(trans 1 3)"]

        # (def …) → pipeline lane
        r2 = mc_run(MC.new_core_space(), facts, raw"(def s () (match (edge $x $y) (emit (reach $x $y))))")
        @test r2.lane == :pipeline
        @test "(reach 0 1)" in r2.results

        # (theory …) → theory lane (last theory = TransGraph), saturate → full closure
        prog = raw"""
        (theory Graph () (rewrites (~> (edge $x $y) (path $x $y))))
        (theory TransGraph (extends Graph) (rewrites (~> (, (path $x $y) (edge $y $z)) (path $x $z))))
        """
        r3 = mc_run(MC.new_core_space(), facts, prog; saturate = true)
        @test r3.lane == :theory
        @test "(path 0 3)" in r3.results

        # otherwise → direct lane (MM2 / !(match …))
        r4 = mc_run(MC.new_core_space(), facts, raw"!(match &self (edge $x $y) (e $x $y))")
        @test r4.lane == :direct
        @test !isempty(r4.results.matched)               # the route bridged the !(match …)
    end

    @testset "mode override + theory= selection" begin
        # force the rewrite lane to fixpoint
        il = raw"""
        (~> (edge $x $y) (path $x $y))
        (~> (, (path $x $y) (edge $y $z)) (path $x $z))
        """
        r = mc_run(MC.new_core_space(), facts, il; mode = :rewrite, saturate = true)
        @test r.lane == :rewrite && "(path 0 3)" in r.results

        # theory=NAME picks the base theory → only one-hop, no closure
        prog = raw"""
        (theory Graph () (rewrites (~> (edge $x $y) (path $x $y))))
        (theory TransGraph (extends Graph) (rewrites (~> (, (path $x $y) (edge $y $z)) (path $x $z))))
        """
        r2 = mc_run(MC.new_core_space(), facts, prog; theory = "Graph")
        @test r2.lane == :theory
        @test "(path 0 1)" in r2.results && !("(path 0 3)" in r2.results)
    end
end
