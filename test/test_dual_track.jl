# Dual-track unified entry (src/standard/DualTrack.jl) — mc_run auto-dispatches to the right lane.
using MeTTaCore
const MC = MeTTaCore
using Test
using MORK   # space dump for the supercompiler-opt-in test

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

    @testset "direct lane: supercompiler opt-in (semantics-preserving)" begin
        # `supercompile=true` routes the Direct lane through the MorkSupercompiler instead of the lean
        # streaming calculus — closing the gap that the SC was only reachable via the MeTTa-IL saturate
        # lane. It must derive the SAME atoms (the SC is a planning/decomposition layer, not a different
        # semantics — just materializing, so opt-in).
        prog = raw"!(match &self (, (edge $x $y) (edge $y $z)) (path $x $z))"
        derived(cs) = sort([strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n')
                            if occursin("(path", l)])
        cs1 = MC.new_core_space(); r1 = mc_run(cs1, facts, prog)                       # streaming default
        cs2 = MC.new_core_space(); r2 = mc_run(cs2, facts, prog; supercompile = true)  # SC opt-in
        @test r1.lane == :direct && r2.lane == :direct
        @test !isempty(derived(cs1)) && derived(cs1) == derived(cs2)   # opt-in derives the same atoms
    end

    @testset "magic-sets goal-direction — shared SCOptions stage on BOTH lanes" begin
        # magic-sets is a pre-saturation rule transform in the shared SCPipeline → reachable from BOTH the
        # Direct lane (supercompile=true) and the MeTTa-IL saturate lane via the SAME `sc_opts`. It
        # goal-directs the bottom-up saturation (the bottom-up equivalent of top-down SLG tabling): only
        # facts relevant to the query are derived. Node 5→6 is unreachable from the seed 0 ⇒ pruned.
        edges = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)\n(edge 5 6)"
        paths0(cs) = sort([strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n')
                           if startswith(strip(l), "(path ")])
        msq = MC.SCOptions(saturate = true, use_magic_sets = true, magic_query = raw"(path 0 $y)", magic_bound = 0)

        # Direct lane: (==>) rules + supercompile=true
        dd = raw"(==> (edge $x $y) (path $x $y))" * "\n" * raw"(==> (, (path $x $y) (edge $y $z)) (path $x $z))"
        csd = MC.new_core_space(); mc_run(csd, edges, dd; supercompile = true, sc_opts = msq)
        @test paths0(csd) == ["(path 0 1)", "(path 0 2)", "(path 0 3)"]   # goal-directed (only from 0)

        # MeTTa-IL lane: (~>) rewrites + saturate=true — SAME goal-direction via the same sc_opts
        il = raw"(~> (edge $x $y) (path $x $y))" * "\n" * raw"(~> (, (path $x $y) (edge $y $z)) (path $x $z))"
        csi = MC.new_core_space(); mc_run(csi, edges, il; mode = :rewrite, saturate = true, sc_opts = msq)
        @test paths0(csi) == ["(path 0 1)", "(path 0 2)", "(path 0 3)"]   # IL lane reaches it too
    end

    @testset "magic-sets safety — falls back to full closure outside its sound fragment" begin
        # magic_sets_transform is the single-predicate / self-recursive / bound-FIRST fragment only.
        # Outside it (mutual recursion, non-first bound position) a naive magic transform would silently
        # DROP query-relevant answers — so it must fall back to FULL closure (correct, just un-directed).
        # These cases REQUEST magic-sets but must still derive the COMPLETE answer.
        dumpall(cs) = [strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]

        # (a) mutual recursion even↔odd: (even 4) needs (odd 3) needs (even 2)… cross-predicate.
        nums = "(succ 0 1)\n(succ 1 2)\n(succ 2 3)\n(succ 3 4)\n(even 0)"
        eo = raw"(==> (, (succ $m $n) (odd $m)) (even $n))" * "\n" *
             raw"(==> (, (succ $m $n) (even $m)) (odd $n))"
        cs1 = MC.new_core_space()
        mc_run(cs1, nums, eo; supercompile = true,
            sc_opts = MC.SCOptions(saturate = true, use_magic_sets = true, magic_query = "(even 4)", magic_bound = 0))
        @test "(even 4)" in dumpall(cs1)        # NOT dropped — fell back to full closure

        # (b) bound SECOND argument (path $x 3) → non-first position → fall back to full closure.
        edges = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"
        dd = raw"(==> (edge $x $y) (path $x $y))" * "\n" * raw"(==> (, (path $x $y) (edge $y $z)) (path $x $z))"
        cs2 = MC.new_core_space()
        mc_run(cs2, edges, dd; supercompile = true,
            sc_opts = MC.SCOptions(saturate = true, use_magic_sets = true, magic_query = raw"(path $x 3)", magic_bound = 1))
        d2 = dumpall(cs2)
        @test "(path 0 3)" in d2 && "(path 1 3)" in d2 && "(path 2 3)" in d2   # complete closure, nothing dropped
    end
end
