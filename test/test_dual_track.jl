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

    @testset "saturation guard premises — comparison filters (Phase 1)" begin
        # A comparison premise (`< > <= >= == !=`) in a saturation rule body is EVALUATED as a guard
        # (filter), not looked up as a fact (a `(< $x 3)` premise has no `(< …)` fact, so pre-fix it
        # silently blocked the rule). Semantics mirror GROUNDED_REGISTRY (numbers parse as Syms whose
        # text is read as Float64). Guards bind no vars / add no facts ⇒ always-terminating filters.
        facts = "(num 1)\n(num 2)\n(num 3)\n(num 5)"
        der(cs, p) = sort([strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n')
                           if startswith(strip(l), "($p ")])
        sat(rule) = (cs = MC.new_core_space();
                     mc_run(cs, facts, rule; supercompile = true, sc_opts = MC.SCOptions(saturate = true)); cs)

        # (a) `<` fires AND filters to the in-range subset (proves the guard is evaluated, not looked up)
        @test der(sat(raw"(==> (, (num $x) (< $x 3)) (small $x))"), "small") == ["(small 1)", "(small 2)"]
        # (b) `<=` includes the boundary — distinct from `<` (precise boundary semantics)
        @test der(sat(raw"(==> (, (num $x) (<= $x 3)) (le $x))"), "le") == ["(le 1)", "(le 2)", "(le 3)"]
        # (c) `!=` (IR-layer guard, no GROUNDED_REGISTRY counterpart) drops exactly the equal one
        @test der(sat(raw"(==> (, (num $x) (!= $x 3)) (keep $x))"), "keep") == ["(keep 1)", "(keep 2)", "(keep 5)"]
        # (d) two conjoined guards form a range: 1 < x <= 3 ⇒ {2,3}
        @test der(sat(raw"(==> (, (num $x) (> $x 1) (<= $x 3)) (mid $x))"), "mid") == ["(mid 2)", "(mid 3)"]
        # (e) metamorphic order-invariance (Vibe §12.1): reversed fact order ⇒ identical fixpoint
        csR = MC.new_core_space()
        mc_run(csR, "(num 5)\n(num 3)\n(num 2)\n(num 1)", raw"(==> (, (num $x) (< $x 3)) (small $x))";
               supercompile = true, sc_opts = MC.SCOptions(saturate = true))
        @test der(csR, "small") == ["(small 1)", "(small 2)"]
    end

    @testset "saturation arithmetic premises + termination (Phase 2)" begin
        # A 3-arg `(op a b c)` premise (`+ - * / %`) BINDS its output c from bound inputs (the moded
        # lowering of `(= c (op a b))`; matches GROUNDED_REGISTRY: Float64 then Int-narrowed). A value-
        # generating rule needs a bounding comparison guard to terminate; an unbounded one is truncated
        # at the round cap with a warning (the homeomorphic-embedding whistle's pragmatic stand-in).
        der(cs, p) = sort([strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n')
                           if startswith(strip(l), "($p ")])
        runr(data, rule) = (cs = MC.new_core_space();
                            mc_run(cs, data, rule; supercompile = true, sc_opts = MC.SCOptions(saturate = true)); cs)

        # (a) bounded counter terminates via the (< $n 5) guard; `(+ $n 1 $m)` binds the next value
        c = runr("(count 0)", raw"(==> (, (count $n) (< $n 5) (+ $n 1 $m)) (count $m))")
        @test der(c, "count") == ["(count 0)", "(count 1)", "(count 2)", "(count 3)", "(count 4)", "(count 5)"]

        # (b) arithmetic binds the output, Int-narrowed (GROUNDED_REGISTRY parity): $y = $x + 10
        r = runr("(val 1)\n(val 2)", raw"(==> (, (val $x) (+ $x 10 $y)) (r $x $y))")
        @test der(r, "r") == ["(r 1 11)", "(r 2 12)"]

        # (c) CHECK mode — output already bound: keep iff consistent (2+2==4 kept, 2+2≠5 dropped)
        d = runr("(p 2 4)\n(p 2 5)", raw"(==> (, (p $x $y) (+ $x $x $y)) (dbl $x))")
        @test der(d, "dbl") == ["(dbl 2)"]

        # (d) UNBOUNDED generating rule still TERMINATES via the round-cap whistle (would hang without it).
        # The cap is KBSaturation.saturate!(; max_rounds=1000): one new (c k) per round ⇒ (c 0)..(c 1000)
        # = 1001 atoms. Bound by the cap (not a hang) rather than an exact count so a cap change won't nag.
        u = runr("(c 0)", raw"(==> (, (c $n) (+ $n 1 $m)) (c $m))")
        nc = length(der(u, "c"))
        @test 2 <= nc <= 1001           # produced a capped prefix and returned — did not hang
    end

    @testset "saturation stratified negation-as-failure (NAF)" begin
        # A `(not (p …))` premise succeeds iff no fact matches `p` — sound under STRATIFIED evaluation
        # (negated predicate is in a strictly-lower, completed stratum). Canonical case: a node is a
        # `source` iff nothing reaches it — needs `reachable` fully derived (stratum 0) before `source`
        # (stratum 1) tests `(not (reachable $x))`.
        der(cs, p) = sort([strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n')
                           if startswith(strip(l), "($p ")])
        facts = "(node a)\n(node b)\n(node c)\n(edge a b)\n(edge b c)"
        rules = raw"(==> (edge $x $y) (reachable $y))" * "\n" *
                raw"(==> (, (node $x) (not (reachable $x))) (source $x))"
        cs = MC.new_core_space()
        mc_run(cs, facts, rules; supercompile = true, sc_opts = MC.SCOptions(saturate = true))
        @test der(cs, "reachable") == ["(reachable b)", "(reachable c)"]   # stratum 0 closure
        @test der(cs, "source")    == ["(source a)"]                       # NAF over completed `reachable`

        # non-stratifiable (recursion through negation) falls back to flat saturation + warns — no hang/crash
        ns = raw"(==> (not (q a)) (p a))" * "\n" * raw"(==> (not (p a)) (q a))"
        cs2 = MC.new_core_space()
        mc_run(cs2, "(seed s)", ns; supercompile = true, sc_opts = MC.SCOptions(saturate = true))
        @test "(seed s)" in [strip(l) for l in split(MORK.space_dump_all_sexpr(cs2.inner), '\n')]  # terminated
    end

    @testset "direct lane: interpreter fallback for deferred bangs (fastlane-first)" begin
        # Design §5 R7 lane 3 / MeTTa-spec §4: a `!`-atom the ZAM lane cannot serve must still be
        # EVALUATED — on the interpreter, over the same program. Before this, `deferred` was a dead-end.
        fibp = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n!(fib 2)"

        # (a) fib: rule stays off the MM2 kernel (per design), bang answered by the fallback
        cs = MC.new_core_space()
        r = mc_run(cs, "", fibp)
        @test r.lane == :direct
        @test r.results.n_exec == 0 && r.results.deferred == ["(fib 2)"]   # routing record unchanged
        @test r.results.evaluated == [("(fib 2)", ["1"])]                  # …but the bang is SERVED
        @test MORK.space_val_count(cs.inner) == 1   # scratch-Space eval — MORK space holds only the rule

        # (b) servable class: exec fires on the ZAM (substrate reduction) AND the bang gets an answer
        wr = raw"(= (wrapit $x) (wrapped $x))" * "\n!(wrapit a)"
        cs2b = MC.new_core_space()
        r2 = mc_run(cs2b, "(wrapit a)", wr)
        @test r2.results.n_exec == 1                                        # rule lowered to a ZAM exec
        dump2 = [strip(l) for l in split(MORK.space_dump_all_sexpr(cs2b.inner), '\n')]
        @test "(wrapped a)" in dump2                                        # …which fired at the substrate
        @test ("(wrapit a)", ["(wrapped a)"]) in r2.results.evaluated       # and the bang is answered

        # (c) grounded arith bang (the canonical deferred example from the router tests)
        cs3 = MC.new_core_space()
        r3 = mc_run(cs3, "", "!(+ 1 2)")
        @test r3.results.evaluated == [("(+ 1 2)", ["3"])]

        # (d) fallback=:none reproduces pure-routing behavior (empty evaluated, deferred intact)
        cs4 = MC.new_core_space()
        r4 = mc_run(cs4, "", fibp; fallback = :none)
        @test r4.results.deferred == ["(fib 2)"] && isempty(r4.results.evaluated)

        # (e) fallback tabling (default ON): deep recursion is memoized — fib(17) answers fast — and
        #     the PROCESS-GLOBAL tabling state is snapshot/restored (no head leak, prior heads survive)
        MC.Interpreter.table!(:keepme_dt)                       # pre-existing global tabled head
        fib17 = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n!(fib 17)"
        cs5 = MC.new_core_space()
        t0 = time_ns(); r5 = mc_run(cs5, "", fib17); dt5 = (time_ns() - t0) / 1e9
        @test r5.results.evaluated == [("(fib 17)", ["1597"])]
        @test dt5 < 10.0                                        # untabled ≈ 18 s; tabled ≈ 0.1 s
        @test :fib ∉ MC.Interpreter._TABLED_HEADS               # scratch tabling did NOT leak
        @test :keepme_dt in MC.Interpreter._TABLED_HEADS        # pre-existing head restored
        delete!(MC.Interpreter._TABLED_HEADS, :keepme_dt); MC.Interpreter._table_reset!()  # tidy up

        # (f) fallback_table=false still answers (untabled path stays available)
        cs6 = MC.new_core_space()
        r6 = mc_run(cs6, "", fibp; fallback_table = false)
        @test r6.results.evaluated == [("(fib 2)", ["1"])]
    end

    @testset "supercompile lane: bang hygiene (non-match bangs answered, not corrupted)" begin
        # The SC frontend's byte parsers treat `!` as a symbol byte: a raw `!(fib 2)` used to be
        # CORRUPTED into two inert trie atoms (`!` + `(fib 2)`) and never evaluated. Now bangs are
        # stripped bang-aware before sc_execute!: non-match bangs → interpreter fallback; match-bangs
        # pass BARE (still lowered via §10.3, minus the stray-`!` trie pollution).
        dumpl(cs) = [strip(l) for l in split(MORK.space_dump_all_sexpr(cs.inner), '\n') if !isempty(strip(l))]

        # (a) non-match bang under supercompile: ANSWERED via fallback, and the trie is CLEAN
        fibp = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n!(fib 2)"
        cs = MC.new_core_space()
        r = mc_run(cs, "", fibp; supercompile = true)
        @test r.results.evaluated == [("(fib 2)", ["1"])]
        @test r.results.deferred == ["(fib 2)"]
        d = dumpl(cs)
        @test !("!" in d)             # corruption regression: no stray `!` symbol atom
        @test !("(fib 2)" in d)       # …and the query was NOT materialized as inert data
        @test r.results.sc isa MC.SCResult   # SC result still fully accessible

        # (b) match-bang under supercompile: still derives (§10.3), now WITHOUT the stray `!` atom
        facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"
        prog = raw"!(match &self (, (edge $x $y) (edge $y $z)) (path $x $z))"
        cs2 = MC.new_core_space()
        r2 = mc_run(cs2, facts, prog; supercompile = true)
        d2 = dumpl(cs2)
        @test "(path 0 2)" in d2 && "(path 1 3)" in d2   # §10.3 lowering still fires
        @test !("!" in d2)                                # stray-`!` pollution gone
        @test isempty(r2.results.deferred)                # match-bang was served by the SC lane
    end
end
