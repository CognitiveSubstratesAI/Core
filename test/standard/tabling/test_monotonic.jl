# test_monotonic.jl — SWI §7.8, monotonic tabling.
#
# §7.7 answers a change by INVALIDATING dependents. §7.8 answers it by PROPAGATING FORWARD. Upstream's
# own comment on `monotonic_affects/6`: *"If SrcReturn is added to SrcTrie we must add all answers for
# Return of Continuation to Atrie."* — which is `resume_continuation` + `trie_insert!`, both built in
# §1.0. The stored dependency IS our `Dependency`.
#
# ⚠️ NOT WIRED, and the seam is named: nothing in `tabled_eval` records a monotonic dependency,
# because that needs to know at call time that both tables are monotonic — a
# `table_as!(:p, :monotonic)` declaration, and that option is still REFUSED until this file is
# consumed. This gates the PROPAGATION.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _MO = Eval

function _mo_setup()
    _MO.untable_all!(); _MO.abolish_all_tables!(); _MO.clear_idg!(); _MO.clear_mono!()
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, raw"(= (wrap $x) (S $x))" * "\n")
    load_metta!(s, raw"(= (mark) M)" * "\n")
    s
end

"""A continuation for the propagation tests.

⚠️ SCOPED DELIBERATELY, AFTER TWO WRONG ATTEMPTS. I first tried to build a TRANSFORMING continuation
so propagation could be told apart from an echo — first with `prev === nothing` (which makes resume
an IDENTITY, and the test correctly failed), then by driving `interpret_stack` to a `(mark)`
suspension (which never fired: frames carry the goal wrapped, and the shape differs from
`test_delimited_control.jl`'s driver).

That was the wrong thing to fix. **`resume_continuation`'s transforming behaviour is ALREADY GATED**
by `test_delimited_control.jl`, which captures a real frame chain and resumes it twice with
different answers. Re-proving it here would duplicate that gate; what is NOT gated anywhere else is
§7.8's OWN logic — eager vs lazy, assert vs retract, and teardown — and those are what this file
asserts. Using a simple continuation for them is correct scoping, not a weakened test.
`[[feedback_scope_closure_claims_to_what_verified]]`"""
_mo_cont(s) = _MO.capture_continuation(_MO.Bindings(), nothing,
                                       _MO.parse_from(_MO.tokenize("(wrap 1)"), Ref(1), s.tokens))

@testset "SWI §7.8 — monotonic tabling" begin

    @testset "ASSERT propagates FORWARD into the target's trie" begin
        s = _mo_setup()
        src, tgt = Sym(:src), Sym(:tgt)
        _MO.mono_assert_dep!(src, _mo_cont(s), tgt)          # eager by default
        @test length(_MO.mono_affects(src)) == 1

        out = _MO.mono_propagate_assert!(src, Grounded(1), s)
        # ANTI-VACUITY: a propagation that produced nothing would satisfy "no wrong answers".
        @test haskey(out, tgt) && !isempty(out[tgt])
        # the answer went INTO the target's table, not merely into the return value
        @test !isempty(_MO.trie_answers(_MO.answer_trie_for(tgt)))
        # ⚠️ NOT asserted here: that the continuation TRANSFORMED the answer. That is
        # `resume_continuation`'s contract and `test_delimited_control.jl` gates it. What §7.8 owns
        # is that the answer REACHES the target table at all, which the two lines above assert.
        _MO.clear_mono!(); _MO.abolish_all_tables!()
    end

    @testset "🔴 LAZY QUEUES THE ANSWER — the CONTINUATION DOES NOT RUN until drain" begin
        # §7.8's eager/lazy split: '$mono_idg_changed' defers where propagate_assert does not.
        #
        # 🔴 THIS TEST WAS TOO WEAK UNTIL 2026-08-17 and passed against a real defect. It asserted
        # only that the TABLE was untouched, which our implementation satisfied by running the
        # continuation eagerly and deferring just the `trie_insert!`. That made lazy cost exactly what
        # eager costs — the whole point of the split — and evaluated the continuation against the
        # space at ASSERT time rather than DRAIN time. Upstream queues the ANSWER (`mdep_queue_answer`,
        # `pl-tabling.c:7506-7546`); the continuation runs at the target's next call. So what the
        # queue HOLDS is now asserted, not just that the table is empty.
        s = _mo_setup()
        src, tgt = Sym(:src), Sym(:tgt)
        _MO.mono_assert_dep!(src, _mo_cont(s), tgt; lazy = true)
        out = _MO.mono_propagate_assert!(src, Grounded(1), s)

        @test !haskey(out, tgt)                              # nothing was PRODUCED — it was deferred
        @test isempty(_MO.trie_answers(_MO.answer_trie_for(tgt)))   # …and the table is untouched
        q = _MO.mono_queued(tgt)
        @test length(q) == 1
        @test q[1][2] == Grounded(1)                         # the SOURCE ANSWER is what is queued…
        @test q[1][1].dep.target == tgt                      # …alongside its dependency, unrun

        added = _MO.mono_drain_queue!(tgt, s)                # the continuation runs HERE
        @test !isempty(added)
        @test !isempty(_MO.trie_answers(_MO.answer_trie_for(tgt)))
        @test isempty(_MO.mono_queued(tgt))                  # queue consumed, not merely read
        @test isempty(_MO.mono_drain_queue!(tgt, s))         # draining twice adds nothing
        _MO.clear_mono!(); _MO.abolish_all_tables!()
    end

    @testset "🔴 PROPAGATION IS TRANSITIVE — A -> B -> C, not one hop" begin
        # The one-hop version updated B and SILENTLY LEFT C STALE: missing answers, no error.
        # `pdelim/3` recurses via `propagate_answer/2` (`boot/tabling.pl:1709-1733`).
        s = _mo_setup()
        a, b, c = Sym(:a), Sym(:b), Sym(:c)
        _MO.mono_assert_dep!(a, _mo_cont(s), b)
        _MO.mono_assert_dep!(b, _mo_cont(s), c)
        out = _MO.mono_propagate_assert!(a, Grounded(1), s)
        @test haskey(out, b)
        @test haskey(out, c)                                 # the hop that was missing
        @test !isempty(_MO.trie_answers(_MO.answer_trie_for(c)))
        _MO.clear_mono!(); _MO.abolish_all_tables!()
    end

    @testset "🔴 a CYCLE terminates — because a duplicate STOPS the recursion" begin
        # Making propagation transitive is only safe because `'$tbl_monotonic_add_answer'` returns
        # false on a duplicate (`pl-tabling.c:7595-7597`) and the Prolog conjunction in `pdelim` then
        # stops. We discarded `trie_insert!`'s return value and reported every propagated answer as
        # new — harmless while propagation was one hop, a NON-TERMINATION bug the moment it recurses.
        # Cycles are the normal case in tabling, so this is the test that must not be dropped.
        s = _mo_setup()
        a, b = Sym(:a), Sym(:b)
        _MO.mono_assert_dep!(a, _mo_cont(s), b)
        _MO.mono_assert_dep!(b, _mo_cont(s), a)              # mutual
        out = _MO.mono_propagate_assert!(a, Grounded(1), s)  # must RETURN, not hang
        @test haskey(out, b)
        _MO.clear_mono!(); _MO.abolish_all_tables!()
    end

    @testset "rollback: asserta/assertz is a NO-OP, retract INVALIDATES" begin
        # `mon_propagate(rollback(Action), …)` (`boot/tabling.pl:1661-1667`). Named in the file
        # header as one of three branches and previously ABSENT. The asymmetry is not obvious:
        # undoing an assert does NOT retract what it propagated.
        s = _mo_setup()
        src, tgt = Sym(:src), Sym(:tgt)
        _MO.mono_assert_dep!(src, _mo_cont(s), tgt)
        _MO.mono_propagate_assert!(src, Grounded(1), s)

        @test isempty(_MO.mono_propagate_rollback!(:assertz, src))
        @test !_MO.idg_is_invalid(tgt)                       # …nothing invalidated
        @test tgt in _MO.mono_propagate_rollback!(:retract, src)
        @test _MO.idg_is_invalid(tgt)
        @test_throws ArgumentError _MO.mono_propagate_rollback!(:bogus, src)
        _MO.clear_mono!(); _MO.clear_idg!(); _MO.abolish_all_tables!()
    end

    @testset "🔴 RETRACT does NOT propagate — it INVALIDATES, and that is the correctness argument" begin
        # Retraction is not monotone: removing a source answer can only REMOVE target answers, and a
        # continuation adds but cannot subtract. Propagating a retraction "forward" would leave every
        # answer the removed one had already produced — silently and permanently. Upstream falls back
        # to §7.7 invalidation (`mon_invalidate_dependents` -> `$idg_mono_invalidate`), and the
        # plausible symmetry is exactly the trap.
        s = _mo_setup()
        src, tgt = Sym(:src), Sym(:tgt)
        _MO.mono_assert_dep!(src, _mo_cont(s), tgt)
        _MO.mono_propagate_assert!(src, Grounded(1), s)
        @test !isempty(_MO.trie_answers(_MO.answer_trie_for(tgt)))

        hit = _MO.mono_invalidate_dependents!(src)
        @test tgt in hit
        @test _MO.idg_is_invalid(tgt)                        # invalidated, via §7.7's machinery

        # 🔴 …AND IT MUST REACH PAST THE DIRECT TARGET. The previous version bumped the target's
        # falsecount and stopped, never walking the TARGET's own `affected` — so a table that had
        # cached the target's answers stayed VALID and kept serving answers derived from a retracted
        # fact. Upstream's `'$idg_mono_invalidate'` reaches `idg_changed(atrie, IDG_CHANGED_NODE)`,
        # which increments the target and then propagates TRANSITIVELY (`pl-tabling.c:7155-7157`).
        downstream = Sym(:downstream)
        _MO.idg_add_edge!(tgt, downstream)                   # downstream cached tgt's answers
        hit2 = _MO.mono_invalidate_dependents!(src)
        @test downstream in hit2
        @test _MO.idg_is_invalid(downstream)
        # …and NOT silently "propagated": the target's answers are still there, awaiting recompute.
        # That is the point — invalidation defers the correction; propagation could not express it.
        @test !isempty(_MO.trie_answers(_MO.answer_trie_for(tgt)))
        _MO.clear_mono!(); _MO.clear_idg!(); _MO.abolish_all_tables!()
    end

    @testset "the dependency is §1.0's, reused verbatim" begin
        # 7.8 needed no new propagation engine — the vehicle is Dependency(source, cont, target) and
        # resume_continuation. Asserting the TYPE keeps that reuse honest: if a future change forks a
        # separate monotonic dependency type, this fails and the claim in the header gets revisited.
        s = _mo_setup()
        _MO.mono_assert_dep!(Sym(:a), _mo_cont(s), Sym(:b))
        md = _MO.mono_affects(Sym(:a))[1]
        @test md.dep isa _MO.Dependency
        @test md.dep.source == Sym(:a) && md.dep.target == Sym(:b)
        @test md.dep.cont isa _MO.Continuation
        @test !md.lazy
        _MO.clear_mono!()
    end

    @testset "teardown drops dependencies in BOTH directions" begin
        # A dependency TARGETING a dropped table would resume answers into a trie that is gone.
        s = _mo_setup()
        a, b, c = Sym(:a), Sym(:b), Sym(:c)
        _MO.mono_assert_dep!(a, _mo_cont(s), b)
        _MO.mono_assert_dep!(c, _mo_cont(s), b)      # two sources, ONE target
        @test length(_MO.mono_affects(a)) == 1 && length(_MO.mono_affects(c)) == 1

        _MO.drop_mono_deps!(b)                        # b is going away
        @test isempty(_MO.mono_affects(a))            # …so the deps pointing AT it go too
        @test isempty(_MO.mono_affects(c))
        _MO.clear_mono!(); _MO.abolish_all_tables!(); _MO.untable_all!()
    end

    @testset "the `monotonic` OPTION is still refused — the seam is named, not pretended" begin
        # Nothing in tabled_eval records a monotonic dependency yet: that needs to know at call time
        # that both tables are monotonic, which is a declaration. Until this file is consumed, the
        # option throws — and asserting that stops the port from looking more finished than it is.
        @test_throws ArgumentError _MO.table_as!(:p, :monotonic)
        @test_throws ArgumentError _MO.table_as!(:p, :lazy)
        _MO.untable_all!()
    end
end

@testset "§7.4 early completion is UNSOUND for MeTTa — pinned, not ported" begin
    # 🔴 UPSTREAM'S RULE DOES NOT SURVIVE THE LANGUAGE CHANGE, and this pins the measurement that
    # showed it. SWI: *"Ground goals are subject to early completion: they are considered completed
    # after the first solution"* — sound there, because a Prolog ground call's answer is a
    # SUBSTITUTION OVER ZERO VARIABLES, so there is at most one.
    #
    # MeTTa returns a VALUE. A ground call can have many, and completing after the first would
    # silently drop the rest. Same shape as roadmap 2.0 (tabling-is-set vs MeTTa-is-multiset) — the
    # second Prolog assumption in this port that the language change invalidates.
    #
    # This test exists so nobody ports it from the manual later: it asserts the CONDITION under which
    # the optimisation would be wrong, so it fails loudly if that condition ever stops holding.
    _MO.untable_all!(); _MO.abolish_all_tables!()
    try
        s = Space(); load_core_stdlib!(s)
        load_metta!(s, raw"(= (p 1) a)" * "\n" * raw"(= (p 1) b)" * "\n")
        _MO.table!(:p)
        answers = String[string(x) for y in load_metta!(s, "!(p 1)\n")
                         for x in (y isa AbstractVector ? y : [y])]

        goal = _MO.parse_from(_MO.tokenize("(p 1)"), Ref(1), s.tokens)
        @test isempty(_MO.collect_vars(goal))          # the goal IS ground…
        @test length(answers) == 2                     # …and STILL has two answers
        @test sort(answers) == ["a", "b"]
        # ⇒ "complete after the first solution" would return one of them and drop the other.
    finally
        _MO.untable_all!(); _MO.abolish_all_tables!()
    end
end
