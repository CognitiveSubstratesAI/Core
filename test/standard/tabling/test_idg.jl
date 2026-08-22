# test_idg.jl — the INCREMENTAL DEPENDENCY GRAPH. SWI §7.7, and the substrate for §7.8.
#
# Our current invalidation is the REVISION STAMP: any space mutation bumps `space.revision` and every
# table whose stamp no longer matches is evicted. Sound, and maximally coarse — one unrelated
# `add-atom` throws away every table. The IDG makes it PER-TABLE.
#
# ⚠️ PARTIALLY WIRED, AND THE HALVES DIFFER — BUT THE LINE HAS MOVED. `tabled_eval` records edges at
# the call point behind `_IDG_RECORD` / `CORE_TABLING_IDG=1`, and the end-to-end testset below drives
# a real `fib 8`. §7.7's RE-EVALUATION half now EXISTS (`prepare_reeval!` / `reeval_complete!` /
# `reset_reevaluation!` and the decrement walk) — see `test_reeval.jl`, which owns those assertions.
# 🔴 WHAT IS STILL MISSING IS THE INVALIDATION *ENTRY*: nothing calls `idg_changed!` on a space
# mutation, so no table can ever BE invalid and the re-evaluation lifecycle is unreachable in
# ordinary use. That is the dynamic-predicate edge (upstream's `dyn_changed_pattern/1`,
# boot/tabling.pl:1807-1813). Until it lands, invalidation still comes from the revision stamp.
# So a green file means the GRAPH is correct, NOT that tabling uses it.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _DG = Eval
_dg_k(name::Symbol) = Sym(name)

@testset "SWI §7.7 — the incremental dependency graph" begin

    @testset "🔴 the TWO DIRECTIONS, in both roles" begin
        # `idg_add_edge(atrie, ctrie)` -> `idg_add_child(ctrie->IDG, atrie->IDG)`: the CURRENT table
        # becomes the PARENT of the one it consulted. So `affected` = who depends on me, `dependent`
        # = who I depend on, and invalidation flows UP through `affected`.
        #
        # Reversing them is SILENT AND CATASTROPHIC: invalidation would flow to the tables the
        # changed one CONSULTED, leaving every table that actually cached its answers stale. Asserted
        # from both ends so a swap cannot pass.
        _DG.clear_idg!()
        a, b = _dg_k(:a), _dg_k(:b)
        _DG.idg_add_edge!(a, b)                     # b (current) now depends on a (consulted)
        @test a in _DG.idg_node_for(b).dependent    # b depends on a
        @test b in _DG.idg_node_for(a).affected     # a is depended on BY b
        @test !(b in _DG.idg_node_for(a).dependent) # …and NOT the other way round
        @test !(a in _DG.idg_node_for(b).affected)

        _DG.idg_add_edge!(a, a)                     # a table does not depend on itself
        @test isempty(_DG.idg_node_for(a).dependent)
        _DG.clear_idg!()
    end

    @testset "invalidation is TRANSITIVE and flows UPWARD only" begin
        # C depends on B depends on A. Changing A must invalidate B and C — and NOT A itself:
        # upstream walks `n->affected`, not `n`. The changed table is handled by whatever changed it.
        _DG.clear_idg!()
        a, b, c = _dg_k(:a), _dg_k(:b), _dg_k(:c)
        _DG.idg_add_edge!(a, b)                     # b depends on a
        _DG.idg_add_edge!(b, c)                     # c depends on b
        hit = _DG.idg_propagate_change!(a)
        @test hit == Set([b, c])
        @test _DG.idg_is_invalid(b) && _DG.idg_is_invalid(c)
        @test !_DG.idg_is_invalid(a)                # the CHANGED table is not self-invalidated

        # …and changing a LEAF invalidates nobody, which is the whole point versus the revision stamp
        _DG.clear_idg!()
        _DG.idg_add_edge!(a, b)
        @test isempty(_DG.idg_propagate_change!(b))
        @test !_DG.idg_is_invalid(a)
        _DG.clear_idg!()
    end

    @testset "cycle-safe — recursive dependencies are the NORMAL case here" begin
        # Tabling exists to admit recursive dependencies, so a propagation that could not handle a
        # cycle would fail on exactly the programs the feature is for.
        _DG.clear_idg!()
        a, b = _dg_k(:a), _dg_k(:b)
        _DG.idg_add_edge!(a, b)
        _DG.idg_add_edge!(b, a)   # mutual
        hit = _DG.idg_propagate_change!(a)
        @test hit == Set([a, b])                    # a IS reached, via b — it is a genuine parent here
        # 🔴 THESE COUNTS WERE WRONG UNTIL 2026-08-17, and asserted OUR bug as the contract.
        # Upstream increments on EVERY incoming edge and recurses only on the 0->1 transition
        # (`ATOMIC_INC(&n->falsecount) == 1`, `pl-tabling.c:7043`). So walking a↔b from `a`: b goes
        # 0->1 and is pushed; b's affected gives a 0->1, pushed; a's affected gives b 1->2, NOT
        # pushed — and it terminates there. Termination comes from the SAME test as the count, which
        # is why a `seen` set was not a harmless substitute for it.
        @test _DG.idg_node_for(b).falsecount == 2   # …reached twice: directly, and back around
        @test _DG.idg_node_for(a).falsecount == 1
        _DG.clear_idg!()
    end

    @testset "falsecount is a COUNT, and a call RESETS it" begin
        # `complete_or_invalid_status` reads `falsecount > 0`. It counts because a table can be
        # invalidated from several children before it is re-evaluated.
        _DG.clear_idg!()
        a, b, c = _dg_k(:a), _dg_k(:b), _dg_k(:c)
        _DG.idg_add_edge!(a, c)
        _DG.idg_add_edge!(b, c)   # c depends on BOTH a and b
        _DG.idg_propagate_change!(a)
        _DG.idg_propagate_change!(b)
        @test _DG.idg_node_for(c).falsecount == 2          # counted, not flagged
        @test _DG.idg_invalid_tables() == [c]

        # `:6480` note (*): a call resets it to 0, because a re-evaluated table may have a NEW
        # dependency set and must not carry invalidation counted against the OLD one.
        _DG.idg_reset_falsecount!(c)
        @test !_DG.idg_is_invalid(c) && isempty(_DG.idg_invalid_tables())
        _DG.clear_idg!()
    end

    @testset "🔴 idg_changed! is the ENTRY POINT — three guards the inner walk does not have" begin
        # `idg_propagate_change!` is upstream's INNER loop; every real caller goes through
        # `idg_changed` (`pl-tabling.c:7133`). Calling the walk directly skips all three of these,
        # which is how the monotonic retract path was leaving its own source table valid.
        _DG.clear_idg!()
        a, b = _dg_k(:a), _dg_k(:b)
        _DG.idg_add_edge!(a, b)                          # b depends on a

        hit = _DG.idg_changed!(a)
        @test _DG.idg_is_invalid(a)                      # (2) the CHANGED table IS invalidated
        @test a in hit && b in hit
        @test _DG.idg_node_for(a).falsecount == 1
        @test _DG.idg_node_for(b).falsecount == 1

        # (1) already-invalid ⇒ no re-propagation, so counts do NOT inflate on a repeat change
        @test isempty(_DG.idg_changed!(a))
        @test _DG.idg_node_for(b).falsecount == 1

        # (3) an INCOMPLETE table cannot be invalidated — permission error, not silent corruption
        _DG.clear_idg!()
        _DG.idg_add_edge!(a, b)
        push!(_DG._TABLE_INPROG, a)
        try
            @test_throws ArgumentError _DG.idg_changed!(a)
            @test isempty(_DG.idg_changed!(a; mono=true))   # …mono STOPS instead of erroring
            @test !_DG.idg_is_invalid(b)
        finally
            delete!(_DG._TABLE_INPROG, a)
        end
        _DG.clear_idg!()
    end

    @testset "dropping a node unlinks BOTH directions" begin
        # A dropped table that left its edges behind would propagate invalidation into nothing, or
        # worse, keep a stale key alive as someone else's dependency.
        _DG.clear_idg!()
        a, b, c = _dg_k(:a), _dg_k(:b), _dg_k(:c)
        _DG.idg_add_edge!(a, b)
        _DG.idg_add_edge!(b, c)
        _DG.drop_idg_node!(b)
        @test !_DG.has_idg_node(b)
        @test isempty(_DG.idg_node_for(a).affected)    # a no longer lists b as a dependant
        @test isempty(_DG.idg_node_for(c).dependent)   # c no longer depends on b
        @test isempty(_DG.idg_propagate_change!(a))    # …and the chain is genuinely broken
        _DG.clear_idg!()
    end

    @testset "untable! drops the head's IDG node with its table" begin
        _DG.untable_all!()
        _DG.clear_idg!()
        k = _DG._variant_rename(Expression(Atom[Sym(:p), Grounded(1)]))
        _DG.table!(:p)
        _DG.idg_add_edge!(_dg_k(:other), k)
        @test _DG.has_idg_node(k)
        _DG.untable!(:p)
        @test !_DG.has_idg_node(k)
        _DG.untable_all!()
        _DG.clear_idg!()
    end

    @testset "a FRESH node's re-evaluation fields are the documented defaults" begin
        # 🔴 THIS TESTSET USED TO ASSERT THE FEATURE WAS ABSENT. It is not, as of 2026-08-18 — but the
        # assertions are still worth keeping, retargeted: they now pin that a FRESH `IDGNode` starts
        # in the state `prepare_reeval!` expects. If a default moves, the lifecycle silently starts
        # mid-flight, and `test_reeval.jl`'s abort path is the only other thing that would notice.
        # The lifecycle itself is asserted in `test_reeval.jl`, which owns it.
        _DG.clear_idg!()
        n = _DG.idg_node_for(_dg_k(:a))
        @test !n.reevaluating && !_DG.idg_is_reevaluating(_dg_k(:a))
        @test n.answer_count == 0
        @test !n.monotonic && !n.lazy               # §7.8 fields, likewise unset
        _DG.clear_idg!()
    end
end

@testset "§7.7 end-to-end — edges from a REAL run, and per-table invalidation" begin
    # 🔴 THE EDGE MUST BE AT THE CALL, NOT THE CACHE HIT. First implementation recorded it when a
    # table answered from another's cache, which MISSES every dependency where the caller COMPUTED
    # the subgoal instead of reusing it. Upstream adds it in `tbl_variant_table`
    # (`pl-tabling.c:4549-4560`) — looked up OR CREATED, on every tabled call, before any answer
    # exists. A missed edge means a stale table is never invalidated: the one failure an IDG cannot
    # have. Measured on fib 8: the cache-hit version recorded 6 edges and missed fib(7)->fib(6).
    _DG.untable_all!()
    _DG.abolish_all_tables!()
    _DG.clear_idg!()
    _DG._IDG_RECORD[] = true
    try
        s = Space()
        load_core_stdlib!(s)
        load_metta!(
            s, raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n"
        )
        _DG.table!(:fib)
        @test String[
            string(x) for y in load_metta!(s, "!(fib 8)\n")
            for x in (y isa AbstractVector ? y : [y])
        ] == ["21"]

        # ANTI-VACUITY: an empty graph would satisfy every "invalidates only N" claim below.
        @test length(_DG._IDG) > 5
        @test sum(length(n.dependent) for (_, n) in _DG._IDG; init=0) > 10

        k(n) = _DG._variant_rename(
            _DG._reduced_goal(
                _DG.parse_from(_DG.tokenize("(fib $n)"), Ref(1), s.tokens), s,
                _DG.Bindings())
        )

        # fib(7) = fib(6)+fib(5) and fib(8) = fib(7)+fib(6), so changing fib(6) must reach BOTH.
        # The cache-hit version reached only fib(8) — the assertion that catches that regression.
        hit = _DG.idg_propagate_change!(k(6))
        @test k(7) in hit
        @test k(8) in hit

        # …and this is §7.7's whole point: FEWER than the revision stamp, which evicts every table.
        @test length(hit) < length(_DG._ANSWER_TABLE)
    finally
        _DG.reset_execution_flags!()   # restore the ENV default, never a literal — defaults move
        _DG.untable_all!()
        _DG.abolish_all_tables!()
        _DG.clear_idg!()
    end
end
