# test_worklist.jl — the per-table worklist dequeue. Roadmap §1.0, step 3 of 4.
#
# ─── WHAT IS BEING GATED ─────────────────────────────────────────────────────────────────────────
# ONE invariant (Desouter §4.4, pl-tabling.c:3133/3158/3105):
#
#     an answer is to the LEFT of a dependency IF AND ONLY IF they have not been combined
#
# Everything else follows: answers append left, dependencies append right, any adjacent
# (ANSWERS, SUSPENSIONS) pair is uncombined work, and combining is recorded by SWAPPING the pair.
# There is no "done" flag anywhere — THE ORDER IS THE STATE — so these tests are the only thing
# standing between that design and a subtly wrong one that still returns plausible pairs.
#
# ⚠️ NOT WIRED. The completion loop still reaches its fixpoint by re-running `_leader_pass`; nothing
# consumes a `Worklist` yet. That is step 4. A green file means the structure is correct, NOT that
# tabling uses it. `[[feedback_report_green_against_the_arrow_not_the_test_list]]`
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _WL = Eval

_wl_key() = Sym(:q)
_wl_dep(k::Atom, n::Int) =
    _WL.Dependency(k, _WL.Continuation(nothing, _WL.Bindings(), Sym(Symbol("c$n"))), k)
"Compact shape, e.g. \"A3 S2\" — answer/suspension clusters left to right with their sizes."
_wl_shape(wl) = join(
    [string(c.kind == _WL.CLUSTER_ANSWERS ? "A" : "S", length(c)) for c in wl.clusters],
    " "
)

@testset "worklist — answers LEFT, dependencies RIGHT, combining is a SWAP (§1.0 step 3)" begin
    k = _wl_key()

    @testset "the insertion invariant, and same-kind runs MERGE" begin
        wl = _WL.Worklist(k)
        @test isempty(wl)
        @test _WL.wkl_get_work!(wl) === nothing         # nothing to do, and it must not throw

        _WL.wkl_add_answer!(wl, Grounded(1))
        @test _wl_shape(wl) == "A1"
        _WL.wkl_add_suspension!(wl, _wl_dep(k, 1))
        @test _wl_shape(wl) == "A1 S1"
        # a later answer goes LEFT — it has not been combined with the dependency already present
        _WL.wkl_add_answer!(wl, Grounded(2))
        @test _wl_shape(wl) == "A2 S1"
        # …and consecutive same-kind insertions MERGE rather than appending a new cluster. Without
        # this every element is its own cluster and the batch design degenerates to element-wise.
        _WL.wkl_add_suspension!(wl, _wl_dep(k, 2))
        @test _wl_shape(wl) == "A2 S2"
        _WL.wkl_add_answer!(wl, Grounded(3))
        @test _wl_shape(wl) == "A3 S2"
        @test length(wl.clusters) == 2                  # still TWO clusters, not five
    end

    @testset "taking work swaps the pair, so it is not work twice" begin
        wl = _WL.Worklist(k)
        for v in (1, 2, 3)
            _WL.wkl_add_answer!(wl, Grounded(v))
        end
        for n in (1, 2)
            _WL.wkl_add_suspension!(wl, _wl_dep(k, n))
        end
        @test _WL.wkl_riac(wl) == 1 && _WL.wkl_has_work(wl)

        w = _WL.wkl_get_work!(wl)
        @test w !== nothing
        @test length(w[1]) == 3 && length(w[2]) == 2    # the Cartesian product is 3x2
        # the SWAP is what records "combined" — answers are now RIGHT of those dependencies.
        @test _wl_shape(wl) == "S2 A3"
        @test !_WL.wkl_has_work(wl)
        @test _WL.wkl_get_work!(wl) === nothing         # and it stays not-work

        # 🔴 THE CASE THE WHOLE DESIGN EXISTS FOR: an answer arriving DURING completion is work
        # against the existing dependencies, while the answers already combined with them are NOT
        # re-combined. A design that re-offered everything would loop; one that offered nothing
        # would lose answers. Assert the exact count.
        _WL.wkl_add_answer!(wl, Grounded(9))
        @test _wl_shape(wl) == "A1 S2 A3"
        w2 = _WL.wkl_get_work!(wl)
        @test w2 !== nothing
        @test length(w2[1]) == 1 && length(w2[2]) == 2  # ONLY the new answer, against BOTH deps
        @test !_WL.wkl_has_work(wl)
    end

    @testset "termination: a drained worklist stays drained" begin
        wl = _WL.Worklist(k)
        for v in 1:4
            _WL.wkl_add_answer!(wl, Grounded(v))
        end
        for n in 1:3
            _WL.wkl_add_suspension!(wl, _wl_dep(k, n))
        end
        n = 0
        while _WL.wkl_get_work!(wl) !== nothing
            n += 1
            n > 100 && break                            # a non-terminating drain IS the failure
        end
        @test n == 1                                    # one batch pair, then done
        @test !_WL.wkl_has_work(wl)
    end

    @testset "dependencies with no answers, and answers with no dependencies, are not work" begin
        wl = _WL.Worklist(k)
        for n in 1:3
            _WL.wkl_add_suspension!(wl, _wl_dep(k, n))
        end
        @test !_WL.wkl_has_work(wl)                     # nothing to feed them yet
        @test _WL.wkl_get_work!(wl) === nothing

        wl2 = _WL.Worklist(k)
        for v in 1:3
            _WL.wkl_add_answer!(wl2, Grounded(v))
        end
        @test !_WL.wkl_has_work(wl2)                    # nobody waiting
        @test _WL.wkl_get_work!(wl2) === nothing

        # …and a dependency arriving after answers makes them work, in that order.
        _WL.wkl_add_suspension!(wl2, _wl_dep(k, 1))
        @test _WL.wkl_has_work(wl2)
        @test length(_WL.wkl_get_work!(wl2)[1]) == 3
    end

    @testset "registry: one worklist per table, and it dies with its table" begin
        _WL.clear_worklists!()
        k2 = Sym(:other)
        @test !_WL.has_worklist(k)
        w1 = _WL.worklist_for(k)
        @test _WL.has_worklist(k)
        @test _WL.worklist_for(k) === w1                # get!, not a fresh one each call
        _WL.wkl_add_answer!(_WL.worklist_for(k2), Grounded(1))
        @test _wl_shape(_WL.worklist_for(k)) == ""     # …and the two do not share state
        @test _wl_shape(_WL.worklist_for(k2)) == "A1"
        _WL.drop_worklist!(k)
        @test !_WL.has_worklist(k) && _WL.has_worklist(k2)
        _WL.clear_worklists!()
        @test !_WL.has_worklist(k2)
    end
end
