# The COMPLETION MERGE POINT — `Tabling._merge_partial`, and the growth signal it reports.
#
# WHY THIS FILE EXISTS. Every fixpoint round in `Tabling.jl` merges a pass's answers into a table and
# asks "did anything change?". Until 2026-08-16 that question had two hand-rolled answers, both
# `length(_PARTIAL[m]) != n0`. CARDINALITY IS THE WRONG SIGNAL and it fails SILENTLY: under §7.3
# aggregation a merge changes a VALUE while leaving the COUNT fixed, so a length test reports
# convergence and completes a HALF-AGGREGATED table — no error, no missing answer, a wrong number.
#
# ⚠️ THE GATE SET CANNOT SEE THIS CHANGE ON ITS OWN. With no modes declared the switch is
# behaviour-preserving by construction (set-union merge ⇒ "a new element appeared" and "the length
# grew" coincide exactly), so health, the corpus and both swipl differentials stay green either way —
# they prove the EQUIVALENT half and are blind to the half that matters
# (`[[feedback_oracle_must_observe_the_defect_class]]`). This file is the half they cannot see: it
# pins the case where the two signals DISAGREE, so a reversion to `length(…) != n0` fails here loudly.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _CM = Eval

@testset "completion merge point — the growth signal is VALUE-based, not cardinality" begin

    # ── the disagreement itself, at the merge point Tabling.jl actually calls ───────────────────
    # `lattice(sum)` folding (k,1)+(k,2) into (k,3): ONE answer before, ONE after. A cardinality test
    # sees no growth and stops; the value test sees the fold. This is the whole reason for the switch.
    @testset "same length, different value ⇒ changed = true" begin
        _CM.untable_all_modes!()
        k(v) = Expression(Atom[Sym(:p), Sym(:k), Grounded(v)])
        _CM.table_mode!(:p, Atom[Sym(:index), Expression(Atom[Sym(:lattice), Sym(:sum)])])

        existing = Atom[k(1)]
        (merged, changed) = _CM._merge_partial(existing, Atom[k(2)], k(1))
        @test length(merged) == length(existing)     # CARDINALITY SAYS: nothing happened
        @test changed                                 # VALUE SAYS: it did — this is the disagreement
        @test merged == Atom[k(3)]                    # …and the fold is the one §7.3 specifies

        # NEGATIVE CONTROL — the signal must not simply always be true, or the fixpoint never ends.
        # Uses lattice(MAX), which is idempotent. `sum` cannot serve as this control; see below.
        _CM.untable_all_modes!()
        _CM.table_mode!(:p, Atom[Sym(:index), Expression(Atom[Sym(:lattice), Sym(:max)])])
        (_, unchanged) = _CM._merge_partial(Atom[k(3)], Atom[k(3)], k(3))
        @test !unchanged
        _CM.untable_all_modes!()
    end

    # ── 🔴 THE FINDING: `lattice(sum)` IS NOT IDEMPOTENT, AND OUR FIXPOINT RECOMPUTES ────────────
    # This started as the negative control above and failed, which is how it was found.
    #
    # `_leader_pass` is RE-RUN every fixpoint round (the "extension table" design Desouter et al.
    # name and reject) — so every round re-derives the SAME answers and merges them again. Under an
    # idempotent lattice (min/max) that is harmless: re-merging an answer is a no-op and the loop
    # converges. Under `sum` it is not. Re-merging (p k 3) with itself yields (p k 6), the signal
    # says "changed", and the next round does it again: THE FIXPOINT DOES NOT CONVERGE, and every
    # intermediate table is a wrong number rather than a missing answer.
    #
    # ⇒ §7.3's non-idempotent aggregates are UNSOUND ON THE RECOMPUTATION BASE, independent of where
    # the merge point sits. That is a §1.0-before-§7.3 ordering constraint, and it is a REASON TO
    # MOVE THE BASE that the roadmap does not currently list. (It is NOT roadmap 2.0 — that is the
    # tabling-is-set vs MeTTa-is-multiset mismatch, which the base move does not fix. This one the
    # base move DOES fix, because dependency-driven resumption feeds each answer forward ONCE.)
    #
    # Pinned as the hazard it is: when the rewire lands, `sum` must stop doubling and this test must
    # be REWRITTEN to assert convergence — not deleted.
    @testset "HAZARD: sum re-merges under recomputation (blocks §7.3 until §1.0 lands)" begin
        _CM.untable_all_modes!()
        k(v) = Expression(Atom[Sym(:p), Sym(:k), Grounded(v)])
        _CM.table_mode!(:p, Atom[Sym(:index), Expression(Atom[Sym(:lattice), Sym(:sum)])])
        (once, ch1) = _CM._merge_partial(Atom[k(3)], Atom[k(3)], k(3))
        @test once == Atom[k(6)] && ch1              # re-deriving the same answer DOUBLES it
        (twice, ch2) = _CM._merge_partial(once, Atom[k(3)], k(3))
        @test twice == Atom[k(9)] && ch2             # …and again, so the loop cannot converge
        # idempotent lattices are unaffected — this is specific to non-idempotent aggregates
        _CM.untable_all_modes!()
        _CM.table_mode!(:p, Atom[Sym(:index), Expression(Atom[Sym(:lattice), Sym(:max)])])
        @test _CM._merge_partial(Atom[k(3)], Atom[k(3)], k(3)) == (Atom[k(3)], false)
        _CM.untable_all_modes!()
    end

    # ── with no modes declared, the new signal is EXACTLY the old one ───────────────────────────
    # The equivalence the whole change rests on, asserted rather than argued: set-union merge, so a
    # value change and a length change coincide, and answer ORDER is unchanged too (existing first,
    # then new arrivals). If this ever parts, every tabled answer order in the corpus moves with it.
    @testset "undeclared head: value signal ≡ length signal, order preserved" begin
        _CM.untable_all_modes!()
        a(n) = Expression(Atom[Sym(:q), Grounded(n)])
        for (existing, incoming) in (
            (Atom[], Atom[a(1), a(2)]),                  # from empty
            (Atom[a(1)], Atom[a(1)]),                    # pure duplicate ⇒ no growth
            (Atom[a(1)], Atom[a(2), a(1)]),              # partial overlap
            (Atom[a(1), a(2)], Atom[a(2), a(1)]),        # full overlap, reordered
            (Atom[a(2)], Atom[a(1)]))                    # disjoint
            (merged, changed) = _CM._merge_partial(existing, incoming, a(0))
            @test merged == unique(vcat(existing, incoming))          # the exact old expression
            @test changed == (length(merged) != length(existing))     # …and the exact old signal
        end
    end

    # ── the merge point is reached on BOTH paths through tabled_eval ────────────────────────────
    # A non-recursive head takes the singleton fast path and never enters a fixpoint round, so a merge
    # point wired only into the loops would skip it — which is why the INITIAL pass goes through
    # `_merge_partial` too. Asserted on an UNDECLARED head, where the merge's observable effect is
    # dedup, because what belongs to §1.0 is REACHABILITY; the aggregation SEMANTICS is §7.3's.
    @testset "both tabled_eval paths run through _merge_partial" begin
        for (label, prog, query, want) in (
            ("non-recursive: singleton fast path (initial pass only)",
                raw"(= (nr) 1)  (= (nr) 1)  (= (nr) 2)", "!(nr)", ["1", "2"]),
            ("self-recursive: enters the fixpoint loop",
                raw"(= (sr 0) 1)  (= (sr 1) 1)  (= (sr $n) (sr 0))", "!(sr 1)", ["1"]))
            _CM.untable_all!()
            _CM.untable_all_modes!()
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, prog)
            _CM.table!(label[1] == 'n' ? :nr : :sr)
            got = sort!(
                String[
                    string(x) for y in load_metta!(s, query * "\n")
                    for x in (y isa AbstractVector ? y : [y])
                ]
            )
            @test got == want || (@info "merge point NOT reached" label got want; false)
        end
        _CM.untable_all!()
        _CM.untable_all_modes!()
    end
end

# ── 🔴 OPEN, AND DELIBERATELY NOT DECIDED HERE — what does a mode KEY off, in MeTTa? ─────────────
# `_merge_partial` looks modes up by `table_modes(head_name(key))`, i.e. by the TABLED GOAL's head.
# That is SWI-faithful: there an answer to `p(K,V)` IS a `p/2` term, so goal head and answer head are
# the same symbol and `mode_key` reads the answer's own arguments.
#
# ⚠️ MeTTa BREAKS THAT IDENTITY. `(= (fib 5) 5)` answers a `fib` goal with `5` — an atom with no
# argument structure at all, on which `mode_key` returns the answer itself and no aggregation is
# expressible. When the answer IS a structure, e.g. `(= (agg k) (P k 1))`, its head (`P`) is not the
# tabled head (`agg`), so the two lookups disagree and pick different modes.
#
# Two defensible readings — TABLE head (SWI-faithful, what is implemented) vs ANSWER head (what MeTTa's
# functional answers would need). This is §7.3 semantics and belongs to whoever owns it; §1.0 owns the
# merge point's REACHABILITY and growth signal, which is what this file gates. Recorded, not resolved.
