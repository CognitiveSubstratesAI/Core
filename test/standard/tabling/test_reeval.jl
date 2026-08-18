# test_reeval.jl — §7.7's RE-EVALUATION half. `reeval/3` (`boot/tabling.pl:1858-1893`),
# `prepare_reeval` / `reeval_complete` / `reset_reevaluation` (`pl-tabling.c:8315` / `:8477` / `:8548`).
#
# ─── 🔴 WHY THE ANTI-VACUITY ASSERTIONS ARE THE POINT OF THIS FILE ───────────────────────────────
# Every "did re-evaluation return the right answers?" test in here PASSES ON AN IMPLEMENTATION THAT
# NEVER RE-EVALUATES. Our fallback invalidation is the REVISION STAMP: any space mutation bumps
# `space.revision`, every table whose stamp no longer matches is evicted, and the next call
# recomputes it from scratch — returning exactly the right answers, for every table, always. So a
# green suite that only checks ANSWERS is evidence of nothing at all about §7.7.
#
# What §7.7 adds is NOT correctness, it is SCOPE: the tables that did NOT depend on the change must
# survive it, and the tables whose source re-derived IDENTICAL answers must be re-validated WITHOUT
# being re-run. Both of those are statements about work NOT DONE, and work not done is invisible to
# an answer comparison. Hence, in every testset below:
#
#   * `idg_reeval_count` — upstream's `stats.reevaluated` (`pl-tabling.h:216-219`) — asserted to be
#     ZERO on the tables that must have been left alone;
#   * TRIE OBJECT IDENTITY (`===` on the trie AND on its ROOT NODE) asserted unchanged on the
#     unrelated table, because `prepare_reeval!` swaps the root, so a preserved root is direct
#     evidence that the table was never prepared;
#   * a counting probe inside the recompute closure, so "the re-evaluation ran" is measured rather
#     than assumed.
#
# `[[feedback_run_the_check_before_making_the_claim]]` · `[[feedback_green_suite_hides_unwired_correct_code]]`
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _RV = Eval

_rv_k(name::Symbol) = Sym(name)

"Give `key` a COMPLETE table holding `answers`, as a real completion would leave it."
function _rv_table!(key::Atom, answers::Vector{Atom})
    _RV.drop_answer_trie!(key)
    t = _RV.answer_trie_for(key)
    for a in answers; _RV.trie_insert!(t, a); end
    _RV.set_table_status!(t, :complete)
    _RV.idg_node_for(key)                       # the IDG node must exist before it can be invalidated
    t
end

_rv_reset!() = (_RV.clear_idg!(); _RV.clear_answer_tries!())

# ═══════════════════════════════════════════════════════════════════════════════
@testset "SWI §7.7 — re-evaluation" begin

# ── A ────────────────────────────────────────────────────────────────────────────────────────────
@testset "🔴 A. an UNRELATED table SURVIVES the change — the whole point of §7.7" begin
    # This is the assertion the revision stamp CANNOT satisfy: it evicts every table on any
    # mutation, so `u` would be recomputed and would still return the right answers. Only the trie
    # IDENTITY and the reeval counter can tell the two implementations apart.
    _rv_reset!()
    a, b, u = _rv_k(:a), _rv_k(:b), _rv_k(:unrelated)
    _rv_table!(a, Atom[Grounded(1)])
    _rv_table!(b, Atom[Grounded(10)])
    ut = _rv_table!(u, Atom[Grounded(99)])
    uroot = ut.root
    _RV.idg_add_edge!(a, b)                       # b depends on a; u depends on nothing

    _RV.idg_changed!(a)
    @test _RV.idg_is_invalid(a) && _RV.idg_is_invalid(b)
    @test !_RV.idg_is_invalid(u)                  # …and u is untouched by the graph walk

    @test _RV.with_reeval(a) do
        t = _RV.answer_trie_for(a)
        _RV.trie_insert!(t, Grounded(1))          # same answer ⇒ :same
    end === :same

    # THE ANTI-VACUITY BLOCK. Answers alone would pass on an implementation that rebuilt everything.
    @test _RV.answer_trie_for(u) === ut           # the trie OBJECT was never replaced
    @test _RV.answer_trie_for(u).root === uroot   # …nor its root — `prepare_reeval!` swaps the root,
                                                  #    so an untouched root proves it never ran
    @test _RV.idg_reeval_count(u) == 0            # `stats.reevaluated` — u was NOT re-evaluated
    @test _RV.idg_reeval_count(a) == 1            # …and the changed table was, exactly once
    @test _RV.idg_reeval_count(b) == 0            # b was re-VALIDATED, never re-RUN (see B)
    @test _RV.trie_answers(_RV.answer_trie_for(u)) == Atom[Grounded(99)]
    _rv_reset!()
end

# ── B ────────────────────────────────────────────────────────────────────────────────────────────
@testset "B. same answers ⇒ dependants RE-VALIDATED without being re-run" begin
    # `reeval_complete` (`:8495`): on a no-change verdict it calls `idg_propagate_change(n, 0)` —
    # the DECREMENT walk. Every dependant whose falsecount returns to 0 is valid again and is never
    # recomputed. That is the entire payoff of the IDG over the revision stamp, and the reason
    # `falsecount` is a COUNT: the decrement has to be symmetric with the increment.
    _rv_reset!()
    a, b, c = _rv_k(:a), _rv_k(:b), _rv_k(:c)
    _rv_table!(a, Atom[Grounded(1), Grounded(2)])
    _rv_table!(b, Atom[Grounded(10)])
    _rv_table!(c, Atom[Grounded(100)])
    _RV.idg_add_edge!(a, b); _RV.idg_add_edge!(b, c)      # c -> b -> a

    _RV.idg_changed!(a)
    @test _RV.idg_node_for(b).falsecount == 1
    @test _RV.idg_node_for(c).falsecount == 1             # transitively invalid

    ran = Ref(0)                                          # …the probe that makes "it ran" MEASURED
    verdict = _RV.with_reeval(a) do
        ran[] += 1
        t = _RV.answer_trie_for(a)
        # ANTI-VACUITY, from inside: `prepare_reeval!` must have EMPTIED the table for the
        # re-derivation. If it had not, this closure would be inserting duplicates and the whole
        # file would be testing an implementation that never prepared anything.
        @test isempty(t) && _RV.table_status(t) === :fresh   # `complete_or_invalid_status` -> fresh (:3235)
        _RV.trie_insert!(t, Grounded(1)); _RV.trie_insert!(t, Grounded(2))
    end
    @test ran[] == 1
    @test verdict === :same

    @test _RV.idg_node_for(b).falsecount == 0             # re-VALIDATED by the decrement walk
    @test _RV.idg_node_for(c).falsecount == 0             # …transitively, on the 1->0 recursion
    @test !_RV.idg_is_invalid(b) && !_RV.idg_is_invalid(c)
    @test _RV.idg_reeval_count(b) == 0 && _RV.idg_reeval_count(c) == 0   # NEITHER was re-run
    @test _RV.table_status(_RV.answer_trie_for(a)) === :complete
    @test _RV.idg_node_for(a).answer_count == 2

    # …and the contrapositive, so the testset is not just asserting "everything becomes valid":
    # a CHANGED source leaves its dependants invalid.
    _RV.idg_changed!(a)
    @test _RV.with_reeval(a) do
        t = _RV.answer_trie_for(a)
        _RV.trie_insert!(t, Grounded(1))                  # 2 answers -> 1: genuinely changed
    end === :changed
    @test _RV.idg_is_invalid(b) && _RV.idg_is_invalid(c)
    @test _RV.idg_reeval_count(b) == 0                    # still not re-run — it will be, when CALLED
    _rv_reset!()
end

# ── C ────────────────────────────────────────────────────────────────────────────────────────────
@testset "🔴🔴 C. THE TRAP — a CONSTANT-CARDINALITY change, and the mutant that misses it" begin
    # Upstream's verdict is `new_answer == false && answer_count == value_count` (`:8484-8485`) —
    # CARDINALITY. Safe in Prolog, where an answer IS its substitution. Here every answer carries a
    # VALUE, and `trie_insert_moded!` REPLACES `node.answer` IN PLACE on its `:delete` action, so a
    # §7.3 aggregate can move while `t.count` does not.
    #
    # The failure a cardinality verdict produces is SILENT: dependants marked valid while holding
    # results computed from a min that has since dropped. So this testset does two things, and the
    # second is the one that earns the first — a claim that the digest is NECESSARY is worth nothing
    # until the cardinality version is SHOWN to break on the same input.
    _rv_reset!()
    modes = _RV.TableMode[_RV.update_goal(Sym(:index)), _RV.update_goal(Sym(:min))]
    p, d = _rv_k(:path), _rv_k(:consumer)
    ans(v) = Expression(Atom[Sym(:path), Sym(:x), Grounded(v)])

    # the previous complete state: one aggregated answer, min = 9
    _rv_table!(p, Atom[ans(9)])
    _rv_table!(d, Atom[Grounded(0)])
    _RV.idg_add_edge!(p, d)

    # re-evaluation derives 9 AND 3; min moves to 3 — ONE answer before, ONE answer after.
    recompute = function ()
        t = _RV.answer_trie_for(p)
        _RV.trie_insert_moded!(t, ans(9), modes)
        _RV.trie_insert_moded!(t, ans(3), modes)
    end

    _RV.idg_changed!(p)
    @test _RV.idg_node_for(d).falsecount == 1
    @test _RV.with_reeval(recompute, p) === :changed          # the CONTENT digest sees it
    t = _RV.answer_trie_for(p)
    @test length(t) == 1                                       # …at CONSTANT cardinality — the trap
    @test _RV.trie_answers(t) == Atom[ans(3)]                  # …and the value really did move
    @test _RV.idg_is_invalid(d)                                # ⇒ the dependant stays INVALID
    @test _RV.idg_node_for(d).falsecount == 1

    # ── THE MUTANT: upstream's clause, ported as written. It MUST get this wrong. ────────────────
    _rv_reset!()
    _rv_table!(p, Atom[ans(9)])
    _rv_table!(d, Atom[Grounded(0)])
    _RV.idg_add_edge!(p, d)
    cardinality_verdict = (snap, tt) -> length(snap.answers) == length(_RV.trie_answers(tt))

    _RV.idg_changed!(p)
    @test _RV.idg_node_for(d).falsecount == 1
    mutant = _RV.with_reeval(recompute, p; verdict = cardinality_verdict)

    # 🔴 THE FALSIFICATION. Same input, same table, ONE line of verdict swapped — and the mutant
    # calls it a no-change and RE-VALIDATES a dependant whose cached results are now stale. These
    # two assertions are deliberately the inverse of the two above.
    @test mutant === :same                                     # …the cardinality test is FOOLED
    @test !_RV.idg_is_invalid(d)                               # …and the dependant is wrongly VALID
    @test _RV.trie_answers(_RV.answer_trie_for(p)) == Atom[ans(3)]   # while the source really changed
    # i.e. `d` is now marked valid holding an answer derived from min=9 against a table that says 3.
    _rv_reset!()
end

# ── D ────────────────────────────────────────────────────────────────────────────────────────────
@testset "🔴 D. two bottoms, different DNFs, DIFFERENT digests — the hash-collision regression" begin
    # `Base.hash(w::WFSBottom, h)` (`Tabling.jl`) hashes `length(w.delays)` BY DESIGN, and its
    # comment says why: `==` is `dnf_equiv`, set equality over a set of sets, with no stable order to
    # hash. Correct for a Dict, where a collision falls through to `==`. FATAL for a digest, which
    # has nothing to fall through to — and the collision is SYSTEMATIC, not occasional: any two
    # conditions with the same number of disjuncts collide.
    #
    # `merge_bottom_into!` (`Tabling.jl`) is the measured mutation that makes this reachable: it
    # replaces a stored bottom with a WIDER-CONDITION bottom at constant cardinality.
    _rv_reset!()
    d(x) = _RV.DelayDNF([_RV.DelaySet([_RV.delay_negative(Sym(x))])])
    b1, b2 = _RV.undefined_with(d(:p)), _RV.undefined_with(d(:q))

    # the defect, asserted directly — if this ever stops holding, the comment above is stale
    @test hash(b1.value) == hash(b2.value)          # SYSTEMATIC collision: both have 1 disjunct
    @test b1.value != b2.value                      # …while `==` is exact (`dnf_equiv`)
    @test !_RV.variant_eq(b1, b2)                   # …and so is `variant_eq`, via GroundKey's `==`

    # …and the digest, which is what the verdict is built on, must NOT inherit the collision
    @test _RV.answer_digest(b1) != _RV.answer_digest(b2)
    @test _RV.table_digest(Atom[b1]) != _RV.table_digest(Atom[b2])

    # ORDER-INSENSITIVE within a DelaySet and across the DNF — matching `set_eq` / `dnf_equiv`,
    # which is what the digest has to agree with or it reports spurious changes forever.
    s1 = _RV.DelaySet([_RV.delay_negative(Sym(:p)), _RV.delay_negative(Sym(:q))])
    s2 = _RV.DelaySet([_RV.delay_negative(Sym(:q)), _RV.delay_negative(Sym(:p))])
    @test _RV.answer_digest(_RV.undefined_with(_RV.DelayDNF([s1]))) ==
          _RV.answer_digest(_RV.undefined_with(_RV.DelayDNF([s2])))
    @test _RV.answer_digest(_RV.undefined_with(_RV.DelayDNF([d(:p)[1], d(:q)[1]]))) ==
          _RV.answer_digest(_RV.undefined_with(_RV.DelayDNF([d(:q)[1], d(:p)[1]])))

    # 🔴 AND THE WHOLE POINT, END TO END: widening a bottom's condition at CONSTANT CARDINALITY
    # must be a `:changed` verdict. This is `merge_bottom_into!`'s mutation, in the reeval lane.
    k, dep = _rv_k(:paradox), _rv_k(:consumer)
    _rv_table!(k, Atom[b1])
    _rv_table!(dep, Atom[Grounded(0)])
    _RV.idg_add_edge!(k, dep)
    _RV.idg_changed!(k)
    @test _RV.with_reeval(k) do
        _RV.trie_insert!(_RV.answer_trie_for(k), _RV.undefined_with(_RV.dnf_or(d(:p), d(:q))))
    end === :changed
    @test length(_RV.answer_trie_for(k)) == 1        # one answer before, one after
    @test _RV.idg_is_invalid(dep)

    # …while re-deriving the SAME condition is a no-change, so the test above is not vacuous
    _RV.idg_changed!(k)
    @test _RV.with_reeval(k) do
        _RV.trie_insert!(_RV.answer_trie_for(k), _RV.undefined_with(_RV.dnf_or(d(:p), d(:q))))
    end === :same
    _rv_reset!()
end

# ── E ────────────────────────────────────────────────────────────────────────────────────────────
@testset "E. ABORT — old answers still readable, `aborted` set, falsecount 1" begin
    # `reset_reevaluation` (`:8548-8564`). Its own header states the contract: *"This must ensure
    # that a subsequent call on the table will restart the re-evaluation and forward a not-changed
    # to the affected nodes if the table evaluates to the same values."* So a half-built table must
    # never become visible, and the table must stay INVALID so the next call retries it.
    _rv_reset!()
    k, dep = _rv_k(:a), _rv_k(:b)
    old = Atom[Grounded(1), Grounded(2)]
    _rv_table!(k, old)
    _rv_table!(dep, Atom[Grounded(10)])
    _RV.idg_add_edge!(k, dep)
    _RV.idg_changed!(k)

    @test_throws ErrorException _RV.with_reeval(k) do
        t = _RV.answer_trie_for(k)
        _RV.trie_insert!(t, Grounded(1))
        _RV.trie_insert!(t, Grounded(999))          # a half-built table…
        error("boom — an exception escaping the re-evaluation")
    end

    t = _RV.answer_trie_for(k)
    @test _RV.trie_answers(t) == old                # …the OLD answers are back, in order
    @test !_RV.trie_contains(t, Grounded(999))      # …and the half-built one is GONE
    @test length(t) == 2
    @test _RV.table_status(t) === :complete         # `set(atrie, TRIE_COMPLETE)` (:8561)
    @test _RV.idg_was_aborted(k)                    # :8558
    @test _RV.idg_node_for(k).falsecount == 1       # :8559 — still INVALID, so the next call retries
    @test !_RV.idg_is_reevaluating(k)               # :8562
    @test _RV.idg_reeval_count(k) == 0              # an abort is NOT a completed re-evaluation
    @test _RV.idg_is_invalid(dep)                   # …and the dependant was never re-validated

    # …and the retry works: `aborted` is cleared by the next SUCCESSFUL completion (`:8503`)
    @test _RV.with_reeval(k) do
        tt = _RV.answer_trie_for(k)
        _RV.trie_insert!(tt, Grounded(1)); _RV.trie_insert!(tt, Grounded(2))
    end === :same
    @test !_RV.idg_was_aborted(k)
    @test _RV.idg_reeval_count(k) == 1
    @test !_RV.idg_is_invalid(dep)                  # re-validated on the no-change verdict
    _rv_reset!()
end

# ── the guards the two entry points share ────────────────────────────────────────────────────────
@testset "both entry points BAIL when the table is already valid (`:8358` / `:8393`)" begin
    # `if ( idg->falsecount == 0 ... ) /* someone else re-evaluated it */` — present at BOTH
    # `$tbl_reeval_prepare_top` and `$tbl_reeval_prepare`. Load-bearing, not defensive: upstream
    # re-evaluates whole false PATHS, so a table can already be fresh by the time it is reached.
    # Preparing anyway would discard a fresh table AND leave `reevaluating` set on one nobody
    # completes.
    _rv_reset!()
    k = _rv_k(:a)
    t = _rv_table!(k, Atom[Grounded(1)])
    root = t.root

    @test !_RV.prepare_reeval!(k)                   # falsecount == 0 ⇒ nothing prepared
    @test t.root === root                           # …and the table was NOT emptied
    @test !_RV.idg_is_reevaluating(k)
    @test _RV.with_reeval(k) do; error("must not run"); end === :already_valid

    # `force` is upstream's `force_reeval` hole in that guard — a keyword here because §7.8's lazy
    # monotonic path that SETS that field is not ported (see IDG.jl's header).
    @test _RV.prepare_reeval!(k; force = true)
    @test _RV.idg_is_reevaluating(k)
    @test !_RV.prepare_reeval!(k)                   # …and a second prepare is refused, not nested
    @test _RV.reeval_complete!(k) === :changed      # emptied and not refilled ⇒ genuinely changed
    @test _RV.reeval_complete!(k) === :not_reevaluating   # `:8480`'s guard
    @test !_RV.reset_reevaluation!(k)               # …likewise: nothing to reset
    _rv_reset!()
end

# ── the `reevaluating` skip, in BOTH directions ──────────────────────────────────────────────────
@testset "🔴 a RE-EVALUATING node is skipped by BOTH walks (`:7011-7012`)" begin
    # The skip sits at the TOP of `idg_changed_loop`, above the increment/decrement split, so it
    # applies to both. Increment: a table mid-re-evaluation has had its falsecount deliberately
    # zeroed and its child edges cleared, so counting invalidation against the OLD dependency set is
    # exactly what `prepare_reeval!` just undid. Decrement: it would drive that zero below zero.
    _rv_reset!()
    a, b = _rv_k(:a), _rv_k(:b)
    _rv_table!(a, Atom[Grounded(1)]); _rv_table!(b, Atom[Grounded(2)])
    _RV.idg_add_edge!(a, b)                          # b depends on a
    _RV.idg_node_for(b).reevaluating = true
    try
        _RV.idg_propagate_change!(a)
        @test _RV.idg_node_for(b).falsecount == 0    # skipped: NOT incremented
        _RV.idg_node_for(b).falsecount = 3
        _RV.idg_propagate_revalidate!(a)
        @test _RV.idg_node_for(b).falsecount == 3    # skipped: NOT decremented
    finally
        _RV.idg_node_for(b).reevaluating = false
    end

    # …and with the flag down, both walks move it — so the test above measures the SKIP rather than
    # a walk that does nothing.
    _RV.idg_node_for(b).falsecount = 0
    _RV.idg_propagate_change!(a)
    @test _RV.idg_node_for(b).falsecount == 1
    _RV.idg_propagate_revalidate!(a)
    @test _RV.idg_node_for(b).falsecount == 0
    # the CLAMP: upstream's note (***) (`:6954`) says it can decrement below zero and calls giving
    # up that sanity check "dubious". On a `size_t` an underflow wraps to "invalid forever".
    _RV.idg_propagate_revalidate!(a)
    @test _RV.idg_node_for(b).falsecount == 0        # clamped, never negative
    _rv_reset!()
end

# ── `idg_clean_dependent!` ───────────────────────────────────────────────────────────────────────
@testset "prepare drops the CHILD edges (and upstream's asymmetry is kept, deliberately)" begin
    # `idg_clean_dependent` (`:6128-6134`) clears only `node->dependent`; the children's `affected`
    # KEEP their back-link. Asserted in both directions so that "we kept upstream's asymmetry" is a
    # checked fact rather than a comment — and because the safe direction matters: a stale back-link
    # over-invalidates (sound), while clearing both would risk losing a dependency entirely.
    _rv_reset!()
    child, me = _rv_k(:child), _rv_k(:me)
    _rv_table!(child, Atom[Grounded(1)]); _rv_table!(me, Atom[Grounded(2)])
    _RV.idg_add_edge!(child, me)                     # me depends on child
    _RV.idg_changed!(me)
    @test _RV.prepare_reeval!(me)
    @test isempty(_RV.idg_node_for(me).dependent)    # forward links dropped, to be rebuilt
    @test me in _RV.idg_node_for(child).affected     # …back-link KEPT — upstream's asymmetry
    @test _RV.idg_node_for(me).falsecount == 0       # :8325
    _RV.reeval_complete!(me)
    _rv_reset!()
end

end # SWI §7.7 — re-evaluation
