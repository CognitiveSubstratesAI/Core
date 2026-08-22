# tabling/Monotonic.jl — MONOTONIC TABLING. SWI §7.8.
#
# Mirrors `boot/tabling.pl`'s MONOTONIC TABLING section (`:1556-1760`).
#
# ─── WHAT IT IS, AND WHY IT IS NOT ANOTHER INVALIDATION SCHEME ───────────────────────────────────
# Incremental tabling (§7.7) answers a change by INVALIDATING dependents; they are recomputed on
# next call. Monotonic tabling answers a change by PROPAGATING IT FORWARD. Upstream's own comment on
# `monotonic_affects/6` says it plainly:
#
#     "Dependency between two monotonic tables. If SrcReturn is added to SrcTrie we must add all
#      answers for Return of Continuation to Atrie."
#
# 🔑 THAT IS §1.0 STEP 2, APPLIED ACROSS TABLE BOUNDARIES. The stored dependency is
# `dependency(SrcSkel, IsMono, Cont, Skel)` — SOURCE · CONTINUATION · TARGET — which is our
# `Tabling.Dependency`, and feeding an answer through it is `resume_continuation`. §7.8 needed no new
# propagation engine; it needed the assert/retract branch and the eager/lazy split.
#
# ─── THE BRANCH THAT MAKES IT SOUND ──────────────────────────────────────────────────────────────
# `mon_propagate/3` (`boot/tabling.pl:1644`) dispatches on the ACTION, and the asymmetry is the whole
# correctness argument:
#
#     assert   -> propagate_assert            (eager)  + '$mono_idg_changed'  (lazy)
#     retract  -> mon_invalidate_dependents   -> '$idg_mono_invalidate'
#     rollback -> mon_propagate_rollback
#
# ⚠️ RETRACTION IS NOT MONOTONE, SO IT CANNOT BE PROPAGATED. Removing a source answer can only
# REMOVE target answers, and a continuation can add but not subtract — so upstream falls back to
# §7.7-style INVALIDATION there. Propagating a retraction "forward" would leave every answer the
# removed one had already produced, silently and permanently. This is the single place where a
# plausible symmetry is wrong, and it is why the branch exists.
#
# ─── SCOPE ───────────────────────────────────────────────────────────────────────────────────────
# Dependencies are recorded and propagated HERE; nothing in `tabled_eval` records a monotonic
# dependency yet, because that requires knowing at call time that both tables are monotonic — which
# is a `table_as!(:p, :monotonic)` declaration, and that option is still REFUSED (`tabling/Options.jl`)
# until this file is consumed. Recording that as the seam rather than pretending it is wired.

"""A monotonic dependency: an answer added to `dep.source` must be pushed through `dep.cont` into
`dep.target`. Upstream's `dependency(SrcSkel, IsMono, Cont, Skel)`.

`lazy` is §7.8's eager/lazy split: an EAGER dependency propagates the moment the source answer
lands; a LAZY one is QUEUED and drained on demand (`'\$mono_idg_changed'` vs `propagate_assert`)."""
struct MonoDep
    dep::Dependency
    lazy::Bool
end

const _MONO_DEPS = Dict{Atom, Vector{MonoDep}}()   # source key ⇒ dependencies watching it
const _MONO_QUEUE = Dict{Atom, Vector{Tuple{MonoDep, Atom}}}()  # target ⇒ (dep, answer) pairs a
# LAZY dep deferred: the CONTINUATION IS NOT
# RUN until drain (see `_mono_propagate!` #7)

"""
    mono_assert_dep!(source, cont, target; lazy=false)

`mon_assert_dep/4` (`boot/tabling.pl:1562`). Record that `target` must gain answers whenever
`source` does, by resuming `cont`.
"""
function mono_assert_dep!(source::Atom, cont::Continuation, target::Atom; lazy::Bool=false)
    push!(
        get!(_MONO_DEPS, source, MonoDep[]), MonoDep(Dependency(source, cont, target), lazy)
    )
    nothing
end

"Dependencies watching `source` — `monotonic_affects/6`."
mono_affects(source::Atom)::Vector{MonoDep} = get(_MONO_DEPS, source, MonoDep[])

"""
    mono_propagate_assert!(source, answer, space) -> Dict{Atom,Vector{Atom}}

`propagate_assert` — the ASSERT branch of `mon_propagate/3`. Push `answer` through every dependency
watching `source`, insert into each target's table, and **recurse**, returning everything new grouped
by TARGET table.

EAGER dependencies propagate now. LAZY ones queue the (dependency, answer) pair against the target
WITHOUT running the continuation, to be drained by `mono_drain_queue!`.
"""
function mono_propagate_assert!(source::Atom, answer::Atom, space)::Dict{Atom, Vector{Atom}}
    out = Dict{Atom, Vector{Atom}}()
    _mono_propagate!(out, source, answer, space)
    for (k, v) in out
        out[k] = _variant_unique(v)
    end
    out
end

# 🔴 #2 CRITICAL: PROPAGATION IS A TRANSITIVE CLOSURE, NOT ONE HOP — FIXED 2026-08-17.
# This inserted into `d.target` and STOPPED. With monotonic tables A -> B -> C, asserting into A
# updated B and SILENTLY LEFT C STALE: missing answers, no error. Upstream recurses —
# `pdelim/3` (`boot/tabling.pl:1727-1733`) calls `'$tbl_monotonic_add_answer'(ATrie, Skel)` and then
# `propagate_answer(ATrie, Skel)` (`:1709-1714`), which re-enters `pdelim` for everything depending
# on ATrie.
#
# 🔴 …AND #8 IS WHAT MAKES THAT TERMINATE. The insert's return value was DISCARDED and every
# propagated answer was reported new. Upstream's `'$tbl_monotonic_add_answer'` is
# `if (node->value) return false` (`pl-tabling.c:7595-7597`), and the Prolog CONJUNCTION in `pdelim`
# then stops — so a duplicate never reaches `propagate_answer`. Without that test the recursion above
# loops FOREVER on any cycle in the monotonic graph, and cycles are the normal case in tabling.
function _mono_propagate!(out::Dict{Atom, Vector{Atom}}, source::Atom, answer::Atom, space)
    for md in mono_affects(source)
        d = md.dep
        if md.lazy
            # 🔴 #7: LAZY MUST NOT RUN THE CONTINUATION. It did, deferring only the `trie_insert!` —
            # so lazy cost exactly what eager cost (the entire point of §7.8's split, lost), and the
            # continuation was evaluated against the space AT ASSERT TIME rather than at drain time,
            # so a lazy dependency's answers could differ from upstream's whenever anything changed
            # in between. Upstream queues the ANSWER and sets `lazy_queued`
            # (`mdep_queue_answer`, `pl-tabling.c:7506-7546`); the continuation runs at the target's
            # next call. So what we queue is the (dependency, answer) PAIR, not a computed result.
            push!(get!(_MONO_QUEUE, d.target, Tuple{MonoDep, Atom}[]), (md, answer))
            continue
        end
        for new in _mono_resume(d, answer, space)
            trie_insert!(answer_trie_for(d.target), new) || continue   # #8: duplicate ⇒ stop here
            push!(get!(out, d.target, Atom[]), new)
            _mono_propagate!(out, d.target, new, space)                # #2: and onward
        end
    end
    nothing
end

"Feed one answer through a dependency's continuation — the shared half of eager and lazy."
function _mono_resume(d::Dependency, answer::Atom, space)::Vector{Atom}
    got = Atom[]
    for a in _project(Atom[answer], d.cont.goal)
        for (at, bnd) in resume_continuation(d.cont, a, space)
            is_empty_atom(at) || push!(got, subst(at, bnd))
        end
    end
    got
end

"""
    mono_drain_queue!(target, space) -> Vector{Atom}

Run the continuations a LAZY dependency deferred for `target` and insert what they produce. Takes
`space` because the continuation runs HERE, at drain time — see `_mono_propagate!`'s `#7` note.
Returns the answers that were NEW, and propagates them onward exactly as the eager path does.
"""
function mono_drain_queue!(target::Atom, space)::Vector{Atom}
    queued = get(_MONO_QUEUE, target, Tuple{MonoDep, Atom}[])
    isempty(queued) && return Atom[]
    delete!(_MONO_QUEUE, target)                       # consumed before running, so a re-entrant
    t = answer_trie_for(target)                        # propagation cannot drain it twice
    added = Atom[]
    onward = Dict{Atom, Vector{Atom}}()
    for (md, answer) in queued
        for new in _mono_resume(md.dep, answer, space)
            trie_insert!(t, new) || continue
            push!(added, new)
            _mono_propagate!(onward, target, new, space)
        end
    end
    added
end

"The (dependency, answer) pairs a lazy dependency has deferred for `target`."
mono_queued(target::Atom)::Vector{Tuple{MonoDep, Atom}} =
    copy(get(_MONO_QUEUE, target, Tuple{MonoDep, Atom}[]))

"""
    mono_propagate_rollback!(action, source) -> Set{Atom}

`mon_propagate(rollback(Action), …)` (`boot/tabling.pl:1661-1667`), and the ASYMMETRY IS NOT
OBVIOUS: rolling back an `asserta`/`assertz` is a **no-op** — the answers it propagated are NOT
retracted, because a monotonic table may legitimately hold answers no longer derivable and
monotonicity only promises they were true when added. Rolling back a `retract` **does** invalidate,
since the retraction's own invalidation must be undone by recomputation.

Named in this file's header as one of `mon_propagate/3`'s three branches and previously ABSENT.
"""
function mono_propagate_rollback!(action::Symbol, source::Atom)::Set{Atom}
    action in (:asserta, :assertz) && return Set{Atom}()      # deliberate no-op, per upstream
    action === :retract && return mono_invalidate_dependents!(source)
    throw(
        ArgumentError(
            "domain_error(mono_rollback_action, $(action)) — " *
            "expected :asserta, :assertz or :retract"
        )
    )
end

"""
    mono_invalidate_dependents!(source) -> Set{Atom}

`mon_invalidate_dependents/1` — the RETRACT branch. Falls back to §7.7 INVALIDATION.

🔴 THIS ASYMMETRY IS THE CORRECTNESS ARGUMENT, NOT AN OPTIMISATION GAP. Retraction is NOT monotone:
removing a source answer can only REMOVE target answers, and a continuation adds but cannot
subtract. Propagating a retraction "forward" would leave every answer the removed one had already
produced — silently, and permanently. So the dependents are invalidated and recomputed instead.
"""
function mono_invalidate_dependents!(source::Atom)::Set{Atom}
    hit = idg_propagate_change!(source)             # §7.7's machinery, reused verbatim
    # 🔴 #3 CRITICAL: INVALIDATION MUST GO PAST THE DIRECT TARGET — FIXED 2026-08-17.
    # This bumped each monotonic target's falsecount and stopped, never walking the TARGET's own
    # `affected` set. So the retract branch — the one this file's header correctly identifies as the
    # soundness argument — invalidated only the first ring: a table that had cached the TARGET's
    # answers stayed valid and kept serving answers derived from a retracted fact. Upstream's
    # `'$idg_mono_invalidate'` reaches `idg_changed(atrie, IDG_CHANGED_NODE)`
    # (`pl-tabling.c:8141-8146`), which increments the target's own falsecount and then calls
    # `idg_propagate_change(n, flags)` (`:7155-7157`) — walking `affected` TRANSITIVELY.
    for md in mono_affects(source)
        tgt = md.dep.target
        push!(hit, tgt)
        idg_node_for(tgt).falsecount += 1
        union!(hit, idg_propagate_change!(tgt))     # …and everyone who cached the TARGET
    end
    hit
end

"Drop a source's monotonic dependencies — called by `abolish_table_subgoals!`."
function drop_mono_deps!(key::Atom)
    delete!(_MONO_DEPS, key)
    delete!(_MONO_QUEUE, key)
    # 🔴 #18: `collect(keys(...))` — the previous loop deleted from `_MONO_DEPS` WHILE ITERATING it.
    # Julia gives no guarantee there; entries can be skipped, and a skipped entry leaves a dependency
    # targeting an abolished table — the exact hazard this function exists to prevent. Worse, it is
    # called FROM a loop already iterating `collect(keys(_MONO_DEPS))`.
    for src in collect(keys(_MONO_DEPS))            # …and any dependency TARGETING it, or a resume
        mds = _MONO_DEPS[src]                       # would feed answers into a table that is gone
        filter!(md -> md.dep.target != key, mds)
        isempty(mds) && delete!(_MONO_DEPS, src)
    end
    nothing
end
clear_mono!() = (empty!(_MONO_DEPS); empty!(_MONO_QUEUE); nothing)
