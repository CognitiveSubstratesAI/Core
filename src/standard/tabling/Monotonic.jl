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

const _MONO_DEPS  = Dict{Atom,Vector{MonoDep}}()   # source key ⇒ dependencies watching it
const _MONO_QUEUE = Dict{Atom,Vector{Atom}}()      # target key ⇒ answers queued by LAZY deps

"""
    mono_assert_dep!(source, cont, target; lazy=false)

`mon_assert_dep/4` (`boot/tabling.pl:1562`). Record that `target` must gain answers whenever
`source` does, by resuming `cont`.
"""
function mono_assert_dep!(source::Atom, cont::Continuation, target::Atom; lazy::Bool = false)
    push!(get!(_MONO_DEPS, source, MonoDep[]), MonoDep(Dependency(source, cont, target), lazy))
    nothing
end

"Dependencies watching `source` — `monotonic_affects/6`."
mono_affects(source::Atom)::Vector{MonoDep} = get(_MONO_DEPS, source, MonoDep[])

"""
    mono_propagate_assert!(source, answer, space) -> Dict{Atom,Vector{Atom}}

`propagate_assert` — the ASSERT branch of `mon_propagate/3`. Push `answer` through every dependency
watching `source` and return the new answers grouped by TARGET table.

EAGER dependencies propagate now and their answers are inserted into the target's trie. LAZY ones
are QUEUED against the target instead (`'\$mono_idg_changed'`), to be drained by
`mono_drain_queue!`. Both are returned, so a caller can see what a lazy dependency deferred rather
than having to infer it.
"""
function mono_propagate_assert!(source::Atom, answer::Atom, space)::Dict{Atom,Vector{Atom}}
    out = Dict{Atom,Vector{Atom}}()
    for md in mono_affects(source)
        d = md.dep
        for a in _project(Atom[answer], d.cont.goal)
            for (at, bnd) in resume_continuation(d.cont, a, space)
                is_empty_atom(at) && continue
                new = subst(at, bnd)
                push!(get!(out, d.target, Atom[]), new)
                if md.lazy
                    push!(get!(_MONO_QUEUE, d.target, Atom[]), new)   # deferred: '$mono_idg_changed'
                else
                    trie_insert!(answer_trie_for(d.target), new)      # eager: straight into the table
                end
            end
        end
    end
    for (k, v) in out; out[k] = unique(v); end
    out
end

"""
    mono_drain_queue!(target) -> Vector{Atom}

Drain the answers a LAZY dependency deferred for `target`, inserting them into its trie. Returns the
answers that were NEW — the same value-based signal the completion loop uses, not a count.
"""
function mono_drain_queue!(target::Atom)::Vector{Atom}
    queued = get(_MONO_QUEUE, target, Atom[])
    isempty(queued) && return Atom[]
    t = answer_trie_for(target)
    added = Atom[a for a in queued if trie_insert!(t, a)]
    delete!(_MONO_QUEUE, target)
    added
end

mono_queued(target::Atom)::Vector{Atom} = copy(get(_MONO_QUEUE, target, Atom[]))

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
    for md in mono_affects(source)                  # …and the monotonic targets too
        push!(hit, md.dep.target)
        idg_node_for(md.dep.target).falsecount += 1
    end
    hit
end

"Drop a source's monotonic dependencies — called by `abolish_table_subgoals!`."
function drop_mono_deps!(key::Atom)
    delete!(_MONO_DEPS, key)
    delete!(_MONO_QUEUE, key)
    for (src, mds) in _MONO_DEPS                    # …and any dependency TARGETING it, or a resume
        filter!(md -> md.dep.target != key, mds)    # would feed answers into a table that is gone
        isempty(mds) && delete!(_MONO_DEPS, src)
    end
    nothing
end
clear_mono!() = (empty!(_MONO_DEPS); empty!(_MONO_QUEUE); nothing)
