# tabling/Worklists.jl — the per-table WORKLIST. Roadmap §1.0, step 3 of 4.
#
# Mirrors `src/pl-tabling.c`'s own TABLE WORKLIST (`:2908`) and ANSWER/SUSPENSION CLUSTERS (`:2708`)
# sections, and Desouter et al. §4.4. File boundary matches upstream's section boundary.
#
# ─── WHAT IT IS, AND WHY A PLAIN QUEUE WILL NOT DO ───────────────────────────────────────────────
# Completion has to combine every ANSWER of a table with every DEPENDENCY waiting on it, exactly
# once, while both keep arriving during the combining. The structure that makes that O(1) to decide
# is a DEQUEUE of CLUSTERS with one invariant (§4.4):
#
#     "an answer is to the left of a dependency IF AND ONLY IF they have not been combined"
#
# So: new answers are appended LEFT (`wkl_add_answer` → `wkl_append_left`, pl-tabling.c:3144), new
# dependencies RIGHT (`wkl_add_suspension` → `wkl_append_right`, :3168). Any adjacent
# (ANSWERS, SUSPENSIONS) pair is therefore uncombined work. Take it, yield the Cartesian product,
# then SWAP the two clusters (`wkl_swap_clusters`, :3105) so the answers now sit to the RIGHT of
# those dependencies — which is precisely what "combined" means. No flags, no per-pair bookkeeping:
# the ORDER IS the state.
#
# ⚠️ CONSECUTIVE SAME-KIND CLUSTERS MERGE ON INSERTION (`add_to_answer_cluster` :3141,
# `add_to_suspension_cluster` :3162). Not an optimisation to skip — without it every single answer
# becomes its own cluster and the swap walk degrades from "batches" to "elements".
#
# ─── JULIA SHAPE, NOT TRANSLITERATION ────────────────────────────────────────────────────────────
# Upstream is a hand-rolled doubly-linked list of malloc'd clusters with a free-list, because C has
# no growable vector. Julia has one. `clusters` is a `Vector{Cluster}` in left-to-right order; the
# swap is an element swap. `[[feedback_native_julia_not_transliteration]]`
#
# ⚠️ ONE DELIBERATE DEVIATION, STATED. Upstream CACHES the work position in `wl->riac` ("rightmost
# innermost answer cluster") and maintains it incrementally at every insert and swap (:3145, :3170,
# `update_riac` :3118). We COMPUTE it by scanning instead. Reason: the cached field is the part of
# this structure most likely to go silently stale — three call sites must agree — and a table holds
# few clusters, since consecutive same-kind insertions merge rather than append. If a table ever
# holds enough clusters for the scan to matter, cache it then, with a test that the cached and
# scanned answers agree.

"Which kind of work a cluster holds. `CLUSTER_ANSWERS` / `CLUSTER_SUSPENSIONS` (pl-tabling.c:2708)."
@enum ClusterKind CLUSTER_ANSWERS CLUSTER_SUSPENSIONS

# 🔴 A DIVERGENCE FROM UPSTREAM, FOUND 2026-08-17 AND NOT YET COSTLY — but it becomes so when the
# trie is wired into `tabled_eval`. Upstream's cluster member is a TRIE NODE POINTER, not a term:
#
#     answer ans = {an};                              /* `an` is a `trie_node *` */
#     wkl_add_answer(worklist *wl, trie_node *an)     /* pl-tabling.c:3133 */
#     typedef struct cluster { ...; buffer members; }  /* pl-tabling.h:106-111 */
#
# So THE TRIE OWNS THE ANSWERS AND THE WORKLIST ONLY REFERENCES THEM. Taking an answer off the
# worklist, upstream can go straight back to its node — to test `TN_IDG_DELETED`, to re-check
# conditionality, to prune (`ctx.garbage` / `prune_answers_worklist`).
#
# Ours stores a bare `Atom`. In Julia that costs no copy — `Atom` is already a heap reference — but
# the IDENTITY is lost: we cannot get from a dequeued answer back to its trie node without re-walking
# its path. Harmless today (worklist and trie are not yet connected); when they are,
# `Cluster.answers` should hold `TrieNode` references instead, matching `:106-111`.

"""A run of consecutive same-kind work items.

Upstream keeps one `members` buffer whose element type depends on `type`; Julia gets two typed
fields instead of an untyped buffer, so `answers`/`deps` are never `Vector{Any}`
(`[[feedback_no_any_typed_containers]]`). Exactly one is populated, per `kind`."""
mutable struct Cluster
    kind::ClusterKind
    answers::Vector{Atom}
    deps::Vector{Dependency}
end
answer_cluster(a::Atom) = Cluster(CLUSTER_ANSWERS, Atom[a], Dependency[])
suspension_cluster(d::Dependency) = Cluster(CLUSTER_SUSPENSIONS, Atom[], Dependency[d])
Base.length(c::Cluster) = c.kind == CLUSTER_ANSWERS ? length(c.answers) : length(c.deps)

"""The per-table worklist: clusters in LEFT-to-RIGHT order.

`key` is the table's variant key, so a worklist can name the table it belongs to when it reports."""
mutable struct Worklist
    key::Atom
    clusters::Vector{Cluster}
end
Worklist(key::Atom) = Worklist(key, Cluster[])
Base.isempty(wl::Worklist) = isempty(wl.clusters)

"""
    wkl_add_answer!(wl, a)

`wkl_add_answer` (`pl-tabling.c:3133`). A new answer joins the LEFTMOST cluster if that cluster is
already answers, else becomes a new cluster appended LEFT — so it sits left of every dependency it
has not been combined with.
"""
function wkl_add_answer!(wl::Worklist, a::Atom)
    if !isempty(wl.clusters) && wl.clusters[1].kind == CLUSTER_ANSWERS
        push!(wl.clusters[1].answers, a)             # add_to_answer_cluster (:3141)
    else
        pushfirst!(wl.clusters, answer_cluster(a))   # wkl_append_left (:3144)
    end
    wl
end

"""
    wkl_add_suspension!(wl, d)

`wkl_add_suspension` (`pl-tabling.c:3158`). A new dependency joins the RIGHTMOST cluster if that is
already suspensions, else becomes a new cluster appended RIGHT — so every answer already present
sits to its left and is therefore uncombined work.
"""
function wkl_add_suspension!(wl::Worklist, d::Dependency)
    if !isempty(wl.clusters) && wl.clusters[end].kind == CLUSTER_SUSPENSIONS
        push!(wl.clusters[end].deps, d)              # add_to_suspension_cluster (:3162)
    else
        push!(wl.clusters, suspension_cluster(d))    # wkl_append_right (:3168)
    end
    wl
end

"""
    wkl_riac(wl) -> Int

Index of the RIGHTMOST answer cluster that has a suspension cluster immediately to its right, or `0`.
Upstream's `wl->riac` (`pl-tabling.c:3099,3145,3170`), computed rather than cached — see the header.

That adjacency IS the uncombined-work test, by the invariant.
"""
function wkl_riac(wl::Worklist)::Int
    for i in (length(wl.clusters) - 1):-1:1
        wl.clusters[i].kind == CLUSTER_ANSWERS &&
            wl.clusters[i + 1].kind == CLUSTER_SUSPENSIONS && return i
    end
    0
end

wkl_has_work(wl::Worklist)::Bool = wkl_riac(wl) != 0

"""
    wkl_swap_clusters!(wl, i)

`wkl_swap_clusters` (`pl-tabling.c:3105`). Exchange the adjacent pair at `i`, `i+1`, moving the
answers to the RIGHT of those dependencies — which is how the invariant records "combined".
"""
function wkl_swap_clusters!(wl::Worklist, i::Int)
    wl.clusters[i], wl.clusters[i + 1] = wl.clusters[i + 1], wl.clusters[i]
    _wkl_merge_adjacent!(wl, i)
    wl
end

"""Merge the same-kind neighbours a SWAP just created — `advance_wkl_state` (`pl-tabling.c:4276`).

🔴 THIS WAS MISSING, AND IT FALSIFIED THIS FILE'S OWN JUSTIFICATION. The header argued that riac may
be COMPUTED rather than cached because "a table holds few clusters, since consecutive same-kind
insertions merge rather than append" — true on INSERTION, and insertion was the only place we
merged. A swap also creates adjacency, and post-swap adjacency was never merged, so the cluster count
grew monotonically across a long completion with `wkl_riac`'s O(n) scan on top of it. Correctness is
unaffected either way (the invariant still combines every pair, and the swap count still strictly
decreases) — this is what makes the header's cost argument true."""
function _wkl_merge_adjacent!(wl::Worklist, i::Int)
    for j in min(i + 1, length(wl.clusters) - 1):-1:max(i - 1, 1)
        j + 1 <= length(wl.clusters) || continue
        a, b = wl.clusters[j], wl.clusters[j + 1]
        a.kind == b.kind || continue
        if a.kind == CLUSTER_ANSWERS
            append!(a.answers, b.answers)
        else
            append!(a.deps, b.deps)
        end
        deleteat!(wl.clusters, j + 1)
    end
    wl
end

"""
    wkl_get_work!(wl) -> Union{Tuple{Vector{Atom},Vector{Dependency}},Nothing}

`table_get_work/3` (Desouter §4.4) / `'\$tbl_wkl_work'`. Take the batch of answers immediately left
of a batch of dependencies, SWAP them, and return the pair whose Cartesian product is the work.

Returns `nothing` when the table has no uncombined pair — which, when it holds for every table in a
scheduling component, is completion.

⚠️ THE SWAP HAPPENS HERE, NOT AT THE CALLER. If a caller took the pair and forgot to swap, the same
pair would be returned forever and completion would never terminate. Making it inseparable from the
take is the difference between an invariant and a convention
(`[[feedback_guarantee_not_convention]]`).
"""
function wkl_get_work!(wl::Worklist)
    i = wkl_riac(wl)
    i == 0 && return nothing
    # ⚠️ SNAPSHOT BEFORE THE SWAP. These were returned BY REFERENCE, which was safe only while the
    # swap did nothing but exchange two slots. Now that it also MERGES the same-kind neighbours it
    # creates (`_wkl_merge_adjacent!`), the surviving cluster's vector is `append!`ed to — so the
    # caller's `ans` would grow under it and the batch would no longer be the batch that was taken.
    # Copying makes the returned batch immutable-in-practice, which is what the caller assumes.
    ans = copy(wl.clusters[i].answers)
    deps = copy(wl.clusters[i + 1].deps)
    wkl_swap_clusters!(wl, i)
    (ans, deps)
end

# ── the per-table registry ───────────────────────────────────────────────────────────────────────
const _WORKLISTS = Dict{Atom, Worklist}()

"The worklist for table `key`, created empty on first use (`new_worklist`, pl-tabling.c:2911)."
worklist_for(key::Atom)::Worklist = get!(() -> Worklist(key), _WORKLISTS, key)
has_worklist(key::Atom)::Bool = haskey(_WORKLISTS, key)
"Drop one table's worklist — called by `abolish_table_subgoals!` so it dies with its table."
drop_worklist!(key::Atom) = (delete!(_WORKLISTS, key); nothing)
clear_worklists!() = (empty!(_WORKLISTS); nothing)
