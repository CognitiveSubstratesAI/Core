# tabling/IDG.jl — the INCREMENTAL DEPENDENCY GRAPH. SWI §7.7 (and the substrate for §7.8).
#
# Mirrors `src/pl-tabling.c`'s IDG CONSTRUCTION (`:6105`) and IDG QUERYING (`:6612`) sections, and
# the `idg_node` struct (`pl-tabling.h:194-216`).
#
# ─── WHAT IT IS ──────────────────────────────────────────────────────────────────────────────────
# Tabling caches answers. When the SPACE changes, cached answers may be wrong. Our current answer is
# the REVISION STAMP: any mutation bumps `space.revision`, and every table whose stamp no longer
# matches is evicted on next lookup. That is SOUND — it never serves a stale answer — and MAXIMALLY
# COARSE: one unrelated `add-atom` throws away every table in the process.
#
# The IDG makes invalidation PER-TABLE. Each table records which tables it depends on; a change
# invalidates only the tables reachable from it.
#
# ─── THE TWO DIRECTIONS, AND GETTING THEM THE RIGHT WAY ROUND ────────────────────────────────────
# `idg_node` (`pl-tabling.h:197-198`) holds BOTH:
#
#     TablePP affected;     /* parent IDG nodes */      <- who depends on ME
#     TablePP dependent;    /* child IDG nodes  */      <- who I depend on
#
# and `idg_add_edge(atrie, ctrie)` calls `idg_add_child(ctrie->IDG, atrie->IDG)` — note the ORDER:
# the CURRENT table (`ctrie`, the one being evaluated) becomes the PARENT, and the table it just
# consulted (`atrie`) the CHILD. So "parent" means "depends on", and INVALIDATION FLOWS UP THROUGH
# `affected` — from the changed table to the tables that used it.
#
# Getting this backwards is silent and catastrophic: invalidation would flow to the tables the
# changed one CONSULTED, leaving every table that actually cached its answers untouched and stale.
# Both directions are asserted in the test, in both roles.
#
# ─── `falsecount` IS A COUNT, NOT A FLAG, AND THE STATUS READS IT ────────────────────────────────
# `complete_or_invalid_status` (`pl-tabling.c:3233`) returns `invalid` when `n->falsecount > 0`.
# It counts because a table can be invalidated from several children before it is re-evaluated.
#
# ⚠️ UPSTREAM RESETS IT TO ZERO ON A CALL, and says why (`:6480` note (*)): *"If we make a call we
# should reset the falsecount to 0 as this may have added a new dependency… Setting the falsecount
# to zero should be considered similar to re-evaluating an incremental tabled predicate when it is
# called."* Kept, because a table re-evaluated with a NEW dependency set must not carry invalidation
# counted against its OLD one.
#
# ─── SCOPE: BOTH HALVES NOW — THE GRAPH *AND* THE RE-EVALUATION ──────────────────────────────────
# The graph half is above. The RE-EVALUATION half (`prepare_reeval!` / `reeval_complete!` /
# `reset_reevaluation!` / the DECREMENT walk) is the bottom of this file, mirroring `reeval/3`
# (`boot/tabling.pl:1858-1893`) and `pl-tabling.c:8315-8564`.
#
# 🔴 THE ONE PLACE WE DELIBERATELY DO NOT PORT UPSTREAM IS ITS VERDICT. `reeval_complete`
# (`:8484-8485`) decides "same answers" by CARDINALITY — `new_answer == false && answer_count ==
# value_count`. That is safe in Prolog because an answer IS its substitution; here every answer
# carries a VALUE, and two measured mutations change the value at CONSTANT cardinality
# (`trie_insert_moded!` replaces `node.answer` in place; `merge_bottom_into!` widens a WFS bottom's
# condition). The cardinality clause is replaced by a CONTENT DIGEST — see the long argument at
# `tabling/AnswerTrie.jl`'s digest section, and the mutant test in `test_reeval.jl` that shows the
# cardinality version failing on exactly that case.
#
# ─── WHAT IS NOT PORTED, AND WHY ─────────────────────────────────────────────────────────────────
#   * `force_reeval`, `mono_reevaluating`, `lazy_queued`, `tt_*` (`pl-tabling.h:203-215`) — §7.8
#     lazy-monotonic and transaction machinery. `Monotonic.jl` does not have them either; adding
#     the fields here without the paths that set them would make the struct claim more than the
#     code does.
#   * `trie_discard_clause` (the CHANGED branch of `reeval_complete`, `:8496`) — it drops the
#     JIT-COMPILED clause form of the answer trie so it is recompiled. We have no compiled answer
#     form, so the changed branch reduces to "leave the dependants invalid", which is exactly what
#     not calling the decrement walk does.
#   * shared tabling (`claim_answer_table`, the `deadlock`/`retry_reeval` arm of `reeval/3`) — we
#     are single-threaded here; `with_reeval` keeps `reeval/3`'s catch SHAPE because the abort path
#     is real, but there is no deadlock to retry.
#   * `reeval_paths` / `false_path/2` (`boot/tabling.pl:1868-1880`) — upstream RANKS the invalid
#     tables and re-evaluates the deepest false paths first, so an outer table re-evaluates against
#     already-fresh children. That is a SCHEDULING optimisation over the same lifecycle; the
#     lifecycle is what lands here. Doing it out of order costs re-work, not correctness.

"""The previous COMPLETE state of a table, frozen by `prepare_reeval!` so `reeval_complete!` can
decide whether re-evaluation changed anything — and so `reset_reevaluation!` can put it back.

🔴 UPSTREAM HAS NO SUCH STRUCT, AND THE DIFFERENCE IS MECHANISM, NOT SEMANTICS. `prepare_reeval`
(`pl-tabling.c:8315`) keeps ONE trie and MARKS it: `reeval_prep_node` sets `TN_IDG_DELETED` /
`TN_IDG_UNCONDITIONAL` on every existing answer node, re-evaluation clears the mark on any answer
that reappears, and `reeval_complete_node` (`:8437`) then deletes what stayed marked. The abort path
(`reset_reevaluation`, `:8548`) restores "the state after the initial preparation" by leaving those
marks in place, which is why `prepare_reeval` skips the marking pass when `aborted` is set.

We snapshot the trie's ROOT NODE instead and install a fresh one, because our re-evaluation refills
the table through the ordinary insert path (`trie_insert!` from `tabled_eval`'s completion mirror),
which has no way to distinguish "re-derived" from "left over" — mark-and-sweep needs a marker that
the insert path maintains, and it does not. Swapping the root gets the same three properties with no
new coupling:

  * a disappeared answer is GONE rather than lingering (upstream's sweep);
  * the OLD answers survive intact for the comparison and for the abort restore — same `TrieNode`
    objects, so per-answer `instances` are preserved exactly rather than rebuilt;
  * the `AnswerTrie` OBJECT ITSELF is never replaced, so any live reference keeps working and
    `test_reeval.jl` can assert identity on an unrelated table.

⇒ `aborted` therefore does NOT gate a marking pass here (there are no marks to keep); it records
that the last attempt failed and is cleared by the next successful `reeval_complete!`. It is still
read: `idg_was_aborted` exposes it, and `reset_reevaluation!` sets `falsecount = 1` so the table is
re-evaluated again rather than being trusted."""
struct ReevalSnapshot
    answers::Vector{Atom}          # the previous complete answer set, IN ORDER
    digest::UInt                   # `table_digest(trie)` — answers AND per-answer metadata
    root::TrieNode                 # the previous trie root, held for the comparison and the abort
    count::Int                     # upstream's `value_count` at prepare time
end

"""A node of the incremental dependency graph — upstream's `idg_node` (`pl-tabling.h:194`).

`affected` and `dependent` are the two directions, named as upstream names them: `affected` = the
tables that DEPEND ON this one (invalidation flows here), `dependent` = the tables this one depends
on. See the header — reversing them is silent and leaves every stale table untouched."""
mutable struct IDGNode
    key::Atom                      # the table's variant key — upstream's `atrie`
    affected::Set{Atom}            # parents: who depends on me   ⇒ invalidation flows UP through this
    dependent::Set{Atom}           # children: who I depend on
    falsecount::Int                # invalidate COUNT; `> 0` ⇒ status :invalid (pl-tabling.c:3233)
    answer_count::Int              # #answers in the previous COMPLETE state — RECORDED, NOT THE VERDICT
    reevaluating::Bool             # a re-evaluation is in progress (`pl-tabling.h:201`)
    aborted::Bool                  # the last re-evaluation was aborted (`pl-tabling.h:202`)
    new_answer::Bool               # an answer was ADDED during this re-evaluation (`pl-tabling.h:200`)
    monotonic::Bool                # §7.8
    lazy::Bool                     # §7.8's eager/lazy split
    snapshot::Union{ReevalSnapshot,Nothing}   # the previous complete state, frozen by `prepare_reeval!`
    # ── `stats` (`pl-tabling.h:216-219`, upstream's O_TRIE_STATS block) ──────────────────────────
    # ⚠️ NOT DECORATION. `reevaluated` is what makes the ANTI-VACUITY assertion in `test_reeval.jl`
    # possible: every other re-evaluation test passes on an implementation that never re-evaluates,
    # because the revision stamp recomputes and returns the right answers anyway. A counter is the
    # only way to assert that an UNRELATED table SURVIVED a change rather than being quietly redone.
    invalidated::Int               # # times falsecount went 0 -> 1
    reevaluated::Int               # # times `reeval_complete!` finished
end
IDGNode(key::Atom) = IDGNode(key, Set{Atom}(), Set{Atom}(), 0, 0,
                             false, false, false, false, false, nothing, 0, 0)

const _IDG = Dict{Atom,IDGNode}()

"The IDG node for a table, created on first use (`new_idg_node`)."
idg_node_for(key::Atom)::IDGNode = get!(() -> IDGNode(key), _IDG, key)
has_idg_node(key::Atom)::Bool = haskey(_IDG, key)
drop_idg_node!(key::Atom) = begin
    n = get(_IDG, key, nothing)
    n === nothing && return nothing
    # unlink BOTH directions, or a dropped table leaves dangling edges that propagate into nothing
    for p in n.affected;  haskey(_IDG, p) && delete!(_IDG[p].dependent, key); end
    for c in n.dependent; haskey(_IDG, c) && delete!(_IDG[c].affected,  key); end
    delete!(_IDG, key)
    nothing
end
clear_idg!() = (empty!(_IDG); nothing)

"""
    idg_add_edge!(consulted, current)

`idg_add_edge(atrie, ctrie)` → `idg_add_child(ctrie->IDG, atrie->IDG)` (`pl-tabling.c`).

`current` (the table being evaluated) comes to DEPEND ON `consulted`. Argument order follows
upstream's call site, where the consulted table is named first.
"""
function idg_add_edge!(consulted::Atom, current::Atom)
    consulted == current && return nothing          # a table does not depend on itself
    push!(idg_node_for(current).dependent, consulted)
    push!(idg_node_for(consulted).affected, current)
    nothing
end

"""
    idg_propagate_change!(key) -> Set{Atom}

`idg_propagate_change` (`pl-tabling.c:7087`). Bump `falsecount` on every table REACHABLE UPWARD from
`key` through `affected`, and return the set invalidated.

Transitive: if C depends on B and B on A, changing A invalidates both. Cycle-safe by construction —
a node already visited is not re-walked, which matters because tabling's whole purpose is admitting
recursive dependencies.

⚠️ `key` ITSELF IS NOT INVALIDATED. Upstream walks `n->affected`, not `n`. The table that CHANGED is
handled by whatever changed it (a re-evaluation, or the revision-stamp eviction); the IDG's job is
everyone who cached ITS answers.
"""
function idg_propagate_change!(key::Atom)::Set{Atom}
    touched = Set{Atom}()
    stack = Atom[key]
    while !isempty(stack)
        k = pop!(stack)
        n = get(_IDG, k, nothing)
        n === nothing && continue
        for parent in n.affected
            p = get(_IDG, parent, nothing)
            p === nothing && continue
            # 🔴 A NODE BEING RE-EVALUATED IS SKIPPED — `if ( n->reevaluating ) continue;`
            # (`pl-tabling.c:7011-7012`). It sits at the TOP of `idg_changed_loop`, BEFORE the
            # increment/decrement split, so it applies to BOTH DIRECTIONS — and it must, for two
            # different reasons. Incrementing a table mid-re-evaluation would count invalidation
            # against a dependency set that is being rebuilt (`prepare_reeval!` has just zeroed
            # `falsecount` and cleared `dependent` for exactly that reason), and decrementing one
            # would drive a count that is deliberately at 0 below zero.
            p.reevaluating && continue
            # 🔴 INCREMENT ALWAYS, RECURSE ONLY ON 0->1 — FIXED 2026-08-17 (audit vs the C).
            # This was `parent in seen && continue`, i.e. ONE increment per node per call and a
            # re-walk on first visit regardless. Upstream (`idg_changed_loop`, `pl-tabling.c:7043`):
            #     if ( ATOMIC_INC(&n->falsecount) == 1 ) { ... pushSegStack(...) }
            # Two differences, both material. (a) The count rises ONCE PER INCOMING EDGE from an
            # invalidated ancestor: in a diamond A->{B,C}->D upstream leaves `D.falsecount == 2` and
            # ours left 1. (b) Recursion stops on an already-invalid node, so the walk is bounded by
            # transitions, not by a visited set — cycle-safety comes from the SAME test.
            # `falsecount` is a COUNT precisely so re-validation can decrement it symmetrically
            # (`:7053`); undercounting would let one re-validation mark a table valid while a second
            # invalidating dependency is still outstanding. Latent today (no re-validation path), but
            # this file's header asserted the counting semantics were ported, and they were not.
            p.falsecount += 1
            push!(touched, parent)
            p.falsecount == 1 && (p.invalidated += 1; push!(stack, parent))   # TRIE_STAT_INC(n, invalidated)
        end
    end
    touched
end

"""
    idg_changed!(key; mono=false) -> Set{Atom}

`idg_changed` (`pl-tabling.c:7133-7169`) — THE entry point every upstream caller uses.
`idg_propagate_change!` is only its inner walk, and calling that directly skips three things:

1. **the `falsecount == 0` guard** — a table already invalid is not re-propagated, so repeated
   changes to the same table cost nothing and cannot inflate its dependants' counts;
2. **incrementing `key` ITSELF** (`:7155`) — the CHANGED table *is* invalidated. Ours documented the
   opposite ("`key` ITSELF IS NOT INVALIDATED") as if it were the whole story; that is true of the
   inner walk and false of the operation, which is why the monotonic retract path was leaving its
   source table valid;
3. **the incomplete-table check** (`:7148-7153`) — changing a table mid-completion is a permission
   error upstream, not a silent corruption of a running fixpoint. `mono=true` is upstream's
   `IDG_CHANGED_MONO`, which STOPS propagation on an incomplete table instead of erroring.
"""
function idg_changed!(key::Atom; mono::Bool = false)::Set{Atom}
    n = get(_IDG, key, nothing)
    n === nothing && return Set{Atom}()
    n.falsecount == 0 || return Set{Atom}()                 # (1) already invalid ⇒ done
    if key in _TABLE_INPROG                                 # (3) `table_is_incomplete`
        mono && return Set{Atom}()
        throw(ArgumentError("permission_error(update, variant, $(key)) — a table cannot be " *
                            "invalidated while it is being completed (pl-tabling.c:7148)"))
    end
    n.falsecount += 1                                       # (2) the CHANGED table is invalidated
    n.invalidated += 1                                      # TRIE_STAT_INC(n, invalidated) (:7159)
    hit = idg_propagate_change!(key)
    push!(hit, key)
    hit
end

"Is this table invalidated? `complete_or_invalid_status`: `n->falsecount > 0` ⇒ `invalid`."
idg_is_invalid(key::Atom)::Bool = (n = get(_IDG, key, nothing); n !== nothing && n.falsecount > 0)

"""
    idg_reset_falsecount!(key)

`:6480` note (*): *"If we make a call we should reset the falsecount to 0 as this may have added a
new dependency… similar to re-evaluating an incremental tabled predicate when it is called."*

A table re-evaluated with a NEW dependency set must not carry invalidation counted against its OLD
one.
"""
idg_reset_falsecount!(key::Atom) = (n = get(_IDG, key, nothing);
                                    n === nothing || (n.falsecount = 0); nothing)

"Is a re-evaluation in progress? `complete_or_invalid_status` reports such a table as `fresh`\n(`pl-tabling.c:3235`), which is why `prepare_reeval!` sets the trie status to `:fresh` and not to a\nstatus of our own invention."
idg_is_reevaluating(key::Atom)::Bool =
    (n = get(_IDG, key, nothing); n !== nothing && n.reevaluating)

"Every table currently invalid — `idg_falsecount`-style querying (`pl-tabling.c:6612`)."
idg_invalid_tables()::Vector{Atom} =
    sort!(Atom[k for (k, n) in _IDG if n.falsecount > 0]; by = string)

# ═══════════════════════════════════════════════════════════════════════════════
# §7.7, SECOND HALF — RE-EVALUATION.
#
# `reeval/3` (`boot/tabling.pl:1858-1893`) is the whole lifecycle in six lines of Prolog:
#
#     reeval(ATrie, Goal, Return) :- catch(try_reeval(...), deadlock, retry_reeval(...)).
#     try_reeval(...) :- findall(Path, false_path(ATrie,Path), Paths0), ..., reeval_paths(Paths),
#                        do_reeval(ATrie, Goal, Return).
#     do_reeval(ATrie, Goal, Return) :- '$tbl_reeval_prepare_top'(ATrie, Clause),
#         (   Clause == 0 -> moded_gen_answer(...)     % already complete, answer subsumption
#         ;   nonvar(Clause) -> trie_gen_compiled(...) % already complete
#         ;   call(Goal) ).                            % ACTUALLY RE-EVALUATE
#
# and the C is `prepare_reeval` (`:8315`) at the front, `reeval_complete` (`:8477`) at the back, and
# `reset_reevaluation` (`:8548`) on the exception path. `with_reeval` below is that shape.
#
# ─── WHY THIS EXISTS AT ALL: WHAT THE GRAPH HALF ALONE CANNOT DO ─────────────────────────────────
# The graph half marks a table INVALID. Something then has to recompute it — and the interesting
# case is that recomputing it very often produces THE SAME ANSWERS. `p` depends on `q`; `q` is
# re-derived after a change and comes out identical; `p` has no reason to run again. Upstream turns
# that observation into the DECREMENT walk: on a no-change verdict, `reeval_complete` calls
# `idg_propagate_change(n, 0)`, which walks `affected` SUBTRACTING one from each falsecount and
# recursing on the 1->0 transition — the exact mirror of the increment walk, and the reason
# `falsecount` had to be a count rather than a flag in the first place.
#
# Without it, one change at the bottom of a dependency chain re-runs everything above it,
# unconditionally, which is the coarseness §7.7 exists to remove.

"""
    idg_clean_dependent!(n)

`idg_clean_dependent` (`pl-tabling.c:6128-6134`): drop the CHILD links of a node about to be
re-evaluated, because re-evaluation rebuilds them (`idg_add_edge!` fires at every tabled call).

⚠️ ASYMMETRIC, AND DELIBERATELY SO — THIS IS UPSTREAM'S SHAPE, NOT AN OVERSIGHT OF OURS. Upstream
clears only `node->dependent`; each child's `affected` KEEPS its back-link to us, even though we no
longer claim to depend on it. Compare `drop_idg_node!` above, which unlinks BOTH directions and must.

The asymmetry is the SAFE direction and that is why it is kept. A stale back-link can only cause an
UNNECESSARY invalidation (a child we no longer consult still bumps our falsecount) — sound, merely
imprecise, and self-correcting on the next re-evaluation. Clearing both would risk the opposite: if
the re-evaluation does not in fact re-add an edge (a path that answers from a cache without calling,
a re-evaluation that aborts), the dependency is GONE and the table is never invalidated again —
stale answers served forever, the one failure an IDG must not have.
"""
idg_clean_dependent!(n::IDGNode) = (empty!(n.dependent); nothing)

"""
    idg_propagate_revalidate!(key) -> Set{Atom}

The DECREMENT direction of `idg_changed_loop` (`pl-tabling.c:7051-7070`) — the `else` branch, taken
when `idg_propagate_change(n, 0)` is called with no flags.

Walk UP through `affected` from `key`, SUBTRACTING one from each falsecount, and recurse only on the
1->0 transition — the exact mirror of `idg_propagate_change!`'s 0->1 rule, and cycle-safe by the same
test rather than by a visited set.

Three guards, each ported for a stated reason:

  * `p.reevaluating` — `:7011-7012`, the skip that sits above the direction split and applies to
    both (a table mid-re-evaluation has a deliberately-zeroed falsecount).
  * `parent in _TABLE_INPROG` — `!table_is_incomplete(n->atrie)`, `:7050`. A table still being
    completed has no settled count to revalidate.
  * `p.falsecount == 0` — WE CLAMP WHERE UPSTREAM DOES NOT, and upstream says why we should. Its
    guard is `(n->monotonic ? n->falsecount > 0 : true /* see (***) */)`, and note (***) at `:6954`
    reads: *"We can decrement below zero if an internal '\$mono_reeval_done'/3 completes a component
    after which a more external one propagates a no-change. Giving up this sanity check is dubious.
    Possibly we need some other way to detect this situation."* So upstream ALLOWS the underflow on
    the non-monotonic path, on a `size_t` where it wraps to an enormous number, and records that it
    is unhappy about it. `falsecount > 0` means INVALID; a wrapped count means "invalid forever".
    Clamping keeps the field's only meaning intact, and the stale back-links `idg_clean_dependent!`
    leaves behind make an extra decrement reachable here rather than hypothetical.
"""
function idg_propagate_revalidate!(key::Atom)::Set{Atom}
    touched = Set{Atom}()
    stack = Atom[key]
    while !isempty(stack)
        k = pop!(stack)
        n = get(_IDG, k, nothing)
        n === nothing && continue
        for parent in n.affected
            p = get(_IDG, parent, nothing)
            p === nothing && continue
            p.reevaluating && continue                  # :7011-7012 — both directions
            parent in _TABLE_INPROG && continue         # !table_is_incomplete (:7050)
            p.falsecount == 0 && continue               # the clamp — see the docstring, note (***)
            p.falsecount -= 1
            push!(touched, parent)
            p.falsecount == 0 && push!(stack, parent)   # 1->0: this table is VALID again ⇒ recurse
        end
    end
    touched
end

"""
    prepare_reeval!(key; force = false) -> Bool

`prepare_reeval` (`pl-tabling.c:8315-8339`) plus the bail its two entry points share.

Returns `false` — nothing prepared, nothing to do — when the table is not invalid. That guard is
upstream's, at BOTH entry points, with the same comment at each: `'\$tbl_reeval_prepare_top'`
(`:8358`) and `'\$tbl_reeval_prepare'` (`:8393`) both read

    if ( idg->falsecount == 0 ... )   /* someone else re-evaluated it */

and it is load-bearing rather than defensive: `reeval_paths` re-evaluates a whole false PATH, so by
the time the table the caller actually asked for is reached, a table deeper in the path may already
have re-validated it. Preparing anyway would discard a table that is already fresh, and — worse —
would leave `reevaluating` set on a table nobody is going to complete.

`force` is `force_reeval`'s hole in that guard (`:8358` again, `&& !idg->force_reeval`). §7.8's lazy
monotonic path is what sets that field upstream; we have no such field (see the header's not-ported
list), so it is a keyword the caller supplies rather than state we pretend to track.

After preparing: `answer_count` and the snapshot hold the previous complete state, `falsecount` is
zeroed (`:8324`), the child edges are dropped (`:8325`), the trie is emptied for the re-derivation
and its status becomes `:fresh` — which is what `complete_or_invalid_status` reports for a
re-evaluating table (`:3235`), not a status of our own.

⚠️ AND IT REFUSES TO NEST — `n.reevaluating` already set ⇒ `false`, which upstream expresses
differently rather than not at all: `try_reeval/3` (`boot/tabling.pl:1871-1875`) branches on
`nb_current('\$tbl_reeval', true)` to take the nested path instead of re-planning. We have no
false-path planner to skip, so the only thing nesting could do here is overwrite a live snapshot with
the half-built table it is meant to protect. Refusing is the whole of the nested case for us.

⚠️ NO WORKLIST RESET, and it is not an omission. Upstream ends with
`wl->negative = wl->has_answers = wl->neg_delayed = false` because ITS worklists outlive completion.
Ours do not: `tabled_eval`'s `finally` calls `drop_worklist!(m)` for every completed member (with
upstream's own justification quoted there — `complete_worklist`'s `destroy` is always true in our
configuration). A complete table therefore has no live worklist to reset.
"""
function prepare_reeval!(key::Atom; force::Bool = false)::Bool
    n = get(_IDG, key, nothing)
    n === nothing && return false
    (n.falsecount == 0 && !force) && return false        # :8358 / :8393 — someone else did it
    n.reevaluating && return false                       # already in progress ⇒ not re-prepared
    t = answer_trie_for(key)
    n.snapshot     = ReevalSnapshot(trie_answers(t), table_digest(t), t.root, t.count)
    # ⚠️ RECORDED, NOT THE VERDICT. `idg->answer_count = atrie->value_count` (:8323) is the number
    # `reeval_complete` compares against, and that comparison is the one thing here we do NOT port
    # (see the header, and the digest argument in AnswerTrie.jl). Kept because it is genuinely
    # upstream's field and `library(tables)`-style introspection is entitled to it — but nothing
    # decides anything from it, and a reader who assumes otherwise should find this note first.
    n.answer_count = t.count
    n.new_answer   = false                               # :8324
    n.falsecount   = 0                                   # :8325
    idg_clean_dependent!(n)                              # :8326
    # `t.inserts` is NOT reset: its docstring makes it a monotonic stamp source, "never decremented
    # on delete". Re-derived answers therefore get FRESH, HIGHER `seq` values, so insertion order
    # inside the new root is correct, and an abort that restores the old root restores its old,
    # lower stamps untouched.
    t.root  = TrieNode()
    t.count = 0
    set_table_status!(t, :fresh)                         # `complete_or_invalid_status` -> fresh (:3235)
    n.reevaluating = true                                # :8331
    true
end

"""
    reeval_same_answers(snap, t) -> Bool

THE VERDICT — the replacement for `reeval_complete`'s cardinality test (`pl-tabling.c:8484-8485`).

Two parts, and they are not redundant:

  * `answers_identical` is the REAL DECISION — exact, ordered, pairwise `variant_eq`. No hash, so no
    collision, and `variant_eq` is already correct on a WFS bottom (its `==` is `dnf_equiv`).
  * `table_digest(t) == snap.digest` covers what an answer VECTOR cannot see: the per-answer
    metadata on the trie node, today `length(node.instances)`, which §7.11.1 subgoal abstraction
    reads. Same answers derived from a different set of goal instances is not a no-change for it.

Passed as `verdict` to `reeval_complete!` so a test can substitute a deliberate mutant — which
`test_reeval.jl` does, running the cardinality version (`length(old) == length(new)`) against a
mode-directed table whose aggregate moves at constant cardinality and showing it get the answer
wrong. A digest is only justified once the cheap test is shown to break.
"""
reeval_same_answers(snap::ReevalSnapshot, t::AnswerTrie)::Bool =
    answers_identical(snap.answers, trie_answers(t)) && table_digest(t) == snap.digest

"""
    reeval_complete!(key; verdict = reeval_same_answers) -> Symbol

`reeval_complete` (`pl-tabling.c:8477-8505`). Decide whether the re-evaluation changed the table and
act on it. Returns `:same`, `:changed`, or `:not_reevaluating` (no `prepare_reeval!` is outstanding —
upstream's `if ( (n=atrie->data.IDG) && n->reevaluating )` guard, `:8480`).

  `:same`    ⇒ `idg_propagate_change(n, 0)` (`:8495`) — the DECREMENT walk. Every dependant whose
               falsecount returns to 0 is VALID AGAIN AND IS NEVER RE-RUN. That is the entire payoff
               of §7.7 over the revision stamp.
  `:changed` ⇒ dependants keep their falsecount and will re-evaluate when next called. Upstream also
               calls `trie_discard_clause` here; we have no compiled answer form (see the header).

`new_answer` is honoured as upstream sets it — `\$tbl_wkl_add_answer` (`:3669-3671`) flips it when a
node is ADDED while `reevaluating`. It can only make the verdict MORE conservative, never less.

⚠️ AND OUR DIGEST SUBSUMES THE OTHER THING UPSTREAM USES IT FOR. `reeval_complete_node` (`:8449-8455`)
sets `new_answer` when an answer's CONDITIONALITY changed — unconditional became conditional or the
reverse — because in SWI the delay list hangs off the trie node and the answer TERM is identical
either way, so no content comparison could see it. Here the condition RIDES ON THE VALUE
(`WFSBottom` carries the DNF — roadmap 7.A, and `Delays.jl` explains why it must), so a
conditionality change IS a value change and `answers_identical` catches it directly. That is why
nothing in our insert path needs to replicate `reeval_complete_node`'s three-way mark inspection.
"""
function reeval_complete!(key::Atom; verdict::Function = reeval_same_answers)::Symbol
    n = get(_IDG, key, nothing)
    (n === nothing || !n.reevaluating) && return :not_reevaluating      # :8480
    snap = n.snapshot
    snap === nothing && return :not_reevaluating
    t = answer_trie_for(key)
    same = !n.new_answer && verdict(snap, t)::Bool                      # :8484-8485, verdict replaced
    set_table_status!(t, :complete)
    n.answer_count = t.count
    n.reevaluating = false                                              # :4815, after reeval_complete
    n.aborted      = false                                              # :8503
    n.new_answer   = false
    n.snapshot     = nothing
    n.reevaluated += 1                                                  # TRIE_STAT_INC(n, reevaluated)
    same && idg_propagate_revalidate!(key)                              # :8495
    same ? :same : :changed
end

"""
    reset_reevaluation!(key) -> Bool

`reset_reevaluation` (`pl-tabling.c:8548-8564`) — the ABORT path, taken when an exception escapes a
re-evaluation in progress. Its own header states the contract: *"This must ensure that a subsequent
call on the table will restart the re-evaluation and forward a not-changed to the affected nodes if
the table evaluates to the same values."*

So: the OLD answers come back (a half-built table must never be served), `aborted` records that the
attempt failed, and `falsecount = 1` leaves the table INVALID so the next call re-evaluates it
properly instead of trusting what is there.

⚠️ UPSTREAM'S `assert(n->answer_count == atrie->value_count)` (`:8560`) IS NOT REPRODUCED, and the
reason is that here it would be vacuous rather than a check. Upstream's reset ENUMERATES the trie
undoing per-node marks, so the assert genuinely tests that the undo was complete. We restore the
snapshotted root wholesale, from which both numbers come — asserting them equal would test the
assignment two lines above it. A check that cannot fail is worse than no check: it reads as
verification. `[[feedback_verify_the_oracle_runs]]`

⚠️ Upstream's TBD is inherited and worth repeating: the child links dropped by `prepare_reeval!` are
NOT restored, so a modification to a former dependency during the aborted window is not counted
against this table. `falsecount = 1` makes the table re-evaluate regardless, which is what bounds
the damage.
"""
function reset_reevaluation!(key::Atom)::Bool
    n = get(_IDG, key, nothing)
    (n === nothing || !n.reevaluating) && return false
    snap = n.snapshot
    snap === nothing && return false
    t = answer_trie_for(key)
    t.root  = snap.root                       # the old answers, same TrieNode objects ⇒ `instances` intact
    t.count = snap.count
    n.new_answer   = false                    # :8557
    n.aborted      = true                     # :8558
    n.falsecount   = 1                        # :8559 — still INVALID, so the next call retries
    n.reevaluating = false                    # :8562 (COMPLETE_WORKLIST's argument)
    n.snapshot     = nothing
    set_table_status!(t, :complete)           # `set(atrie, TRIE_COMPLETE)` (:8561)
    true
end

"""
    with_reeval(recompute, key; verdict = reeval_same_answers) -> Symbol

`reeval/3` (`boot/tabling.pl:1858-1893`) as one call: prepare, run `recompute`, complete — and on an
exception, `reset_reevaluation!` before re-raising.

Returns `:already_valid` when `prepare_reeval!` declined (the table was not invalid), otherwise
`reeval_complete!`'s verdict.

The `catch` mirrors `reeval/3`'s. What it does NOT mirror is the recovery: upstream catches
`deadlock` specifically and retries via `retry_reeval/2` because a SHARED table can be claimed by
another thread. We are single-threaded, so there is no deadlock to retry — the abort path is real,
the retry is not, and inventing one would be fiction. Rethrow, having left the table restored and
invalid, and let the caller's next call re-evaluate.
"""
function with_reeval(recompute::Function, key::Atom;
                     verdict::Function = reeval_same_answers)::Symbol
    prepare_reeval!(key) || return :already_valid
    try
        recompute()
    catch
        reset_reevaluation!(key)
        rethrow()
    end
    reeval_complete!(key; verdict = verdict)
end

"""Record that re-evaluation ADDED an answer — `idg->new_answer = true` (`pl-tabling.c:3669-3671`).

A no-op unless a re-evaluation is in progress, exactly as upstream's guard
(`if ( (idg=...) && idg->reevaluating )`). Conservative only: it can force a `:changed` verdict, it
can never force a `:same` one."""
idg_note_new_answer!(key::Atom) = (n = get(_IDG, key, nothing);
                                   (n === nothing || !n.reevaluating) || (n.new_answer = true);
                                   nothing)

"Was this table's last re-evaluation aborted? — `idg_node.aborted` (`pl-tabling.h:202`)."
idg_was_aborted(key::Atom)::Bool = (n = get(_IDG, key, nothing); n !== nothing && n.aborted)

"""How many times this table has been RE-EVALUATED — upstream's `stats.reevaluated`.

The anti-vacuity instrument: a table that was not re-evaluated by a change must be able to PROVE it,
because returning the right answers proves nothing (the revision stamp would too)."""
idg_reeval_count(key::Atom)::Int = (n = get(_IDG, key, nothing); n === nothing ? 0 : n.reevaluated)

"How many times this table has been INVALIDATED (0 -> 1 transitions) — `stats.invalidated`."
idg_invalidated_count(key::Atom)::Int =
    (n = get(_IDG, key, nothing); n === nothing ? 0 : n.invalidated)
