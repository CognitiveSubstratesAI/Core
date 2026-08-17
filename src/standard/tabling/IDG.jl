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
# ─── SCOPE: THE GRAPH, NOT THE RE-EVALUATION ─────────────────────────────────────────────────────
# This file builds and invalidates the graph. It does NOT re-evaluate: upstream's `reeval` path
# (`:reevaluating`, `aborted`, `answer_count` comparison, `new_answer`) is §7.7's second half and
# needs the completion loop to re-enter a table with its old answers held for comparison. The fields
# are present and documented; nothing sets them yet, and `is_reevaluating` exists so that stays
# queryable rather than implied.

"""A node of the incremental dependency graph — upstream's `idg_node` (`pl-tabling.h:194`).

`affected` and `dependent` are the two directions, named as upstream names them: `affected` = the
tables that DEPEND ON this one (invalidation flows here), `dependent` = the tables this one depends
on. See the header — reversing them is silent and leaves every stale table untouched."""
mutable struct IDGNode
    key::Atom                      # the table's variant key — upstream's `atrie`
    affected::Set{Atom}            # parents: who depends on me   ⇒ invalidation flows UP through this
    dependent::Set{Atom}           # children: who I depend on
    falsecount::Int                # invalidate COUNT; `> 0` ⇒ status :invalid (pl-tabling.c:3233)
    answer_count::Int              # #answers in the previous COMPLETE state (for §7.7's reeval half)
    reevaluating::Bool             # ⚠️ set by the reeval path, which is NOT built — see the header
    monotonic::Bool                # §7.8
    lazy::Bool                     # §7.8's eager/lazy split
end
IDGNode(key::Atom) = IDGNode(key, Set{Atom}(), Set{Atom}(), 0, 0, false, false, false)

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
            p.falsecount == 1 && push!(stack, parent)
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

"Is a re-evaluation in progress? ⚠️ Always false: the reeval half of §7.7 is not built (see header)."
idg_is_reevaluating(key::Atom)::Bool =
    (n = get(_IDG, key, nothing); n !== nothing && n.reevaluating)

"Every table currently invalid — `idg_falsecount`-style querying (`pl-tabling.c:6612`)."
idg_invalid_tables()::Vector{Atom} =
    sort!(Atom[k for (k, n) in _IDG if n.falsecount > 0]; by = string)
