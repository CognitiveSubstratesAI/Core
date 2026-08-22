# tabling/AnswerTrie.jl — the ANSWER TRIE. Roadmap §1.0, step 4 of 4 (structure half).
#
# Mirrors `src/pl-trie.c`'s term trie as tabling uses it (`trie_lookup`, `pl-trie.h:229`) and
# Desouter et al. §4.4, where the trie is 40% of the whole library's line count.
#
# ─── WHY A TRIE AND NOT THE `Dict`/`Vector` WE HAVE ──────────────────────────────────────────────
# Four things the current `Dict{Atom,Vector{Atom}}` cannot do, each blocking a named §7 item:
#
#   * DUPLICATE DETECTION IS STRUCTURAL. §4.4: the trie "allows store_answer/2 to quickly check
#     whether a newly produced answer has already been computed". Today we call `unique(vcat(…))`,
#     which is O(n) per insert and needs `_is_general_variant` bolted on for the general answer
#     (`tabling/Tripwires.jl`) precisely because a Vector has no structural identity.
#   * VARIANT IDENTITY COMES FREE. Two answers equal up to variable renaming reach the SAME NODE,
#     because variables are keyed by FIRST-OCCURRENCE INDEX, not by name (upstream threads a `vars`
#     argument through `trie_lookup` for this).
#   * ABSTRACTION NEEDS TRIE TERMS. §7.11.1/2 (`subgoal_abstract`/`answer_abstract`) truncate a term
#     at a DEPTH — a walk down a path. `tabling/Tripwires.jl` currently REFUSES both, naming this
#     file as the prerequisite.
#   * MODE-DIRECTED MERGE HAPPENS AT INSERTION. Upstream folds a `lattice`/`po` answer inside
#     `$tbl_wkl_add_answer`; our `merge_answers` is a standalone fold over a Vector only because
#     there is no trie to insert into. Its own header says it "disappears into the trie".
#
# ─── WHY NOT PathMap, WHICH IS ALREADY A TRIE AND ALREADY A DEPENDENCY ───────────────────────────
# Checked before writing this, not assumed. PathMap is a BYTE trie (CODEMAP: "the byte-trie +
# zippers + `.act` persistence"), keyed on byte paths via `read_zipper_at_path` / `set_val_at!`.
# Upstream's answer trie is a TERM trie keyed on term structure — a different data structure for a
# different key.
#
# 🔴 AND THE BYTE ROUTE IS MEASURABLY WRONG FOR THIS USE. Our byte-path encoding stores `$x` as the
# GROUND SYMBOL `__var_x` (`space/CoreSpace.jl:13,46`). Answers are not always ground — the
# maximally-general answer that `bounded_rationality` inserts (`generalise_answer_substitution`) is
# nothing but variables — so routing answers through byte paths would destroy exactly the property
# the trie exists to preserve. PathMap remains the right substrate for the SPACE; it is the wrong
# one for the answer table. (If the store seam ever makes variables first-class in the byte
# encoding, revisit this — the note is here so the question is re-asked rather than re-derived.)
#
# ─── JULIA SHAPE ─────────────────────────────────────────────────────────────────────────────────
# Upstream hand-rolls hash buckets with an indirection table for node children. Julia has `Dict`.
# Keys are a small closed set of concrete structs under one abstract type, so the child map is typed
# rather than `Dict{Any,…}` (`[[feedback_no_any_typed_containers]]`).

"""One step of a term's path through the trie.

A closed set: symbols, grounded payloads, expressions (by arity) and variables (by FIRST-OCCURRENCE
index). Variable keying by index, not name, is what makes two variants of an answer land on one
node — upstream's `vars` argument to `trie_lookup` (`pl-trie.h:229`)."""
abstract type TrieKey end
struct SymKey <: TrieKey
    name::Symbol
end
struct ExprKey <: TrieKey
    arity::Int
end
struct VarKey <: TrieKey
    idx::Int
end
struct GroundKey{T} <: TrieKey
    v::T
end

Base.hash(k::SymKey, h::UInt) = hash(k.name, hash(:sym, h))
Base.hash(k::ExprKey, h::UInt) = hash(k.arity, hash(:expr, h))
Base.hash(k::VarKey, h::UInt) = hash(k.idx, hash(:var, h))
# ⚠️ TYPE IS PART OF THE KEY. `1 == 1.0` in Julia, so a value-only comparison would conflate the
# integer and float answers — and upstream keeps them DISTINCT (standard order sorts float before
# int on equal value, pl-prims.c:1777). Hash and equality both carry the type.
Base.hash(k::GroundKey{T}, h::UInt) where {T} = hash(k.v, hash(T, hash(:gnd, h)))
Base.:(==)(a::SymKey, b::SymKey) = a.name == b.name
Base.:(==)(a::ExprKey, b::ExprKey) = a.arity == b.arity
Base.:(==)(a::VarKey, b::VarKey) = a.idx == b.idx
Base.:(==)(a::GroundKey{T}, b::GroundKey{T}) where {T} = a.v == b.v
Base.:(==)(::GroundKey, ::GroundKey) = false          # different payload TYPES are different keys
Base.:(==)(::TrieKey, ::TrieKey) = false          # different key kinds never collide

"""A node of the answer trie.

`answer` is set only on a node that terminates a stored answer — upstream's `set_trie_value_word`
marking a node with `ATOM_trienode` (`pl-tabling.c:3668`). An interior node on the path to a longer
answer is NOT itself an answer, which is why the flag is a field and not "has no children"."""
mutable struct TrieNode
    children::Dict{TrieKey, TrieNode}
    answer::Union{Atom, Nothing}
    seq::Int                      # insertion order; 0 until this node terminates an answer
    # ── PER-ANSWER METADATA (roadmap 7.A, added 2026-08-17) ──────────────────────────────────────
    # 🔑 THE NODE IS THE ONLY PLACE THIS CAN LIVE, and that is upstream's design, not a convenience.
    # A Prolog answer IS its skeleton, so the trie node carries the goal instance inherently and the
    # delay list hangs off the same node. A MeTTa answer is a VALUE, so both have to be attached
    # explicitly — but they attach HERE, because the trie is the only store with VARIANT identity:
    # `p($x)` and `p($y)` reach one node, which is exactly the grouping the metadata needs. A
    # `Dict{Atom,...}` side table cannot do it (`==` splits variants), and an index-aligned parallel
    # vector cannot survive `_merge_partial`'s dedup.
    #
    # THREE features converge here — see the roadmap 0e table:
    #   instances -> §7.11.1 subgoal abstraction, currently OVER-APPROXIMATING without them
    #   delays    -> WFS residuation and §7.11.2 `answer_abstract`
    instances::Vector{Atom}       # goal instances that PRODUCED this answer; empty = unrecorded
end
TrieNode() = TrieNode(Dict{TrieKey, TrieNode}(), nothing, 0, Atom[])

"""The answer table for ONE tabled goal.

`count` is maintained rather than derived: `tripwire_answers_for_subgoal` consults it on EVERY
insert (`pl-tabling.c` reads `wl->table->value_count`), so an O(n) walk per answer would make the
§7.11.3 restraint quadratic in the thing it exists to bound."""
mutable struct AnswerTrie
    root::TrieNode
    count::Int
    inserts::Int                  # monotonic stamp source for `seq` — never decremented on delete
    status::Symbol                # `\$tbl_table_status` — see TABLE_STATUSES
end
AnswerTrie() = AnswerTrie(TrieNode(), 0, 0, :fresh)

"""Table statuses, from `unify_table_status`/`complete_or_invalid_status` (`pl-tabling.c:3208-3239`).

  :fresh     — created, not yet completed. Upstream also uses `fresh` while REEVALUATING.
  :active    — a completion is running. Upstream has no atom for this: it returns the COMPOUND
               `fresh(SCC, Worklist)`, so "has a worklist" IS the active marker. We name it, because
               a Symbol field cannot carry the pair and `untable!`'s incomplete-table guard needs to
               ask the question directly (it currently approximates via `_TABLE_INPROG`).
  :complete  — completion finished.
  :invalid   — ⚠️ UNREACHABLE FOR US. Upstream returns it when `n->falsecount > 0` on the IDG, i.e.
               incremental invalidation (§7.7), which we do not have. Listed so the set is upstream's
               rather than ours, and so §7.7 finds the name already reserved.
  :dynamic   — ⚠️ UNREACHABLE FOR US: pseudo answer tries for dynamic predicates (`:3295`)."""
const TABLE_STATUSES = (:fresh, :active, :complete, :invalid, :dynamic)

"`\$tbl_table_status` — the table's status atom."
table_status(t::AnswerTrie)::Symbol = t.status
function set_table_status!(t::AnswerTrie, s::Symbol)
    s in TABLE_STATUSES || throw(
        ArgumentError(
            "unknown table status $(s) — upstream's set is $(TABLE_STATUSES) (pl-tabling.c:3208-3239)"
        )
    )
    t.status = s
    t
end
is_complete(t::AnswerTrie)::Bool = t.status === :complete
Base.length(t::AnswerTrie) = t.count
Base.isempty(t::AnswerTrie) = t.count == 0

"""
    trie_keys(a) -> Vector{TrieKey}

Flatten `a` into its prefix-order path. Variables are numbered by FIRST OCCURRENCE, so `(f \$x \$x)`
and `(f \$y \$y)` produce the same path while `(f \$x \$y)` does not — variant identity, structurally.

This is the same canonicalisation `_variant_rename` performs for table KEYS; doing it here is what
lets the trie decide duplicate-ness without a separate rename pass.
"""
function trie_keys(a::Atom)::Vector{TrieKey}
    out = TrieKey[]
    _trie_walk!(out, Dict{Var, Int}(), a)
    out
end

# ⚠️ A TOP-LEVEL RECURSIVE FUNCTION, NOT AN INNER CLOSURE. Written first as a `walk(x) = …` closure
# inside `trie_keys`, which JET reported as "captured variable `walk` detected" plus a runtime
# dispatch: a SELF-RECURSIVE inner closure is boxed (`Core.Box`) because the name is assigned in the
# same scope it is called from, so Julia cannot infer it. Hoisting it costs nothing and removes both.
function _trie_walk!(out::Vector{TrieKey}, seen::Dict{Var, Int}, x::Atom)
    if x isa Var
        push!(out, VarKey(get!(seen, x, length(seen) + 1)))
    elseif x isa Sym
        push!(out, SymKey(x.name))
    elseif x isa Expression
        ch = (x::Expression).children
        push!(out, ExprKey(length(ch)))
        for c in ch
            _trie_walk!(out, seen, c)
        end
    elseif x isa Grounded
        push!(out, GroundKey((x::Grounded).value))
    else
        push!(out, SymKey(Symbol(string(x))))         # unreachable today; keyed rather than dropped
    end
    nothing
end

"""
    trie_lookup!(t, a; add) -> Union{TrieNode,Nothing}

`trie_lookup` (`pl-trie.h:229`). Walk `a`'s path; with `add` true create missing nodes and return the
terminal node, else return it only if the path already exists.

Does NOT mark the node an answer — that is `trie_insert!`'s job, because upstream separates lookup
from `set_trie_value_word` so a restraint can inspect the node and DELETE it before it becomes an
answer (`pl-tabling.c:3613 trie_delete`).
"""
# ⚠️ `add` is POSITIONAL, not a keyword. As `; add::Bool=false` it compiled to a `Core.kwcall`, which
# JET reported as a runtime dispatch at EVERY call site (trie_insert!, trie_contains, trie_delete!).
function trie_lookup!(t::AnswerTrie, a::Atom, add::Bool=false)::Union{TrieNode, Nothing}
    node = t.root
    for k in trie_keys(a)
        nxt = get(node.children, k, nothing)
        if nxt === nothing
            add || return nothing
            nxt = TrieNode()
            node.children[k] = nxt
        end
        node = nxt
    end
    node
end

"""
    trie_insert!(t, a) -> Bool

Store `a`, returning `true` if it is NEW. This is the structural duplicate detection §4.4 describes:
a second insert of the same answer (up to variable renaming) finds the node already marked and
returns `false` — no scan, no `unique`, no separate variant check.
"""
function trie_insert!(t::AnswerTrie, a::Atom)::Bool
    node = trie_lookup!(t, a, true)::TrieNode
    node.answer === nothing || return false          # already an answer ⇒ duplicate
    node.answer = a
    t.inserts += 1
    node.seq = t.inserts             # stamp AT INSERT — see `trie_answers`
    t.count += 1
    true
end

"""
    trie_record_instance!(t, a, instance) -> Bool

Record that goal `instance` produced answer `a`. Returns whether the instance was NEW.

🔴 WHY IT IS KEYED BY THE ANSWER RATHER THAN STORED ALONGSIDE IT. In Prolog the question does not
arise: an answer is a substitution over the goal skeleton, so the instance IS the answer. Here the
value `deep` says nothing about which call produced it, and the same value can come from many
instances — so the relation is one answer to MANY instances, and the node is where they collect.

The instance list is VARIANT-deduped for the same reason the trie itself is: two instances differing
only by variable naming are one instance, and a fixpoint that re-derives an answer each round would
otherwise grow this list without bound.

⚠️ AN EMPTY LIST MEANS "NOT RECORDED", NOT "NO INSTANCE". Recording happens in `_leader_pass`, which
is the only place that still holds the binding; answers arriving by other routes (the completion
mirror, monotonic propagation) leave it empty. Consumers MUST treat empty as unknown and fall back
to the sound over-approximation — treating it as "no instance matches" would silently DROP answers,
turning an imprecision into an unsoundness.
"""
function trie_record_instance!(t::AnswerTrie, a::Atom, instance::Atom)::Bool
    node = trie_lookup!(t, a, true)::TrieNode
    any(x -> variant_eq(x, instance), node.instances) && return false
    push!(node.instances, instance)
    true
end

"""The goal instances known to have produced `a` — EMPTY means unrecorded, not none.

See `trie_record_instance!`: a consumer that reads empty as "nothing matches" drops real answers."""
function trie_instances(t::AnswerTrie, a::Atom)::Vector{Atom}
    node = trie_lookup!(t, a, false)
    node === nothing ? Atom[] : node.instances
end

"Is `a` already stored? Structural, so variants of a stored answer count as present."
trie_contains(t::AnswerTrie, a::Atom)::Bool =
    (n=trie_lookup!(t, a, false); n !== nothing && n.answer !== nothing)

"""
    trie_delete!(t, a) -> Bool

`trie_delete` (`pl-tabling.c:3613`). Unmark an answer; the path is left in place, matching upstream,
which unlinks the value rather than pruning the spine.
"""
function trie_delete!(t::AnswerTrie, a::Atom)::Bool
    n = trie_lookup!(t, a, false)
    (n === nothing || n.answer === nothing) && return false
    n.answer = nothing
    t.count -= 1
    true
end

"""
    trie_answers(t) -> Vector{Atom}

Every stored answer, in INSERTION ORDER.

⚠️ Order is explicit, not incidental. A trie's natural walk order is its key order, which would
silently reorder answers relative to the `Vector` tables this replaces — and while the corpus was
measured not to DEPEND on answer order, it is user-visible, so changing it must be a decision rather
than a side effect of the data structure.
"""
function trie_answers(t::AnswerTrie)::Vector{Atom}
    out = Tuple{Int, Atom}[]
    stack = TrieNode[t.root]
    while !isempty(stack)
        n = pop!(stack)
        n.answer === nothing || push!(out, (n.seq, n.answer::Atom))
        for (_, c) in n.children
            push!(stack, c)
        end
    end
    sort!(out; by=first)        # by the stamp taken AT INSERT, not by traversal position
    Atom[a for (_, a) in out]
end

# ── the per-table registry ───────────────────────────────────────────────────────────────────────
const _ANSWER_TRIES = Dict{Atom, AnswerTrie}()
answer_trie_for(key::Atom)::AnswerTrie = get!(() -> AnswerTrie(), _ANSWER_TRIES, key)
has_answer_trie(key::Atom)::Bool = haskey(_ANSWER_TRIES, key)
"Drop one table's trie — called by `abolish_table_subgoals!` so it dies with its table."
drop_answer_trie!(key::Atom) = (delete!(_ANSWER_TRIES, key); nothing)
clear_answer_tries!() = (empty!(_ANSWER_TRIES); nothing)

# ═══════════════════════════════════════════════════════════════════════════════
# MODE-DIRECTED INSERTION — §7.3 re-seated onto the trie (roadmap step after §1.0).
#
# `Aggregation.merge_answers` folds a mode vector over a `Vector{Atom}`. That existed only because
# there was no trie to insert into — its own header says so. Upstream has no such entry point: the
# merge happens INSIDE `$tbl_wkl_add_answer` (`pl-tabling.c:3577`), and a moded table is marked
# `TRIE_ISMAP` — a MAP from key to aggregated value, not a set of answers.
#
# ─── WHAT THE TRIE GIVES THAT THE VECTOR COULD NOT ───────────────────────────────────────────────
#   * the KEY IS THE PATH. `mode_key` replaces every moded argument with `MODED_SLOT`, so answers
#     differing only in aggregated positions land on ONE NODE by construction — no scan, no grouping.
#   * VARIANT identity is structural, so `_is_general_variant` (`tabling/Tripwires.jl`, bolted on
#     because a Vector has no structural identity) becomes unnecessary here.
#   * `=@=` COMES FREE: two atoms are variants iff `trie_keys` agree, because variables are keyed by
#     FIRST-OCCURRENCE INDEX. That matters — see the changed-signal note below.
#
# ─── PORTED FROM `update/7` (`boot/tabling.pl:732-773`), INCLUDING WHAT WE CANNOT USE YET ────────
# Upstream dispatches on a CONDITIONALITY BITMASK — which of (old, new) are unconditional:
#
#   0b11 both unconditional  -> merge; action DELETE (replace old); succeeds iff `Agg \=@= Next`
#   0b10 old uncond, new cond -> merge; action KEEP (old stays, new is ADDED alongside)
#   0b01 old cond, new uncond -> merge WITH ARGUMENTS SWAPPED (`New, Agg`); action KEEP
#   0b00 both conditional     -> NO merge at all; `Next = New`; action KEEP
#
# 🔴 WE ARE ALWAYS IN 0b11, AND THAT IS A CONSEQUENCE OF A GAP, NOT A SIMPLIFICATION. A conditional
# answer is one delayed under WFS, which requires DELAY LISTS — recorded as absent (§7.6.1 in
# `Core/docs/TABLING_ROADMAP.md`). Until they exist no answer can be conditional, so the other three
# clauses are unreachable rather than unimplemented. They are written out here so that whoever lands
# delay lists finds the three cases named instead of discovering the bitmask afterwards.
#
# ⚠️ AND THE C CONFIRMS THE CONSEQUENCE — checked in `pl-tabling.c`, not inferred from the Prolog:
#   * `wkl_mode_add_answer` (:3928) receives the answer as `Skel/MArgs` — a `/2` functor SPLITTING
#     the key part from the moded arguments — and calls `trie_lookup` on **arg0 only**. So upstream's
#     moded trie is keyed on the SKELETON ALONE. That is what `mode_key` does here.
#   * `update_subsuming_answers` (:3871) then does
#         map_trie_node(root, update_subsuming_answer, &ctx)
#     i.e. it MAPS OVER EVERY CHILD of that key's node. A moded table upstream therefore holds
#     POSSIBLY MANY answers per key, and "update" means visiting each.
#   * two mechanisms put them there, and WE HAVE NEITHER: `ctx.flags = AS_NEW_DEFINED` is set only
#     when both delay lists are nil, so CONDITIONAL answers coexist under one key; and `ctx.garbage`
#     + `prune_answers_worklist` means deleted answers LINGER until pruned.
#
# ⇒ one-row-per-key is correct for our feature set and WRONG the moment delay lists land. When they
# do, `node.answer` becomes a SET and this function becomes a map-over-children, matching :3871.
#
# ⚠️ THE CHANGED SIGNAL IS VARIANT INEQUALITY (`\=@=`), NOT STRUCTURAL (`\==`). `merge_answers` used
# `new != cur`. For ground values they coincide, which is why the differential never caught it; for a
# non-ground aggregated value — a generalised answer is nothing but variables — they differ, and a
# structural test reports "changed" on a pure renaming, so the completion fixpoint would never
# converge. `trie_keys` equality IS `=@=`.

"`=@=` — variant equality. Two atoms are variants iff their trie paths agree (variables keyed by
first occurrence), which is exactly upstream's `\\=@=` test in `update/7`'s 0b11 clause."
variant_eq(a::Atom, b::Atom)::Bool = trie_keys(a) == trie_keys(b)

"""
    trie_insert_moded!(t, a, modes) -> (inserted_or_changed::Bool, action::Symbol)

Insert `a` under `modes`, merging into the existing answer for its mode key. The trie-seated form of
`update/7`'s 0b11 clause: merge, REPLACE the old answer, and report change by VARIANT inequality.

`action` is `:new` (no answer for this key yet), `:delete` (replaced — upstream's word for it) or
`:unchanged`. With no moded position this degrades to `trie_insert!`, so an all-`index` declaration
behaves exactly as no declaration.
"""
function trie_insert_moded!(t::AnswerTrie, a::Atom, modes::Vector{<:TableMode})
    has_aggregation(modes) || return (trie_insert!(t, a), :new)
    key = mode_key(a, modes)
    node = trie_lookup!(t, key, true)::TrieNode
    cur = node.answer
    if cur === nothing                                  # first answer for this key
        node.answer = a
        t.inserts += 1
        node.seq = t.inserts
        t.count += 1
        return (true, :new)
    end
    (cur isa Expression && a isa Expression) || return (false, :unchanged)
    cc, ac = (cur::Expression).children, (a::Expression).children
    length(cc) == length(ac) || return (false, :unchanged)
    merged = Atom[cc[1]]
    for i in 2:length(cc)
        mi = i - 1
        push!(
            merged,
            if (mi <= length(modes) && is_moded(modes[mi]))
                update_body(modes[mi], cc[i], ac[i])
            else
                cc[i]
            end
        )
    end
    new = Expression(merged)
    variant_eq(new, cur) && return (false, :unchanged)   # `Agg \=@= Next` failed ⇒ no change
    node.answer = new                                    # action `delete`: old replaced in place
    (true, :delete)
end

# ═══════════════════════════════════════════════════════════════════════════════
# RESTRAINED INSERTION — §7.11.3 re-seated onto the trie.
#
# `Tripwires.apply_answer_restraint` works over a `Vector{Atom}` and needs `_is_general_variant`
# bolted on, because a Vector has no structural identity and each generalisation mints fresh
# variables. The trie supplies both: variant identity is the path, so the general answer dedups by
# construction.
#
# 🔴 AND THE C EXPOSES AN ORDERING BUG IN THE VECTOR VERSION. `$tbl_wkl_add_answer`
# (`pl-tabling.c:3596-3646`) does, in this order:
#
#     rc = trie_lookup_abstract(..., add=true, ...)   /* CREATE the node */
#     if ( node->value )            -> already an answer: DUPLICATE, return false
#     else if ( (action = tripwire_answers_for_subgoal(wl)) )   /* only reached when NEW */
#          ... bounded_rationality: trie_delete(node); generalise; add_answer_count_restraint()
#
# THE TRIPWIRE SITS IN THE `else` BRANCH. A DUPLICATE ANSWER NEVER TRIPS THE RESTRAINT — which is
# right, because a duplicate does not grow the table. `apply_answer_restraint` consults the bound
# BEFORE knowing whether the candidate is a duplicate, so re-inserting the same answer at the bound
# fires the restraint on every attempt and can mark a table approximate that never grew. Fixed here
# by construction: the node tells us.

"""
    trie_insert_restrained!(t, head, a) -> (added::Bool, action)

Insert `a` subject to `head`'s §7.11.3 restraint. The trie-seated `\$tbl_wkl_add_answer` answer path.

Returns `action` `:duplicate` (already present — the restraint is NOT consulted, per the C),
`nothing` (inserted, no restraint fired), or the `TripwireAction` that fired.
"""
function trie_insert_restrained!(t::AnswerTrie, head::Symbol, a::Atom)
    node = trie_lookup!(t, a, true)::TrieNode
    if node.answer !== nothing                       # `if ( node->value )` — duplicate.
        return (false, :duplicate)                   # NOT a restraint event (pl-tabling.c:3618)
    end
    act = tripwire_answers_for_subgoal(head, t.count)
    if act === nothing
        node.answer = a
        t.inserts += 1
        node.seq = t.inserts
        t.count += 1
        return (true, nothing)
    elseif act == TW_WARNING                          # `goto add_anyway` (:3660)
        @warn "tabling: max_answers exceeded for $(head) — answer added anyway" bound=max_answers(
            head
        )
        node.answer = a
        t.inserts += 1
        node.seq = t.inserts
        t.count += 1
        return (true, act)
    elseif act == TW_FAIL
        return (false, act)                           # `trie_delete` + false (:3662)
    elseif act == TW_ERROR || act == TW_SUSPEND
        act == TW_SUSPEND &&
            @warn "tabling: max_answers exceeded for $(head) — SWI would break to a debugger here"
        throw(ErrorException("resource_error(tripwire(max_answers_for_subgoal, $(head)))"))
    end
    # BOUNDED_RATIONALITY (:3636-3654): delete the offending node, then insert ONE maximally general
    # answer subsuming what the bound stopped computing, and mark the table an approximation.
    # ⚠️ NO `_is_general_variant` HERE: `trie_insert!` dedups by variant structurally, so a second
    # generalisation of the same shape finds the node already marked and returns false. That helper
    # exists in Tripwires.jl only because a Vector cannot do this.
    add_answer_count_restraint!(head)
    (trie_insert!(t, generalise_answer_substitution(a)), act)
end

# ═══════════════════════════════════════════════════════════════════════════════
# CONTENT DIGESTS — §7.7's "did the answers change?" verdict.
#
# `reeval_complete` (`pl-tabling.c:8477-8505`) decides whether a re-evaluated table produced the
# same answers, and if so RE-VALIDATES its dependants instead of re-running them. Its verdict is
# `:8484-8485`:
#
#     same_answers = ( n->new_answer == false && n->answer_count == atrie->value_count );
#
# 🔴🔴 THAT TEST IS CARDINALITY, AND PORTING IT AS WRITTEN WOULD BE SILENTLY WRONG HERE.
#
# It is safe in Prolog because AN ANSWER *IS* ITS SUBSTITUTION: a stored answer has no payload
# beyond the term that reached the node, so the only way the table's content can change is for a
# node to appear or disappear — which the count sees. Upstream knows the test is insufficient the
# moment that stops holding, and says so itself at `:7663-7679` (`$mono_reeval_prepare`):
#
#     "Without answer subsumption, this is easy: as the trie is monotonic no answers are deleted
#      and thus the trie is unchanged iff the `value_count` of the trie is unchanged.
#      With answer subsumption this is harder as each primary node (`value_count`) has one
#      secondary node (the _ModeArgs_) ..."
#
# `value_count` counts only TN_PRIMARY nodes (`pl-trie.c:1436-1437`), and a mode-directed
# aggregate lives on a SECONDARY node — so upstream patches around the hole (TN_IDG_AS_LAST) ONLY
# in the monotonic path, where it is forced to.
#
# ⇒ FOR US THE EXCEPTION IS THE NORMAL CASE. Every MeTTa answer carries a VALUE, and two measured
# mutations change the value at CONSTANT CARDINALITY:
#
#   * `trie_insert_moded!` (above) REPLACES `node.answer` in place on the `:delete` action — the
#     §7.3 aggregate moves, `t.count` does not.
#   * `merge_bottom_into!` (`Tabling.jl`) replaces a WFS bottom with a WIDER-CONDITION bottom —
#     one answer before, one after, a different residual condition.
#
# A cardinality verdict calls both "same answers" and re-validates every dependant while it holds
# STALE RESULTS. That failure is silent: nothing errors, the dependants simply answer from a cache
# that no longer matches its source. So the cardinality clause is REPLACED, not ported, and
# `test/standard/tabling/test_reeval.jl` runs the same case against a deliberate
# `length(old) == length(new)` mutant and shows it fail — a claim that the digest is NECESSARY is
# worth nothing until the cardinality version is shown to break.
#
# ─── 🔴 WHY THE DIGEST CANNOT BE BUILT ON `hash` ─────────────────────────────────────────────────
# `Base.hash(w::WFSBottom, h)` (`Tabling.jl`) hashes `length(w.delays)` — the DISJUNCT COUNT — BY
# DESIGN, and its comment says why: `==` on a bottom is `dnf_equiv`, SET equality over a set of
# sets, which has no stable order to hash, so the count is "the strongest order-independent key
# available; collisions merely fall through to `==`". Correct for a Dict. FATAL for a digest:
# `(p ∨ q)` and `(r ∨ s)` are two disjuncts either way, so two DIFFERENT residual conditions
# collide SYSTEMATICALLY rather than by accident, and a digest has no `==` to fall through to.
#
# So `_dnf_digest` folds the DNF EXPLICITLY, the way `dnf_equiv`/`set_eq`/`delay_eq` COMPARE it:
# order-insensitive within a `DelaySet` and across the `DelayDNF`, by digesting the members and
# SORTING the digests. Sorting rather than `xor`-folding is deliberate — `xor` is the obvious
# order-insensitive combiner and it CANCELS duplicates, which is another systematic collision.
#
# ⚠️ AND NOTE WHAT IS *NOT* BROKEN: `variant_eq` is already EXACT on bottoms. `trie_keys` yields
# `GroundKey{WFSBottom}`, whose `==` is `a.v == b.v`, i.e. `dnf_equiv`. Only the HASH is lossy.
# That is why `answers_identical` — the real decision — is pairwise `variant_eq` and the digest is
# the CHEAP STAMP that additionally covers metadata `variant_eq` cannot see.
#
# ⚠️ DIGESTS ARE SESSION-LOCAL. They are built on `Base.hash` of Symbols/values, which is not
# guaranteed stable across processes. Every comparison here is prepare→complete inside one run;
# nothing persists a digest, and nothing should.

"Seed for the answer digests. A named constant so a stray `hash(x)` with no seed cannot silently
produce a digest that compares equal to a properly seeded one."
const _ANSWER_DIGEST_SEED = hash(:core_tabling_answer_digest)

"""
    answer_digest(a, h = _ANSWER_DIGEST_SEED) -> UInt

A content digest of one answer, folded into `h`.

VARIANT-CANONICAL: it walks `trie_keys(a)`, so two answers equal up to variable renaming digest
identically — the same identity `trie_insert!` and `variant_eq` use, not a weaker one.

🔴 The WFS bottom is folded EXPLICITLY rather than through `hash`. See the section header: the
bottom's `Base.hash` deliberately hashes only its disjunct COUNT, so two different residual
conditions would collide systematically. Recursion through `_delay_digest` terminates because a
`DelayDNF` names other tables' variants and answers, which are finite terms and never contain the
bottom currently being digested.
"""
function answer_digest(a::Atom, h::UInt=_ANSWER_DIGEST_SEED)::UInt
    for k in trie_keys(a)
        h = _key_digest(k, h)
    end
    h
end

# ⚠️ TWO METHODS, NOT AN `isa` INSIDE ONE. `GroundKey{WFSBottom}` is a concrete type, so the split
# is a dispatch rather than a runtime type test on a `Union` — the same reasoning `is_undefined`
# records in Tabling.jl.
_key_digest(k::TrieKey, h::UInt)::UInt = hash(k, h)
_key_digest(k::GroundKey{WFSBottom}, h::UInt)::UInt =
    _dnf_digest(k.v.delays, hash(:wfsbottom, h))

"""Digest a DNF the way `dnf_equiv` COMPARES it: order-insensitive across the disjunction.

Sort-then-fold, not `xor`-fold: `xor` is order-insensitive but CANCELS duplicates, and a digest has
no `==` to fall through to when it collides."""
function _dnf_digest(dnf::DelayDNF, h::UInt)::UInt
    ds = UInt[_delayset_digest(s) for s in dnf]
    sort!(ds)
    for d in ds
        h = hash(d, h)
    end
    hash(length(ds), h)
end

"Digest one conjunction — order-insensitive within the set, matching `set_eq`."
function _delayset_digest(s::DelaySet)::UInt
    ds = UInt[_delay_digest(d) for d in s]
    sort!(ds)
    h = hash(:delayset, _ANSWER_DIGEST_SEED)
    for d in ds
        h = hash(d, h)
    end
    hash(length(ds), h)
end

"Digest one delayed literal — the three fields `delay_eq` compares, and no others."
function _delay_digest(d::Delay)::UInt
    h = hash(d.kind, hash(:delay, _ANSWER_DIGEST_SEED))
    h = answer_digest(d.variant, h)
    d.answer === nothing ? hash(:table_level, h) : answer_digest(d.answer::Atom, h)
end

"""
    table_digest(answers) -> UInt

An ORDERED digest of an answer SEQUENCE — upstream's `value_count`, replaced by content.

⚠️ ORDERED, and that is a decision. `trie_answers` returns INSERTION order by explicit design (see
its docstring: order is user-visible because `Eval.jl` propagates store order into answer order), so
a re-evaluation that returns the same answers in a DIFFERENT order has changed what a caller sees
and its dependants must not be re-validated.
"""
function table_digest(answers::Vector{Atom})::UInt
    h = hash(:answers_only, _ANSWER_DIGEST_SEED)
    for a in answers
        h = answer_digest(a, h)
    end
    hash(length(answers), h)
end

"""
    table_digest(t::AnswerTrie) -> UInt

The digest of a whole table: every answer in insertion order, PLUS the per-answer metadata that a
`Vector{Atom}` cannot carry.

Today that means `length(node.instances)`, which §7.11.1 subgoal abstraction READS (see
`trie_record_instance!`: an empty list means UNRECORDED, and abstraction over-approximates without
it). A re-evaluation that produced the same answers from a different set of goal instances has
changed what abstraction will compute, so it is not a no-change.

🔴 NOT INTERCHANGEABLE WITH THE `Vector{Atom}` METHOD, and salted differently so that comparing the
two can only ever mismatch loudly instead of coinciding by luck.
"""
function table_digest(t::AnswerTrie)::UInt
    h = hash(:with_metadata, _ANSWER_DIGEST_SEED)
    for n in _answer_nodes_ordered(t)
        h = answer_digest(n.answer::Atom, h)
        h = hash(length(n.instances), hash(:instances, h))
    end
    hash(t.count, h)
end

"""The answer-bearing nodes in INSERTION order — `trie_answers`, keeping the NODE.

Separate from `trie_answers` rather than a refactor of it: that function is on the hot read path and
returns `Vector{Atom}`; this one is called once per re-evaluation and needs the metadata that lives
on the node."""
function _answer_nodes_ordered(t::AnswerTrie)::Vector{TrieNode}
    out = Tuple{Int, TrieNode}[]
    stack = TrieNode[t.root]
    while !isempty(stack)
        n = pop!(stack)
        n.answer === nothing || push!(out, (n.seq, n))
        for (_, c) in n.children
            push!(stack, c)
        end
    end
    sort!(out; by=first)
    TrieNode[n for (_, n) in out]
end

"""
    answers_identical(old, new) -> Bool

THE re-evaluation verdict on answer VALUES: same length, and pairwise `variant_eq` IN ORDER.

Exact, not a digest — no hash, so no collision. `variant_eq` is `trie_keys(a) == trie_keys(b)`, and
that is already correct for a WFS bottom: the path yields `GroundKey{WFSBottom}`, whose `==` is
`dnf_equiv`, set equality over the DNF. Only the bottom's HASH is lossy, which is exactly why the
digest above cannot be built on it and why this function exists alongside it.

ORDERED for the reason `table_digest` documents: answer order is user-visible.
"""
function answers_identical(old::Vector{Atom}, new::Vector{Atom})::Bool
    length(old) == length(new) || return false
    for i in eachindex(old)
        variant_eq(old[i], new[i]) || return false
    end
    true
end
