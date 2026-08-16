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
struct SymKey    <: TrieKey; name::Symbol; end
struct ExprKey   <: TrieKey; arity::Int;   end
struct VarKey    <: TrieKey; idx::Int;     end
struct GroundKey{T} <: TrieKey; v::T;      end

Base.hash(k::SymKey,  h::UInt) = hash(k.name, hash(:sym, h))
Base.hash(k::ExprKey, h::UInt) = hash(k.arity, hash(:expr, h))
Base.hash(k::VarKey,  h::UInt) = hash(k.idx, hash(:var, h))
# ⚠️ TYPE IS PART OF THE KEY. `1 == 1.0` in Julia, so a value-only comparison would conflate the
# integer and float answers — and upstream keeps them DISTINCT (standard order sorts float before
# int on equal value, pl-prims.c:1777). Hash and equality both carry the type.
Base.hash(k::GroundKey{T}, h::UInt) where {T} = hash(k.v, hash(T, hash(:gnd, h)))
Base.:(==)(a::SymKey,  b::SymKey)  = a.name  == b.name
Base.:(==)(a::ExprKey, b::ExprKey) = a.arity == b.arity
Base.:(==)(a::VarKey,  b::VarKey)  = a.idx   == b.idx
Base.:(==)(a::GroundKey{T}, b::GroundKey{T}) where {T} = a.v == b.v
Base.:(==)(::GroundKey, ::GroundKey) = false          # different payload TYPES are different keys
Base.:(==)(::TrieKey, ::TrieKey) = false          # different key kinds never collide

"""A node of the answer trie.

`answer` is set only on a node that terminates a stored answer — upstream's `set_trie_value_word`
marking a node with `ATOM_trienode` (`pl-tabling.c:3668`). An interior node on the path to a longer
answer is NOT itself an answer, which is why the flag is a field and not "has no children"."""
mutable struct TrieNode
    children::Dict{TrieKey,TrieNode}
    answer::Union{Atom,Nothing}
    seq::Int                      # insertion order; 0 until this node terminates an answer
end
TrieNode() = TrieNode(Dict{TrieKey,TrieNode}(), nothing, 0)

"""The answer table for ONE tabled goal.

`count` is maintained rather than derived: `tripwire_answers_for_subgoal` consults it on EVERY
insert (`pl-tabling.c` reads `wl->table->value_count`), so an O(n) walk per answer would make the
§7.11.3 restraint quadratic in the thing it exists to bound."""
mutable struct AnswerTrie
    root::TrieNode
    count::Int
    inserts::Int                  # monotonic stamp source for `seq` — never decremented on delete
end
AnswerTrie() = AnswerTrie(TrieNode(), 0, 0)
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
    _trie_walk!(out, Dict{Var,Int}(), a)
    out
end

# ⚠️ A TOP-LEVEL RECURSIVE FUNCTION, NOT AN INNER CLOSURE. Written first as a `walk(x) = …` closure
# inside `trie_keys`, which JET reported as "captured variable `walk` detected" plus a runtime
# dispatch: a SELF-RECURSIVE inner closure is boxed (`Core.Box`) because the name is assigned in the
# same scope it is called from, so Julia cannot infer it. Hoisting it costs nothing and removes both.
function _trie_walk!(out::Vector{TrieKey}, seen::Dict{Var,Int}, x::Atom)
    if x isa Var
        push!(out, VarKey(get!(seen, x, length(seen) + 1)))
    elseif x isa Sym
        push!(out, SymKey(x.name))
    elseif x isa Expression
        ch = (x::Expression).children
        push!(out, ExprKey(length(ch)))
        for c in ch; _trie_walk!(out, seen, c); end
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
function trie_lookup!(t::AnswerTrie, a::Atom, add::Bool=false)::Union{TrieNode,Nothing}
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
    t.inserts += 1; node.seq = t.inserts             # stamp AT INSERT — see `trie_answers`
    t.count += 1
    true
end

"Is `a` already stored? Structural, so variants of a stored answer count as present."
trie_contains(t::AnswerTrie, a::Atom)::Bool =
    (n = trie_lookup!(t, a, false); n !== nothing && n.answer !== nothing)

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
    out = Tuple{Int,Atom}[]
    stack = TrieNode[t.root]
    while !isempty(stack)
        n = pop!(stack)
        n.answer === nothing || push!(out, (n.seq, n.answer::Atom))
        for (_, c) in n.children; push!(stack, c); end
    end
    sort!(out; by = first)        # by the stamp taken AT INSERT, not by traversal position
    Atom[a for (_, a) in out]
end

# ── the per-table registry ───────────────────────────────────────────────────────────────────────
const _ANSWER_TRIES = Dict{Atom,AnswerTrie}()
answer_trie_for(key::Atom)::AnswerTrie = get!(() -> AnswerTrie(), _ANSWER_TRIES, key)
has_answer_trie(key::Atom)::Bool = haskey(_ANSWER_TRIES, key)
"Drop one table's trie — called by `abolish_table_subgoals!` so it dies with its table."
drop_answer_trie!(key::Atom) = (delete!(_ANSWER_TRIES, key); nothing)
clear_answer_tries!() = (empty!(_ANSWER_TRIES); nothing)
