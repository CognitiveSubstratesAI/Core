# ╔══════════════════════════════════════════════════════════════════════════════════════════════╗
# ║ Index.jl — CLAUSE/ATOM INDEXING. Extracted from Eval.jl 2026-08-28.                          ║
# ╚══════════════════════════════════════════════════════════════════════════════════════════════╝
#
# WHY ITS OWN FILE. Upstream keeps indexing in `src/pl-index.c`, separate from the machine in
# `pl-wam.c`, and for the same reason it belongs apart here: indexing is a SELECTION strategy over the
# store, not part of evaluation. It had accreted across ~340 lines of `Eval.jl` in three disjoint
# blocks (the token/trie TYPES hoisted above the store, the key derivation below it, the trie
# machinery 130 lines further down), which is why "where is the index?" had no single answer.
#
# ── WHAT IS HERE, AND WHAT IT IS NOT ────────────────────────────────────────────────────────────
# THREE acceleration structures, none of which is on `match`'s path (see the ⚠️ below):
#   `index`        a FIRST-ARGUMENT discriminant — `Dict{(head-sym, arg1-head-sym) => Vector{Atom}}`.
#                  Prolog's classic first-argument indexing; our implementation is modelled on
#                  hyperon's AtomIndex / CeTTa's eq_idx / the legacy CoreSpace rule_cache
#                  (`b980b69`, 2026-06-17), NOT ported from `pl-index.c`.
#   `wildcard`     atoms whose discriminant is not concrete; checked on EVERY query.
#   `bucket_trie`  a LAZY per-bucket discrimination trie over a MORK-shaped token stream, promoted
#                  above `_TRIE_MIN_BUCKET`. Threshold and idea from CeTTa `subst_tree` (space.c:497);
#                  the TOKENS are MORK's `Expr` encoding (arity-prefixed pre-order) — see `_Tok`.
#
# ⚠️ 🔴 THE PRIMITIVE MeTTa PROGRAMS ACTUALLY USE DOES NOT COME HERE. `match` runs `_match_pat`
# (`Eval.jl`), which scans `all_atoms` UNCONDITIONALLY — no key, no bucket, no trie. Everything in
# this file serves `query()`, i.e. `(=)` rule lookup and `(:)` type lookup. MEASURED 2026-08-27:
# `query` is O(1) at ~4 µs, while a `match` over 4000 atoms costs ~62 ms. So the largest indexing
# opportunity in this engine is not tuning what is here — it is that `match` never arrives.
#
# ⚠️ AND THERE IS NO UPSTREAM ORACLE FOR THIS FILE. The swipl differential covers TABLING, which is a
# port; the index is ours. Any change here needs its own test — it cannot lean on `swipl_tabling_oracle.sh`.

# ── DISCRIMINATION-TRIE TYPES — HOISTED HERE ON PURPOSE ──────────────────────────────────────────
# These are declared BEFORE `VectorStore` only so that `bucket_trie` can name its value type. They
# were originally beside their functions (~250 lines below); the field was then typed `Any`, which is
# the ONE `Any` this package had in `src/` and a standing-rule violation with no upside — the value
# stored is always `(_TNode, IdDict{Atom,Int})`, a concrete type that simply was not nameable yet.
# The functions stay where they were; only the declarations moved.
# Concrete, isbits token — NO `Any` (dense `Vector{_Tok}` + isbits `Dict` keys ⇒ zero boxing / no dynamic dispatch;
# what the JIT wants). A Var is a wildcard (`_KVAR`); a Sym/Grounded is keyed by the 64-bit hash of its name/value
# (a hash collision only WIDENS the candidate set — match_atoms stays authoritative — so a match is never dropped);
# an Expression by its arity. `kind` disambiguates hash spaces (a Sym and a Grounded with equal hashes stay separate).
const _KVAR = 0x00
const _KSYM = 0x01
const _KEXPR = 0x02
const _KGND = 0x03
struct _Tok
    kind::UInt8
    pay::UInt64
end

mutable struct _TNode
    atoms::Vector{Atom}                    # every stored atom routed through this node (⇒ query-var collect)
    concrete::Dict{_Tok, _TNode}
    star::Union{_TNode, Nothing}
    _TNode() = new(Atom[], Dict{_Tok, _TNode}(), nothing)
end


# discriminant head of an atom-position: a Sym's name, or an Expression's Sym head; else nothing.
_idx_head(x::Atom)::Union{Symbol, Nothing} =
    if x isa Sym
        x.name
    elseif (x isa Expression && !isempty(x.children) && x.children[1] isa Sym)
        (x.children[1]::Sym).name
    else
        nothing
    end
# (outer-head, 2nd-child-head) discriminant; nothing ⇒ not indexable ⇒ wildcard bucket.
function _index_key(a::Atom)::Union{Tuple{Symbol, Symbol}, Nothing}
    (a isa Expression && length(a.children) >= 2 && a.children[1] isa Sym) || return nothing
    sub = _idx_head(a.children[2])
    sub === nothing && return nothing
    ((a.children[1]::Sym).name, sub)
end

# ── per-bucket discrimination trie: a conservative candidate filter ─────────────────────────────────────
# Prunes a WIDE same-discriminant bucket by shared LHS structure. Tokens are the pre-order flattening of an
# atom; a Var (either side) is a WILDCARD. The stored trie routes each atom by its ground tokens (a stored Var
# → the `star` edge). Retrieval descends the query stream: a ground query token follows the matching concrete
# edge AND the star edge (a stored Var matches the query's whole subterm, so skip it); a query Var (or query
# exhaustion) collects the whole subtrie. Result = a duplicate-free SUPERSET of true matches (each stored atom
# lies on exactly one path, so it is collected ≤1×); match_atoms remains authoritative. Correctness: match_atoms
# succeeds ⇒ at every position one side is a Var or both are equal ground tokens ⇒ the atom is on a followed
# path ⇒ collected. So the filter never drops a match.
const _TRIE_MIN_BUCKET = 16                # build/use the trie only for buckets larger than this (CeTTa promotes at 16)
@inline _tok(a::Atom)::_Tok =
    if a isa Sym
        _Tok(_KSYM, hash(a.name))
    elseif a isa Expression
        _Tok(_KEXPR, UInt64(length(a.children)))
    elseif a isa Grounded
        _Tok(_KGND, hash(a.value))
    else
        _Tok(_KVAR, UInt64(0))
    end               # Var (or unknown) = wildcard

function _flat_tokens!(toks::Vector{_Tok}, a::Atom, d::Int)
    if d > _MAX_ATOM_DEPTH
        push!(toks, _Tok(_KVAR, UInt64(0)))
        return nothing          # depth cap → wildcard (conservative)
    elseif a isa Expression
        push!(toks, _Tok(_KEXPR, UInt64(length(a.children))))
        for c in a.children
            _flat_tokens!(toks, c, d + 1)
        end
    else
        push!(toks, _tok(a))
    end
    return nothing
end
_flat_tokens(a::Atom) = (t=_Tok[]; _flat_tokens!(t, a, 0); t)

function _skip_term(toks::Vector{_Tok}, i::Int)::Int         # advance past one whole term (isbits ⇒ alloc-free)
    @inbounds t = toks[i]
    if t.kind == _KEXPR
        i += 1
        for _ in 1:Int(t.pay)
            i = _skip_term(toks, i)
        end
        return i
    end
    i + 1
end


function _trie_insert!(root::_TNode, a::Atom)
    node = root
    push!(node.atoms, a)
    for t in _flat_tokens(a)
        if t.kind == _KVAR
            node.star === nothing && (node.star = _TNode())
            node = node.star
        else
            node = get!(_TNode, node.concrete, t)
        end
        push!(node.atoms, a)
    end
    return nothing
end

function _trie_build(bucket::Vector{Atom})
    root = _TNode()
    pos = IdDict{Atom, Int}()
    for (i, a) in enumerate(bucket)
        pos[a] = i
        _trie_insert!(root, a)
    end
    (root, pos)
end

function _trie_collect!(acc::Vector{Atom}, node::_TNode, q::Vector{_Tok}, qi::Int)
    if qi > length(q) || (@inbounds q[qi].kind == _KVAR)
        append!(acc, node.atoms)
        return nothing                     # query exhausted / query-var → all in subtrie
    end
    @inbounds t = q[qi]
    c = get(node.concrete, t, nothing)
    c !== nothing && _trie_collect!(acc, c, q, qi + 1)        # ground token → matching concrete edge
    node.star !== nothing && _trie_collect!(acc, node.star, q, _skip_term(q, qi))  # stored var → skip query subterm
    return nothing
end

# ⚠️ TAKES THE TRIE DICT, NOT THE SPACE — changed during the 2026-08-28 extraction. This file is
# included BEFORE `Space` exists (the store's `bucket_trie` field needs `_TNode` at definition time),
# and the function only ever touched `space.store.bucket_trie` anyway. Narrower argument, no
# behaviour change, and it keeps the index free of any dependency on the evaluator's types.
function _bucket_candidates(
    tries::Dict{Tuple{Symbol, Symbol}, Tuple{_TNode, IdDict{Atom, Int}}},
    k::Tuple{Symbol, Symbol}, b::Vector{Atom}, pattern::Atom
)::Vector{Atom}
    entry = get(tries, k, nothing)
    if entry === nothing
        entry = _trie_build(b)
        tries[k] = entry
    end
    root, pos = entry            # no `::` assert needed — `bucket_trie` is concretely typed now
    acc = Atom[]
    _trie_collect!(acc, root, _flat_tokens(pattern), 1)
    sort!(acc; by=a -> get(pos, a, typemax(Int)))          # preserve linear-scan order (⇒ identical results)
    acc
end

# query (= pattern $X) → the matching binding sets (interpreter.rs query:604). Each stored atom's variables are
# freshened before matching (make_variables_unique). Same-discriminant atoms are scanned linearly for a small
# bucket, or pruned via the per-bucket discrimination trie for a wide one (identical results either way).
