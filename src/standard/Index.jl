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

# ══════════════════════════════════════════════════════════════════════════════════════════════════
#  ADAPTIVE (JIT) ARGUMENT INDEXING — ported from SWI-Prolog `src/pl-index.c`, 2026-08-28
# ══════════════════════════════════════════════════════════════════════════════════════════════════
#
# WHAT THE FIXED INDEX ABOVE CANNOT DO. `_index_key` is a FIRST-ARGUMENT discriminant: always
# `(head, arg1-head)`. When argument 1 is a variable in the QUERY, the pair cannot be formed and the
# whole index is skipped — even if argument 3 is ground and perfectly selective. Upstream does not
# have that failure mode: `bestHash` picks WHICH argument to index from the arguments the CALL
# actually instantiated, so an uninstantiated arg 1 costs one candidate, not the index.
#
# ── THE SCORE, verbatim from pl-index.c:3004-3020 ───────────────────────────────────────────────
# For each indexable argument it establishes:
#   * the total number of clauses,
#   * the count of DISTINCT values at that argument,
#   * the count of NON-INDEXABLE clauses (a variable at that argument).
# and the expected speedup is
#
#                    #clauses * #distinct
#     speedup = ----------------------------------
#               #clauses - #var + #var * #distinct
#
# The denominator is the expected bucket population: non-var clauses spread over `#distinct` keys,
# while every var-at-this-argument clause lands in EVERY bucket. So an argument that is var in many
# clauses scores near 1.0 (no gain) however many distinct values the rest have — which is exactly why
# a plain distinct-count heuristic picks the wrong argument.
#
# ⚠️ WHY THIS IS AN ADDITION ABOVE UPSTREAM'S ORACLE AND NEEDS ITS OWN TEST: the swipl differential
# covers TABLING. Nothing upstream grades our index, and `pl-index.c` cannot be run against us — its
# unit of indexing is a CLAUSE with argument positions, ours is an ATOM in a store. The FORMULA ports
# exactly; the plumbing around it does not.

"Assessment of one candidate argument position — upstream's `arg_info` / `hash_assessment`."
struct ArgAssessment
    argpos::Int          # 1-based child position that was assessed
    distinct::Int        # count of DISTINCT discriminants at this position
    nvar::Int            # clauses with a VARIABLE (non-indexable) here
    speedup::Float64     # pl-index.c:3016's formula
end

"""
    _assess_argument(atoms, pos) -> ArgAssessment

Score child position `pos` over `atoms`, by `pl-index.c`'s formula. A position that is a variable in
every atom scores 1.0 (no gain); a ground, all-distinct position scores `#clauses`.
"""
function _assess_argument(atoms::Vector{Atom}, pos::Int)::ArgAssessment
    n = length(atoms)
    n == 0 && return ArgAssessment(pos, 0, 0, 1.0)
    seen = Set{Symbol}()
    nvar = 0
    for a in atoms
        if a isa Expression && length(a.children) >= pos
            h = _idx_head(a.children[pos])
            h === nothing ? (nvar += 1) : push!(seen, h)
        else
            nvar += 1                     # too short to index here — behaves like a var
        end
    end
    d = length(seen)
    d == 0 && return ArgAssessment(pos, 0, nvar, 1.0)
    # speedup = (#clauses * #distinct) / (#clauses - #var + #var * #distinct)
    denom = n - nvar + nvar * d
    ArgAssessment(pos, d, nvar, denom <= 0 ? 1.0 : (n * d) / denom)
end

"Upstream's `better_index` (pl-index.c:3026): supersede only by a MARGIN, never on a tie."
_better_index(cand::Float64, incumbent::Float64; min_speedup::Float64=_INDEX_MIN_SPEEDUP) =
    incumbent <= 0.0 ? true : cand > incumbent * min_speedup

"Upstream requires a margin before replacing a live index; 1.0 would thrash on noise."
const _INDEX_MIN_SPEEDUP = 1.2

"How many child positions to consider — upstream's MAXINDEXARG. Beyond this the assessment costs more than it saves."
const _MAX_INDEX_ARG = 4

"""
    best_index_argument(atoms, instantiated) -> Union{ArgAssessment, Nothing}

`bestHash` (pl-index.c:3052). Assess only the positions the CALL instantiated — indexing on an
argument the caller left open buys nothing — and return the best, or `nothing` when no position is
instantiated or none beats a flat scan.

🔑 THE `instantiated` FILTER IS THE WHOLE POINT, and it is what our fixed key lacks: upstream returns
false when `ninstantiated == 0` (`:3068`) rather than failing over to a full scan on a technicality.
"""
function best_index_argument(
    atoms::Vector{Atom}, instantiated::Vector{Int}
)::Union{ArgAssessment, Nothing}
    isempty(instantiated) && return nothing          # pl-index.c:3068
    best = nothing
    for pos in instantiated
        pos > _MAX_INDEX_ARG + 1 && continue         # child 1 is the head; args start at 2
        a = _assess_argument(atoms, pos)
        a.speedup <= 1.0 && continue                 # no gain over a flat scan
        if best === nothing || _better_index(a.speedup, (best::ArgAssessment).speedup)
            best = a
        end
    end
    best
end

"""
    instantiated_positions(pattern) -> Vector{Int}

Which child positions of a QUERY pattern are concrete enough to index on — upstream's `canIndex`
over the argument vector. Position 1 (the head) is excluded: it is already the first half of
`_index_key`, so it is not a candidate for the ADAPTIVE choice.
"""
function instantiated_positions(pattern::Atom)::Vector{Int}
    out = Int[]
    pattern isa Expression || return out
    for i in 2:min(length(pattern.children), _MAX_INDEX_ARG + 1)
        _idx_head(pattern.children[i]) === nothing || push!(out, i)
    end
    out
end

# ── THE LIVE PATH: JIT indexes for `match` ───────────────────────────────────────────────────────
#
# 🔑 WHY `match` AND NOT `query`. `query()` only ever sees `(= subj $X)` / `(: subj $T)` — THREE
# children, one of which is the output variable — so there is exactly ONE indexable position and the
# fixed `_index_key` already uses it. Adaptive selection adds nothing there. `match` is where
# multi-argument patterns live (`(belief $k $s $c)`), and it is the path that scans `all_atoms`
# unconditionally: MEASURED 2026-08-27, ~62 ms over 4000 atoms against `query`'s ~4 µs.
#
# ⚠️ CORRECTNESS BEFORE SPEED: AN INDEX THAT OUTLIVES A MUTATION IS A WRONG ANSWER. Upstream tracks
# generations; we take the same route as `bucket_trie` and DROP every adaptive index on any
# add/remove. Rebuilding is O(bucket) and only happens on the next query that wants one — a stale
# index would be silent and unbounded, which is not a trade worth making.

"A JIT index: `discriminant => atoms`, plus the assessment that justified building it."
struct ArgIndex
    argpos::Int
    speedup::Float64
    buckets::Dict{Symbol, Vector{Atom}}
end

"Build the index `best` describes, over `atoms`. Var-at-position atoms go in EVERY bucket — they can match anything."
function _build_arg_index(atoms::Vector{Atom}, best::ArgAssessment)::ArgIndex
    buckets = Dict{Symbol, Vector{Atom}}()
    wild = Atom[]
    for a in atoms
        h = (a isa Expression && length(a.children) >= best.argpos) ?
            _idx_head(a.children[best.argpos]) : nothing
        h === nothing ? push!(wild, a) : push!(get!(() -> Atom[], buckets, h), a)
    end
    # A var at this position matches ANY key, so it must appear under every one — this is exactly the
    # `#var * #distinct` term in the speedup denominator, made real.
    isempty(wild) || for (_, v) in buckets
        append!(v, wild)
    end
    ArgIndex(best.argpos, best.speedup, buckets)
end

"""
    index_candidates(store_atoms, arg_index, jiti_tried, pattern) -> Vector{Atom}

Candidate atoms for `pattern`, narrowed by a JIT argument index when one pays for itself. Returns
`store_atoms` unchanged when no index applies — the caller's behaviour is then bit-identical to the
unindexed scan, which is what makes this safe to put on `match`'s path.

Upstream's `jiti_tried` is mirrored by the `tried` set: an assessment that declined must NOT be
re-run on every query, or the assessment costs more than the scan it was meant to save.
"""
function index_candidates(
    store_atoms::Vector{Atom},
    arg_index::Dict{Tuple{Symbol, Int}, ArgIndex},
    tried::Set{Symbol},
    pattern::Atom
)::Vector{Atom}
    pattern isa Expression || return store_atoms
    head = _idx_head(pattern)
    head === nothing && return store_atoms          # var-headed pattern: nothing to key on
    inst = instantiated_positions(pattern)
    isempty(inst) && return store_atoms             # pl-index.c:3068 — no instantiated argument

    for pos in inst                                 # an index we already built and can use
        ix = get(arg_index, (head, pos), nothing)
        ix === nothing && continue
        key = _idx_head(pattern.children[pos])
        key === nothing && continue
        return get(ix.buckets, key, Atom[])         # absent key ⇒ genuinely no candidates
    end

    head in tried && return store_atoms             # assessed before and declined; do not re-assess
    push!(tried, head)

    same_head = Atom[a for a in store_atoms
                     if a isa Expression && !isempty(a.children) && _idx_head(a) === head]
    length(same_head) <= _TRIE_MIN_BUCKET && return store_atoms   # too small to be worth an index
    best = best_index_argument(same_head, inst)
    best === nothing && return store_atoms

    ix = _build_arg_index(same_head, best)
    arg_index[(head, best.argpos)] = ix
    key = _idx_head(pattern.children[best.argpos])
    key === nothing ? store_atoms : get(ix.buckets, key, Atom[])
end
