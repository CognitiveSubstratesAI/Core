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
# ⚠️ ✅ CORRECTED 2026-09-03 — THE WARNING BELOW WAS TRUE FOR ONE DAY AND IS NOW STALE. It read:
# "THE PRIMITIVE MeTTa PROGRAMS ACTUALLY USE DOES NOT COME HERE. `match` runs `_match_pat`, which
# scans `all_atoms` UNCONDITIONALLY … the largest indexing opportunity in this engine is that
# `match` never arrives." MEASURED 2026-08-27: `query` O(1) at ~4 µs vs a `match` over 4000 atoms
# at ~62 ms.
#
# THAT GAP WAS CLOSED THE SAME DAY THIS FILE WAS EXTRACTED, by the pl-index port itself:
#   a0447d6  port pl-index.c's ADAPTIVE argument selection (the assessment layer, with its oracle)
#   78e6358  WIRE the JIT argument index into `match` — O(N) becomes O(1) on a ground argument
#   f10505d  fix: `arg_tried` must be keyed (head, POSITION)
# `_match_pat` (`Eval.jl:2550`) now calls `index_candidates(...)`, which returns the full store
# whenever no index applies — so the unindexed behaviour stays bit-identical.
#
# The header was simply never updated after the wiring landed. Left visible rather than deleted
# because a stale "largest opportunity" note is exactly the kind of thing a later session acts on:
# it would send someone to build what `78e6358` already shipped.
# [[feedback_verify_code_body_not_comments]] · [[feedback_refresh_generated_indexes_after_commits]]
#
# STILL TRUE from the original note: the three structures below serve `query()` — `(=)` rule lookup
# and `(:)` type lookup. What changed is that `match` ALSO reaches the JIT argument index now.
#
# ⚠️ AND THERE IS NO UPSTREAM ORACLE FOR THIS FILE. The swipl differential covers TABLING, which is a
# port; the index is ours. Any change here needs its own test — it cannot lean on `swipl_tabling_oracle.sh`.
#
# 🔶 PARTIALLY WRONG, corrected 2026-09-03: a partial oracle DOES exist —
# `dev-zone/swipl-devel/tests/db/test_jit.pl` (237 lines). Most of it is useless to us (6 of ~25
# tests assert DETERMINISM — `Det == true`, `var(Det)`, `nondet` — which is meaningless here), but
# `test(retract)` / `test(retract2)` / `test(clause)` (:101-115) assert the COMPLETE, ORDERED answer
# set (`Xs == Xsok`, `numlist(11,100,Xsok)`) survives enumeration while the index is mutated
# underneath, including a `garbage_collect_clauses/0` fired mid-walk. That is exactly our multiset
# requirement, and `test(remove)` ×2 covers index MIGRATION between arguments. Reframe as: "the index
# yields a SUPERSET of the true matches, and enumerating it gives exactly the true multiset in source
# order." [[feedback_upstream_tests_are_the_first_thing_to_port]]
#
# ── 🔴 IF YOU TAKE MORE OF `pl-index.c`, TWO OF ITS DECISIONS ARE WRONG FOR A MULTISET LANGUAGE ──
# Analysed 2026-09-03 against HEAD `63240a40`. We currently have NEITHER — verified by grep, not
# assumed. Do not acquire them by transcribing.
#
#   1. THE METRIC IS BIASED TOWARD DETERMINISM. We ported the formula's clean half. Upstream then
#      divides by a stdev term ("punish bad distributions", `pl-index.c:2657-2660`) and bails out at
#      `a->size == 1` (`:2652`), because for Prolog an argument where every clause shares a key is a
#      FAILURE. For MeTTa that is a legitimate multi-answer relation. `first_clause_guarded`
#      (`:672-690`) also short-circuits the moment the primary scan is unique, and only hunts for a
#      better index when it finds DUPLICATES — the opposite of what we want.
#      ✅ ABSENT here: no `stdev`, no `perfect_size`, no `size == 1` bailout, nothing dedupes.
#
#   2. 🔴 DEEP (nested-argument) INDEXING IS INCOMPLETE BY DESIGN — IT DROPS ANSWERS.
#      `nextClauseFromList` (`:380-410`) recurses into the matching functor and RETURNS
#      UNCONDITIONALLY; the variable-clause sublist (`!cref->d.key`) is reached only when the functor
#      lookup FAILS. Upstream knows, and guards it by building a list index only when NO clause has a
#      variable there (`var_count == 0`, `:2666-2669`), admitting at `:2599-2603`: *"we cannot combine
#      variables with functor indexes … after going into the recursive indexes we lose the context to
#      find the unbound clause."*
#      That precondition WE CANNOT HONOUR. MeTTa heads routinely mix them: `(= (foo (bar $x)) …)` and
#      `(= (foo $y) …)` must BOTH fire on `(foo (bar 1))`. Porting `nextClauseFromList` as-is would
#      silently drop the second — the same defect class as the frozen-call miscompile
#      (`COMPILER_IL_STAGE.md` §5). The idea is worth having; the control flow must union the functor
#      and variable sublists instead of tail-calling.
#      ✅ ABSENT here: no deep/list index at all.
#
# ── AND `MAX_LOOKAHEAD` IS DEAD WEIGHT FOR US ──
# `pl-index.c:302-320` scans ahead up to 100 clauses PURELY to answer "will there be a second
# answer?", so the VM can skip creating a choice point. We always want every answer. ✅ ABSENT.
#
# ── COST, IF SOMEONE PROPOSES TAKING MORE ──
# You cannot PORT this file, you can only READ it. Every index key upstream derives from a stored
# clause comes from decoding WAM head BYTECODE (`indexKeyFromClause` :1600 -> `skipToTerm` :2733 ->
# `argKey` pl-comp.c:5416); no function there takes a clause and a TERM. That is ~450 lines replaced
# by ~60 in Julia. About 60% of the 4128 lines are deletions for us: ~540 MVCC/generations, ~150
# threading, ~640 Prolog-level plumbing. A full port is ~1000-1200 lines of Julia, a useful subset
# ~400-500 — concentrated in the assessment/policy layer, which is the part already here.
# READ FIRST, before any C: `dev-zone/swipl-devel/man/overview.plx:3761` (§Just-in-time clause
# indexing) and `:3859` (§Deep indexing) — ~140 lines of prose giving the strategy ordering, the
# formula's rationale, and deep indexing's stated limitations.

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
"""The index key for a GROUNDED value. 🔴 ONE FUNCTION, used by the bucket trie's `_tok` today and
by the argument index's grounded keys when those land, so the two cannot drift apart.

🔴 IT MUST AGREE WITH `==`, NOT WITH `hash` OR `isequal`, BECAUSE `match` COMPARES WITH `==` AND THE
THREE DISAGREE EXACTLY WHERE IT COSTS ANSWERS. MEASURED 2026-10-02:

    0.0 == -0.0   TRUE    isequal FALSE    hash(0.0) == hash(-0.0)   FALSE
    1   == 1.0    TRUE    isequal TRUE     hash equal                TRUE
    NaN == NaN    FALSE   isequal TRUE     hash equal                TRUE

Keying by bare `hash` therefore put a stored `(= (f 0.0) zero)` under one token and a call
`(f -0.0)` under another: the trie MISSED IT and the answer was DROPPED — and only once the bucket
exceeded `_TRIE_MIN_BUCKET`, so a program changed behaviour as its clause count crossed 16.
MEASURED: 4 clauses answered `["zero"]`, 41 answered `["(f -0.0)"]`.

🔴 AND `hash`-AGREES-WITH-`isequal` ONLY HELPS WHERE `==` AND `isequal` AGREE, WHICH FAILS FOR
CONTAINERS AND CUSTOM TYPES. `==` on a vector or tuple compares ELEMENTS with `==`, while `hash`
goes through `isequal`. MEASURED 2026-10-02 — every one of these is `==`-equal with DIFFERENT hashes:

    [0.0] vs [-0.0]        (0.0,1) vs (-0.0,1)        0.0+0.0im vs 0.0-0.0im
    a custom grounded type with its own `==` and no matching `hash`

Not hypothetical here: FactorVSA vectors and FabricPC tensors are grounded atoms.

⇒ KEY ONLY TYPES WHERE AGREEMENT IS GUARANTEED; return `nothing` for everything else, exactly as
`_idx_head` already signals "not indexable", so the two cannot drift apart.

🔴 AND "UNKEYED" MUST MEAN **WILDCARD**, NOT A SHARED BUCKET. Emitting one constant grounded token
for unkeyable values would put them all on a CONCRETE edge together — which fixes vector-vs-vector
but breaks EQUALITY ACROSS TYPES: a grounded type whose `==` accepts a built-in scalar (a dual
number, a unit-carrying quantity, a wrapper where `x == 1.0` holds) would sit under that shared
token while a query `1.0` looks under `hash(1.0)`, and the answer is dropped again. `_tok` therefore
emits `_Tok(_KVAR, 0)`, which is a wildcard in BOTH directions: a stored atom goes on the trie's
`star` edge, followed for EVERY query token, and a variable token in the QUERY collects the whole
subtrie (`_trie_collect!`). No narrowing, always a candidate.

⚠️ SIGNED ZERO ACROSS TYPES: raw `hash(0)` and `hash(-0.0)` DIFFER, but the normalisation maps
`-0.0` to `hash(0.0)` and `hash(0.0) == hash(0)`, so integer zero and both float zeros share one
key. Pinned in the test.
⚠️ `Bool <: Integer` in Julia, so it is covered by the `Integer` branch and agrees with `1`/`0` as
`==` requires. Do NOT add a separate branch for it."""
function gnd_key(v)::Union{UInt64, Nothing}
    if v isa AbstractFloat
        return v == 0.0 ? hash(0.0) : hash(v)   # -0.0 and 0.0 agree; NaN matches nothing anyway
    elseif v isa Integer || v isa Rational || v isa AbstractString ||
           v isa Char || v isa Symbol
        return hash(v)                          # `==` and `isequal` agree on these
    end
    nothing                                     # containers, complex, user types ⇒ WILDCARD
end

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
        # `nothing` ⇒ we cannot key this value in a way that agrees with `==` ⇒ WILDCARD, not a
        # shared grounded bucket. See `gnd_key`.
        let _k = gnd_key(a.value)
            _k === nothing ? _Tok(_KVAR, UInt64(0)) : _Tok(_KGND, _k)
        end
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
    # 🔴 ATOMS WITH A VARIABLE AT `argpos`, KEPT SEPARATELY AS WELL AS MERGED INTO EVERY BUCKET.
    # They match ANY key — including one NO stored atom carries, which is exactly the case
    # `get(buckets, key, Atom[])` used to answer with an empty list under the comment "absent key ⇒
    # genuinely no candidates". That is false whenever this list is non-empty, and it DROPPED
    # ANSWERS rather than merely slowing them down.
    wild::Vector{Atom}
end

"Build the index `best` describes, over `atoms`. Var-at-position atoms go in EVERY bucket — they can match anything."
function _build_arg_index(atoms::Vector{Atom}, best::ArgAssessment)::ArgIndex
    _key(a) = (a isa Expression && length(a.children) >= best.argpos) ?
              _idx_head(a.children[best.argpos]) : nothing

    # 🔴 TWO PASSES, AND STORE ORDER IS THE REASON. The previous version filled the buckets and THEN
    # `append!`ed the var-at-position atoms to the end of each one, so a bucket read back
    # [keyed…, wild…] while the unindexed scan reads the store in insertion order. Answers came back
    # REORDERED — set-equal but not list-equal — and MeTTa answers are a MULTISET whose ORDER
    # `collapse` exposes, so that is a semantic difference, not a cosmetic one. MEASURED:
    # `(≞ (⊗ Q) $t)` gave [0.4, 0.9] unindexed and [0.9, 0.4] indexed.
    # Collecting the keys first lets ONE ordered walk place every atom — into its own bucket, or
    # into EVERY bucket when it is wild — so each bucket keeps store order by construction.
    # ⚠️ A SET ALONGSIDE THE VECTOR, NOT THE VECTOR ALONE. `k in keys_seen` on a Vector is O(K) per
    # atom, so building costs O(N·K). With the HEAD-SYMBOL key K is tiny and that is invisible — but
    # the DEEP KEY makes K ≈ N (one key per `(→, A_i)`), and the build becomes O(N²): exactly the
    # shape the deep key exists to remove. The vector keeps FIRST-SEEN ORDER, which is what makes
    # each bucket store-ordered; the set answers membership in O(1).
    keys_seen = Symbol[]
    keys_set  = Set{Symbol}()
    for a in atoms
        k = _key(a)
        (k === nothing || k in keys_set) || (push!(keys_seen, k); push!(keys_set, k))
    end
    buckets = Dict{Symbol, Vector{Atom}}(k => Atom[] for k in keys_seen)
    wild = Atom[]
    for a in atoms
        k = _key(a)
        if k === nothing
            push!(wild, a)                       # matches any key …
            for kk in keys_seen                  # … so it belongs in every bucket, IN ORDER
                push!(buckets[kk], a)
            end
        else
            push!(buckets[k], a)
        end
    end
    ArgIndex(best.argpos, best.speedup, buckets, wild)
end

"""
    index_candidates(store_atoms, arg_index, jiti_tried, pattern) -> Vector{Atom}

Candidate atoms for `pattern`, narrowed by a JIT argument index when one pays for itself. Returns
`store_atoms` unchanged when no index applies — the caller's behaviour is then bit-identical to the
unindexed scan, which is what makes this safe to put on `match`'s path.

Upstream's `jiti_tried` is mirrored by the `tried` set: an assessment that declined must NOT be
re-run on every query, or the assessment costs more than the scan it was meant to save.
"""
# ─── IS JIT INDEXING LIVE, AND HOW WELL? — modelled on SWI's `library(prolog_jiti)`/`jiti_list` ──
# 🔴 THERE WERE NO COUNTERS AT ALL, so "is indexing still wired after the store/space refactors"
# could only be ANSWERED BY READING CALL SITES — and a seam added in front of `rule_results` could
# bypass it with nothing to show. These make it a measurement. Cost is four integer increments on a
# path that already builds a vector.
"""Turn every candidate narrowing OFF, so `index_candidates` returns the whole store.

🔴 THE UNINDEXED SCAN IS THE ORACLE for every narrowing in this file — a filter's only licence is to
return a SUPERSET of what can match, and a filter that drops a candidate returns FEWER ANSWERS,
which no assertion about the remaining answers can see. `test_index_candidates_differential.jl`
runs each pattern both ways and demands identical answers, order and multiplicity included."""
const INDEX_ENABLED = Ref(true)

const _IDX_LOOKUPS   = Ref(0)   # calls to `index_candidates`
const _IDX_SERVED    = Ref(0)   # … where an index actually applied (a bucket was returned)
const _IDX_CANDS     = Ref(0)   # candidates handed back, summed
const _IDX_STORE     = Ref(0)   # atoms that would have been scanned without an index, summed
const _IDX_BUILT     = Ref(0)   # indexes constructed

"""Per-run JIT-indexing statistics — the `jiti_list` equivalent. `served/lookups` is how often an
index applied; `1 - cands/store` is the fraction of the store it SKIPPED. Zero lookups on a real
workload means something bypassed the indexed path."""
index_stats() = (; lookups = _IDX_LOOKUPS[], served = _IDX_SERVED[], built = _IDX_BUILT[],
                 candidates = _IDX_CANDS[], store_scanned = _IDX_STORE[],
                 skipped_frac = _IDX_STORE[] == 0 ? 0.0 :
                                1 - _IDX_CANDS[] / _IDX_STORE[])
reset_index_stats!() = (_IDX_LOOKUPS[] = 0; _IDX_SERVED[] = 0; _IDX_CANDS[] = 0;
                        _IDX_STORE[] = 0; _IDX_BUILT[] = 0; nothing)

function index_candidates(
    store_atoms::Vector{Atom},
    arg_index::Dict{Tuple{Symbol, Int}, ArgIndex},
    tried::Set{Tuple{Symbol, Int}},
    pattern::Atom
)::Vector{Atom}
    _IDX_LOOKUPS[] += 1
    _IDX_STORE[] += length(store_atoms)
    INDEX_ENABLED[] || (_IDX_CANDS[] += length(store_atoms); return store_atoms)
    pattern isa Expression || (_IDX_CANDS[] += length(store_atoms); return store_atoms)
    head = _idx_head(pattern)
    head === nothing && (_IDX_CANDS[] += length(store_atoms); return store_atoms)          # var-headed pattern: nothing to key on
    inst = instantiated_positions(pattern)
    isempty(inst) && (_IDX_CANDS[] += length(store_atoms); return store_atoms)             # pl-index.c:3068 — no instantiated argument

    for pos in inst                                 # an index we already built and can use
        ix = get(arg_index, (head, pos), nothing)
        ix === nothing && continue
        key = _idx_head(pattern.children[pos])
        key === nothing && continue
        # 🔴 AN ABSENT KEY IS NOT "no candidates" — the var-at-position atoms match it. Returning
        # `Atom[]` here DROPPED THEM.
        _b = get(ix.buckets, key, ix.wild)
        _IDX_SERVED[] += 1; _IDX_CANDS[] += length(_b)
        return _b
    end

    # 🔴 `tried` IS KEYED (head, position), NOT head — FIXED 2026-08-28, found by comparing against
    # JeTTa's global trie. Keyed by head alone, the FIRST query's choice locked out every other
    # position forever: an index built at position 2 marked `belief` tried, so a later
    # `(belief $k s7 $c)` — instantiating position 3, the very case this exists for — short-circuited
    # to the full store and never assessed. MEASURED: 2123 of 2123 candidates, i.e. no narrowing at
    # all. Upstream has no such bug; `bestHash` is called with the CURRENT argument vector each time
    # and several indexes coexist per predicate (`args[MAX_MULTI_INDEX]`).
    all(pos -> (head, pos) in tried, inst) && (_IDX_CANDS[] += length(store_atoms); return store_atoms)
    for pos in inst
        push!(tried, (head, pos))
    end

    # 🔴 `_idx_head(a) === nothing` MEANS THE STORED ATOM'S HEAD IS NOT A SYMBOL — a variable head
    # like `($h A0 A1)`, which matches ANY head and so must stay a candidate for this one. Keeping
    # only `=== head` silently dropped such atoms the moment an index applied. It is the HEAD that
    # is wild, not the position, so these are still keyed by their argument and keep their
    # selectivity. Filtering `store_atoms` in place preserves store order.
    same_head = Atom[
        a for a in store_atoms
        if a isa Expression && !isempty(a.children) &&
           (_idx_head(a) === head || _idx_head(a) === nothing)
    ]
    length(same_head) <= _TRIE_MIN_BUCKET && (_IDX_CANDS[] += length(store_atoms); return store_atoms)   # too small to be worth an index
    best = best_index_argument(same_head, inst)
    best === nothing && (_IDX_CANDS[] += length(store_atoms); return store_atoms)

    ix = _build_arg_index(same_head, best)
    arg_index[(head, best.argpos)] = ix
    key = _idx_head(pattern.children[best.argpos])
    # 🔴 THE BUILD PATH RETURNS CANDIDATES TOO, AND IT WAS UNCOUNTED — which is why `served` read 0
    # on exactly the calls that were reordering answers, hiding the defect from the statistics.
    if key === nothing
        _IDX_CANDS[] += length(store_atoms)
        return store_atoms
    end
    _b = get(ix.buckets, key, ix.wild)
    _IDX_SERVED[] += 1; _IDX_CANDS[] += length(_b)
    return _b
end
