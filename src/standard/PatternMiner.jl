# PatternMiner.jl — simplified frequent-pattern miner (the Hyperon Pattern Miner core) on the
# def/match/emit surface (F1R3FLY MeTTa-IL layered track).
#
# Faithful to Pattern-Miner-Tutorial-MeTTa4 §2 + the scalable-infra §9.1 def/match/emit staging,
# simplified to the FREQUENT-pattern core:
#   (1) ABSTRACTION — generate one-hole candidate patterns via a def/match/emit pipeline that emits
#       `(cand PATTERN)` with `_` wildcards in abstracted positions (`_` is a literal marker — no fresh
#       variable needed; MORK dedups identical candidates automatically).
#   (2) SUPPORT — count the distinct ground atoms each pattern matches (a `_` matches anything). Counted
#       by scanning the trie dump with structural wildcard matching (encoding-safe; a production miner
#       would use the MORK CountSink / an indexed prefix scan — see MORK-Miner).
#   (3) MARK-KEPT — keep candidates whose support ≥ minsup.
#
# Follow-ons (per the tutorial): build-specialization, conjunction expansion (do-conjunct → `(and …)`),
# and I-surprisingness ranking (needs grounded arithmetic: P_obs/P_exp/I).

# --- Three-dialect support comparison (scalable-infra §9: same algorithm, compare the dialects) ------
# §9 implements the SAME miner across language dialects to COMPARE them. `support` (the §7.3 stream op)
# is the heart. Three ways to count a pattern's support:
#   * RAW-MeTTa (interpreter): `(size-atom (collapse (match …)))` — MeTTa-level aggregation [this fn].
#   * RELATIONAL (MeTTa-IL→MM2): structural trie-dump wildcard match [pattern_support below].
#   * MORK-NATIVE (trie index): `space_query_multi` on the comma-wrapped pattern `(, P)` — O(matches),
#     no full scan [pattern_support_native]. The wrapper is REQUIRED (query_multi processes a `(, …)`
#     conjunction; a bare pattern matches nothing — see space.rs `dump_sexpr`).

"Support via the RAW-MeTTa interpreter dialect: `(size-atom (collapse (match &self P P)))` over `data`.
`pattern` uses dollar-prefixed query variables; counts distinct matching atoms."
function pattern_support_interp(data::AbstractString, pattern::AbstractString)::Int
    sp = Eval.Space(); Eval.load_core_stdlib!(sp); Eval.load_metta!(sp, data)
    r = Eval.load_metta!(sp, "!(size-atom (collapse (match &self $pattern $pattern)))")
    vs = [string(x) for rr in r for x in (rr isa AbstractVector ? rr : [rr])]
    isempty(vs) ? 0 : something(tryparse(Int, vs[1]), 0)
end

"Support via the MORK-NATIVE trie-index query: `space_query_multi` on the comma-wrapped pattern — counts
matches by walking the index (O(matches)), no O(N) scan. `pattern` uses dollar-vars."
function pattern_support_native(cs::CoreSpace, pattern::AbstractString)::Int
    pat = sexpr_to_expr("(, $pattern)")        # comma-functor wrapper REQUIRED by query_multi
    n = Ref(0)
    space_query_multi(cs.inner, pat, (_b, _l) -> (n[] += 1; true))
    n[]
end

"Support of a `_`-wildcard `pattern`: the count of distinct ground atoms in `cs` that it matches."
function pattern_support(cs::CoreSpace, pattern::AbstractString)::Int
    pt = mm2_expr_args(pattern)
    n = 0
    for line in split(space_dump_all_sexpr(cs.inner), '\n')
        atom = strip(line)
        (isempty(atom) || !startswith(atom, "(")) && continue
        toks = mm2_expr_args(atom)
        length(toks) == length(pt) || continue
        all(((p, t),) -> p == "_" || p == t, zip(pt, toks)) && (n += 1)
    end
    n
end

"""
    mine_frequent(cs, abstract_pipeline, minsup) -> Vector{Tuple{String,Int}}

Mine frequent patterns from `cs`: run `abstract_pipeline` (a def/match/emit program emitting
`(cand PATTERN)` facts with `_` wildcards) to generate candidate patterns, count each pattern's support
(distinct matches), and keep those with support ≥ `minsup`. Returns sorted `(pattern, support)` pairs.
"""
function mine_frequent(cs::CoreSpace, abstract_pipeline::AbstractString, minsup::Integer)
    cands = metta_il_run_pipeline!(cs, "", abstract_pipeline)
    kept = Tuple{String, Int}[]
    for c in cands
        mm2_head(c) == "cand" || continue
        pat = mm2_expr_args(c)[2]                       # inner pattern from (cand PATTERN)
        s = pattern_support(cs, pat)
        s >= minsup && push!(kept, (pat, s))
    end
    sort(unique(kept))
end

# --- MORK-native prefix-locality miner (MORK-Miner.pdf) ----------------------------------------------
# A complementary miner that exploits MORK PathMap LOCALITY: atoms stored as token-paths share byte-trie
# prefixes, so atoms with a common leading-token prefix are "nearby"/semantically related. Patterns are
# LEFT-ANCHORED prefixes `(head t1 … tk _)` (vs mine_frequent's any-position `_` wildcards), and support
# is the count of atoms under a prefix — the MORK-Miner's "in-place prefix counter". The pipeline:
#   (1) SEED — distinct prefixes at a given depth; (2) SUPPORT — count atoms under each prefix;
#   (3) GROW — extend a frequent prefix one token deeper.
# This realizes the prefix-locality CONCEPT; the production O(1) optimization (counters incremented at
# trie nodes on insert, read via a zipper at the prefix node) refines the dump-scan support here.

# --- MORK-Miner IN-PLACE prefix counters (the ACTUAL §2.3 mechanism) ---------------------------------
# §2.3: "Whenever a new data item is STORED, the miner increments a counter at each prefix node along its
# key path. The support of any pattern is obtained by READING the counter — no separate counting pass."
# So support is O(1) (a counter read), maintained at INSERT time — that is the source of the paper's
# "orders of magnitude / no global scans" speedup. (A post-hoc query/scan is the WRONG mechanism — the
# very "separate counting pass" §2.3 says you don't do; benchmarking that mis-read the claim as negative.)

"""
    PrefixCounter()

In-place prefix-support counters (MORK-Miner §2.3). Holds an integer counter at every prefix node of every
stored atom's key path, maintained at insert time by [`prefix_insert!`](@ref); support is then an O(1)
read via [`prefix_count_support`](@ref) — no scan or query pass. Build one from a dataset with
[`prefix_counter`](@ref).
"""
struct PrefixCounter
    counts::Dict{Vector{String}, Int}
end
PrefixCounter() = PrefixCounter(Dict{Vector{String}, Int}())

"Store an atom: increment the counter at EVERY prefix node along its key path (MORK-Miner §2.3 insert)."
function prefix_insert!(pc::PrefixCounter, atom::AbstractString)
    toks = mm2_expr_args(atom)
    @inbounds for k in 1:length(toks)
        key = toks[1:k]
        pc.counts[key] = get(pc.counts, key, 0) + 1
    end
    pc
end

"Build the in-place prefix counters from a newline-separated atom set (the one-time storage pass)."
function prefix_counter(data::AbstractString)::PrefixCounter
    pc = PrefixCounter()
    for line in split(data, '\n')
        a = strip(line); (isempty(a) || !startswith(a, "(")) && continue
        prefix_insert!(pc, a)
    end
    pc
end

"O(1) support: READ the in-place counter at `prefix`'s node (no scan, no query pass) — MORK-Miner §2.3."
prefix_count_support(pc::PrefixCounter, prefix::AbstractVector{<:AbstractString})::Int =
    get(pc.counts, collect(String, prefix), 0)

"Prefix support: count of atoms in `cs` whose leading tokens equal `prefix` (the MORK prefix counter)."
function prefix_support(cs::CoreSpace, prefix::AbstractVector{<:AbstractString})::Int
    n = 0
    for line in split(space_dump_all_sexpr(cs.inner), '\n')
        atom = strip(line)
        (isempty(atom) || !startswith(atom, "(")) && continue
        toks = mm2_expr_args(atom)
        length(toks) >= length(prefix) && all(((p, t),) -> p == t, zip(prefix, toks)) && (n += 1)
    end
    n
end

"""
    mine_prefix_patterns(cs, depth, minsup) -> Vector{Tuple{String,Int}}

MORK-native seed extraction + support: group atoms by their leading `depth` tokens (trie prefix), count
atoms under each prefix, and keep prefixes with support ≥ `minsup`, returned as `(t1 … _)` patterns.
"""
function mine_prefix_patterns(cs::CoreSpace, depth::Integer, minsup::Integer)
    counts = Dict{Vector{String}, Int}()
    for line in split(space_dump_all_sexpr(cs.inner), '\n')
        atom = strip(line)
        (isempty(atom) || !startswith(atom, "(")) && continue
        toks = mm2_expr_args(atom)
        length(toks) > depth || continue                 # proper prefix: atom extends past `depth`
        counts[toks[1:depth]] = get(counts, toks[1:depth], 0) + 1
    end
    sort(Tuple{String, Int}[("(" * join(p, " ") * " _)", n) for (p, n) in counts if n >= minsup])
end

"""
    grow_prefix(cs, prefix, minsup) -> Vector{Tuple{String,Int}}

MORK-native growth: extend a frequent `prefix` (token vector) by one token via prefix proximity, keeping
the deeper prefixes whose support ≥ `minsup`.
"""
function grow_prefix(cs::CoreSpace, prefix::AbstractVector{<:AbstractString}, minsup::Integer)
    counts = Dict{String, Int}()
    for line in split(space_dump_all_sexpr(cs.inner), '\n')
        atom = strip(line)
        (isempty(atom) || !startswith(atom, "(")) && continue
        toks = mm2_expr_args(atom)
        (length(toks) > length(prefix) && all(((p, t),) -> p == t, zip(prefix, toks))) || continue
        counts[toks[length(prefix) + 1]] = get(counts, toks[length(prefix) + 1], 0) + 1
    end
    sort(Tuple{String, Int}[("(" * join(vcat(prefix, [t]), " ") * " _)", n)
                            for (t, n) in counts if n >= minsup])
end
