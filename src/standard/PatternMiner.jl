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
