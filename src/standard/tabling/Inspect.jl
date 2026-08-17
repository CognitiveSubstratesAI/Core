# tabling/Inspect.jl — the TABLE INSPECTION API. SWI's `library(tables)`.
#
# Ports the portable half of `library/tables.pl` (381 lines of Prolog over 7 C primitives). Read from
# the VENDORED SOURCE (`dev-zone/swipl-devel/library/tables.pl`), not the rendered doc page — which
# differs: the source exports `'t not'/1` WITH A SPACE, plus `abolish_all_tables/0`,
# `abolish_module_tables/1` and `op(900, fy, tnot)`.
#
# ─── WHY THIS IS CHEAP NOW AND WAS NOT BEFORE ────────────────────────────────────────────────────
# `library(tables)` is a THIN layer: 381 Prolog lines resting on seven C primitives. Five we already
# have, and the answer trie (§1.0 step 4) is the substrate the rest need:
#
#   $tbl_variant_table    -> _ANSWER_TRIES, keyed by variant        HAVE
#   $tbl_answer           -> trie_answers                           HAVE
#   $tbl_trienode         -> MODED_SLOT                             HAVE
#   $table_mode           -> table_modes                            HAVE
#   $tbl_table_status     -> table_status (AnswerTrie.status)       HAVE as of this file
#   $tbl_answer_dl        -> —                                      MISSING: delay lists
#   $tbl_answer_update_dl -> —                                      MISSING: delay lists
#
# ⚠️ THE MISSING TWO ARE EXACTLY THE SPLIT. `get_residual/2`, `get_returns_and_dls/3` and
# `get_returns_and_tvs/3` are the three predicates that need a DELAY LIST, and they are the three
# NOT ported here. That boundary is visible in the primitive list rather than being a judgement call
# — see §7.6.1 in `Core/docs/TABLING_ROADMAP.md`, which needs delay lists structurally.
#
# 🛑 DO NOT PORT `set_pil_on/0` / `set_pil_off/0`. The source documents them as DUMMIES retained for
# XSB compatibility — they have no effect. A faithful port of a no-op is still a no-op.
#
# ─── WHAT WE DELIBERATELY DO NOT MIRROR ──────────────────────────────────────────────────────────
# Upstream threads a MODULE through everything (`'$tbl_implementation'(Goal0, M:Goal)`,
# `abolish_module_tables/1`). MeTTa has no module system at this layer, so the module argument is
# dropped rather than faked with a placeholder. `abolish_module_tables/1` is therefore absent, not
# missing: it names a concept we do not have.

"""
    get_call(goal_or_key) -> Union{Tuple{Atom,AnswerTrie,Symbol},Nothing}

`get_call/3` (`library/tables.pl`). Returns `(variant_key, answer_trie, status)` for a tabled call,
or `nothing` if no table exists for it.

Upstream returns `(Trie, Return)` where `Return` is a skeleton extended by the mode declaration
(`extend_return(Moded, Skeleton, Return)`). We return the VARIANT KEY instead: for us the key IS the
skeleton, since `mode_key` already replaced moded positions with `MODED_SLOT` — upstream's
`extend_return` exists to re-attach the moded arguments that its `Skel/MArgs` split removed.
"""
function get_call(goal::Atom)
    key = _variant_rename(goal)
    has_answer_trie(key) || return nothing
    t = answer_trie_for(key)
    (key, t, table_status(t))
end

"""
    get_calls(head) -> Vector{Tuple{Atom,AnswerTrie,Symbol}}

`get_calls/3` — the NONDETERMINISTIC form: every table whose variant key is headed by `head`.

Upstream enumerates on backtracking; the Julia analogue is a vector, since a caller that wants
laziness can iterate it. `[[feedback_native_julia_not_transliteration]]`
"""
function get_calls(head::Symbol)::Vector{Tuple{Atom,AnswerTrie,Symbol}}
    out = Tuple{Atom,AnswerTrie,Symbol}[]
    for key in sort!(collect(keys(_ANSWER_TRIES)); by = string)
        head_name(key) === head || continue
        t = answer_trie_for(key)
        push!(out, (key, t, table_status(t)))
    end
    out
end

"""
    get_returns(t) -> Vector{Atom}

`get_returns/2`. Every answer in the trie, in insertion order.

Upstream branches: a MODED table generates through `moded_gen_answer/3` (which re-attaches the
aggregated arguments), a plain one through `trie_gen/2`. Ours needs no branch — `trie_insert_moded!`
stores the already-merged answer AT the node, so the answer in the trie is the aggregated one.
"""
get_returns(t::AnswerTrie)::Vector{Atom} = trie_answers(t)

"""
    get_returns_with_nodes(t) -> Vector{Tuple{Atom,TrieNode}}

`get_returns/3` — `'\$trie_gen_node'(AnswerTrie, Return, NodeID)`, the answer WITH its trie node.

Upstream's NodeID is what lets a caller mutate or delete a specific answer. Returning the node
itself is the Julia form; there is no id table to index through.
"""
function get_returns_with_nodes(t::AnswerTrie)::Vector{Tuple{Atom,TrieNode}}
    out = Tuple{Int,Atom,TrieNode}[]
    stack = TrieNode[t.root]
    while !isempty(stack)
        n = pop!(stack)
        n.answer === nothing || push!(out, (n.seq, n.answer::Atom, n))
        for (_, c) in n.children; push!(stack, c); end
    end
    sort!(out; by = first)
    Tuple{Atom,TrieNode}[(a, nd) for (_, a, nd) in out]
end

"""
    get_returns_for_call(goal) -> Vector{Atom}

`get_returns_for_call/2`. The answers of the table for `goal`, or empty if it has none.
"""
function get_returns_for_call(goal::Atom)::Vector{Atom}
    c = get_call(goal)
    c === nothing ? Atom[] : get_returns(c[2])
end

"""
    abolish_table_pred!(head) -> Bool

`abolish_table_pred/1` — invalidate every tabled subgoal of `head`, keeping the DECLARATION.

⚠️ NOT the same as `untable!`, and the difference is upstream's: `untable/1` also retracts the
declaration and clears the predicate's attributes, so the predicate stops being tabled.
`abolish_table_pred/1` only drops the TABLES; the next call re-tables. Conflating them would make
"clear the cache" silently mean "stop memoising".
"""
function abolish_table_pred!(head::Symbol)::Bool
    had = any(k -> head_name(k) === head, keys(_ANSWER_TRIES)) ||
          any(k -> head_name(k) === head, keys(_ANSWER_TABLE))
    abolish_table_subgoals!(head)
    had
end

"""
    abolish_all_tables!()

`abolish_all_tables/0`. Drops every table, keeping every declaration — the whole-registry form of
`abolish_table_pred!`, and the counterpart to `untable_all!` which also drops declarations.
"""
function abolish_all_tables!()
    empty!(_ANSWER_TABLE); empty!(_ANSWER_STAMP); empty!(_PARTIAL); empty!(_PARTIAL_READ)
    clear_answer_tries!(); clear_worklists!()
    nothing
end

"Every head that currently has at least one table. The inspection entry point `get_calls` needs."
tabled_heads()::Vector{Symbol} =
    sort!(unique(Symbol[head_name(k) for k in keys(_ANSWER_TRIES)]))
