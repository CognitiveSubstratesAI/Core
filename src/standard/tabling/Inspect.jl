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
#   $tbl_trienode         -> MODED_SLOT                             HAVE
#   $table_mode           -> table_modes                            HAVE
#   $tbl_table_status     -> table_status (AnswerTrie.status)       HAVE as of this file
#   $tbl_answer           -> trie_answers + answer_condition        HAVE as of 2026-08-18
#   $tbl_answer_dl        -> answer_condition (Delays.jl)           HAVE as of 2026-08-18
#   $tbl_answer_update_dl -> N/A BY CONSTRUCTION — see below
#
# ─── 🔴 THE "MISSING PRIMITIVE" SPLIT WAS WRONG IN BOTH DIRECTIONS ───────────────────────────────
# This header used to say `get_residual/2`, `get_returns_and_dls/3` and `get_returns_and_tvs/3` were
# blocked on two absent C primitives. Read against the code, neither half of that holds:
#
#  1. **No new primitive was needed.** `get_residual/2` (`library/tables.pl:269-271`) and
#     `get_returns_and_dls/3` (`:227`) are both built on `'$tbl_answer'/3`, which is
#     `trie_gen` + `unify_delay_info` (`pl-tabling.c:5391-5399`). We already had BOTH halves: the
#     enumeration is `trie_answers`, the condition is `delays_of`. All that was missing was the
#     accessor that names the trichotomy — `answer_condition`, now in `Delays.jl`.
#
#  2. **`'$tbl_answer_update_dl'` can NEVER be ported as a unit, so it is not a gap.** Its return
#     value is the same condition; its PURPOSE is the side effect at `pl-tabling.c:5520`,
#     `tbl_push_delay` onto the trail-scoped delay register — which is exactly the register roadmap
#     7.A replaces by putting the condition ON the value. Porting the side effect re-introduces what
#     the design removed. It is N/A by construction, not deferred.
#
# ⇒ the three predicates below are ported. What DOES stay unported is the RENDERING detail flagged on
# `delay_lists`: upstream writes a negative delay `tnot(G)`, we write `(not g)`, and in MeTTa `not` is
# a different (truth-functional) operator. That is a real divergence, and a smaller one than a
# missing predicate.
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

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# THE DELAY-LIST HALF — the three predicates this file used to declare unportable.
#
# All three read ONE thing, `'$tbl_answer'/3`'s Condition, which is `answer_condition` in
# `Delays.jl`. What differs between them is the SHAPE of the report, and the differences are not
# cosmetic:
#
#   get_returns_and_tvs/3   one row per ANSWER, condition collapsed to `t`/`u`   (`:200-218`)
#   get_returns_and_dls/3   one row per ANSWER, condition as a list of lists     (`:226-238`)
#   get_residual/2          one row per DISJUNCT of the condition                (`:262-286`)
#
# 🔴 THE LAST ROW IS THE WHOLE POINT OF HAVING BOTH. Upstream's own doc says
# `get_returns_and_tvs/3` "will succeed only once" for a multi-delay-list answer and is therefore
# cheaper than `get_residual/2`; `get_residual/2` is nondeterministic PER DISJUNCT
# (`condition_delay_list/3`, `:280-283`, a `;` between the two recursive calls) while
# `condition_delay_lists/3` (`:232-235`) collects every disjunct into ONE solution. An
# implementation that gives both the same row count has broken both.
# ═══════════════════════════════════════════════════════════════════════════════════════════════

"""
    get_returns_and_tvs(t) -> Vector{Tuple{Atom,Symbol}}

`get_returns_and_tvs/3` (`library/tables.pl:200-218`) — every answer with its WFS TRUTH VALUE:
`:t` when the answer is unconditional, `:u` when it is conditional. ONE row per answer, even when
the condition has several disjuncts (upstream says so explicitly, which is why it is cheaper than
`get_residual`).

🔴 `:u` INCLUDES THE REASON-LESS BOTTOM. Upstream's test is `AN == true -> t ; u` over
`'\$tbl_answer_dl'`, and `unify_delay_info` hands back the ATOM `undefined` — not `true` — for a
`DL_UNDEFINED` node (`pl-tabling.c:5371`), so that answer is `u`. Ours goes through
`answer_condition`, which is built on `is_undefined` for exactly this reason: computing the truth
value as `answer_residual(a) != Sym("True")` would report `:t` for an UNDEFINED answer, because
`answer_residual` renders an empty DNF as `True`. That is a soundness INVERSION and it is the
shortest implementation available — see `answer_condition`'s docstring.

⚠️ NO MODED BRANCH. Upstream needs two clauses (`:201-212` moded, `:214-218` plain) because a moded
table stores `Skeleton` and `Moded` separately and `extend_return/3` has to re-attach them.
`trie_insert_moded!` stores the already-merged answer AT the node, so `get_returns` is already the
aggregated answer and one clause covers both — the same reason `get_returns/2` needs no branch.
"""
get_returns_and_tvs(t::AnswerTrie)::Vector{Tuple{Atom,Symbol}} =
    Tuple{Atom,Symbol}[(a, answer_condition(a) === COND_TRUE ? :t : :u) for a in get_returns(t)]

"""
    get_returns_and_dls(t) -> Vector{Tuple{Atom,Vector{Vector{Atom}}}}

`get_returns_and_dls/3` (`library/tables.pl:226-228`) — every answer with its DELAY LISTS: a list of
lists, inner list a conjunction, outer list a disjunction (`condition_delay_lists/3`, `:230-238`,
here `delay_lists`).

ONE row per ANSWER. An unconditional answer appears with an EMPTY outer list — it is not filtered
out, matching `condition_delay_lists(true, _, [])` (`:230`). Contrast `get_residual`, which splits
the outer list across rows.
"""
get_returns_and_dls(t::AnswerTrie)::Vector{Tuple{Atom,Vector{Vector{Atom}}}} =
    Tuple{Atom,Vector{Vector{Atom}}}[(a, delay_lists(a)) for a in get_returns(t)]

"""
    get_residual(goal) -> Vector{Tuple{Atom,Vector{Atom}}}

`get_residual/2` (`library/tables.pl:262-286`) — the answers of `goal`'s table, each paired with ONE
DISJUNCT of its condition. XSB's shape: a conjunction as a LIST, produced nondeterministically per
disjunct.

🔴 IT CANNOT KEEP ITS ARITY, AND THE REASON IS THE LANGUAGE, NOT THE PORT. Upstream is
`get_residual(:CallTerm, -DelayList)`: the ANSWER comes back THROUGH `CallTerm`, because in Prolog
an answer IS a substitution over the goal term — binding the goal's variables IS reporting the
answer, so two arguments suffice. Here an answer is an unrelated VALUE: `(r)` reduces to `1`, and
nothing about `1` is recoverable from the atom `(r)`. Both halves must therefore come out, hence
`Vector{Tuple{answer, delay_list}}`. Collapsing to just the delay lists would report WHICH
conditions the table holds while losing which answer each belongs to.

🔴 ONE ROW PER DISJUNCT — this is what separates it from `get_returns_and_dls`. `condition_delay_list/3`
(`:277-283`) puts a `;` between its two recursive calls, so a 2-disjunct condition SUCCEEDS TWICE
with one conjunction each; `condition_delay_lists/3` succeeds once with both. An answer whose
condition is `(A ∨ B)` therefore yields ONE row from `get_returns_and_dls` and TWO from here. An
unconditional answer still yields exactly one row, with an empty list (`:274-276`).

⚠️ EXACT-VARIANT LOOKUP, not upstream's variant-trie unification. `get_residual/2` enumerates
`trie_gen(VariantTrie, M:Variant, Trie)` (`:277`), so a partially-instantiated goal walks EVERY
matching table. We resolve through `get_call`, which is the exact variant key — the same choice
`get_returns_for_call` already makes, kept consistent deliberately rather than diverging within one
file. `get_calls(head)` is the enumeration entry point when several tables are wanted.
"""
function get_residual(goal::Atom)::Vector{Tuple{Atom,Vector{Atom}}}
    out = Tuple{Atom,Vector{Atom}}[]
    c = get_call(goal)
    c === nothing && return out                      # no table ⇒ no solutions, as upstream: `trie_gen` fails
    for a in get_returns(c[2]), dl in delay_list_disjuncts(a)
        push!(out, (a, dl))
    end
    out
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
    # 🔴 THE DEPENDENCY GRAPHS GO TOO — upstream says so outright (`boot/tabling.pl:1007-1016`):
    # *"The dependency graphs for incremental and monotonic tabling are reclaimed as well."* Leaving
    # them was the dangling-`_DEPS` class `abolish_table_subgoals!` is careful about — a resumption
    # firing into a table that no longer exists — and it made the two "clear everything" entry points
    # disagree, since `_table_reset!` already cleared all of them.
    empty!(_IDG); empty!(_MONO_DEPS); empty!(_MONO_QUEUE); empty!(_DEPS)
    empty!(_TABLE_INPROG); empty!(_GEN_STACK); empty!(_COMPONENT); empty!(_SCC_NEG)
    _CURRENT_TARGET[] = nothing
    empty!(_ANSWER_TABLE); empty!(_ANSWER_STAMP); empty!(_PARTIAL); empty!(_PARTIAL_READ)
    clear_answer_tries!(); clear_worklists!()
    nothing
end

"Every head that currently has at least one table. The inspection entry point `get_calls` needs."
tabled_heads()::Vector{Symbol} =
    sort!(unique(Symbol[head_name(k) for k in keys(_ANSWER_TRIES)]))

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# THE MeTTa SURFACE — and why it MUST take the GOAL, not the answer.
#
# 🔴 AN ANSWER-TAKING REPORTING OP IS UNREACHABLE FOR EXACTLY THE INPUTS IT EXISTS TO DESCRIBE.
# MEASURED 2026-08-18 (parent session, with a `println` inside the op body):
#
#     !(answer-residual 42)      op CALLED  with Grounded{Int64}   -> "True"        ✅
#     !(answer-residual (f))     op CALLED  with Grounded{Int64}   -> "True"        ✅  (tabled, value 7)
#     !(answer-residual (p))     op NEVER CALLED                   -> "undefined"   ❌  (tabled, ⊥)
#
# The cause is the WFS-bottom contagion guard the strict-op layer is built on: an argument that
# reduces to ⊥ short-circuits the ENCLOSING application, so an op whose whole purpose is to explain a
# ⊥ is the one op that never receives one. That guard is CORRECT for every strict operation and must
# not be punched through — which means the reporting surface has to sit UPSTREAM of argument
# evaluation, not downstream of it.
#
# Upstream reached the same shape for a different reason: `get_residual(:CallTerm, -DelayList)`
# (`library/tables.pl:262-274`) takes a GOAL and looks its table up. So the op below takes the goal
# UNEVALUATED — declared `Atom`-typed, exactly as `add-atom` does — and never sees a ⊥ argument at
# all, because it never has an evaluated argument.
# ═══════════════════════════════════════════════════════════════════════════════════════════════

"""
    GET_RESIDUAL — the MeTTa surface op `get-residual`.

`!(get-residual (r))` yields ONE result per `get_residual` row:

    (residual <answer> (<literal> …))

so an answer whose condition has two disjuncts appears TWICE, matching `get_residual/2`'s
nondeterminism (`library/tables.pl:280-283`). An UNCONDITIONAL answer appears once with an empty
literal list, and a goal with no table yields nothing at all — upstream's `trie_gen` simply fails,
and `Empty` is the MeTTa form of that.

🔴 THE GOAL ARRIVES UNEVALUATED, and that is load-bearing rather than stylistic — see the block
above. Registration MUST therefore declare the argument `Atom`-typed
(`_GROUNDED_OP_TYPES[GET_RESIDUAL] = "(-> Atom Atom)"`), the same mechanism `add-atom` uses to
receive its atom unreduced. The `Atom` RETURN half matters too: without it the reported rows take the
untyped path and are re-`metta`d, so `(residual 1 ())` would be reduced as an application — the
defect the `get-atoms` comment in `Eval.jl` records.

⚠️ IT DOES NOT DRIVE THE GOAL. `get_residual/2` is an INSPECTION predicate: it reads existing tables
and fails when there is none, and `library(wfs)`'s `call_residual_program/2` is the separate
predicate that calls first. Forcing evaluation here would silently make an inspector a driver, so the
caller runs `!(r)` and then `!(get-residual (r))`. This matches `get_call` / `get_returns_for_call`,
which do not drive either.
"""
const GET_RESIDUAL = Grounded(SpaceOp("get-residual", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    g = xs[1]
    (g isa Expression && !isempty(g.children)) || return ExecNoReduce()
    # `_reduced_goal` normalises the ARGUMENTS (`(fib (+ 4 4))` → `(fib 8)`) without evaluating the
    # goal itself — the same canonicalisation `tabled_eval` keys tables by, so a caller need not know
    # the internal key form. `get_residual` then applies `_variant_rename` on top.
    goal = _reduced_goal(g, space, Bindings())
    ExecOk(Atom[Expression(Atom[Sym("residual"), a, Expression(dl)])
                for (a, dl) in get_residual(goal)])
end))
