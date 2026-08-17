# tabling/Aggregation.jl — MODE-DIRECTED TABLING / answer subsumption. SWI manual §7.3.
#
# Mirrors `boot/tabling.pl`'s own AGGREGATION section (`:1515-1534`) plus the `update_goal/5` mode
# parser (`:1451-1513`). File boundary chosen to match upstream's section boundary, not invented.
#
# ─── WHAT IT IS ──────────────────────────────────────────────────────────────────────────────────
# Normally every distinct answer is kept. Under a MODE, one or more argument positions stop being
# part of the table KEY and become AGGREGATED: a second answer with the same key does not add a row,
# it MERGES into the existing row's value. `:- table path(_,_,min)` keeps the shortest path, not all
# paths.
#
# Two mode families, ported exactly (`boot/tabling.pl:1459-1495`):
#
#   lattice(F/3)   F(S0,S1,S)  — S is the merge of the stored S0 and the new S1.
#   po(F/2)        F(S0,S1)    — a PARTIAL ORDER test; upstream expands it to
#                                `(Call -> S2 = S0 ; S2 = S1)`, i.e. KEEP S0 WHEN F(S0,S1) HOLDS.
#
# and the six aliases (`:1503-1508`): first / - / last / min / max / sum.
#
# ─── JULIA SHAPE, NOT TRANSLITERATION ────────────────────────────────────────────────────────────
# Upstream's lattice is a 3-argument RELATION because Prolog returns through an argument. Ours is a
# 2-argument function returning the merged value, and `po` is a 2-argument predicate returning Bool.
# The SEMANTICS are 1:1; only the calling convention is native. `[[feedback_native_julia_not_transliteration]]`
#
# 🔴 THE CATCH THE ROADMAP RECORDED, AND WHY IT IS HANDLED HERE RATHER THAN AT THE CALL SITE.
# `Tabling.jl`'s completion loop decides "did this round grow?" by CARDINALITY:
#
#     _PARTIAL[m] = unique(vcat(_PARTIAL[m], np)); length(_PARTIAL[m]) != n0 && (grew = true)
#
# Under aggregation a merge CHANGES A VALUE WITHOUT CHANGING THE COUNT — `sum` folding (k,1) and
# (k,2) into (k,3) leaves the length identical. A cardinality test therefore reports "no growth" and
# the fixpoint terminates EARLY, silently, with a half-aggregated table. So `merge_answers` returns
# an explicit `changed::Bool` computed from the VALUES, and any caller must use that instead of a
# length comparison. This is the whole reason the function returns a tuple.
#
# ─── UPSTREAM TRACE ──────────────────────────────────────────────────────────────────────────────
# Names here follow swipl-devel so a reader can grep upstream directly. Ours ← theirs:
#
#   update_goal        ←  update_goal/5            boot/tabling.pl:1451   (mode spec → mode)
#   update_body        ←  update_body/6            boot/tabling.pl:1446   (apply per argument)
#   UPDATE_ALIAS       ←  update_alias/2           boot/tabling.pl:1503
#   LATTICE_OPS        ←  the public lattice preds boot/tabling.pl:1524
#   agg_first/last/…   ←  first/3 last/3 min/3 max/3 sum/3   boot/tabling.pl:1526-1531
#   ModeLattice        ←  lattice(F/3)             boot/tabling.pl:1459
#   ModePO             ←  po(F/2)                  boot/tabling.pl:1474
#   MODED_SLOT         ←  '$tbl_trienode'          the moded-argument placeholder in the answer trie
#
# ⚠️ NO DIRECT UPSTREAM ANALOGUE — do not go looking for these names in swipl-devel:
#   merge_answers, mode_key, table_mode!, TableMode/ModeIndex, has_aggregation
# Upstream performs the merge INSIDE the answer trie as part of `$tbl_wkl_add_answer`; it has no
# standalone "fold a list of answers under a mode vector" entry point, because it has no list — the
# trie is the table. These are the seam where our Vector-backed tables meet upstream's semantics,
# and they disappear into the trie when §1.0's rewire lands.

# 🔴🔴 SOUNDNESS: NON-IDEMPOTENT AGGREGATES ARE UNSOUND ON THE RECOMPUTATION BASE.
# Found 2026-08-16 while writing the negative control for the `_merge_partial` change, NOT by this
# file's differential — which compares `merge_answers` directly and never through a fixpoint.
#
# `_leader_pass` RE-RUNS every fixpoint round (the "extension table" design; see
# `Core/docs/tabling_delimited_control_spec.md`), so the same answers are re-derived and MERGED AGAIN
# each round. Measured:
#
#     _merge_partial([(p k 3)], [(p k 3)])  ->  (p k 6), changed=true
#     _merge_partial([(p k 6)], [(p k 3)])  ->  (p k 9), changed=true
#
# `min`/`max`/`first`/`last` are IDEMPOTENT — re-merging is a no-op and the loop converges. `sum` is
# NOT, and it does not converge; worse, every intermediate table is a WRONG NUMBER rather than a
# missing answer, so nothing downstream can detect it.
#
# ⇒ **`sum` (and any future non-idempotent lattice) MUST NOT BE ADVERTISED AS WORKING END TO END
# until §1.0's dependency-driven resumption lands**, which feeds each answer forward exactly once.
# This is an ordering constraint the roadmap did not list, and A REASON TO MOVE THE BASE IN ITS OWN
# RIGHT. ⚠️ It is NOT roadmap 2.0 — that is tabling-is-set vs MeTTa-is-multiset, which the base move
# does NOT fix. This one it does. Pinned as a hazard test in `test/standard/tabling/test_completion_merge.jl`,
# to be REWRITTEN to assert convergence when the rewire lands, not deleted.
#
# ⚠️ OPEN, AND DELIBERATELY NOT DECIDED HERE: what a mode KEYS OFF in MeTTa. Upstream can identify
# the TABLE head with the ANSWER head because an answer to `p(K,V)` IS a `p/2` term. MeTTa breaks
# that identity: `(= (fib 5) 5)` answers a fib goal with `5` — no argument structure, so `mode_key`
# returns the answer itself and no aggregation is expressible; and `(= (agg k) (P k 1))` answers with
# a term whose head is not the tabled head, so a table-head lookup and an answer-head lookup select
# DIFFERENT modes. That choice is §7.3 semantics, not an implementation detail.

# ── the mode ladder (boot/tabling.pl:1451-1513) ──────────────────────────────────────────────────
abstract type TableMode end

"An ordinary argument: part of the variant KEY, not aggregated. Upstream's default / `index`."
struct ModeIndex <: TableMode end

"""`lattice(F/3)` — `f(stored, new) -> merged`. `boot/tabling.pl:1459`.

Parameterised on the function type so `f` is a CONCRETE field: `f::Function` would make every
`update_body` call a dynamic dispatch through an abstract field, in the completion loop's hot path.
`[[feedback_no_any_typed_containers]]` / `[[feedback_perf_diagnosis_typeinstability_first]]`"""
struct ModeLattice{F} <: TableMode
    name::Symbol
    f::F
end

"`po(F/2)` — `f(stored, new) -> Bool`; TRUE keeps `stored`. `boot/tabling.pl:1474`. Parameterised
on the function type for the same reason as `ModeLattice` — a concrete `f`, not a dynamic dispatch."
struct ModePO{F} <: TableMode
    name::Symbol
    f::F
end

# ── the built-in lattice operations (boot/tabling.pl:1526-1531), ported line for line ────────────
#     first(S, _, S).                                    last(_, S, S).
#     min(S0,S1,S) :- (S0 @< S1 -> S = S0 ; S = S1).     max(S0,S1,S) :- (S0 @> S1 -> S = S0 ; S = S1).
#     sum(S0,S1,S) :- S is S0+S1.
# ⚠️ min/max are on the STANDARD ORDER (`@<`/`@>`), not numeric `<` — see StandardOrder.jl's header.
agg_first(s0::Atom, ::Atom)::Atom = s0
agg_last(::Atom, s1::Atom)::Atom  = s1
agg_min(s0::Atom, s1::Atom)::Atom = standard_lt(s0, s1) ? s0 : s1
agg_max(s0::Atom, s1::Atom)::Atom = standard_gt(s0, s1) ? s0 : s1

"`sum/3` is `S is S0+S1` — defined only on numbers, and upstream raises a type error off them."
function agg_sum(s0::Atom, s1::Atom)::Atom
    (s0 isa Grounded && (s0::Grounded).value isa Real) &&
    (s1 isa Grounded && (s1::Grounded).value isa Real) ||
        throw(ArgumentError("sum/3 aggregation expects numbers, got $(s0) and $(s1)"))
    Grounded((s0::Grounded).value + (s1::Grounded).value)
end

"`update_alias/2` — boot/tabling.pl:1503-1508. Note `-` is a synonym for `first`, not for `last`."
const UPDATE_ALIAS = Dict{Symbol,TableMode}(
    :first  => ModeLattice(:first, agg_first),
    Symbol("-") => ModeLattice(:first, agg_first),
    :last   => ModeLattice(:last,  agg_last),
    :min    => ModeLattice(:min,   agg_min),
    :max    => ModeLattice(:max,   agg_max),
    :sum    => ModeLattice(:sum,   agg_sum),
)

# 🔴 THESE REGISTRIES ARE OPEN, AND THAT IS THE PORT — CORRECTED 2026-08-17.
# They were closed sets, and `lattice(NAME)` THREW off them. Upstream accepts **any** atom:
# `lattice(Name/Arity)` requires only arity 3 (`boot/tabling.pl:1459-1495`) and `po(Name/Arity)` only
# arity 2. The six builtins are merely `update_alias/2` SHORTHANDS (`:1503-1508`) — and upstream ships
# **no built-in `po` predicates at all**; ours are a convenience, not a ceiling. Closing the set
# rejected the entire user-defined half of §7.3, which is what mode-directed tabling is FOR.
"Named lattice/3 operations. OPEN — `register_lattice!` adds one; the six below are the aliases."
const LATTICE_OPS = Dict{Symbol,Function}(
    :first => agg_first, :last => agg_last, :min => agg_min, :max => agg_max, :sum => agg_sum,
)
"Named po/2 operations. OPEN — upstream ships NONE of these; they are ours, and users may add more."
const PO_OPS = Dict{Symbol,Function}(
    :leq => (s0, s1) -> compare_standard(s0, s1) <= 0,
    :lt  => standard_lt,
    :geq => (s0, s1) -> compare_standard(s0, s1) >= 0,
    :gt  => standard_gt,
)

"""
    register_lattice!(name, f)   # f(stored, new) -> Atom, i.e. upstream's arity 3
    register_po!(name, f)        # f(stored, new) -> Bool, i.e. upstream's arity 2

Upstream's `lattice(Name/3)` / `po(Name/2)` accept any predicate of the right arity. These are the
Julia surface for that: register once, then `(lattice NAME)` resolves. The arity check is upstream's
only precondition, and here it is the function signature.
"""
register_lattice!(name::Symbol, f::Function) = (LATTICE_OPS[name] = f; nothing)
register_po!(name::Symbol, f::Function) = (PO_OPS[name] = f; nothing)

"""
    update_goal(spec) -> TableMode

`update_goal/5` (`boot/tabling.pl:1451`). Accepts `index`/`_`, a bare alias (`min`, `sum`, `-`, …),
`(lattice NAME)` and `(po NAME)`. Upstream raises `domain_error(tabled_mode, Mode)` on anything
else (`:1512`); we mirror that with a throw rather than silently defaulting to `index`, because a
mistyped mode that silently becomes a key argument is exactly the failure that reads as "aggregation
did nothing".
"""
function update_goal(spec::Atom)::TableMode
    if spec isa Sym
        n = (spec::Sym).name
        # `indexed_mode/1` has THREE clauses (`boot/tabling.pl:1421-1425`), one per dialect:
        # `var(Mode)` (XSB) · `index` (YAP) · `+` (B-Prolog). `+` was missing, so the legal
        # `:- table p(+, min)` was a domain_error for us. `:_` is our spelling of the var clause.
        (n === :index || n === :_ || n === Symbol("+")) && return ModeIndex()
        haskey(UPDATE_ALIAS, n) && return UPDATE_ALIAS[n]
        throw(ArgumentError("domain_error(tabled_mode, $(n)) — known: index, " *
                            join(sort(string.(collect(keys(UPDATE_ALIAS)))), ", ")))
    elseif spec isa Expression
        ch = (spec::Expression).children
        length(ch) == 2 && ch[1] isa Sym && ch[2] isa Sym || throw(ArgumentError(
            "domain_error(tabled_mode, $(spec)) — expected (lattice NAME) or (po NAME)"))
        kind, nm = (ch[1]::Sym).name, (ch[2]::Sym).name
        if kind === :lattice
            haskey(LATTICE_OPS, nm) || throw(ArgumentError(
                "unknown lattice/3: $(nm) — upstream accepts any Name/3; register it with " *
                "`register_lattice!(:$(nm), f)` where `f(stored, new) -> Atom`"))
            return ModeLattice(nm, LATTICE_OPS[nm])
        elseif kind === :po
            haskey(PO_OPS, nm) || throw(ArgumentError(
                "unknown po/2: $(nm) — upstream accepts any Name/2 (and ships none built in); " *
                "register it with `register_po!(:$(nm), f)` where `f(stored, new) -> Bool`"))
            return ModePO(nm, PO_OPS[nm])
        end
        throw(ArgumentError("domain_error(tabled_mode, $(spec))"))
    end
    throw(ArgumentError("domain_error(tabled_mode, $(spec))"))
end

is_moded(m::TableMode)::Bool = !(m isa ModeIndex)
"Does this spec aggregate at all? A mode vector of all-`index` must behave exactly like no mode."
has_aggregation(ms::Vector{<:TableMode})::Bool = any(is_moded, ms)

"Placeholder occupying a moded argument position in a variant key — upstream's `'\$tbl_trienode'`."
const MODED_SLOT = Sym(Symbol("\$moded"))

"""
    mode_key(goal, modes) -> Atom

The variant key with every MODED argument replaced by `MODED_SLOT`, so answers differing only in
their aggregated positions collapse to one row. `modes[i]` governs `goal.children[i+1]`, since
`children[1]` is the head.

A goal with fewer arguments than modes keeps the surplus modes unused rather than erroring — the
arity check belongs at declaration time, and failing here would abort a completing table.
"""
function mode_key(goal::Atom, modes::Vector{<:TableMode})::Atom
    goal isa Expression || return goal
    ch = (goal::Expression).children
    isempty(ch) && return goal
    out = Atom[ch[1]]
    for i in 2:length(ch)
        mi = i - 1
        push!(out, (mi <= length(modes) && is_moded(modes[mi])) ? MODED_SLOT : ch[i])
    end
    Expression(out)
end

"""Apply one mode to a stored/new value pair. `lattice` merges; `po` KEEPS `s0` when the test holds
(`boot/tabling.pl:1478`).

MULTIPLE DISPATCH, not an `isa` chain. Measured with JET: the chain emitted a runtime dispatch per
branch with the callee inferred only as `%::Any`, because `m` arrives from a `Vector{TableMode}` and
the `isa` test cannot narrow the FIELD type. Dispatching on the concrete mode types resolves `f` from
the struct parameter instead — one method lookup rather than a lookup plus an unknown call, and it is
the Julia idiom rather than a transliterated switch.
`[[feedback_perf_diagnosis_typeinstability_first]]` / `[[feedback_native_julia_not_transliteration]]`"""
update_body(::ModeIndex, ::Atom, s1::Atom)::Atom = s1
update_body(m::ModeLattice, s0::Atom, s1::Atom)::Atom = m.f(s0, s1)
update_body(m::ModePO, s0::Atom, s1::Atom)::Atom = m.f(s0, s1) ? s0 : s1

"""
    merge_answers(existing, incoming, modes) -> (answers, changed)

Fold `incoming` into `existing` under `modes`, returning the new answer list and whether ANY VALUE
CHANGED.

🔴 `changed` IS THE POINT. It is computed from values, never from `length(answers)`, because an
aggregating merge changes a value while leaving the count fixed — the silent early-fixpoint bug
described in this file's header. Callers must drive their completion loop on this flag.

With no moded position this degrades to upstream's ordinary behaviour and to ours: set semantics,
first occurrence wins, `changed` true exactly when a genuinely new key arrived.
"""
function merge_answers(existing::Vector{Atom}, incoming::Vector{Atom},
                       modes::Vector{<:TableMode})::Tuple{Vector{Atom},Bool}
    if !has_aggregation(modes)
        out = copy(existing); changed = false
        for a in incoming
            # 🔴 VARIANT, NOT STRUCTURAL — FIXED 2026-08-17 (adversarial audit vs the C).
            # Was `any(x -> x == a, out)`. Upstream's duplicate test IS the answer trie:
            # `trie_lookup_abstract(..., add=true)` then `if (node->value) return false`
            # (`pl-tabling.c:3596-3618`) — and the trie keys variables by FIRST-OCCURRENCE INDEX, so
            # `p($x)` and `p($y)` reach the SAME NODE and the second is a duplicate.
            #
            # `Atom ==` distinguishes `Var("_y",17)` from `Var("_y",23)`. So a non-ground answer whose
            # rule body introduces a FRESH VARIABLE is structurally new EVERY ROUND ⇒ `changed = true`
            # forever ⇒ the completion fixpoints (`Tabling.jl`'s `while true … grew || break`, and
            # `_S_P!`'s) DO NOT TERMINATE and `_PARTIAL` grows without bound. SWI terminates on the
            # same program. This is the single merge point for every completion path, so the bug was
            # reachable from all of them.
            #
            # `variant_eq` (tabling/AnswerTrie.jl) IS `=@=` — equality of `trie_keys`. It existed, its
            # own header argued exactly this point, and it was called ONLY from `trie_insert_moded!`;
            # the default wired path never reached it. Later include is fine — Julia resolves at call.
            any(x -> variant_eq(x, a), out) && continue
            push!(out, a); changed = true
        end
        return (out, changed)
    end

    order  = Atom[]                       # keys in first-seen order — answer order must be stable
    bykey  = Dict{Atom,Atom}()            # key ↦ the current (aggregated) answer
    for a in existing
        k = mode_key(a, modes)
        haskey(bykey, k) || push!(order, k)
        bykey[k] = a
    end

    changed = false
    for a in incoming
        k = mode_key(a, modes)
        if !haskey(bykey, k)
            push!(order, k); bykey[k] = a; changed = true
            continue
        end
        cur = bykey[k]
        (cur isa Expression && a isa Expression) || continue
        cc, ac = (cur::Expression).children, (a::Expression).children
        length(cc) == length(ac) || continue
        merged = Atom[cc[1]]
        for i in 2:length(cc)
            mi = i - 1
            push!(merged, (mi <= length(modes) && is_moded(modes[mi])) ?
                          update_body(modes[mi], cc[i], ac[i]) : cc[i])
        end
        new = Expression(merged)
        # 🔴 VARIANT AGAIN (same audit). Upstream's `update/7` 0b11 clause succeeds only when
        # `Agg \\=@= Next` (`boot/tabling.pl:752-755`). `!=` reports "changed" on a pure RENAMING of a
        # non-ground aggregated value, so the moded fixpoint never converges either.
        if !variant_eq(new, cur)          # VALUE-based change detection, not cardinality
            bykey[k] = new; changed = true
        end
    end
    (Atom[bykey[k] for k in order], changed)
end

# ── declaration surface: head ↦ per-argument modes ───────────────────────────────────────────────
const _MODE_SPEC = Dict{Symbol,Vector{TableMode}}()

"""
    table_mode!(head, specs)

Declare mode-directed tabling for `head`, one spec per argument. `specs` are parsed by `update_goal`,
so `[Sym(:index), Sym(:min)]` and `[Sym(:_), Expression([Sym(:lattice), Sym(:sum)])]` are both valid.
"""
function table_mode!(head::Symbol, specs::Vector{<:Atom})
    _MODE_SPEC[head] = TableMode[update_goal(s) for s in specs]
end

"Modes declared for `head`, or an empty vector — an undeclared head must behave as before."
table_modes(head::Symbol)::Vector{TableMode} = get(_MODE_SPEC, head, TableMode[])
"Is `head` mode-directed? False for an all-`index` declaration, which must be a no-op."
is_mode_directed(head::Symbol)::Bool = has_aggregation(table_modes(head))
untable_modes!(head::Symbol) = (delete!(_MODE_SPEC, head); nothing)
untable_all_modes!() = (empty!(_MODE_SPEC); nothing)
