# tabling/Restraints.jl — RESTRAINTS / tripwires. SWI manual §7.11.
#
# Mirrors `boot/tabling.pl`'s TRIPWIRES section (`:2263-2288`) and the enforcement point in
# `src/pl-tabling.c:3633-3665` (`tripwire_answers_for_subgoal` + the action dispatch).
#
# ─── SCOPE: ALL THREE OF §7.11, AND WHAT EACH ONE OWNS HERE ──────────────────────────────────────
# §7.11 has three restraints. This file owns the COUNT restraint outright and the ACTION FLAGS of
# the other two; the abstraction MECHANISM of both lives in `tabling/Abstract.jl`, because it needs
# `size_abstract` and the answer trie, which are included after this file.
#
#   7.11.3 max_answers      — a COUNT ⇒ `_MAX_ANSWERS` + `tripwire_answers_for_subgoal`.  ← whole
#   7.11.1 subgoal_abstract — flag `_MAX_SUBGOAL_SIZE_ACTION` + `fire_subgoal_size_tripwire`. ← gate
#   7.11.2 answer_abstract  — flag `_MAX_TABLE_ANSWER_SIZE(_ACTION)` + `fire_answer_size_tripwire`.
#
# 🔴 THE HEADER HERE SAID "§7.11.3 ONLY, AND THAT IS DELIBERATE" UNTIL 2026-08-18, on the stated
# ground that the two abstraction restraints "operate on trie terms; our answers live in a
# `Dict`/`Vector`, so they need §1.0's answer trie". BOTH HALVES OF THAT AGED INTO FALSEHOOD and
# neither was re-checked: §1.0's answer trie shipped, and §7.11.1 turned out never to have needed it
# (it rides on subsumptive tabling — see `tabling/Abstract.jl`'s header). A scope claim written as a
# design decision reads as settled long after the thing it describes has moved.
# `[[feedback_capability_claims_expire_retest_the_premise]]`
#
# ⚠️ `restraint!` STILL THROWS on `subgoal_abstract`/`answer_abstract`, and that is now a ROUTING
# fact rather than a capability one: both options are honoured, but they reach their registries
# through `subgoal_abstract!`/`answer_abstract!` (`tabling/Abstract.jl`) from `table_as!`, never
# through this function. Its message is stale prose about a capability gap that no longer exists;
# it is left alone here only because `test/standard/tabling/test_tripwires.jl:123-124` pins the
# throw, and rewriting a test from inside a source file is how a green suite stops meaning anything.
#
# ─── PORTED SEMANTICS, INCLUDING AN ASYMMETRY THAT LOOKS LIKE A TYPO AND IS NOT ──────────────────
# `tripwire_answers_for_subgoal` (`pl-tabling.c`) has TWO paths with DIFFERENT comparisons:
#
#     per-predicate  ps->max_answers        : value_count >= limit  → bounded_rationality
#     global flag    max_answers_for_subgoal: value_count == limit  → the configured action
#
# `>=` fires on the threshold answer AND every one after it; `==` fires EXACTLY ONCE, as the table
# crosses the bound. Collapsing them to one comparison changes how often the action runs — a warning
# printed once versus per answer. Both are kept.
#
# `restraint/4` (`boot/tabling.pl:1337-1342`): a NEGATIVE value means NO RESTRAINT — the option is
# dropped rather than stored. `NO_RESTRAINT` is our `(size_t)-1`.
#
# ─── UPSTREAM TRACE ──────────────────────────────────────────────────────────────────────────────
# File named for upstream's own section header (`boot/tabling.pl:2263` TRIPWIRES). Ours ← theirs:
#
#   restraint!                        ←  restraint/4                  boot/tabling.pl:1337
#                                        table_options/3 (:1325-1333) dispatches into it
#   TripwireAction / TW_*             ←  tripwire_action/2            boot/tabling.pl:2282-2288
#                                        + ATOM_bounded_rationality   pl-tabling.c:3608,3636
#   tripwire_answers_for_subgoal      ←  tripwire_answers_for_subgoal src/pl-tabling.c
#   tbl_wkl_add_answer                ←  '$tbl_wkl_add_answer'/4      src/pl-tabling.c:3577
#                                        (the enforcement site is :3633-3668 inside it)
#   generalise_answer_substitution    ←  generalise_answer_substitution   src/pl-tabling.c:3642
#   add_answer_count_restraint!       ←  add_answer_count_restraint   src/pl-tabling.c:3643
#   answer_count_restraint            ←  system:answer_count_restraint/0  boot/tabling.pl:2297
#   NO_RESTRAINT                      ←  (size_t)-1                   src/pl-tabling.c:8649
#
# ⚠️ NO DIRECT UPSTREAM ANALOGUE: `_is_general_variant`. Upstream needs no variant dedup because the
# answer trie makes the general answer a single node by construction; our Vector needs it explicitly
# (fresh variables make two general answers structurally unequal — measured 4 vs the oracle's 3).

# ─── WHY THIS FEATURE MATTERS MORE THAN ITS SIZE SUGGESTS ────────────────────────────────────────
# CROSS-CHECKED AGAINST UPSTREAM 2026-08-16. A tabled predicate whose answer set is INFINITE does not
# terminate — verified on live swipl:
#
#     :- table q/1.   q(1).   q(s(X)) :- q(X).        ⇒ killed at 30s, no answer
#
# Ours behaves identically, which is CONFORMANT rather than defective — there is no cap because
# upstream has none by default. `max_answers` IS the feature that makes such a program terminable,
# and it is the reason to prioritise the completion loop consulting this file over adding more §7
# leaves: until it does, an unbounded tabled predicate is unbounded, exactly as in SWI.
# (`test/standard/tabling/test_dependency_firing.jl` is exempted from the suite for precisely this
# reason — its program is unbounded, not broken.)

"Upstream's `(size_t)-1` / `restraint/4`'s negative value: this restraint is not in force."
const NO_RESTRAINT = -1

"""
`tripwire_action/2` (`boot/tabling.pl:2283-2288`) plus the enforcement-site actions.

  ERROR                — throw `resource_error(tripwire(...))`
  WARNING              — warn, then `goto add_anyway`: THE ANSWER IS STILL ADDED (pl-tabling.c:3660)
  SUSPEND              — warn and break to a debugger upstream; we warn and behave as ERROR, since
                         there is no interactive break to enter from a completing table
  FAIL                 — drop the answer silently (`trie_delete` + return false)
  BOUNDED_RATIONALITY  — drop it, generalise, and mark the table an APPROXIMATION (see below)
  ABSTRACT             — ONLY valid for `max_table_subgoal_size_action`, and it is the value that
                         PERMITS abstraction at all (`pl-tabling.c:2511-2514`). The flag validator
                         accepts it for that key alone (`:8873-8874`).
"""
@enum TripwireAction TW_ERROR TW_WARNING TW_SUSPEND TW_FAIL TW_BOUNDED_RATIONALITY TW_ABSTRACT

"Default action for the global bound. Upstream's flag default is `error`."
const DEFAULT_TRIPWIRE_ACTION = TW_ERROR

const _MAX_ANSWERS = Dict{Symbol, Int}()          # per-head bound (the `max_answers(N)` option)
const _MAX_ANSWERS_GLOBAL = Ref{Int}(NO_RESTRAINT)      # the global flag
const _MAX_ANSWERS_ACTION = Ref{TripwireAction}(DEFAULT_TRIPWIRE_ACTION)

# ── §7.11.1's own action flag: `max_table_subgoal_size_action` ───────────────────────────────────
"""Upstream's `max_table_subgoal_size_action`. **DEFAULT `TW_ERROR`, exactly as SWI.**

🔴 `subgoal_abstract(N)` DOES NOT MEAN "ABSTRACT" IN SWI — it means "bound the subgoal size", and the
default disposition of that bound is to REFUSE THE PROGRAM. Verified on live swipl 10.1.12:

    :- table p/1 as subgoal_abstract(1).   p(_).
    ?- p(s(s(s(a)))).
    ERROR: resource_error(tripwire(max_table_subgoal_size, user:p(_)))
    ?- current_prolog_flag(max_table_subgoal_size_action, A).   A = error.

Only after `set_prolog_flag(max_table_subgoal_size_action, abstract)` does the goal abstract to
`p(s(_))`. Our port abstracted UNCONDITIONALLY until 2026-08-18, which meant `subgoal_abstract` here
silently did something SWI refuses to do — the worst kind of divergence, because the program runs.

⚠️ THE DEFAULT IS DELIBERATELY THE STRICT ONE, and it is why every §7.11.1 test now sets this flag
explicitly — precisely as the swipl oracle script had to. A conformance port whose default differs
from the reference cannot be differentialled without remembering to compensate, and that is exactly
the kind of thing nobody remembers. `[[feedback_parity_vs_opt_in]]`"""
const _MAX_SUBGOAL_SIZE_ACTION = Ref{TripwireAction}(TW_ERROR)

"Set `max_table_subgoal_size_action`. `TW_ABSTRACT` is the only value that permits abstraction."
set_max_table_subgoal_size_action!(a::TripwireAction) =
    (_MAX_SUBGOAL_SIZE_ACTION[]=a; nothing)
max_table_subgoal_size_action() = _MAX_SUBGOAL_SIZE_ACTION[]

"""
    fire_subgoal_size_tripwire(head) -> Bool

`pl-tabling.c:2506-2523`. Returns TRUE when the caller must RETRY UNABSTRACTED (upstream's
`sa.size = (size_t)-1; goto retry`), and throws for `TW_ERROR`.

The retry is the part that is easy to miss: upstream does not merely refuse the abstraction, it
re-runs the variant lookup with the restraint disabled, so a WARNING disposition still tables the
FULL goal rather than the abstracted one.
"""
function fire_subgoal_size_tripwire(head::Union{Symbol, Nothing})::Bool
    act = _MAX_SUBGOAL_SIZE_ACTION[]
    act == TW_ABSTRACT && return false
    hd = head === nothing ? "?" : String(head)
    if act == TW_ERROR || act == TW_SUSPEND
        throw(
            ArgumentError(
                "resource_error(tripwire(max_table_subgoal_size, $(hd))) — the goal " *
                "exceeds its `subgoal_abstract` bound. SWI's default action for this " *
                "restraint is `error`, NOT `abstract`; call " *
                "`set_max_table_subgoal_size_action!(TW_ABSTRACT)` to abstract instead."
            )
        )
    end
    act == TW_WARNING &&
        @warn "tripwire max_table_subgoal_size for $(hd) — tabling the FULL goal"
    true                                   # retry with the restraint disabled
end

# ── §7.11.2's own flags: `max_table_answer_size` + `max_table_answer_size_action` ────────────────
"""Upstream's `max_table_answer_size` — the GLOBAL answer-size bound (`pl-tabling.c:3570`).

Consulted only when the predicate has no `answer_abstract(N)` of its own: `pred_max_table_answer_size`
(`pl-tabling.c:3563-3572`) reads `def->tabling->answer_abstract` and falls back to this flag when it
is `(size_t)-1`.

⚠️ THAT FALLBACK IS THE OPPOSITE SHAPE FROM §7.11.3's, and the two sit forty lines apart upstream.
`tripwire_answers_for_subgoal` SHORT-CIRCUITS: a per-predicate `max_answers` suppresses the global
flag entirely (see `tripwire_answers_for_subgoal` above). `pred_max_table_answer_size` DELEGATES:
the global flag applies to every predicate that did not override it. Collapsing them to one
convention would silently change which predicates a global bound reaches."""
const _MAX_TABLE_ANSWER_SIZE = Ref{Int}(NO_RESTRAINT)

"""Upstream's `max_table_answer_size_action`. **DEFAULT `TW_ERROR`** (`pl-tabling.c:9341`).

🔴 AND ITS ADMISSIBLE SET IS NOT THE SUBGOAL SIDE'S. `set_restraint_action` (`pl-tabling.c:8866-8882`)
accepts `error`/`warning`/`suspend` for every restraint, then adds PER-KEY extras:

    max_table_subgoal_size_action    + abstract                        (:8873-8874)
    max_table_answer_size_action     + bounded_rationality, fail       (:8875-8877)
    max_answers_for_subgoal_action   + bounded_rationality             (:8878-8879)

So `abstract` is a DOMAIN ERROR here — verified on live swipl 10.1.12:

    ?- set_prolog_flag(max_table_answer_size_action, abstract).
    ERROR: domain_error(restraint_action, abstract)

which is not a quirk but the semantics: on the subgoal side `abstract` is the *permission* to
generalise the CALL, and generalising a call is sound (a more general table answers it). Generalising
an ANSWER is not — it claims more than was derived — so the answer side has no bare `abstract`, only
`bounded_rationality`, which generalises AND records the debt on the delay list."""
const _MAX_TABLE_ANSWER_SIZE_ACTION = Ref{TripwireAction}(TW_ERROR)

"The actions `max_table_answer_size_action` accepts — `pl-tabling.c:8871-8877`. NOTE: no `abstract`."
const ANSWER_SIZE_ACTIONS = (
    TW_ERROR, TW_WARNING, TW_SUSPEND, TW_BOUNDED_RATIONALITY, TW_FAIL
)

"""Set `max_table_answer_size_action`, VALIDATING against upstream's per-key domain.

Throws on `TW_ABSTRACT` exactly as `set_restraint_action` raises `domain_error(restraint_action,
abstract)` — the value is legal for the SUBGOAL flag and illegal for this one."""
function set_max_table_answer_size_action!(a::TripwireAction)
    a in ANSWER_SIZE_ACTIONS || throw(
        ArgumentError(
            "domain_error(restraint_action, $(a)) — `max_table_answer_size_action` accepts " *
            "$(ANSWER_SIZE_ACTIONS) (pl-tabling.c:8871-8877). `TW_ABSTRACT` is legal ONLY for " *
            "`max_table_subgoal_size_action`: generalising a CALL is sound, generalising an ANSWER is " *
            "not, so the answer side offers `TW_BOUNDED_RATIONALITY` (generalise AND delay) instead."
        )
    )
    _MAX_TABLE_ANSWER_SIZE_ACTION[] = a
    nothing
end
max_table_answer_size_action() = _MAX_TABLE_ANSWER_SIZE_ACTION[]

"Set the global `max_table_answer_size`. Negative is `restraint/4`'s removal ⇒ `NO_RESTRAINT`."
set_max_table_answer_size!(n::Int) =
    (_MAX_TABLE_ANSWER_SIZE[]=n < 0 ? NO_RESTRAINT : n; nothing)
max_table_answer_size()::Int = _MAX_TABLE_ANSWER_SIZE[]

"""
    fire_answer_size_tripwire(head) -> Symbol

`pl-tabling.c:3601-3617` — the disposition of an answer that BLEW its `answer_abstract(N)` budget.
Returns one of `:conditional`, `:store`, `:drop`, and THROWS for `TW_ERROR`.

The C, whose three-way shape is easy to flatten into two by accident:

    if      ( action == bounded_rationality )         { add_radial_restraint(); }   /* fall through */
    else if ( action == fail ||
              !tbl_wl_tripwire(wl, action, ATOM_max_table_answer_size) )
            { trie_delete(wl->table, node, true); return false; }
    /* else fall through */

`bounded_rationality` and `warning` BOTH store the generalised answer; they differ ONLY in whether it
is conditional. `fail` alone drops it.

🔴 NOTE THE DIVERGENCE FROM ITS SIBLING: `fire_subgoal_size_tripwire`'s `TW_WARNING` RETRIES
UNABSTRACTED (`sa.size = -1; goto retry`, `pl-tabling.c:2519`), so the FULL goal gets tabled. There
is no retry here — the abstracted node is already in the answer trie by the time the action is read —
so `TW_WARNING` stores the ABSTRACTED answer, unconditionally. MEASURED on live swipl 10.1.12 with
`p(X) :- q(X). q(s(s(s(a)))). q(s(a)).` under `:- table p/1 as answer_abstract(1)`:

    action                 stored answers (get_returns_and_tvs/3)
    error    (DEFAULT)     RAISED resource_error(tripwire(max_table_answer_size, <trie>))
    warning                ret(s(s(_))) tv=t   ret(s(a)) tv=t      ← generalised, UNCONDITIONAL
    fail                                       ret(s(a)) tv=t      ← the big answer is GONE
    bounded_rationality    ret(s(s(_))) tv=u   ret(s(a)) tv=t      ← generalised, CONDITIONAL
    abstract               domain_error(restraint_action, abstract)

`warning` vs `bounded_rationality` differing only in the truth value is what the anti-vacuity test in
`test_abstract.jl` keys on: an implementation that stored the generalised answer and forgot the delay
would pass every answer-set comparison and fail exactly there.
"""
function fire_answer_size_tripwire(head::Union{Symbol, Nothing})::Symbol
    act = _MAX_TABLE_ANSWER_SIZE_ACTION[]
    hd = head === nothing ? "?" : String(head)
    act == TW_BOUNDED_RATIONALITY && return :conditional     # add_radial_restraint(), then store
    act == TW_FAIL && return :drop                           # trie_delete + return false
    if act == TW_ERROR
        throw(
            ArgumentError(
                "resource_error(tripwire(max_table_answer_size, $(hd))) — the answer " *
                "exceeds its `answer_abstract` bound. SWI's default action for this " *
                "restraint is `error`; call " *
                "`set_max_table_answer_size_action!(TW_BOUNDED_RATIONALITY)` to store " *
                "a generalised CONDITIONAL answer, or `TW_FAIL` to drop it."
            )
        )
    end
    act == TW_SUSPEND &&
        @warn "tripwire max_table_answer_size for $(hd) — SWI would break to a debugger here"
    act == TW_WARNING &&
        @warn "tripwire max_table_answer_size for $(hd) — storing the GENERALISED answer " *
            "unconditionally (SWI `warning` action: no retry on this side)"
    :store                                   # warning/suspend: `tripwire/3` succeeds ⇒ add anyway
end

"""
    restraint!(head, name, value)

`table_options/3` (`boot/tabling.pl:1325-1333`) for the restraint options.

Follows `restraint/4`: a NEGATIVE value REMOVES the restraint rather than storing it. Throws on
`subgoal_abstract`/`answer_abstract` — they need the answer trie (§1.0) and a silent no-op would be
indistinguishable from them working.
"""
function restraint!(head::Symbol, name::Symbol, value::Int)
    if name === :max_answers
        value < 0 ? delete!(_MAX_ANSWERS, head) : (_MAX_ANSWERS[head] = value)
        return nothing
    elseif name === :subgoal_abstract || name === :answer_abstract
        throw(
            ArgumentError(
                "$(name) is SWI §7.11.$(name === :subgoal_abstract ? 1 : 2) and operates on TRIE TERMS; " *
                "our answers are a Dict/Vector, so it needs §1.0's answer trie. Refused rather than " *
                "silently accepted — a restraint that appears to apply and does not is worse than none."
            )
        )
    end
    throw(
        ArgumentError("domain_error(table_option, $(name)) — known restraint: max_answers")
    )
end

"Global `max_answers_for_subgoal` flag + its action (`pl-tabling.c:8917-8923`)."
function set_global_max_answers!(value::Int, action::TripwireAction=DEFAULT_TRIPWIRE_ACTION)
    _MAX_ANSWERS_GLOBAL[] = value < 0 ? NO_RESTRAINT : value
    _MAX_ANSWERS_ACTION[] = action
    nothing
end

max_answers(head::Symbol)::Int = get(_MAX_ANSWERS, head, NO_RESTRAINT)
clear_restraints!(head::Symbol) = (delete!(_MAX_ANSWERS, head); nothing)
clear_all_restraints!() = (empty!(_MAX_ANSWERS); _MAX_ANSWERS_GLOBAL[]=NO_RESTRAINT;
    _MAX_ANSWERS_ACTION[]=DEFAULT_TRIPWIRE_ACTION; nothing)

"""
    tripwire_answers_for_subgoal(head, count) -> Union{TripwireAction,Nothing}

`tripwire_answers_for_subgoal` (`pl-tabling.c`), 1:1 including the two comparisons.

`count` is the table's answer count BEFORE adding the candidate — upstream's `wl->table->value_count`
at the same point. Returns `nothing` when no restraint fires.
"""
function tripwire_answers_for_subgoal(
    head::Symbol, count::Int
)::Union{TripwireAction, Nothing}
    lim = max_answers(head)
    if lim != NO_RESTRAINT
        count >= lim && return TW_BOUNDED_RATIONALITY     # per-predicate path: `>=`
        return nothing                                     # …and it SHORT-CIRCUITS the global path
    end
    g = _MAX_ANSWERS_GLOBAL[]
    if g != NO_RESTRAINT
        count == g && return _MAX_ANSWERS_ACTION[]         # global path: `==`, fires exactly once
    end
    nothing
end

"""
    tbl_wkl_add_answer(head, answers, candidate) -> (answers, added, action)

The enforcement site (`pl-tabling.c:3633-3668`) over our `Vector{Atom}` answer set.

  * no tripwire            → the candidate is added, `action === nothing`
  * `TW_WARNING`          → warn and ADD ANYWAY (upstream's `goto add_anyway`, :3660)
  * `TW_FAIL`             → drop silently
  * `TW_ERROR`/`SUSPEND`  → throw a resource error naming head and bound
  * `TW_BOUNDED_RATIONALITY` → drop, and the caller must mark the table an APPROXIMATION

🔴 BOUNDED_RATIONALITY DOES NOT DROP THE EXCESS — IT GENERALISES IT. Measured against live swipl,
because an earlier version of this file DID drop and documented the difference away as "needs the
answer trie":

    :- table p/1 as max_answers(2).   q(1). q(2). q(3). q(4).   p(X) :- q(X).
    findall(X, p(X), Xs)  ⇒  Xs = [2, 1, _5800],  length 3

The third element is a FREE VARIABLE — upstream's `generalise_answer_substitution` (:3641-3654)
replaces the truncated remainder with the most general term, which SUBSUMES every answer it stopped
computing, then marks the table with `answer_count_restraint`. That is what "bounded rationality"
means: the bound converts an exact answer set into a sound OVER-approximation. Dropping instead
yields a silently INCOMPLETE table — the opposite direction, and unsound for any consumer that reads
absence as failure. Generalisation needs no trie; only the *conditional/undefined* marking does, and
that is what `answer_count_restraint` records for the caller.
"""
function tbl_wkl_add_answer(head::Symbol, answers::Vector{Atom},
    candidate::Atom)::Tuple{Vector{Atom}, Bool, Union{TripwireAction, Nothing, Symbol}}
    # `Symbol` in the return union carries `:duplicate` — upstream simply `return false`s there,
    # but naming it keeps a duplicate distinguishable from a `fail` action, which also adds nothing.
    # 🔴 A DUPLICATE MUST NOT TRIP THE RESTRAINT — fixed 2026-08-17 from the C, which orders it
    # differently from this function's original form. `$tbl_wkl_add_answer` creates the trie node
    # FIRST and reaches the tripwire only in the `else` branch (`pl-tabling.c:3618` vs `:3633`):
    #     if ( node->value )        -> DUPLICATE, return false          <- no restraint event
    #     else if ( (action = tripwire_answers_for_subgoal(wl)) ) ...
    # Consulting the bound before knowing whether the candidate is a duplicate fires the restraint on
    # every re-insertion at the bound and marks a table APPROXIMATE that never grew. MEASURED: at
    # bound 2 with answers {1,2}, re-inserting `1` returned BOUNDED_RATIONALITY and set the
    # approximate flag; the trie-seated `trie_insert_restrained!` returns `:duplicate` and does not.
    any(x -> x == candidate, answers) && return (answers, false, :duplicate)
    act = tripwire_answers_for_subgoal(head, length(answers))
    act === nothing && return (push!(copy(answers), candidate), true, nothing)
    if act == TW_WARNING
        @warn "tabling: max_answers exceeded for $(head) — answer added anyway (SWI `warning` action)" bound=max_answers(
            head
        )
        return (push!(copy(answers), candidate), true, act)      # add_anyway (pl-tabling.c:3660)
    elseif act == TW_FAIL
        return (answers, false, act)
    elseif act == TW_ERROR || act == TW_SUSPEND
        act == TW_SUSPEND &&
            @warn "tabling: max_answers exceeded for $(head) — SWI would break to a debugger here"
        throw(
            ErrorException(
                "resource_error(tripwire(max_answers_for_subgoal, $(head))) — " *
                "bound $(max_answers(head) == NO_RESTRAINT ? _MAX_ANSWERS_GLOBAL[] : max_answers(head))"
            )
        )
    end
    # BOUNDED_RATIONALITY (pl-tabling.c:3636-3657): drop the candidate, then add ONE maximally
    # general answer that subsumes everything the bound stopped computing, and mark the table an
    # approximation. Added once — a second generalisation would be a duplicate of the same term.
    add_answer_count_restraint!(head)
    # ⚠️ Dedup by VARIANT, not by `==`. Each generalisation mints fresh variables, so `(p $_g1)` and
    # `(p $_g2)` are structurally UNEQUAL and a `==` check adds one general answer per excess answer
    # — measured 4 against the oracle's 3. Upstream adds it exactly once.
    any(x -> _is_general_variant(x, candidate), answers) && return (answers, false, act)
    (push!(copy(answers), generalise_answer_substitution(candidate)), true, act)
end

"""
    generalise_answer_substitution(a) -> Atom

`generalise_answer_substitution` (`pl-tabling.c:3642`): the most general term of `a`'s shape — every
ARGUMENT position replaced by a fresh variable, the functor kept. `(p 3)` ⇒ `(p \$_g1)`.

Subsumption, not erasure: the result matches every answer the restraint prevented us computing, so
the table over-approximates instead of silently losing rows.
"""
function generalise_answer_substitution(a::Atom)::Atom
    a isa Expression || return Var("_g", UInt64(_gen_counter[] += 1))
    ch = (a::Expression).children
    isempty(ch) && return a
    Expression(
        Atom[i == 1 ? ch[1] : Var("_g", UInt64(_gen_counter[] += 1)) for i in eachindex(ch)]
    )
end
const _gen_counter = Ref{UInt64}(0)

"""Is `x` already the maximally general answer for `shape`'s functor and arity?

Variant test, not equality: generalisation mints fresh variables every call, so two general answers
for the same shape are structurally unequal while denoting the same thing."""
function _is_general_variant(x::Atom, shape::Atom)::Bool
    (x isa Expression && shape isa Expression) || return false
    xc, sc = (x::Expression).children, (shape::Expression).children
    length(xc) == length(sc) || return false
    length(xc) >= 1 && xc[1] == sc[1] || return false
    all(i -> xc[i] isa Var, 2:length(xc))
end

const _APPROXIMATE = Set{Symbol}()
"Record that `head`'s table was truncated by a restraint — upstream's `answer_count_restraint`."
add_answer_count_restraint!(head::Symbol) = (push!(_APPROXIMATE, head); nothing)
"Was this table truncated? An approximate table must not be reported as a complete answer set."
answer_count_restraint(head::Symbol)::Bool = head in _APPROXIMATE
clear_answer_count_restraints!() = (empty!(_APPROXIMATE); nothing)
