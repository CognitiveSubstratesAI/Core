# tabling/Restraints.jl — RESTRAINTS / tripwires. SWI manual §7.11.
#
# Mirrors `boot/tabling.pl`'s TRIPWIRES section (`:2263-2288`) and the enforcement point in
# `src/pl-tabling.c:3633-3665` (`tripwire_answers_for_subgoal` + the action dispatch).
#
# ─── SCOPE: §7.11.3 ONLY, AND THAT IS DELIBERATE ─────────────────────────────────────────────────
# §7.11 has three restraints. Only ONE of them ports to our current table representation:
#
#   7.11.3 max_answers      — a COUNT. Ports to a `Dict` today. ← this file
#   7.11.1 subgoal_abstract — abstraction over TRIE TERMS (depth-bounded generalisation)
#   7.11.2 answer_abstract  — likewise
#
# The two abstraction restraints operate on trie terms; our answers live in a `Dict`/`Vector`, so
# they need §1.0's answer trie and are NOT stubbed here. An empty stub that silently accepts the
# declaration would be worse than its absence: `subgoal_abstract(3)` appearing to work while doing
# nothing is the failure mode. `restraint!` therefore THROWS on them, naming why.
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
"""
@enum TripwireAction TW_ERROR TW_WARNING TW_SUSPEND TW_FAIL TW_BOUNDED_RATIONALITY

"Default action for the global bound. Upstream's flag default is `error`."
const DEFAULT_TRIPWIRE_ACTION = TW_ERROR

const _MAX_ANSWERS        = Dict{Symbol,Int}()          # per-head bound (the `max_answers(N)` option)
const _MAX_ANSWERS_GLOBAL = Ref{Int}(NO_RESTRAINT)      # the global flag
const _MAX_ANSWERS_ACTION = Ref{TripwireAction}(DEFAULT_TRIPWIRE_ACTION)

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
        throw(ArgumentError(
            "$(name) is SWI §7.11.$(name === :subgoal_abstract ? 1 : 2) and operates on TRIE TERMS; " *
            "our answers are a Dict/Vector, so it needs §1.0's answer trie. Refused rather than " *
            "silently accepted — a restraint that appears to apply and does not is worse than none."))
    end
    throw(ArgumentError("domain_error(table_option, $(name)) — known restraint: max_answers"))
end

"Global `max_answers_for_subgoal` flag + its action (`pl-tabling.c:8917-8923`)."
function set_global_max_answers!(value::Int, action::TripwireAction = DEFAULT_TRIPWIRE_ACTION)
    _MAX_ANSWERS_GLOBAL[] = value < 0 ? NO_RESTRAINT : value
    _MAX_ANSWERS_ACTION[] = action
    nothing
end

max_answers(head::Symbol)::Int = get(_MAX_ANSWERS, head, NO_RESTRAINT)
clear_restraints!(head::Symbol) = (delete!(_MAX_ANSWERS, head); nothing)
clear_all_restraints!() = (empty!(_MAX_ANSWERS); _MAX_ANSWERS_GLOBAL[] = NO_RESTRAINT;
                           _MAX_ANSWERS_ACTION[] = DEFAULT_TRIPWIRE_ACTION; nothing)

"""
    tripwire_answers_for_subgoal(head, count) -> Union{TripwireAction,Nothing}

`tripwire_answers_for_subgoal` (`pl-tabling.c`), 1:1 including the two comparisons.

`count` is the table's answer count BEFORE adding the candidate — upstream's `wl->table->value_count`
at the same point. Returns `nothing` when no restraint fires.
"""
function tripwire_answers_for_subgoal(head::Symbol, count::Int)::Union{TripwireAction,Nothing}
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
                                candidate::Atom)::Tuple{Vector{Atom},Bool,Union{TripwireAction,Nothing}}
    act = tripwire_answers_for_subgoal(head, length(answers))
    act === nothing              && return (push!(copy(answers), candidate), true, nothing)
    if act == TW_WARNING
        @warn "tabling: max_answers exceeded for $(head) — answer added anyway (SWI `warning` action)" bound=max_answers(head)
        return (push!(copy(answers), candidate), true, act)      # add_anyway (pl-tabling.c:3660)
    elseif act == TW_FAIL
        return (answers, false, act)
    elseif act == TW_ERROR || act == TW_SUSPEND
        act == TW_SUSPEND &&
            @warn "tabling: max_answers exceeded for $(head) — SWI would break to a debugger here"
        throw(ErrorException("resource_error(tripwire(max_answers_for_subgoal, $(head))) — " *
                             "bound $(max_answers(head) == NO_RESTRAINT ? _MAX_ANSWERS_GLOBAL[] : max_answers(head))"))
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
    Expression(Atom[i == 1 ? ch[1] : Var("_g", UInt64(_gen_counter[] += 1)) for i in eachindex(ch)])
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
