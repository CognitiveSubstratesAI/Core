# tabling/Delays.jl — DELAY LISTS / CONDITIONAL ANSWERS. SWI §7.6, roadmap 7.A–7.D.
#
# Mirrors `delay`, `delay_set` and `delay_info` (`src/pl-tabling.h:168-184`) and the operations on
# them in `pl-tabling.c` (`update_delay_list` :1100, `simplify_answer` :1560,
# `remove_conditional_answer` :1592).
#
# ─── WHAT A DELAY IS ─────────────────────────────────────────────────────────────────────────────
# Under the well-founded semantics an answer can be TRUE, FALSE, or UNDEFINED. SWI records the third
# case CONSTRUCTIVELY: an answer is stored together with the literals whose truth is still unknown —
# its DELAY LIST — so "undefined" carries a reason rather than being a flag. Upstream's shape is
# disjunctive normal form:
#
#     delay_info { buffer delay_sets;   /* the DISJUNCTIVE conditions   */
#                  buffer delays; }     /* store for the delays         */
#     delay_set  { offset, size, active }   /* one CONJUNCTION           */
#     delay      { trie *variant; trie_node *answer; }   /* answer==NULL ⇒ NEGATIVE */
#
# An answer holds if ANY conjunction holds — several derivations, each with its own condition.
#
# ─── 🔴 7.A: WHY OURS RIDES ON THE VALUE AND UPSTREAM'S DOES NOT ─────────────────────────────────
# `LD->tabling.delay_list` is a **trail-scoped THREAD-GLOBAL** (`pl-setup.c:1552`), pushed
# destructively and UNWOUND BY BACKTRACKING; `update_delay_list` decides conditionality by SCRAPING
# that global at the moment of insertion (`:1123-1128`). The invariant that makes it correct is:
# **between generating an answer and inserting it, the engine is executing EXACTLY ONE derivation,
# and any abandoned attempt is erased by the trail.**
#
# THAT INVARIANT IS FALSE HERE. A call yields a COLLECTION of values which we then map over; at the
# moment the k-th result is inserted there is no "current branch", and delayed literals from
# different result values are simultaneously live in the same dynamic extent. Port the register
# literally and value #1's `tnot(p)` condition LEAKS ONTO value #2, with no trail to unwind it.
# (Even SWI hand-rolls save/reset/restore where the linear-branch assumption breaks — `'\$wfs_call'/2`,
# `boot/tabling.pl:938-948`, because `call/1` is a re-entrancy point.)
#
# ⇒ THE CONDITION RIDES WITH THE VALUE. Our WFS bottom is not a flag but a RESIDUATED VALUE:
# `WFSBottom` carries the DNF, so combination is an EXPLICIT conjunction at each join (see
# `propagated_undefined`) instead of a push onto ambient state. That is the adaptation, and it is
# forced by the language, not a preference.
#
# ─── 7.B: THE THIRD KIND, WHICH UPSTREAM'S STRUCT CANNOT EXPRESS ─────────────────────────────────
# Upstream has exactly two kinds, encoded by whether `answer` is NULL: POSITIVE ("that table contains
# this answer") and NEGATIVE ("that table is empty" — table-level, decided by
# `wl->table->value_count == 0`, `:1779`). In a VALUE language the natural negations are both
# `(not (f a))` AND `(not (== (f a) 3))` — and **upstream's struct has nowhere to put the 3**. Hence
# `DELAY_NEGATIVE_ANSWER`.
#
# ⚠️ NO SITE PRODUCES IT YET, and saying so is the point: our `tnot` is table-level (it requires a
# GROUND goal and asks whether the table is empty), so only the first two kinds are reachable today.
# The kind exists because 7.B settles a STRUCT FIELD and the struct is being written now — adding it
# later would mean rewriting every consumer. It is asserted absent in the tests rather than left to
# look implemented.

"Which kind of literal was delayed. Upstream encodes the first two in `answer == NULL`; see 7.B."
@enum DelayKind begin
    DELAY_POSITIVE          # `variant`'s table CONTAINS `answer`      (upstream: answer != NULL)
    DELAY_NEGATIVE          # `variant`'s table is EMPTY               (upstream: answer == NULL)
    DELAY_NEGATIVE_ANSWER   # `variant`'s table does NOT contain `answer`  — 7.B, ours only
end

"""One delayed literal — upstream's `delay { trie *variant; trie_node *answer; }`.

`variant` is the callee's table key. `answer` is `nothing` exactly for `DELAY_NEGATIVE`, which is
table-level; the other two kinds name an answer."""
struct Delay
    variant::Atom
    answer::Union{Atom,Nothing}
    kind::DelayKind
end

delay_positive(v::Atom, a::Atom)        = Delay(v, a,       DELAY_POSITIVE)
delay_negative(v::Atom)                 = Delay(v, nothing, DELAY_NEGATIVE)
delay_negative_answer(v::Atom, a::Atom) = Delay(v, a,       DELAY_NEGATIVE_ANSWER)

"A CONJUNCTION of delayed literals — upstream's `delay_set`."
const DelaySet = Vector{Delay}

"""A DISJUNCTION of conjunctions — upstream's `delay_info.delay_sets`. Empty means UNCONDITIONAL.

⚠️ EMPTY AND "NO REASON RECORDED" ARE THE SAME VALUE HERE, and that is deliberate: an unconditional
answer has no condition, and a bottom whose reason we never recorded must not be treated as one with
an unsatisfiable condition. Consumers read empty as "no information", never as "false"."""
const DelayDNF = Vector{DelaySet}

Base.show(io::IO, d::Delay) =
    print(io, d.kind == DELAY_POSITIVE        ? string(d.variant) :
              d.kind == DELAY_NEGATIVE        ? "(not $(d.variant))" :
                                                "(not (== $(d.variant) $(d.answer)))")

"Two delayed literals are the same literal — used to keep conjunctions and disjunctions dup-free."
delay_eq(a::Delay, b::Delay)::Bool =
    a.kind == b.kind && variant_eq(a.variant, b.variant) &&
    ((a.answer === nothing) == (b.answer === nothing)) &&
    (a.answer === nothing || variant_eq(a.answer::Atom, b.answer::Atom))

"""Are two conditions the same CONDITION? Set equality on the disjunction, set equality within each
conjunction — because a DNF is a set of sets and neither level has a meaningful order.

🔴 THIS IS WHAT `WFSBottom`'s `==` IS BUILT ON, and without it two bottoms carrying the SAME reason
were different answers: Julia's default `==` for a struct holding a `Vector` compares the vector by
IDENTITY, so `dnf_or` returning a fresh vector produced an answer that never compared equal to the
one already stored. Measured: `Set([b1, b2])` held 2 elements and `issetequal([b1],[b2])` was false —
the latter being the alternating fixpoint's own convergence test."""
dnf_equiv(a::DelayDNF, b::DelayDNF)::Bool =
    length(a) == length(b) && all(x -> any(y -> set_eq(x, y), b), a)

"Conjoin one literal into a conjunction, dropping an exact repeat (`A ∧ A = A`)."
function delayset_add(s::DelaySet, d::Delay)::DelaySet
    any(x -> delay_eq(x, d), s) && return s
    DelaySet(vcat(s, [d]))
end

set_eq(a::DelaySet, b::DelaySet)::Bool =
    length(a) == length(b) && all(x -> any(y -> delay_eq(x, y), b), a)

"Disjoin, dropping a repeated conjunction (`C ∨ C = C`)."
function dnf_or(a::DelayDNF, b::DelayDNF)::DelayDNF
    out = DelayDNF(copy(a))
    for s in b
        any(x -> set_eq(x, s), out) || push!(out, s)
    end
    out
end

"""
    dnf_and(a, b) -> DelayDNF

Conjoin two conditions, DISTRIBUTING over the disjunction: `(A∨B) ∧ (C∨D) = AC ∨ AD ∨ BC ∨ BD`.

🔴 THIS IS THE OPERATION UPSTREAM DOES NOT NEED, and its absence there is the whole of 7.A. SWI
conjoins by PUSHING onto the ambient delay register, so the "other" conjunct is whatever the current
derivation already put there — a single implicit conjunction, unwound on backtracking. We have no
current derivation to push onto, so the conjunction has to be written down.

⚠️ EMPTY IS THE UNIT, NOT THE ZERO. An unconditional answer conjoined with a conditional one is the
conditional one; reading empty as "false" would make every combination unconditional-false, which is
the inverted-lattice mistake this comment exists to prevent.
"""
function dnf_and(a::DelayDNF, b::DelayDNF)::DelayDNF
    isempty(a) && return b                      # unconditional ∧ X = X
    isempty(b) && return a
    out = DelayDNF()
    for sa in a, sb in b
        merged = sa
        for d in sb; merged = delayset_add(merged, d); end
        any(x -> set_eq(x, merged), out) || push!(out, merged)
    end
    out
end

"""
    dnf_residual(dnf) -> Atom

Render a condition as a MeTTa atom — `answer_residual/2`'s payload (`library(tables)`).

`(and …)` over a conjunction, `(or …)` over the disjunction, and the unit cases collapse: an empty
DNF renders as `True` (unconditional), a single conjunct as itself. The point is that a user can SEE
why an answer is undefined, which is what conditional answers buy over a bare bottom.
"""
function dnf_residual(dnf::DelayDNF)::Atom
    isempty(dnf) && return Sym("True")
    sets = Atom[_residual_set(s) for s in dnf]
    length(sets) == 1 ? sets[1] : Expression(Atom[Sym(:or), sets...])
end

function _residual_set(s::DelaySet)::Atom
    lits = Atom[_residual_literal(d) for d in s]
    isempty(lits)        ? Sym("True") :
    length(lits) == 1    ? lits[1] :
                           Expression(Atom[Sym(:and), lits...])
end

_residual_literal(d::Delay)::Atom =
    d.kind == DELAY_POSITIVE ? d.variant :
    d.kind == DELAY_NEGATIVE ? Expression(Atom[Sym(:not), d.variant]) :
        Expression(Atom[Sym(:not), Expression(Atom[Sym(Symbol("==")), d.variant, d.answer::Atom])])

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# THE CONDITION ACCESSOR — `'$tbl_answer'/3`'s THIRD ARGUMENT.
#
# `library(tables)`'s three delay-list predicates (`get_returns_and_tvs/3`, `get_returns_and_dls/3`,
# `get_residual/2`) all consume ONE thing: the `Condition` that `'$tbl_answer'(Trie, Answer, Cond)`
# (`pl-tabling.c:5391-5399`) yields alongside each answer. That primitive is a `trie_gen` whose
# per-answer unifier is `unify_delay_info` (`:5342-5375`) — so the accessor below is the whole of
# the "missing C primitive", and it is missing NOTHING: the enumeration half is `trie_answers` and
# the condition half is `delays_of`, both already here.
#
# ⚠️ `'$tbl_answer_update_dl'` (`pl-tabling.c:5505-5535`) CANNOT BE PORTED AS A UNIT, and that is a
# structural fact rather than a to-do. Its return value is the same condition this accessor gives;
# its PURPOSE is the SIDE EFFECT at `:5520`, `tbl_push_delay(...)` onto `LD->tabling.delay_list` —
# the trail-scoped thread-global delay register. That register is EXACTLY what roadmap 7.A replaces
# by putting the condition ON the value (see the header of this file: with no "current derivation"
# at insertion time, a literal port leaks value #1's condition onto value #2). Porting the side
# effect would re-introduce the register the design removed; porting only the return value is
# `answer_condition` under a second name. So it is neither stubbed nor listed as a gap.
# ═══════════════════════════════════════════════════════════════════════════════════════════════

# 🔴 `:true` IS NOT A SYMBOL IN JULIA — IT IS THE `Bool`. `true` and `false` are LITERALS, so `:true`
# quotes the literal and evaluates to `true::Bool`; every other bare word (`:undefined`) quotes to a
# `Symbol` as expected. Writing the trichotomy as `:true | :undefined | DelayDNF` therefore compiles
# and then returns a `Bool` from the unconditional branch — caught here only because
# `answer_condition` carries a `::Union{Symbol,DelayDNF}` return annotation, which turned it into a
# `MethodError: Cannot convert Bool to Union{Symbol, Vector{Vector{Delay}}}` on the FIRST
# unconditional answer instead of a silent `=== :true` that is false forever. The named constants
# below make the mistake unspellable, and they keep upstream's atom names (`ATOM_true`,
# `ATOM_undefined`) visible at the call site.
"`ATOM_true` (`pl-tabling.c:5373`) — the condition of an UNCONDITIONAL answer. `Symbol(\"true\")`, NOT `:true`."
const COND_TRUE = Symbol("true")

"`ATOM_undefined` (`pl-tabling.c:5371`) — conditional with NO delay sets recorded (`DL_UNDEFINED`)."
const COND_UNDEFINED = Symbol("undefined")

"""
    answer_condition(a) -> Union{Symbol,DelayDNF}

The condition under which answer `a` holds — `unify_delay_info` (`pl-tabling.c:5342-5375`).

🔴 IT IS A TRICHOTOMY, NOT A BOOLEAN, and upstream spells all three out:

| upstream (`unify_delay_info`)                         | here            |
|-------------------------------------------------------|-----------------|
| no `delay_info` on the node ⇒ `ATOM_true` (`:5373`)    | `COND_TRUE`     |
| `delay_info` present but not a delay list (`DL_UNDEFINED`) ⇒ `ATOM_undefined` (`:5371`) | `COND_UNDEFINED` |
| a real delay list ⇒ the `;`/`,` term built by `put_delay_set` (`:5233-5336`) | the `DelayDNF` |

🔴🔴 BUILT ON `is_undefined`, NEVER ON `answer_residual` — THE SOUNDNESS INVERSION THIS EXISTS TO
PREVENT. `answer_residual` maps a REASON-LESS bottom to `Sym("True")` deliberately (empty DNF means
"no information", see `dnf_residual`), so the shortest plausible implementation —
`answer_residual(a) == Sym("True") ? COND_TRUE : …` — reports UNCONDITIONAL for an answer that is
UNDEFINED. Upstream's `answer_is_conditional` (`pl-tabling.c:764-770`) is explicitly TRUE for that
case: `di == DL_UNDEFINED || !isEmptyBuffer(&di->delay_sets)`. Reason-less bottoms are REACHABLE —
`_wfs_bottom_for` yields an empty DNF whenever no optimistic answer carried a delay — so this is a
live inversion, not a hypothetical one. The truth value is decided by `is_undefined`, which is a TYPE
test on the value, and only the SHAPE of the reason is read from the DNF.
"""
function answer_condition(a::Atom)::Union{Symbol,DelayDNF}
    is_undefined(a) || return COND_TRUE        # no delay info at all ⇒ unconditional (`:5373`)
    dnf = delays_of(a)
    isempty(dnf) ? COND_UNDEFINED : dnf        # DL_UNDEFINED (`:5371`) vs a real delay list
end

"""
    answer_is_conditional(a) -> Bool

`answer_is_conditional` (`pl-tabling.c:764-770`) — is `a` a CONDITIONAL answer?

True for BOTH non-`COND_TRUE` cases, exactly as upstream's
`di == DL_UNDEFINED || !isEmptyBuffer(&di->delay_sets)`. This is the predicate the truth value
`t`/`u` is read off, and it is `is_undefined` under upstream's name — recorded because reaching for
"has a non-trivial residual" instead is the inversion documented on `answer_condition`.
"""
answer_is_conditional(a::Atom)::Bool = answer_condition(a) !== COND_TRUE

"""
    delay_lists(a) -> Vector{Vector{Atom}}

`condition_delay_lists/3` (`library/tables.pl:230-238`): the condition as a LIST OF LISTS — inner
list a conjunction, outer list a disjunction. This is `get_returns_and_dls/3`'s payload.

Upstream's three clauses map onto `answer_condition`'s three cases:

  * `condition_delay_lists(true, _, [])` (`:230`) ⇒ `COND_TRUE` gives the EMPTY outer list.
  * `(A;B)` (`:232`) ⇒ `semicolon_list//1` splits the disjunction, `conj_list/3` flattens each
    conjunct ⇒ one inner list per `DelaySet`.
  * anything else (`:236`) ⇒ `[List]`, a ONE-disjunct outer list. `undefined` lands here, and
    `comma_list//2`'s catch-all clause (`:302-303`) passes the atom through ⇒ `[[undefined]]`.

🔴 SO `COND_UNDEFINED` DOES NOT GIVE `[]`. `[]` is the UNCONDITIONAL answer's value, and collapsing the
reason-less bottom onto it would make an undefined answer indistinguishable from a true one at the
only API a user reads. `[[undefined]]` is upstream's own rendering, arrived at by its own clause
order, and it keeps the outer list non-empty — which is the property every consumer branches on.

⚠️ Literals are rendered by `_residual_literal`, so a NEGATIVE delay prints `(not g)` where upstream
prints `tnot(G)` (`comma_list//2`, `library/tables.pl:298-300`; `FUNCTOR_tnot1`,
`pl-tabling.c:5323`). That divergence is inherited from `dnf_residual`, deliberately NOT forked here
— two renderings of one condition is worse than one wrong-named rendering — and it is a REAL
divergence to fix at the renderer: in MeTTa `not` is a different, TRUTH-FUNCTIONAL operator (Bool →
Bool), while `tnot` is negation of PROVABILITY. See `Eval.jl`'s `tnot` comment, which draws exactly
that distinction. Changing it means updating the `"(not p)"` assertions pinned in `test_delays.jl`.
"""
function delay_lists(a::Atom)::Vector{Vector{Atom}}
    cond = answer_condition(a)
    cond === COND_TRUE      && return Vector{Atom}[]
    cond === COND_UNDEFINED && return Vector{Atom}[Atom[Sym("undefined")]]
    Vector{Atom}[Atom[_residual_literal(d) for d in s] for s in cond::DelayDNF]
end

"""
    delay_list_disjuncts(a) -> Vector{Vector{Atom}}

`condition_delay_list/3` (`library/tables.pl:274-286`) — the NONDETERMINISTIC form, one solution per
DISJUNCT. `get_residual/2`'s payload.

🔴 THIS IS NOT `delay_lists` WITH A DIFFERENT NAME, and the difference is the ONLY thing separating
`get_residual/2` from `get_returns_and_dls/3`. Upstream's clause for a disjunction is
`( condition_delay_list(A, M, List) ; condition_delay_list(B, M, List) )` (`:280-283`) — a Prolog
CHOICE POINT, so a 2-disjunct condition succeeds TWICE with a conjunction each time, where
`condition_delay_lists/3` succeeds ONCE with a list of both. The Julia analogue of "succeeds N times"
is N elements, so both return a `Vector{Vector{Atom}}` and the two happen to coincide element-wise;
they are kept as separate names because the CALLER's row count differs, and collapsing them makes
both predicates wrong (`get_residual` would under-report, or `get_returns_and_dls` over-report).

The `true` clause (`:274-276`) still yields ONE solution whose list is `[]` — an unconditional answer
appears in `get_residual/2`, it is not filtered out.
"""
function delay_list_disjuncts(a::Atom)::Vector{Vector{Atom}}
    cond = answer_condition(a)
    cond === COND_TRUE && return Vector{Atom}[Atom[]]  # `:274` — ONE solution, the EMPTY conjunction
    delay_lists(a)                                     # COND_UNDEFINED ⇒ 1 row; a DNF ⇒ 1 row PER disjunct
end
