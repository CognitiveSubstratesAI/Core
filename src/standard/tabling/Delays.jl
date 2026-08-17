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
