# tabling/Abstract.jl — SUBGOAL ABSTRACTION. SWI §7.11.1, `subgoal_abstract(N)`.
#
# Mirrors `size_abstract` in the trie walk (`src/pl-trie.c:826-902`) and `start_abstract_tabling/3`
# (`boot/tabling.pl:466-517`).
#
# ─── WHAT IT IS, AND WHAT MAKES IT A RESTRAINT ───────────────────────────────────────────────────
# A recursive predicate over a growing term — `p(s(s(s(X))))` — creates a NEW variant table for every
# call, so the table set grows without bound even though each table is finite. §7.11.1 bounds that:
# a goal larger than N is replaced by a MORE GENERAL one, and the general table answers it.
#
# Upstream states the design in one sentence (`:469-472`): *"This is a merge between variant and
# subsumptive tabling. If the goal is not abstracted this is simple variant tabling. If the goal is
# abstracted we must solve the more general goal and use answers from the abstract table."*
#
# 🔴 THAT SENTENCE IS WHY THIS COULD BE BUILT NOW, AND WHY WE THOUGHT IT COULD NOT. `Options.jl`
# refused `subgoal_abstract` on the stated grounds that it needed "abstraction over TRIE TERMS at a
# depth — trie walk not built", i.e. that the answer trie was the prerequisite. It is not. Subgoal
# abstraction rides on SUBSUMPTIVE TABLING (§7.5, built) plus the size limit below. The refusal
# reason had been carried forward unexamined for long enough to look like a fact.
# `[[feedback_capability_claims_expire_retest_the_premise]]`
#
# ─── 🔴 IT IS A SIZE BUDGET, NOT A DEPTH LIMIT — THE NAME SAYS SO AND IT IS EASY TO MISREAD ──────
# `size_abstract{from_depth, size}` (`pl-trie.h:140-143`) is threaded through the trie walk:
#
#     if ( compounds == sa.from_depth ) aleft = sa.size;      /* :826 — from_depth is 1 */
#     ...
#     case TAG_COMPOUND:
#       if ( unlikely(aleft == 0) ) { rc = TRIE_ABSTRACTED; goto add_var; }   /* :886 */
#       else { if ( aleft != (size_t)-1 ) aleft--; ... pushWorkAgenda_P(...); }
#
# So `aleft` is ONE budget for the WHOLE term, decremented at every compound subterm and never
# restored per branch — the (N+1)-th compound encountered becomes a fresh VARIABLE, wherever it sits.
# A depth limit would abstract `f(g(a), g(b))`'s two `g`s alike at depth 1; the size budget with N=1
# keeps the first and abstracts the second. Traversal order therefore MATTERS, and it is DFS
# pre-order, left to right: `nextTermAgenda_P` pops the most recently pushed range
# (`pl-termwalk.c:241-260`), and a compound pushes its arguments as that range.
#
# ⚠️ THE TOP-LEVEL GOAL IS FREE. `from_depth = 1` means `aleft` is only armed once one compound has
# been seen — the goal itself — so `subgoal_abstract(0)` abstracts every ARGUMENT that is compound
# while leaving the goal's own functor intact. Abstracting the goal itself would be a table for
# "anything", which is not a table.

"""How many compound subterms a goal may contain before abstraction — `subgoal_abstract(N)`.

Keyed by head symbol, like the other per-predicate registries. `NO_RESTRAINT` (absent) = unlimited,
which is upstream's `size = (size_t)-1`."""
const _SUBGOAL_ABSTRACT = Dict{Symbol,Int}()

"""
    subgoal_abstract!(head, n)

Declare `:- table head as subgoal_abstract(n)`. A NEGATIVE `n` REMOVES the restraint, matching
`restraint/4`'s rule (`boot/tabling.pl:1337-1342`) — the same convention `max_answers` follows, kept
identical so the two restraints cannot drift apart.
"""
function subgoal_abstract!(head::Symbol, n::Int)
    n < 0 ? delete!(_SUBGOAL_ABSTRACT, head) : (_SUBGOAL_ABSTRACT[head] = n)
    nothing
end

"The subgoal-abstraction budget for a head, or `NO_RESTRAINT` when it has none."
subgoal_abstract_for(head::Symbol)::Int = get(_SUBGOAL_ABSTRACT, head, NO_RESTRAINT)
clear_subgoal_abstract!() = (empty!(_SUBGOAL_ABSTRACT); nothing)

"""
    size_abstract(goal, n) -> (abstracted, was_abstracted)

The trie walk's `size_abstract` (`pl-trie.c:826-902`), as a term rewrite.

Walk `goal` DFS pre-order. The goal's own functor is free (`from_depth = 1`); thereafter a budget of
`n` compound subterms is spent left to right, and every compound past it becomes a FRESH VARIABLE.
Returns the rewritten goal and whether anything was abstracted — upstream's `TRIE_ABSTRACTED`, which
is what `start_abstract_tabling` branches on.

`n < 0` (`NO_RESTRAINT`) is upstream's `size = (size_t)-1`: unlimited, goal returned unchanged.

    size_abstract((p (s (s (s a)))), 1)  ->  ((p (s \$_sa1)), true)
    size_abstract((p (s (s (s a)))), 9)  ->  ((p (s (s (s a)))), false)
"""
function size_abstract(goal::Atom, n::Int)::Tuple{Atom,Bool}
    n < 0 && return (goal, false)
    goal isa Expression || return (goal, false)     # a non-compound goal has nothing to abstract
    budget = Ref{Int}(n)
    hit = Ref{Bool}(false)
    ctr = Ref{UInt64}(0)
    ch = (goal::Expression).children
    # the goal's own functor is compound #1 and is NOT charged — `from_depth = 1` arms the budget
    # only after it. Its ARGUMENTS are where the walk begins.
    Expression(Atom[_sa_walk(c, budget, hit, ctr) for c in ch]), hit[]
end

"One DFS pre-order step of the size-abstraction walk. `budget` is shared across the WHOLE term."
function _sa_walk(a::Atom, budget::Ref{Int}, hit::Ref{Bool}, ctr::Ref{UInt64})::Atom
    a isa Expression || return a                    # atoms/vars/grounded cost nothing
    if budget[] == 0
        # `if ( aleft == 0 ) { rc = TRIE_ABSTRACTED; goto add_var; }` — the compound is REPLACED by a
        # fresh variable, and the whole subterm below it disappears with it (the C never pushes its
        # arguments onto the agenda). A fresh name per site: two abstracted subterms are independent,
        # so sharing one variable would wrongly force them equal.
        hit[] = true
        ctr[] += 1
        return Var("_sa", ctr[])
    end
    budget[] -= 1                                   # `if ( aleft != (size_t)-1 ) aleft--;`
    Expression(Atom[_sa_walk(c, budget, hit, ctr) for c in (a::Expression).children])
end

"""
    abstract_subgoal(red) -> (general, was_abstracted)

Apply the calling head's declared `subgoal_abstract(N)` to a reduced goal. Returns the goal
unchanged with `false` when the head has no such declaration — the "simple variant tabling" arm of
`start_abstract_tabling`.
"""
function abstract_subgoal(red::Atom)::Tuple{Atom,Bool}
    h = head_name(red)
    h === nothing && return (red, false)
    n = subgoal_abstract_for(h)
    n == NO_RESTRAINT && return (red, false)
    size_abstract(red, n)
end

"""
    abstract_answers(general_answers, gen, specific) -> Vector{Atom}

Specialise the GENERAL table's answers to the SPECIFIC call — upstream's
`'\$tbl_answer_update_dl'(Trie, Skeleton)` (`boot/tabling.pl:472`).

🔴🔴 AND THIS IS WHERE PROLOG'S ANSWER MODEL DOES NOT SURVIVE MeTTa — the THIRD-ASSUMPTION class
again, found by BUILDING it (2026-08-17). Upstream can implement this as a UNIFICATION because a
Prolog answer **is a substitution over the goal skeleton**: the trie stores `p(s(Y))` with `Y` bound,
so unifying that skeleton against `p(s(s(a)))` both filters and instantiates in one step.

**A MeTTa answer is a VALUE.** `(= (depth \$x) ok)` answers `ok`, and `ok` carries no record of WHICH
instance produced it. There is no skeleton to unify against, so the Prolog filter is not merely
awkward here — it has no argument to work on. The first implementation did exactly that
(`match_atoms(answer, specific)`) and returned EMPTY for every non-ground abstraction, because a
value never unifies with a goal.

What IS recoverable is the ABSTRACTION BINDING: `gen` was produced FROM `specific` by replacing
compounds with fresh variables, so `match_atoms(gen, specific)` recovers exactly what those variables
stood for, and substituting it into an answer specialises every answer that MENTIONS them.

⚠️ SO THIS OVER-APPROXIMATES, AND THE BOUNDARY IS SHARP — see `test_abstract.jl`, which pins BOTH
sides rather than only the good one:
  • an answer that MENTIONS the abstracted variable is specialised EXACTLY, as upstream;
  • an answer that does NOT — a constant like `ok`, or two rules giving different constants for
    different instances — cannot be filtered, and the general table's full answer set comes back.
Making it exact requires answers to carry their goal instance, which is the SAME structural change
delay lists need (conditions must ride WITH the value). Recorded in the roadmap under 7.A, not
papered over here: an over-approximating restraint that looked exact would be the worse failure.
"""
function abstract_answers(general::Vector{Atom}, gen::Atom, specific::Atom,
                          trie::Union{AnswerTrie,Nothing} = nothing)::Vector{Atom}
    bs = match_atoms(gen, specific)                 # what the abstraction's variables stood for
    isempty(bs) && return general                   # cannot specialise ⇒ the general set, unfiltered
    out = Atom[]
    for a in general
        # ── roadmap 7.A: FILTER BY THE RECORDED GOAL INSTANCE ────────────────────────────────────
        # This is upstream's filter, restored. It could not be expressed before per-answer metadata
        # existed, because a value carries no record of its derivation; now `_leader_pass` records
        # `subst(key, bnd)` on the answer's trie node, so we can ask the question upstream asks:
        # did any instance that produced this answer unify with the call?
        #
        # ⚠️ AN EMPTY INSTANCE LIST MEANS UNRECORDED, NOT "NONE" — and reading it as "none" would
        # DROP answers, converting a documented imprecision into a silent unsoundness. So the empty
        # case falls through to the over-approximation, which is what this did for everything before.
        _abstract_instance_admits(trie, a, specific) || continue
        for b in bs
            inst = subst(a, b)
            any(x -> variant_eq(x, inst), out) || push!(out, inst)
        end
    end
    out
end

"Does a recorded instance of `a` unify with `specific`? TRUE when nothing was recorded — see above."
function _abstract_instance_admits(trie::Union{AnswerTrie,Nothing}, a::Atom, specific::Atom)::Bool
    trie === nothing && return true
    insts = trie_instances(trie, a)
    isempty(insts) && return true                   # UNRECORDED ⇒ admit (sound over-approximation)
    any(i -> !isempty(match_atoms(i, specific)), insts)
end
