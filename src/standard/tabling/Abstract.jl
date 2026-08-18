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
# ─── 🔴 THE BUDGET IS PER TOP-LEVEL ARGUMENT — AND THIS HEADER SAID OTHERWISE UNTIL 2026-08-18 ────
# `size_abstract{from_depth, size}` (`pl-trie.h:140-143`) is threaded through the trie walk:
#
#     if ( compounds == sa.from_depth ) aleft = sa.size;      /* pl-trie.c:826 */
#     ...
#     case TAG_COMPOUND:
#       if ( unlikely(aleft == 0) ) { rc = TRIE_ABSTRACTED; goto add_var; }   /* :886 */
#       else { if ( aleft != (size_t)-1 ) aleft--; ... pushWorkAgenda_P(...); }
#
# THIS FILE ORIGINALLY READ THAT AS "ONE BUDGET FOR THE WHOLE TERM", and argued the point at length
# with a test built to prove it. It was wrong twice over:
#   1. TABLING DOES NOT USE `from_depth = 1`. That is the GENERIC default at `pl-trie.c:768`; the
#      subgoal variant lookup uses `{.from_depth = 2}` (`pl-tabling.c:2472`, and `:3585` for answers).
#   2. `compounds` IS A DEPTH, NOT A RUNNING TOTAL — the agenda's POP path unwinds it. So the re-arm
#      line fires again at EVERY node of that depth, which is every top-level ARGUMENT.
#
# 📏 GROUND TRUTH, live swipl 10.1.12 (`max_table_subgoal_size_action=abstract`; variants read back
# with `current_table/2`). The middle rows are exactly what the old model got wrong:
#     p(s(s(s(a))))                N=1 -> p(s(_))
#     q(f(a), g(b))                N=1 -> UNCHANGED            (old model abstracted g(b))
#     r(f(a), g(b), h(c))          N=1 -> UNCHANGED            (old model abstracted two arguments)
#     a1(f(g(a)), h(b))            N=1 -> a1(f(_), h(b))
#     a2(f(g(h(a))), k(l(m(b))))   N=2 -> a2(f(g(_)), k(l(_)))
#     a3(s(s(s(s(a)))))            N=2 -> a3(s(s(_)))
#
# ⇒ N = COMPOUND LEVELS KEPT BELOW EACH ARGUMENT. Within a single argument the budget is still shared
# across siblings (upstream re-arms at argument depth, never deeper), so `f(g(a), h(b))` with N=1
# keeps `g(a)` and abstracts `h(b)` — the old "size not depth" intuition survives, but SCOPED TO ONE
# ARGUMENT rather than to the whole goal.
#
# ⚠️ THE GOAL'S OWN FUNCTOR IS NEVER ABSTRACTED. Abstracting it would make a table for "anything",
# which is not a table. `subgoal_abstract(0)` therefore abstracts every compound ARGUMENT whole.
#
# 🔴 THE LESSON, WORTH MORE THAN THE FIX: this file ARGUED for the wrong model, in detail, citing the
# C — and the citation was to the wrong initialiser. Reading the source is not the same as reading the
# CALL SITE. An executable oracle settled in one command what re-reading the C had got wrong twice.
# `[[feedback_verify_oracle_against_upstream_not_assume_canonical]]`

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
    hit = Ref{Bool}(false)
    ctr = Ref{UInt64}(0)
    ch = (goal::Expression).children
    # 🔴 THE BUDGET IS RE-ARMED PER TOP-LEVEL ARGUMENT — CORRECTED 2026-08-18 AGAINST A LIVE ORACLE.
    # This used ONE budget for the whole term, on a reading of `from_depth` that was wrong twice over:
    # tabling does not use `pl-trie.c:768`'s generic `from_depth = 1` but `pl-tabling.c:2472`'s
    # `{.from_depth = 2}` (and `:3585` likewise), AND `compounds` is a DEPTH that unwinds on the
    # agenda's POP, not a running total. So `if (compounds == sa.from_depth) aleft = sa.size;`
    # (`pl-trie.c:826`) fires again at EVERY node of that depth — i.e. at each top-level argument.
    #
    # MEASURED against live swipl 10.1.12 (`max_table_subgoal_size_action=abstract`, variants read
    # back with `current_table/2`) — the second and third rows are what the old model got wrong:
    #     p(s(s(s(a))))                   N=1 -> p(s(_))
    #     q(f(a), g(b))                   N=1 -> UNCHANGED          (ours abstracted g(b))
    #     r(f(a), g(b), h(c))             N=1 -> UNCHANGED          (ours abstracted two args)
    #     a1(f(g(a)), h(b))               N=1 -> a1(f(_), h(b))
    #     a2(f(g(h(a))), k(l(m(b))))      N=2 -> a2(f(g(_)), k(l(_)))
    #     a3(s(s(s(s(a)))))               N=2 -> a3(s(s(_)))
    # ⇒ N is "compound levels kept BELOW EACH ARGUMENT", and within one argument the budget is still
    # shared across siblings (it is only re-armed at argument depth, never deeper).
    args = @view ch[2:end]
    out = Atom[ch[1]]
    for arg in args
        push!(out, _sa_walk(arg, Ref{Int}(n), hit, ctr))   # FRESH budget per argument
    end
    Expression(out), hit[]
end

"""One DFS pre-order step of the walk. `budget` is shared across ONE top-level argument's subtree.

Shared across SIBLINGS inside that argument (upstream re-arms only at argument depth, never deeper),
and re-armed by the caller for the next argument."""
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
    (gen, abstracted) = size_abstract(red, n)
    # 🔴 THE ACTION GATE — `pl-tabling.c:2506-2523`, ADDED 2026-08-18. Abstraction is NOT what
    # `subgoal_abstract(N)` does by default: the flag `max_table_subgoal_size_action` defaults to
    # `error`, and upstream RAISES rather than abstracting. `TW_ABSTRACT` is the only value that
    # permits it, and any other disposition RETRIES UNABSTRACTED (`sa.size = -1; goto retry`).
    abstracted || return (red, false)
    fire_subgoal_size_tripwire(h) && return (red, false)     # retry with the restraint disabled
    (gen, true)
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
function abstract_answers(general::Vector{Atom}, gen::Atom, specific::Atom)::Vector{Atom}
    bs = match_atoms(gen, specific)                 # what the abstraction's variables stood for
    isempty(bs) && return general                   # cannot specialise ⇒ the general set, unfiltered
    out = Atom[]
    for a in general
        # 🔴🔴 THE INSTANCE FILTER WAS REMOVED 2026-08-18 — IT WAS UNSOUND, AND IT WAS MINE.
        # Shipped 2026-08-17 (7425b7d) claiming §7.11.1 was now EXACT. An adversarial audit the same
        # night found it DROPS REAL ANSWERS on the default path, and the reproduction is three lines:
        #
        #     (= (e (f a)) v)              (= (e (f (g $x))) (e (f $x)))
        #     !(e (f (g (g a))))   unrestrained -> ["v"]   subgoal_abstract(1) -> []   ← ANSWER LOST
        #
        # MECHANISM, measured: the general table `(e (f $_v#1))` holds answer `v` with recorded
        # instance `(e (f a))`. The specific call is `(e (f (g (g a))))`, which does NOT unify with
        # that instance — so the filter rejected it. But `v` IS the correct answer: the specific call
        # REDUCES into `(e (f a))` through the recursive rule.
        #
        # ⇒ THE PREMISE IS WRONG, NOT THE IMPLEMENTATION. "Some instance that produced this answer
        # unifies with the call" is NOT equivalent to "this answer holds for the call". Upstream can
        # use the equivalent-looking test only because a Prolog answer IS a substitution over the goal
        # skeleton, so unifying the SKELETON carries the caller's own bindings — it is not asking
        # which instance produced anything. In a REWRITING language the specific call reduces into
        # other instances of the general table, and no instance-provenance test can see that.
        # This is the THIRD ASSUMPTION biting a second time, one level subtler than where it was first
        # found: it is not enough to record the instance; the instance does not answer the question.
        #
        # So §7.11.1 is back to a SOUND OVER-APPROXIMATION, which is what it shipped as in b98f581,
        # and the "EXACT" claim in 7425b7d is retracted. Recovering the precision needs the answer to
        # carry the caller's bindings — the same representation change delay lists needed (7.A/7.D) —
        # not a provenance list. `[[feedback_unexplained_behaviour_is_not_a_contract]]`
        for b in bs
            inst = subst(a, b)
            any(x -> variant_eq(x, inst), out) || push!(out, inst)
        end
    end
    out
end

"""Would a recorded instance of `a` unify with `specific`? **NOT USED AS A FILTER — see above.**

Kept as a QUERY because the recorded instances are still the substrate 7.A promised and other work
may consume them, and because deleting it would erase the evidence of why the filter was wrong. Any
future caller must not treat a `false` here as "this answer does not hold for this call": the
reproduction in `abstract_answers` shows a correct answer whose only recorded instance does not
unify with the call, because the call REDUCES into that instance."""
function _abstract_instance_admits(trie::Union{AnswerTrie,Nothing}, a::Atom, specific::Atom)::Bool
    trie === nothing && return true
    insts = trie_instances(trie, a)
    isempty(insts) && return true
    any(i -> !isempty(match_atoms(i, specific)), insts)
end
