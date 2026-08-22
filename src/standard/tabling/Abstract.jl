# tabling/Abstract.jl — THE TWO ABSTRACTION RESTRAINTS. SWI §7.11.1 `subgoal_abstract(N)` (the CALL,
# below) and §7.11.2 `answer_abstract(N)` (the ANSWER, in the second half of this file).
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
const _SUBGOAL_ABSTRACT = Dict{Symbol, Int}()

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
function size_abstract(goal::Atom, n::Int)::Tuple{Atom, Bool}
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
function abstract_subgoal(red::Atom)::Tuple{Atom, Bool}
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
function abstract_answers(general::Vector{Atom}, gen::Atom, specific::Atom,
    trie::Union{AnswerTrie, Nothing}=nothing)::Vector{Atom}
    bs = match_atoms(gen, specific)                 # what the abstraction's variables stood for
    isempty(bs) && return general                   # cannot specialise ⇒ the general set, unfiltered
    out = Atom[]
    for a in general
        # `trie === nothing` ⇒ the caller could not prove the filter sound for this head (it is
        # self-reaching, so a recorded instance is a REDUCED term, not the call) ⇒ admit everything.
        _abstract_instance_admits(trie, a, specific) || continue
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
function _abstract_instance_admits(
    trie::Union{AnswerTrie, Nothing}, a::Atom, specific::Atom
)::Bool
    trie === nothing && return true
    insts = trie_instances(trie, a)
    isempty(insts) && return true
    any(i -> !isempty(match_atoms(i, specific)), insts)
end

# ═════════════════════════════════════════════════════════════════════════════════════════════════
# §7.11.2 — ANSWER ABSTRACTION, `answer_abstract(N)`.  `pl-tabling.c:3563-3617`.
# ═════════════════════════════════════════════════════════════════════════════════════════════════
#
# The sibling restraint, and the mirror image of the one above. `subgoal_abstract(N)` bounds how MANY
# tables exist by generalising the CALL; `answer_abstract(N)` bounds how BIG one table's terms get by
# generalising the ANSWER. Same trie walk, same `{.from_depth = 2}` (`pl-tabling.c:3585` vs `:2472`),
# opposite soundness direction — and that direction is the whole difficulty.
#
# ─── 🔴 THE HARD PART, RESOLVED WITH EVIDENCE ────────────────────────────────────────────────────
# Generalising a CALL is sound: a more general table answers the specific question, so §7.11.1 needs
# no compensation. Generalising an ANSWER is NOT: the table then asserts `p(s(s(_)))` when only
# `p(s(s(s(a))))` was derived, i.e. it claims answers nobody proved. Upstream pays that debt by
# making the generalised answer UNDEFINED in the well-founded sense — `add_radial_restraint()`
# (`pl-tabling.c:8989`) calls the deliberately paradoxical `system:(radial_restraint :-
# tnot(radial_restraint))` (`boot/tabling.pl:2317`), whose only job is to push a literal onto the
# ambient delay list, which the fall-through `update_delay_list` then attaches to the new node.
#
# 📏 MEASURED, live swipl 10.1.12, `library(tables)`'s own reader — this is the shape to reproduce:
#
#     :- table p/1 as answer_abstract(1).   q(s(s(s(a)))).  q(s(a)).   p(X) :- q(X).
#     ?- get_returns_and_tvs(T, R, TV).      ret(s(s(_))) tv=u      ret(s(a)) tv=t
#     ?- get_returns_and_dls(T, R, DL).      ret(s(s(_))) dl=[[radial_restraint]]   ret(s(a)) dl=[]
#
# ⇒ CONDITIONALITY IS PER-ANSWER, NOT PER-TABLE, and the delay list is a DNF of one conjunction of
# one POSITIVE literal. `tabling/Delays.jl` already has that exact type (`DelayDNF`/`DelaySet`/
# `Delay`), and `dnf_residual` renders it as `radial_restraint` — byte-identical to upstream's.
#
# ─── …AND WHY `undefined_with(...)` IS THE WRONG TOOL, WHICH IS THE QUESTION THAT BLOCKED THIS ───
# `Options.jl` refused this option since 2026-08-17 with the reason "needs DELAY LISTS". Delay lists
# landed the next day (`tabling/Delays.jl`), so the premise was RE-CHECKED rather than assumed — and
# it turns out to have been HALF right, in a way that matters more than the half that was wrong.
#
# Our WFS bottom is `Grounded(WFSBottom(dnf))`: an ATOM that carries a condition and HAS NO VALUE.
# Substituting it for the generalised answer would store "something here is undefined" in place of
# "`(s (s $_))` holds conditionally" — which throws away the generalisation, and the generalisation
# IS the feature (it is what makes the truncated table an over-approximation rather than a silently
# incomplete one). So the value-level bottom cannot express a conditional VALUE. That much of the
# refusal was right, and no amount of delay-list machinery changes it.
#
# 🔑 BUT UPSTREAM DOES NOT PUT IT ON THE VALUE EITHER. `delay_info` hangs off the TRIE NODE
# (`pl-tabling.h:179-184`) — `Tabling.jl`'s `merge_bottom_into!` docstring already says so, for a
# different reason. The node is where conditionality belongs because it is the only object with
# VARIANT identity: several derivations of one answer contribute alternative conjunctions to ONE
# record instead of becoming several answers. `AnswerTrie.jl`'s `TrieNode` comment anticipated this
# exactly — *"delays -> WFS residuation and §7.11.2 `answer_abstract`"* — and only `instances` was
# ever added. So the mechanism was not missing; it was one field short, and the field was named.
#
# ⇒ WE THEREFORE HAVE **TWO** CONDITIONALITY CARRIERS, and they are not redundant:
#     VALUE-LEVEL  `Grounded(WFSBottom(dnf))`  — "the value is unknown"        (`tnot`, WFS)
#     NODE-LEVEL   `_ANSWER_DELAYS[node]`      — "THIS value holds, but only under a condition"
# Prolog needs only the second because a Prolog answer IS a substitution, so "unknown" is just a node
# with no unconditional support. A MeTTa answer is a VALUE, and the two statements come apart.
# `answer_truth_value` below reads BOTH, so a consumer never has to know which one applied.
#
# ⚠️ WHERE THE SIDE TABLE LIVES, AND WHY IT IS NOT THE `Dict{Atom,…}` THAT FILE WARNS AGAINST.
# `AnswerTrie.jl` is right that a `Dict` keyed by the ANSWER TERM cannot carry per-answer metadata:
# `==` splits variants, so `(s (s $_g1))` and `(s (s $_g2))` would be two keys for one answer. The
# key here is the `TrieNode` ITSELF, by object identity — the same object the trie already made
# variant-canonical. `IdDict` is the exact structure for that. The eventual home is a `delays` field
# on `TrieNode` beside `instances`; the patch is in this session's report, and moving it later is a
# field rename, not a redesign.
#
# ─── NOT PORTED, NAMED ───────────────────────────────────────────────────────────────────────────
#  • `radial_restraint` IS NOT A LIVE TABLED PREDICATE HERE. Upstream defines it as a real paradox so
#    the literal is resolvable; we record it as a MARKER literal. Nothing would consume the table:
#    `simplify_answer`/`remove_conditional_answer` (`pl-tabling.c:1560`,`:1592`) are unported, so no
#    delay list is ever simplified against a table — the residual IS the whole content. Defining a
#    live paradox with no consumer would be ceremony that reads as machinery.
#  • DELAY-LIST SIMPLIFICATION generally. A conditional answer never becomes unconditional here, and
#    never gets removed when its condition turns out false. For `radial_restraint` specifically that
#    is a NON-issue rather than a shortcut: its condition is undefined by construction and can never
#    be resolved either way, which is the entire point of the predicate.
#  • THE OTHER `update_delay_list` CALLERS. This file attaches conditionality at exactly one site —
#    the abstraction — because that is the only producer we have. Ordinary answers are unconditional
#    and `_ANSWER_DELAYS` stays empty, so nothing pays for this feature that does not use it.

"""How large an ANSWER may grow before abstraction — `answer_abstract(N)`, per predicate.

Keyed by head symbol. Absent = defer to the global `max_table_answer_size` flag; see
`answer_abstract_for`, which is upstream's `pred_max_table_answer_size` (`pl-tabling.c:3563-3572`)."""
const _ANSWER_ABSTRACT = Dict{Symbol, Int}()

"""
    answer_abstract!(head, n)

Declare `:- table head as answer_abstract(n)`. A NEGATIVE `n` REMOVES the restraint, following
`restraint/4` (`boot/tabling.pl:1337-1342`) — the same convention `subgoal_abstract!` and
`max_answers` use, kept identical so the three cannot drift apart.
"""
function answer_abstract!(head::Symbol, n::Int)
    n < 0 ? delete!(_ANSWER_ABSTRACT, head) : (_ANSWER_ABSTRACT[head] = n)
    nothing
end

"""
    answer_abstract_for(head) -> Int

`pred_max_table_answer_size` (`pl-tabling.c:3563-3572`): the predicate's own `answer_abstract(N)`,
falling back to the GLOBAL `max_table_answer_size` flag when it has none.

⚠️ THIS FALLBACK IS THE OPPOSITE SHAPE FROM §7.11.3's and the difference is deliberate upstream.
`tripwire_answers_for_subgoal` SHORT-CIRCUITS — a per-predicate `max_answers` suppresses the global
flag entirely. This one DELEGATES — the global flag reaches every predicate that did not override it.
Two restraints, forty lines apart in the same file, with genuinely different composition rules.
"""
function answer_abstract_for(head::Symbol)::Int
    n = get(_ANSWER_ABSTRACT, head, NO_RESTRAINT)
    n == NO_RESTRAINT ? max_table_answer_size() : n
end

clear_answer_abstract!() = (empty!(_ANSWER_ABSTRACT); nothing)

"""
    answer_size_abstract(a, n) -> (abstracted, was_abstracted)

The answer-side `size_abstract` — **`size_abstract` ITSELF, unchanged**, and that is a measured
result rather than a convenience.

🔴 THE TWO SIDES DO NOT OBVIOUSLY SHARE A RULE, because they walk DIFFERENT TERMS with the same
`{.from_depth = 2}`. The subgoal trie is keyed on `Module:Goal`, so at the arming depth
(`compounds == 2`, `pl-trie.c:826`) the walk is standing on the goal's ARGUMENTS. The answer trie is
keyed on `ret(A1..An)`, so at the same depth it is standing on each `Ai`'s ARGUMENTS. One extra
wrapper on the subgoal side is the entire difference — and it means the same N keeps ONE MORE
compound level in an answer than in a goal:

    p(s(s(s(a))))  as a GOAL,   subgoal_abstract(1)  ->  p(s(_))
    s(s(s(a)))     as an ANSWER, answer_abstract(1)  ->  s(s(_))

Our `size_abstract(V, n)` leaves `V`'s own functor free and re-arms `n` at each of `V`'s ARGUMENTS —
which is precisely upstream's `ret(V)` walk with `ret` playing the role of the free root. So the
answer case needs no adjustment, while a naive "wrap it like the goal" would have been off by one.

📏 VERIFIED ROW BY ROW against live swipl 10.1.12 (`get_returns_and_tvs/3`, action
`bounded_rationality`); all seven agree with `size_abstract` exactly:

    s(s(s(s(a))))            N=0 -> s(_)                    N=1 -> s(s(_))
                             N=2 -> s(s(s(_)))              N=3 -> UNCHANGED, tv=t
    f(g(h(a)), k(l(m(b))))   N=1 -> f(g(_), k(_))           N=2 -> f(g(h(a)), k(l(_)))
    plainatom                N=1 -> UNCHANGED, tv=t

The N=3 and `plainatom` rows are the load-bearing ones: NO abstraction ⇒ NO `radial_restraint` ⇒ the
answer stays UNCONDITIONAL. A restraint that marked the whole table would fail both.

⚠️ Abstracted positions are named `\$_sa…`, from the shared walk. The prefix says *size-abstract*,
not *subgoal*; renaming it per side would fork a function whose whole point is that it did not fork.
"""
answer_size_abstract(a::Atom, n::Int)::Tuple{Atom, Bool} = size_abstract(a, n)

# ─── NODE-SEATED CONDITIONALITY ──────────────────────────────────────────────────────────────────

"""The delay condition of individual stored answers, keyed by the TRIE NODE that terminates them.

`IdDict`, i.e. OBJECT IDENTITY — the node is the only thing in this engine with variant identity, so
this is upstream's `delay_info` hanging off `trie_node` (`pl-tabling.h:179-184`) rather than the
answer-term `Dict` that `AnswerTrie.jl` correctly rules out. An ABSENT or EMPTY entry means
UNCONDITIONAL; `Delays.jl` fixes that reading for the whole DNF type.

LIFECYCLE: entries are dropped by `clear_answer_delays!`, which `Tabling.jl`'s `_table_reset!` DOES
call (alongside `clear_answer_tries!`), so a reset frees them with the nodes they key. This docstring
previously said the call site did not exist — it was written while the patch was still proposed and
was not updated when the patch landed, which is the same stale-prose defect this file's own
`answer_abstract` refusal suffered for weeks. Verify the caller, not the comment."""
const _ANSWER_DELAYS = IdDict{TrieNode, DelayDNF}()

"""The delayed literal `add_radial_restraint()` pushes — `pl-tabling.c:8989`, `boot/tabling.pl:2317`.

POSITIVE, and measured to be so: upstream renders it `[[radial_restraint]]`, not `[[tnot(...)]]`.
The abstracted answer holds IF `radial_restraint` holds, and `radial_restraint` is undefined by
construction. `Sym(:ret)` is upstream's own answer term for a 0-arity tabled predicate (the nullary
return skeleton); `DELAY_POSITIVE` requires an answer, and inventing a different one would make the
literal print differently from the oracle it is checked against."""
const RADIAL_RESTRAINT = Delay(Sym(:radial_restraint), Sym(:ret), DELAY_POSITIVE)

"The DNF `bounded_rationality` attaches: one disjunct, one conjunct. Upstream's `[[radial_restraint]]`."
const RADIAL_RESTRAINT_DNF = DelayDNF([DelaySet([RADIAL_RESTRAINT])])

"""
    add_radial_restraint!(t, a) -> Bool

`add_radial_restraint()` (`pl-tabling.c:8989`) followed by the fall-through `update_delay_list`
(`:3640`): make stored answer `a` of trie `t` CONDITIONAL on `radial_restraint`.

Returns whether `a` is a stored answer of `t` at all — `false` means the caller mis-ordered the
insert and nothing was marked, which must not pass silently.

Merges by DISJUNCTION (`dnf_or`), because a second derivation of the same answer contributes an
ALTERNATIVE condition to one record; that is `update_delay_list`'s own behaviour and the reason
`delay_info` holds a buffer of `delay_set`s rather than one.
"""
function add_radial_restraint!(t::AnswerTrie, a::Atom)::Bool
    node = trie_lookup!(t, a, false)
    (node === nothing || node.answer === nothing) && return false
    prev = get(_ANSWER_DELAYS, node, DelayDNF())
    _ANSWER_DELAYS[node] = dnf_or(prev, RADIAL_RESTRAINT_DNF)
    true
end

"""
    answer_delays(t, a) -> DelayDNF

The condition under which stored answer `a` holds — `get_returns_and_dls/3` (`library(tables)`).

EMPTY means UNCONDITIONAL **or** not stored; ask `answer_truth_value` if the difference matters.
Reads BOTH carriers: a value-level `WFSBottom` answer contributes its own DNF, so a consumer does not
have to know which of the two mechanisms applied.
"""
function answer_delays(t::AnswerTrie, a::Atom)::DelayDNF
    node = trie_lookup!(t, a, false)
    (node === nothing || node.answer === nothing) && return DelayDNF()
    dnf_or(get(_ANSWER_DELAYS, node, DelayDNF()), delays_of(node.answer::Atom))
end

"""Is this stored answer CONDITIONAL? Upstream's `answer_is_conditional(node)` (`pl-tabling.c:3624`).

Used by the duplicate path exactly as upstream uses it: a re-derivation merges its condition into an
already-conditional answer, and leaves an UNCONDITIONAL one alone (`true ∨ C = true`)."""
answer_is_conditional(t::AnswerTrie, a::Atom)::Bool = !isempty(answer_delays(t, a))

"""
    answer_truth_value(t, a) -> Symbol

`get_returns_and_tvs/3` (`library(tables)`): `:t` (unconditionally true), `:u` (undefined /
conditional), or `:none` when `a` is not a stored answer of `t` at all.

Upstream has no `:none` — a term that is not in the trie simply does not enumerate. Naming it keeps
"absent" distinguishable from "present but undefined", which is the distinction the `fail` action and
the `bounded_rationality` action differ by, and therefore the one a test must be able to see.
"""
function answer_truth_value(t::AnswerTrie, a::Atom)::Symbol
    node = trie_lookup!(t, a, false)
    (node === nothing || node.answer === nothing) && return :none
    is_undefined(node.answer::Atom) && return :u
    haskey(_ANSWER_DELAYS, node) && !isempty(_ANSWER_DELAYS[node]) ? :u : :t
end

"""The residual of a stored answer as a MeTTa atom — `True` when unconditional.

`answer_residual` (`Tabling.jl`) asks the same question of a VALUE; this asks it of a stored ANSWER,
which is the only form that can be conditional while still having a value."""
answer_residual_in(t::AnswerTrie, a::Atom)::Atom = dnf_residual(answer_delays(t, a))


"""`update_delay_list` with an EMPTY delay list (`pl-tabling.c:1127-1136`): an UNCONDITIONAL
derivation of `a` has arrived, so whatever condition the node carried is destroyed.

Not exported as a general operation — the only caller is the non-abstracted insert path, which is the
only place in this engine that knows a derivation was unconditional. `is_undefined` answers are
excluded by that caller: their condition rides on the VALUE, not the node, and is not ours to clear."""
function _clear_answer_conditionality!(t::AnswerTrie, a::Atom)::Bool
    node = trie_lookup!(t, a, false)
    (node === nothing || !haskey(_ANSWER_DELAYS, node)) && return false
    delete!(_ANSWER_DELAYS, node)
    true
end

clear_answer_delays!() = (empty!(_ANSWER_DELAYS); nothing)

# ─── THE INSERT PATH ─────────────────────────────────────────────────────────────────────────────

"""What one §7.11.2-restrained insert did. Returned rather than a tuple because five facts about one
insert, positionally encoded, is how a caller reads `stored` as `added`."""
struct AnswerInsert
    added::Bool                        # did the trie gain an answer?
    stored::Union{Atom, Nothing}        # WHICH term it gained — `gen`, not the candidate
    abstracted::Bool                   # did the §7.11.2 budget blow? (upstream's TRIE_ABSTRACTED)
    disposition::Symbol                # :none | :conditional | :store | :drop
    count_action::Union{TripwireAction, Symbol, Nothing}   # whatever §7.11.3 did on the same insert
end

"""
    trie_insert_answer_restrained!(t, head, a) -> AnswerInsert

`\$tbl_wkl_add_answer`'s answer-size arm (`pl-tabling.c:3596-3617`), over our answer trie.

Upstream's order, kept because it is load-bearing at both ends:

    1. `trie_lookup_abstract(..., &sa, ...)` — ABSTRACT FIRST. The node created is the node for the
       ABSTRACTED term, so everything downstream (duplicate test, count restraint, delay list) sees
       the generalised answer, never the original.
    2. `rc == TRIE_ABSTRACTED` ⇒ the action gate (`fire_answer_size_tripwire`).
       `bounded_rationality` calls `add_radial_restraint()` and FALLS THROUGH to store; `fail` and a
       falsifying tripwire `trie_delete` and return false; `warning`/`suspend` fall through to store
       UNCONDITIONALLY. Three outcomes, and flattening them to two loses the one that matters.
    3. duplicate test, then §7.11.3's count restraint — `trie_insert_restrained!` is exactly that
       pair, so it is delegated to rather than re-implemented.

⚠️ WHEN BOTH RESTRAINTS FIRE ON ONE INSERT the §7.11.3 generalisation replaces the node, and the
radial-restraint condition is attached to the node that ACTUALLY holds the answer — found by
`_is_general_variant` because `generalise_answer_substitution` mints fresh variables and the term
therefore cannot be recomputed. Upstream reaches the same place by construction (`update_delay_list`
runs on whichever node survived); we have to go and find it, and doing so is cheap because the path
is rare. Getting this wrong would strand a condition on a node holding nothing — an answer silently
promoted from `u` to `t`, which is unsound in the direction that matters.
"""
function trie_insert_answer_restrained!(t::AnswerTrie, head::Symbol, a::Atom)::AnswerInsert
    n = answer_abstract_for(head)
    (gen, abstracted) = answer_size_abstract(a, n)
    if !abstracted                                   # `rc == true`: ordinary insert, no §7.11.2 event
        (added, act) = trie_insert_restrained!(t, head, a)
        # 🔴 …AND AN UNCONDITIONAL DERIVATION OF AN ALREADY-CONDITIONAL ANSWER CLEARS THE CONDITION.
        # `update_delay_list` (`pl-tabling.c:1127-1136`) with both delay lists NIL destroys the
        # answer's `delay_info` outright — its own debug string is *"Unconditional answer after
        # conditional"*. Same WFS rule as the duplicate case below (`true ∨ C = true`), reached from
        # the other side, and it is ORDER-INDEPENDENT: MEASURED on live swipl 10.1.12, an answer
        # derived both ways comes back `tv=t` whichever clause is written first —
        #     q(s(s(_))). q(s(s(s(a)))).   and   q(s(s(s(a)))). q(s(s(_))).   both -> ret(s(s(_))) tv=t
        # Without this, only one of those two orders agreed with upstream.
        act === :duplicate && !is_undefined(a) && _clear_answer_conditionality!(t, a)
        return AnswerInsert(added, added ? a : nothing, false, :none, act)
    end
    disp = fire_answer_size_tripwire(head)           # throws for TW_ERROR, as upstream
    disp === :drop && return AnswerInsert(false, nothing, true, :drop, nothing)
    (added, act) = trie_insert_restrained!(t, head, gen)
    # WHICH term landed? `gen` normally; §7.11.3's own generalisation of `gen` when its count bound
    # fired on this same insert; nothing at all when §7.11.3 dropped it.
    stored::Union{Atom, Nothing} =
        if trie_contains(t, gen)
            gen
        elseif act == TW_BOUNDED_RATIONALITY
            (i=findfirst(x -> _is_general_variant(x, gen), trie_answers(t));
                i === nothing ? nothing : trie_answers(t)[i])
        else
            nothing
        end
    # 🔴 A DUPLICATE THAT IS ALREADY UNCONDITIONAL STAYS UNCONDITIONAL — `pl-tabling.c:3618-3628`.
    # The C reaches `update_delay_list` on the duplicate path ONLY inside
    # `if ( answer_is_conditional(node) )`, and otherwise `return false` without touching the delays.
    # That is the WFS rule `true ∨ C = true`: an answer with an unconditional derivation does not
    # become undefined because some OTHER derivation of it was abstracted. `add_radial_restraint()`
    # still ran (it is called before the duplicate test), but its literal lands on nothing.
    #
    # THIS WAS WRONG IN THE FIRST WORKING VERSION and the probe caught it: pre-seeding `(s (s \$_))`
    # unconditionally and then inserting `(s (s (s a)))` under `answer_abstract(1)` reported
    # `tv=:u` — an unconditional answer demoted to undefined by a restraint that added nothing. The
    # rule was already written into `answer_is_conditional`'s docstring one screen above and simply
    # not implemented, which is the shape of defect a docstring cannot catch on its own.
    mark =
        disp === :conditional && stored !== nothing &&
        !(act === :duplicate && !answer_is_conditional(t, stored::Atom))
    mark && add_radial_restraint!(t, stored::Atom)   # `add_radial_restraint()` + `update_delay_list`
    AnswerInsert(added, stored, true, disp, act)
end
