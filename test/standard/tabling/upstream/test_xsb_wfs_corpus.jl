# XSB's Well-Founded Semantics conformance corpus, run against OUR engine.
#
# ─── WHAT THIS IS ────────────────────────────────────────────────────────────────────────────────
# `swipl-devel/tests/xsb/wfs_tests/` holds 72 tiny programs, each opening with a machine-readable
# gold row written by the people who defined the semantics:
#
#     query(p10, p, [p,q,r], [], [p,q,r]).
#     %     name  goal  all-subgoals  TRUE-set  UNDEFINED-set
#
# A subgoal in neither set is FALSE. `verify_corpus.sh` checks all 72 against the live `swipl`
# 10.1.12 — **72 agree, 0 differ** — so the table is safe to grade ourselves against.
#
# 🔴 WHY THIS FILE EXISTS AND `test_delays.jl` IS NOT ENOUGH. That file is mostly DNF ALGEBRA:
# `dnf_and` distributes, `dnf_or` dedups. Algebra assertions cannot see a wrong FIXPOINT — an engine
# with a perfect delay algebra and a broken alternating fixpoint passes every one of them. These
# programs state, per atom, exactly which are true, which are undefined, and by omission which are
# false. That is the defect class our own tests could not observe
# (`[[feedback_oracle_must_observe_the_defect_class]]`), and WFS here has already been wrong once:
# an audit found `tnot` returning THREE WRONG ANSWERS with a QUERY-ORDER dependence.
#
# ─── TRANSLATION, AND WHY IT IS HAND-WRITTEN ─────────────────────────────────────────────────────
# The programs are Prolog; our engine is MeTTa. The mapping for the propositional fragment — which
# is 54 of the 72 goals — is small and total:
#
#     q.                    fact              ->  (= (q) True)
#     t :- fail.            always fails      ->  NO RULE AT ALL (still tabled: an empty table IS
#                                                 "false", and `table!` on a ruleless head is legal)
#     p :- tnot(r).         negation          ->  (= (p) (tnot (r)))
#     p :- q, tnot(r).      conjunction       ->  (= (p) (let $_1 (q) (tnot (r))))
#     p :- q.  p :- r.      disjunction       ->  two rules with the same head
#
# 🔑 CONJUNCTION IS `let`, NOT AN `and`. In MeTTa an expression whose subterm produces nothing
# produces nothing, so binding the left conjunct and returning the right gives Prolog's "both must
# hold" for free — no truth-table, no short-circuit semantics to get wrong. Each `let` uses a
# DISTINCT binder (`$_1`, `$_2`) because reusing one name in a nest is a shadowing bug waiting to
# be blamed on the engine.
#
# ⚠️ HAND-TRANSLATED, DELIBERATELY, AND ONLY 10 OF 72. A generated translator would have to be
# trusted before its output could be, and a wrong translator produces confident wrong conformance —
# the worst possible artifact here. Each of these was run and checked against its gold row
# individually first (`[[feedback_parses_is_not_fires]]`). They are chosen to span the outcome
# space: all-true, all-undefined, single self-loop, mixed true+undefined, a long alternating chain,
# and the three `win/1` game graphs, which exercise a different translation path entirely (facts in
# the space, a binding `match`, compound goals). Extending to the rest is mechanical and is the next
# step, not a hidden gap.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _XW = Eval

"""One row of the XSB corpus: the program, what to table, the atoms it asks about, and the verdict.

`goals` are STRINGS, not symbols, because half the corpus asks about compound goals — `win(a)` — and
a `Symbol` cannot carry the argument. `tabled` is separate from `goals` for the same reason: in the
`win/1` programs one predicate is tabled and four goals are asked of it, while in the propositional
programs the two lists coincide.
"""
struct XsbCase
    name::String
    program::String
    tabled::Vector{Symbol}
    goals::Vector{String}
    true_set::Vector{String}
    undef_set::Vector{String}
end

"Flatten what `load_metta!` returns — a query may yield a vector of vectors."
function _xw_answers(s::Space, goal::AbstractString)::Vector{Atom}
    out = Atom[]
    for y in load_metta!(s, "!$goal\n")
        y isa AbstractVector ? append!(out, y) : push!(out, y)
    end
    out
end

"Classify each goal as TRUE / UNDEFINED / FALSE and return the first two as sorted sets."
function _xw_run(c::XsbCase)::Tuple{Vector{String},Vector{String}}
    _XW.untable_all!(); _XW.abolish_all_tables!()
    s = Space(); load_core_stdlib!(s)
    isempty(c.program) || load_metta!(s, c.program)
    for t in c.tabled
        _XW.table!(t)
    end
    got_true = String[]; got_undef = String[]
    for g in c.goals
        a = _xw_answers(s, g)
        if isempty(a)
            # FALSE — no answer at all. Recorded by omission, exactly as the gold rows do.
        elseif all(_XW.is_undefined, a)
            push!(got_undef, g)
        else
            push!(got_true, g)
        end
    end
    (sort(got_true), sort(got_undef))
end

# ─── THE CASES ───────────────────────────────────────────────────────────────────────────────────
# Each `program` is the MeTTa translation; the comment above it is the upstream Prolog verbatim, so
# a reader can check the translation without opening the corpus.
const _XSB_CASES = XsbCase[

    # p06:  p :- q, tnot(r).   q.   r :- fail.
    XsbCase("p06",
        raw"(= (q) True)" * "\n" *
        raw"(= (p) (let $_1 (q) (tnot (r))))" * "\n",
        [:p, :q, :r], ["(p)", "(q)", "(r)"], ["(p)", "(q)"], String[]),

    # p07:  p :- q, tnot(r).   q.   r :- tnot(s).   s :- tnot(t).   t :- fail.
    # A four-deep alternating chain: t false -> s true -> r false -> p true.
    XsbCase("p07",
        raw"(= (q) True)" * "\n" *
        raw"(= (p) (let $_1 (q) (tnot (r))))" * "\n" *
        raw"(= (r) (tnot (s)))" * "\n" *
        raw"(= (s) (tnot (t)))" * "\n",
        [:p, :q, :r, :s, :t], ["(p)", "(q)", "(r)", "(s)", "(t)"],
        ["(p)", "(q)", "(s)"], String[]),

    # p08:  p :- q, tnot(r), s.   q.   r :- tnot(s).   s.
    # THREE conjuncts — the nested-`let` case, and the one that would expose a binder collision.
    XsbCase("p08",
        raw"(= (q) True)" * "\n" *
        raw"(= (s) True)" * "\n" *
        raw"(= (r) (tnot (s)))" * "\n" *
        raw"(= (p) (let $_1 (q) (let $_2 (tnot (r)) (s))))" * "\n",
        [:p, :q, :r, :s], ["(p)", "(q)", "(r)", "(s)"], ["(p)", "(q)", "(s)"], String[]),

    # p09:  p :- tnot(q).   q :- tnot(p).   q :- r.   r :- tnot(s).   s :- fail.
    # 🔑 THE CASE THAT PUNISHES A NAIVE FIXPOINT. p and q look like a paradox in isolation, but q
    # has a SECOND clause deriving it from r, which is unconditionally true — so q is TRUE and p is
    # FALSE, and NOTHING is undefined. An engine that decides the p/q loop before considering q's
    # other clause reports both undefined and passes any test that only asks "is it a paradox".
    XsbCase("p09",
        raw"(= (p) (tnot (q)))" * "\n" *
        raw"(= (q) (tnot (p)))" * "\n" *
        raw"(= (q) (r))" * "\n" *
        raw"(= (r) (tnot (s)))" * "\n",
        [:p, :q, :r, :s], ["(p)", "(q)", "(r)", "(s)"], ["(q)", "(r)"], String[]),

    # p10:  p :- q.   p :- r.   r :- tnot(q).   q :- tnot(r).
    # The canonical 2-cycle: everything undefined, nothing true.
    XsbCase("p10",
        raw"(= (p) (q))" * "\n" *
        raw"(= (p) (r))" * "\n" *
        raw"(= (r) (tnot (q)))" * "\n" *
        raw"(= (q) (tnot (r)))" * "\n",
        [:p, :q, :r], ["(p)", "(q)", "(r)"], String[], ["(p)", "(q)", "(r)"]),

    # p14:  p :- tnot(p).
    # The one-line paradox. Smallest program in the corpus and the sharpest: an engine that loops
    # forever, and one that answers `false`, both fail here, and neither failure is subtle.
    XsbCase("p14",
        raw"(= (p) (tnot (p)))" * "\n",
        [:p], ["(p)"], String[], ["(p)"]),

    # p22:  a :- fail.   b :- tnot(a).   c :- tnot(b).   c :- a, tnot(p).
    #       p :- tnot(q).   q :- tnot(p), b.
    # MIXED, which is the interesting shape: b TRUE, a and c FALSE, p and q UNDEFINED — all three
    # verdicts in one program, so a uniformly-wrong engine cannot pass it by accident.
    XsbCase("p22",
        raw"(= (b) (tnot (a)))" * "\n" *
        raw"(= (c) (tnot (b)))" * "\n" *
        raw"(= (c) (let $_1 (a) (tnot (p))))" * "\n" *
        raw"(= (p) (tnot (q)))" * "\n" *
        raw"(= (q) (let $_1 (tnot (p)) (b)))" * "\n",
        [:p, :q, :a, :b, :c], ["(p)", "(q)", "(a)", "(b)", "(c)"], ["(b)"], ["(p)", "(q)"]),

    # ── THE `win/1` GAME GRAPHS: p11, p12, p13 ───────────────────────────────────────────────────
    # One rule, three graphs: `win(A) :- m(A,B), tnot(win(B)).` — a position is winning iff it has a
    # move to a LOSING one. This is a genuinely different translation path from everything above:
    # the facts are ATOMS IN THE SPACE, the conjunct is a `match` that BINDS a variable rather than
    # a propositional call, and the goals are COMPOUND (`win(a)`), not bare symbols.
    # 🔑 THE `let` BINDER CARRIES THE MATCH RESULT HERE. In the propositional cases `$_1` is discarded;
    # here `$b` is the successor the negation is applied to, which is exactly Prolog's `m(A,B)` then
    # `tnot(win(B))`. Same construct, doing real work.
    # ⚠️ EACH GOAL IS ASKED GROUND. Our `tnot` requires a ground goal (it raises an
    # instantiation_error otherwise), so we ask `(win a)`, `(win b)`, … rather than `win(_A)` as
    # upstream's gold row is phrased. The gold SETS are per-position, so nothing is lost.

    # p11:  m(a,b). m(b,c). m(c,d). m(b,d).       — a DAG, so everything is decided.
    #       d has no move -> lost; c->d -> won; b->d -> won; a->b(won) only -> lost.
    XsbCase("p11",
        "(m a b)\n(m b c)\n(m c d)\n(m b d)\n" *
        raw"(= (win $a) (let $b (match &self (m $a $b) $b) (tnot (win $b))))" * "\n",
        [:win], ["(win a)", "(win b)", "(win c)", "(win d)"],
        ["(win b)", "(win c)"], String[]),

    # p12:  m(a,b). m(b,a). m(b,c).               — a 2-cycle a<->b PLUS an escape b->c.
    #       c is lost, so b is WON via c; a's only move is to b (won), so a is lost. The cycle does
    #       NOT make these undefined — the escape decides them, and that is the point of the case.
    XsbCase("p12",
        "(m a b)\n(m b a)\n(m b c)\n" *
        raw"(= (win $a) (let $b (match &self (m $a $b) $b) (tnot (win $b))))" * "\n",
        [:win], ["(win a)", "(win b)", "(win c)"], ["(win b)"], String[]),

    # p13:  m(a,b). m(b,a). m(b,c). m(c,d).       — the SAME 2-cycle, but now the escape leads to a
    #       won position instead of a lost one. d lost -> c won; b's moves are a and c(won), a is
    #       undecided; the a<->b cycle no longer has an escape that settles it, so BOTH are
    #       UNDEFINED while c stays TRUE. One extra edge flips two atoms from decided to undefined —
    #       the tightest true/undefined discriminator in the corpus.
    XsbCase("p13",
        "(m a b)\n(m b a)\n(m b c)\n(m c d)\n" *
        raw"(= (win $a) (let $b (match &self (m $a $b) $b) (tnot (win $b))))" * "\n",
        [:win], ["(win a)", "(win b)", "(win c)", "(win d)"],
        ["(win c)"], ["(win a)", "(win b)"]),
]

@testset "XSB wfs_tests corpus — our engine vs upstream's gold rows" begin
    # ANTI-VACUITY: an empty case list would make every claim below trivially true, and this file's
    # whole purpose is to be extended — a bad merge that drops cases must fail, not silently pass.
    @test length(_XSB_CASES) == 10
    @test any(!isempty(c.undef_set) for c in _XSB_CASES)   # …and at least one exercises UNDEFINED

    for c in _XSB_CASES
        @testset "$(c.name)" begin
            try
                (got_true, got_undef) = _xw_run(c)
                @test got_true  == sort(c.true_set)
                @test got_undef == sort(c.undef_set)
            finally
                _XW.untable_all!(); _XW.abolish_all_tables!()
            end
        end
    end
end
