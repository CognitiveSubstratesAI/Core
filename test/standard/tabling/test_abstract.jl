# test_abstract.jl — SUBGOAL ABSTRACTION. SWI §7.11.1, `subgoal_abstract(N)`.
#
# §7.11.3's `max_answers` bounds how big ONE table gets. §7.11.1 bounds how MANY tables there are: a
# recursive predicate over a growing term makes a new variant table per call, and abstraction folds
# the large ones onto a general table that answers them all.
#
# 🔴 THE THING THIS FILE EXISTS TO PIN IS THAT IT IS A **SIZE BUDGET, NOT A DEPTH LIMIT**. The name
# `size_abstract` says so and it is still easy to read as depth, because the motivating example
# (`s(s(s(X)))`) is a chain where the two coincide. They come apart on a BRANCHING term, and that
# case is asserted below — it is the one a depth-limit implementation would fail.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _AB = Eval

# (p (s (s (s a)))) — the chain from the SWI manual, built directly so the test does not depend on
# the parser's treatment of nesting.
_ab_s(n::Int) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), _ab_s(n - 1)])
_ab_p(n::Int) = Expression(Atom[Sym(:p), _ab_s(n)])

@testset "SWI §7.11.1 — subgoal abstraction" begin

    @testset "the budget bounds COMPOUND COUNT, and the top-level goal is FREE" begin
        # `from_depth = 1` (`pl-trie.c:768`) arms `aleft` only after one compound has been seen — the
        # goal itself. So `subgoal_abstract(0)` abstracts every compound ARGUMENT while leaving the
        # goal's own functor intact. Abstracting the goal too would make a table for "anything".
        (g0, hit0) = _AB.size_abstract(_ab_p(3), 0)
        @test hit0
        @test g0 isa Expression
        @test (g0::Expression).children[1] == Sym(:p)          # the functor SURVIVED
        @test (g0::Expression).children[2] isa Var             # …and the argument did not

        # a budget larger than the term abstracts nothing, and returns it UNCHANGED
        (g9, hit9) = _AB.size_abstract(_ab_p(3), 9)
        @test !hit9 && g9 == _ab_p(3)

        # NO_RESTRAINT (negative) is upstream's `size = (size_t)-1`: unlimited
        (gn, hitn) = _AB.size_abstract(_ab_p(3), _AB.NO_RESTRAINT)
        @test !hitn && gn == _ab_p(3)
    end

    @testset "the budget is spent progressively — N compounds survive, the rest go" begin
        # (p (s (s (s a)))) with N=1 keeps ONE compound below the goal: (p (s $_)).
        (g1, hit1) = _AB.size_abstract(_ab_p(3), 1)
        @test hit1
        arg = (g1::Expression).children[2]
        @test arg isa Expression
        @test (arg::Expression).children[1] == Sym(:s)         # the first `s` survived…
        @test (arg::Expression).children[2] isa Var            # …and everything below it is one var

        (g2, hit2) = _AB.size_abstract(_ab_p(3), 2)
        @test hit2
        a2 = (g2::Expression).children[2]
        @test ((a2::Expression).children[2]::Expression).children[2] isa Var   # two `s` survived
    end

    @testset "🔴 SIZE, NOT DEPTH — the case that tells the two implementations apart" begin
        # (q (f a) (g b)) with N=1. Both arguments sit at the SAME DEPTH, so a depth limit treats
        # them alike — keeping both, or abstracting both. A size BUDGET spends its one credit on the
        # first and abstracts the second, because `aleft` is ONE counter for the whole term and is
        # never restored per branch (`pl-trie.c:893`, `aleft--` with no save/restore around the
        # agenda push). This asymmetry IS the semantics.
        t = Expression(Atom[Sym(:q),
                            Expression(Atom[Sym(:f), Sym(:a)]),
                            Expression(Atom[Sym(:g), Sym(:b)])])
        (g, hit) = _AB.size_abstract(t, 1)
        @test hit
        ch = (g::Expression).children
        @test ch[2] == Expression(Atom[Sym(:f), Sym(:a)])      # first argument: SURVIVED intact
        @test ch[3] isa Var                                    # second: abstracted, same depth
    end

    @testset "abstracted subterms get DISTINCT variables" begin
        # Sharing one variable across two abstraction sites would force them EQUAL, turning "we don't
        # know these" into "these are the same" — an unsound generalisation, and a silent one.
        t = Expression(Atom[Sym(:q),
                            Expression(Atom[Sym(:f), Sym(:a)]),
                            Expression(Atom[Sym(:g), Sym(:b)])])
        (g, _) = _AB.size_abstract(t, 0)
        ch = (g::Expression).children
        @test ch[2] isa Var && ch[3] isa Var
        @test ch[2] != ch[3]
    end

    @testset "the RESULT IS MORE GENERAL — which is what makes the general table usable" begin
        # The whole design rests on this: the abstracted goal must SUBSUME the original, or answers
        # from its table do not apply. Checked with §7.5's own subsumption test, not a bespoke one.
        for n in 0:2
            (g, hit) = _AB.size_abstract(_ab_p(3), n)
            @test hit
            @test _AB.subsumes(g, _ab_p(3))                    # g ⊒ the original goal
            @test !_AB.subsumes(_ab_p(3), g)                   # …and STRICTLY so
        end
    end

    @testset "the declaration surface, and the negative-removes convention" begin
        _AB.untable_all!(); _AB.clear_subgoal_abstract!()
        @test _AB.subgoal_abstract_for(:p) == _AB.NO_RESTRAINT
        o = _AB.table_as!(:p, :subgoal_abstract => 2)          # no longer REFUSED — §7.11.1 is built
        @test o.subgoal_abstract == 2
        @test _AB.subgoal_abstract_for(:p) == 2

        # `restraint/4`: a NEGATIVE value REMOVES the restraint. Same convention as `max_answers`,
        # asserted here so the two cannot drift apart.
        _AB.table_as!(:p, :subgoal_abstract => -1)
        @test _AB.subgoal_abstract_for(:p) == _AB.NO_RESTRAINT
        _AB.untable_all!(); _AB.clear_subgoal_abstract!()
    end

    @testset "🔴 END TO END — the abstracted call is ANSWERED, and from the GENERAL table" begin
        # ANTI-VACUITY IS THE WHOLE PROBLEM HERE. A restraint that silently did nothing would still
        # produce the right answers, because the unabstracted program produces them too. So this
        # asserts BOTH halves: the answers are right, AND the table that holds them is the GENERAL
        # one — i.e. the specific variant key was never tabled.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (depth $x) ok)" * "\n")
            _AB.table_as!(:depth, :subgoal_abstract => 1)

            r = String[string(x) for y in load_metta!(s, "!(depth (s (s (s a))))\n")
                       for x in (y isa AbstractVector ? y : [y])]
            @test r == ["ok"]                                   # …answered correctly

            keys_tabled = collect(keys(_AB._ANSWER_TABLE))
            @test !isempty(keys_tabled)                         # anti-vacuity: something WAS tabled
            # the SPECIFIC goal must NOT have its own table — that is the restraint working
            specific = _AB._variant_rename(_ab_p(3))
            @test !(specific in keys_tabled)
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴 THE TABLE SET STAYS BOUNDED — the point of the feature, measured" begin
        # Without abstraction, N calls over a growing term make N tables. With it they collapse onto
        # the general one. Asserting the COUNT is what distinguishes "it ran" from "it restrained":
        # every other assertion in this file passes on an implementation that abstracts nothing.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (grow $x) ok)" * "\n")

            # baseline: no restraint ⇒ a table per distinct goal
            _AB.table!(:grow)
            for n in 1:6; load_metta!(s, "!(grow $(_ab_s(n)))\n"); end
            unrestrained = length(_AB._ANSWER_TABLE)
            @test unrestrained >= 6

            _AB.untable_all!(); _AB.abolish_all_tables!()
            _AB.table_as!(:grow, :subgoal_abstract => 1)
            for n in 1:6; load_metta!(s, "!(grow $(_ab_s(n)))\n"); end
            restrained = length(_AB._ANSWER_TABLE)

            @test restrained < unrestrained                     # …genuinely fewer
            @test restrained <= 3                               # …and BOUNDED, not merely smaller
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴🔴 THE BOUNDARY: exact when the answer MENTIONS the abstracted variable" begin
        # Upstream specialises by unifying the answer SKELETON against the specific call, because a
        # Prolog answer IS a substitution over that skeleton. A MeTTa answer is a VALUE. What we can
        # still recover is the ABSTRACTION BINDING — `gen` came FROM `red`, so matching them back
        # says what the fresh variables stood for. When the answer mentions them, that is EXACT.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (peel (s $x)) (found $x))" * "\n")
            _AB.table_as!(:peel, :subgoal_abstract => 1)
            r = String[string(x) for y in load_metta!(s, "!(peel (s (s (s a))))\n")
                       for x in (y isa AbstractVector ? y : [y])]
            # the abstracted subterm comes BACK — not `(found $_sa1)`, and not the general answer
            @test r == ["(found (s (s a)))"]
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴🔴 …and OVER-APPROXIMATES when it does not — MEASURED, not hidden" begin
        # 🔴 THIS TEST ASSERTS A KNOWN IMPRECISION, DELIBERATELY. Two rules give different constants
        # for different instances; the abstracted call cannot tell them apart, because neither answer
        # mentions the abstracted variable and a VALUE carries no record of which instance produced
        # it. Upstream filters here; we cannot, and making it exact needs answers to carry their goal
        # instance — the same structural change delay lists need (roadmap 7.A).
        #
        # Pinning it as a TEST rather than a comment is the point: an over-approximating restraint
        # that looked exact is a worse failure than one that is documented, and this fails loudly the
        # day the answer representation changes — which is exactly when it should be revisited.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (d (s (s (s a)))) deep)" * "\n" *
                           raw"(= (d (s a)) shallow)" * "\n")

            # WITHOUT the restraint the specific table is exact — the baseline that makes the
            # comparison below mean something rather than just recording current behaviour.
            _AB.table!(:d)
            exact = sort(String[string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                                for x in (y isa AbstractVector ? y : [y])])
            @test exact == ["deep"]

            _AB.untable_all!(); _AB.abolish_all_tables!()
            _AB.table_as!(:d, :subgoal_abstract => 1)
            approx = sort(String[string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                                 for x in (y isa AbstractVector ? y : [y])])
            @test "deep" in approx              # SOUND: the real answer is never lost…
            @test approx != exact               # …but it is an OVER-approximation, not a filter
            @test "shallow" in approx           # …and this is precisely what cannot be filtered out
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "an already-abstracted goal is a FIXPOINT — the recursion cannot run away" begin
        # `_abstract_tabled_eval` drives the general goal back through `tabled_eval`, so termination
        # depends on `abstract_subgoal(gen)` not abstracting again into something new. It cannot:
        # `gen` has strictly fewer compounds than `red`, and the same budget applied to fewer
        # compounds either leaves them alone or produces the same form. Asserted rather than argued.
        (g1, _) = _AB.size_abstract(_ab_p(3), 1)
        (g2, hit2) = _AB.size_abstract(g1, 1)
        @test !hit2 && g2 == g1
    end
end
