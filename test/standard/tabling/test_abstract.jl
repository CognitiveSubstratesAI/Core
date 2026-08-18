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

    @testset "🔴🔴 THE SWIPL ORACLE — six variants, read back from live swipl 10.1.12" begin
        # 🔴 THIS TESTSET REPLACES ONE THAT ASSERTED THE OPPOSITE, and that is the point. The original
        # "SIZE, NOT DEPTH" test encoded OUR model — one budget for the whole term — and passed
        # happily while diverging from upstream on every multi-argument goal. The file even argued the
        # model at length, citing the C; the citation was to `pl-trie.c:768`'s GENERIC `from_depth=1`
        # rather than tabling's own `pl-tabling.c:2472` `{.from_depth = 2}`.
        #
        # These six rows are not our reasoning. They are what `swipl -q` printed via `current_table/2`
        # under `max_table_subgoal_size_action=abstract`. Reading the source is not reading the CALL
        # SITE; an executable oracle settled in one command what re-reading the C got wrong twice.
        f(x...) = Expression(Atom[x...])
        A, B, C = Sym(:a), Sym(:b), Sym(:c)
        isvar(x) = x isa Var

        # p(s(s(s(a)))) N=1 -> p(s(_))
        (g1, h1) = _AB.size_abstract(_ab_p(3), 1)
        @test h1
        arg = (g1::Expression).children[2]
        @test (arg::Expression).children[1] == Sym(:s)
        @test isvar((arg::Expression).children[2])          # ONE `s` kept, rest abstracted

        # q(f(a), g(b)) N=1 -> UNCHANGED  ← the row the old model failed
        q = f(Sym(:q), f(Sym(:f), A), f(Sym(:g), B))
        (g2, h2) = _AB.size_abstract(q, 1)
        @test !h2 && g2 == q

        # r(f(a), g(b), h(c)) N=1 -> UNCHANGED  ← and this one
        r = f(Sym(:r), f(Sym(:f), A), f(Sym(:g), B), f(Sym(:h), C))
        (g3, h3) = _AB.size_abstract(r, 1)
        @test !h3 && g3 == r

        # a1(f(g(a)), h(b)) N=1 -> a1(f(_), h(b))
        a1 = f(Sym(:a1), f(Sym(:f), f(Sym(:g), A)), f(Sym(:h), B))
        (g4, h4) = _AB.size_abstract(a1, 1)
        @test h4
        ch4 = (g4::Expression).children
        @test (ch4[2]::Expression).children[1] == Sym(:f)
        @test isvar((ch4[2]::Expression).children[2])        # f's argument abstracted…
        @test ch4[3] == f(Sym(:h), B)                        # …and the SECOND argument untouched

        # a2(f(g(h(a))), k(l(m(b)))) N=2 -> a2(f(g(_)), k(l(_)))  — budget of 2, RE-ARMED per argument
        a2 = f(Sym(:a2), f(Sym(:f), f(Sym(:g), f(Sym(:h), A))),
                         f(Sym(:k), f(Sym(:l), f(Sym(:m), B))))
        (g5, h5) = _AB.size_abstract(a2, 2)
        @test h5
        ch5 = (g5::Expression).children
        for (i, outer, inner) in ((2, :f, :g), (3, :k, :l))
            e = ch5[i]::Expression
            @test e.children[1] == Sym(outer)
            e2 = e.children[2]::Expression
            @test e2.children[1] == Sym(inner)
            @test isvar(e2.children[2])                      # both arguments kept TWO levels
        end

        # a3(s(s(s(s(a))))) N=2 -> a3(s(s(_)))
        (g6, h6) = _AB.size_abstract(_ab_p(4), 2)
        @test h6
        e = (g6::Expression).children[2]::Expression
        @test e.children[1] == Sym(:s)
        e2 = e.children[2]::Expression
        @test e2.children[1] == Sym(:s)
        @test isvar(e2.children[2])
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

    @testset "🔴🔴 IT OVER-APPROXIMATES, and the attempt to make it EXACT was UNSOUND" begin
        # 🔴 THIS TESTSET HAS NOW BEEN WRITTEN THREE TIMES, AND THE HISTORY IS THE LESSON.
        #   b98f581 — shipped over-approximating; this asserted the imprecision, deliberately.
        #   7425b7d — 7.A recorded each answer's goal INSTANCE, a filter was added, and this was
        #             flipped to assert EXACTNESS.
        #   TODAY   — an adversarial audit found the filter DROPS REAL ANSWERS, and it is reverted.
        #
        # The filter asked "did some instance that produced this answer unify with the call?" That is
        # NOT the same question as "does this answer hold for this call", and upstream only appears to
        # ask it because a Prolog answer IS a substitution over the goal skeleton. See the regression
        # testset below for the three-line program that proves the difference.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            s = Space(); load_core_stdlib!(s)
            load_metta!(s, raw"(= (d (s (s (s a)))) deep)" * "\n" *
                           raw"(= (d (s a)) shallow)" * "\n")
            _AB.table!(:d)
            exact = sort(String[string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                                for x in (y isa AbstractVector ? y : [y])])
            @test exact == ["deep"]

            _AB.untable_all!(); _AB.abolish_all_tables!()
            _AB.table_as!(:d, :subgoal_abstract => 1)
            approx = sort(String[string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                                 for x in (y isa AbstractVector ? y : [y])])
            @test "deep" in approx              # SOUND: the real answer is never lost…
            @test approx != exact               # …but it IS an over-approximation, not a filter
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴🔴 REGRESSION: the instance filter LOST an answer — three lines that prove it" begin
        # The exact program from the audit. The general table `(e (f $_v#1))` holds `v` with recorded
        # instance `(e (f a))`; the call is `(e (f (g (g a))))`, which does NOT unify with that
        # instance — yet `v` is CORRECT, because the call REDUCES into `(e (f a))` via the recursive
        # rule. Any future "precision" filter keyed on instance provenance fails here, which is why
        # this is pinned as its own testset rather than folded into the one above.
        _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        try
            prog = raw"(= (e (f a)) v)" * "\n" * raw"(= (e (f (g $x))) (e (f $x)))" * "\n"
            s = Space(); load_core_stdlib!(s); load_metta!(s, prog)
            _AB.table!(:e)
            base = String[string(x) for y in load_metta!(s, "!(e (f (g (g a))))\n")
                          for x in (y isa AbstractVector ? y : [y])]
            @test base == ["v"]                 # ANTI-VACUITY: the program really does answer

            _AB.untable_all!(); _AB.abolish_all_tables!()
            s2 = Space(); load_core_stdlib!(s2); load_metta!(s2, prog)
            _AB.table_as!(:e, :subgoal_abstract => 1)
            got = String[string(x) for y in load_metta!(s2, "!(e (f (g (g a))))\n")
                         for x in (y isa AbstractVector ? y : [y])]
            @test got == base                   # the restraint must not LOSE it (it did, until today)
        finally
            _AB.untable_all!(); _AB.abolish_all_tables!(); _AB.clear_subgoal_abstract!()
        end
    end

    @testset "instances are still RECORDED and variant-deduped — just not used as a filter" begin
        # 7.A's recording survives the filter's removal: it is cheap (+0.08% measured) and it is the
        # substrate that was promised. What is asserted here is the RECORDING contract, not any
        # answer-selection behaviour — `_abstract_instance_admits` has no caller on the answer path,
        # and its docstring says why a future caller must not treat `false` as "does not hold".
        t = _AB.AnswerTrie()
        @test _AB.trie_insert!(t, Sym(:deep))
        @test isempty(_AB.trie_instances(t, Sym(:deep)))       # empty = NOT RECORDED, never "none"

        inst = Expression(Atom[Sym(:d), _ab_s(1)])
        @test _AB.trie_record_instance!(t, Sym(:deep), inst)
        @test length(_AB.trie_instances(t, Sym(:deep))) == 1
        # variant-deduped, or a fixpoint re-deriving an answer grows this without bound
        @test !_AB.trie_record_instance!(t, Sym(:deep), inst)
        @test length(_AB.trie_instances(t, Sym(:deep))) == 1
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
