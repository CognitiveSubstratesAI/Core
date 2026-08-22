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

# 🔴 EVERY TEST BELOW SETS `max_table_subgoal_size_action` EXPLICITLY, and that is deliberate.
# SWI's default is `error`: `:- table p/1 as subgoal_abstract(1)` RAISES on an oversized goal rather
# than abstracting (verified on live swipl 10.1.12), and our port matches that default since
# 2026-08-18. The oracle script had to set the same flag to observe abstraction at all — so a test
# that did NOT set it would be testing a different configuration from the one it is differentialled
# against, which is the failure this comment exists to prevent.
_ab_abstract_mode!() = _AB.set_max_table_subgoal_size_action!(_AB.TW_ABSTRACT)
_ab_strict_mode!() = _AB.set_max_table_subgoal_size_action!(_AB.TW_ERROR)

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
        t = Expression(
            Atom[Sym(:q),
                Expression(Atom[Sym(:f), Sym(:a)]),
                Expression(Atom[Sym(:g), Sym(:b)])]
        )
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
        _AB.untable_all!()
        _AB.clear_subgoal_abstract!()
        @test _AB.subgoal_abstract_for(:p) == _AB.NO_RESTRAINT
        _ab_abstract_mode!()
        o = _AB.table_as!(:p, :subgoal_abstract => 2)          # no longer REFUSED — §7.11.1 is built
        @test o.subgoal_abstract == 2
        @test _AB.subgoal_abstract_for(:p) == 2

        # `restraint/4`: a NEGATIVE value REMOVES the restraint. Same convention as `max_answers`,
        # asserted here so the two cannot drift apart.
        _ab_abstract_mode!()
        _AB.table_as!(:p, :subgoal_abstract => -1)
        @test _AB.subgoal_abstract_for(:p) == _AB.NO_RESTRAINT
        _AB.untable_all!()
        _AB.clear_subgoal_abstract!()
    end

    @testset "🔴 END TO END — the abstracted call is ANSWERED, and from the GENERAL table" begin
        # ANTI-VACUITY IS THE WHOLE PROBLEM HERE. A restraint that silently did nothing would still
        # produce the right answers, because the unabstracted program produces them too. So this
        # asserts BOTH halves: the answers are right, AND the table that holds them is the GENERAL
        # one — i.e. the specific variant key was never tabled.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, raw"(= (depth $x) ok)" * "\n")
            _ab_abstract_mode!()
            _AB.table_as!(:depth, :subgoal_abstract => 1)

            r = String[
                string(x) for y in load_metta!(s, "!(depth (s (s (s a))))\n")
                for x in (y isa AbstractVector ? y : [y])
            ]
            @test r == ["ok"]                                   # …answered correctly

            keys_tabled = collect(keys(_AB._ANSWER_TABLE))
            @test !isempty(keys_tabled)                         # anti-vacuity: something WAS tabled
            # the SPECIFIC goal must NOT have its own table — that is the restraint working
            specific = _AB._variant_rename(_ab_p(3))
            @test !(specific in keys_tabled)
        finally
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴 THE TABLE SET STAYS BOUNDED — the point of the feature, measured" begin
        # Without abstraction, N calls over a growing term make N tables. With it they collapse onto
        # the general one. Asserting the COUNT is what distinguishes "it ran" from "it restrained":
        # every other assertion in this file passes on an implementation that abstracts nothing.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, raw"(= (grow $x) ok)" * "\n")

            # baseline: no restraint ⇒ a table per distinct goal
            _AB.table!(:grow)
            for n in 1:6
                load_metta!(s, "!(grow $(_ab_s(n)))\n")
            end
            unrestrained = length(_AB._ANSWER_TABLE)
            @test unrestrained >= 6

            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _ab_abstract_mode!()
            _AB.table_as!(:grow, :subgoal_abstract => 1)
            for n in 1:6
                load_metta!(s, "!(grow $(_ab_s(n)))\n")
            end
            restrained = length(_AB._ANSWER_TABLE)

            @test restrained < unrestrained                     # …genuinely fewer
            @test restrained <= 3                               # …and BOUNDED, not merely smaller
        finally
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴🔴 THE BOUNDARY: exact when the answer MENTIONS the abstracted variable" begin
        # Upstream specialises by unifying the answer SKELETON against the specific call, because a
        # Prolog answer IS a substitution over that skeleton. A MeTTa answer is a VALUE. What we can
        # still recover is the ABSTRACTION BINDING — `gen` came FROM `red`, so matching them back
        # says what the fresh variables stood for. When the answer mentions them, that is EXACT.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, raw"(= (peel (s $x)) (found $x))" * "\n")
            _ab_abstract_mode!()
            _AB.table_as!(:peel, :subgoal_abstract => 1)
            r = String[
                string(x) for y in load_metta!(s, "!(peel (s (s (s a))))\n")
                for x in (y isa AbstractVector ? y : [y])
            ]
            # the abstracted subterm comes BACK — not `(found $_sa1)`, and not the general answer
            @test r == ["(found (s (s a)))"]
        finally
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
        end
    end

    @testset "🔴🔴 PRECISION IS GATED ON THE CALL GRAPH — exact when sound, coarse when not" begin
        # 🔴 THIS TESTSET HAS BEEN WRITTEN FOUR TIMES, and the sequence is the whole lesson:
        #   b98f581 — shipped over-approximating; asserted the imprecision deliberately.
        #   7425b7d — an instance filter was added and this was flipped to assert EXACTNESS.
        #   58f434e — the filter was found to LOSE ANSWERS; reverted, back to over-approximating.
        #   NOW     — a `println` trace of one instance showed WHY, and the fix is a GATE, not a
        #             retreat: the filter is exact on a head that cannot reduce into itself, and
        #             meaningless on one that can, because the recorded instance is the goal AT THE
        #             POINT THE RULE MATCHED — a REDUCED term, not the call.
        #
        # `d` here is NON-REDUCING (both rules are facts), so `_self_reaching_heads` clears it and the
        # filter runs: the result is EXACT. The reducing counterpart is the testset below, which must
        # stay coarse — and must not lose its answer.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            s = Space()
            load_core_stdlib!(s)
            load_metta!(
                s,
                raw"(= (d (s (s (s a)))) deep)" * "\n" *
                raw"(= (d (s a)) shallow)" * "\n"
            )
            _AB.table!(:d)
            exact = sort(
                String[
                    string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                    for x in (y isa AbstractVector ? y : [y])
                ]
            )
            @test exact == ["deep"]

            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _ab_abstract_mode!()
            _AB.table_as!(:d, :subgoal_abstract => 1)
            got = sort(
                String[
                    string(x) for y in load_metta!(s, "!(d (s (s (s a))))\n")
                    for x in (y isa AbstractVector ? y : [y])
                ]
            )
            @test got == exact                  # EXACT — the restraint costs no precision here
            @test !("shallow" in got)           # …and this is what the coarse version let through
        finally
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
        end
    end

    @testset "the GATE itself — `_self_reaching_heads` is what separates the two cases" begin
        # Asserting the gate directly, so a future change to the call-graph analysis cannot silently
        # re-enable the filter on a reducing head (which is the unsound direction).
        s = Space()
        load_core_stdlib!(s)
        load_metta!(
            s,
            raw"(= (d (s a)) shallow)" * "\n" *
            raw"(= (e (f a)) v)" * "\n" *
            raw"(= (e (f (g $x))) (e (f $x)))" * "\n" *
            raw"(= (m1) (m2))" * "\n" * raw"(= (m2) (m1))" * "\n"
        )
        sr = _AB._self_reaching_heads(_AB.all_atoms(s))
        @test !(:d in sr)                       # facts only ⇒ cannot reduce into itself
        @test :e in sr                          # directly recursive
        @test :m1 in sr && :m2 in sr            # MUTUAL recursion must be caught too
    end

    @testset "🔴🔴 REGRESSION: the instance filter LOST an answer — three lines that prove it" begin
        # The exact program from the audit. The general table `(e (f $_v#1))` holds `v` with recorded
        # instance `(e (f a))`; the call is `(e (f (g (g a))))`, which does NOT unify with that
        # instance — yet `v` is CORRECT, because the call REDUCES into `(e (f a))` via the recursive
        # rule. Any future "precision" filter keyed on instance provenance fails here, which is why
        # this is pinned as its own testset rather than folded into the one above.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            prog = raw"(= (e (f a)) v)" * "\n" * raw"(= (e (f (g $x))) (e (f $x)))" * "\n"
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, prog)
            _AB.table!(:e)
            base = String[
                string(x) for y in load_metta!(s, "!(e (f (g (g a))))\n")
                for x in (y isa AbstractVector ? y : [y])
            ]
            @test base == ["v"]                 # ANTI-VACUITY: the program really does answer

            _AB.untable_all!()
            _AB.abolish_all_tables!()
            s2 = Space()
            load_core_stdlib!(s2)
            load_metta!(s2, prog)
            _ab_abstract_mode!()
            _AB.table_as!(:e, :subgoal_abstract => 1)
            got = String[
                string(x) for y in load_metta!(s2, "!(e (f (g (g a))))\n")
                for x in (y isa AbstractVector ? y : [y])
            ]
            @test got == base                   # the restraint must not LOSE it (it did, until today)
        finally
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
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

    @testset "🔴🔴 THE DEFAULT ACTION IS `error`, NOT `abstract` — as SWI, verified against it" begin
        # `subgoal_abstract(N)` does NOT mean "abstract" in SWI. It means "bound the subgoal size",
        # and the default disposition of that bound is to REFUSE THE PROGRAM:
        #     ?- current_prolog_flag(max_table_subgoal_size_action, A).   A = error.
        #     ?- p(s(s(s(a)))).   ERROR: resource_error(tripwire(max_table_subgoal_size, user:p(_)))
        # We abstracted unconditionally until 2026-08-18 — silently doing what SWI refuses to do,
        # which is the worst kind of divergence because the program appears to work.
        _AB.untable_all!()
        _AB.abolish_all_tables!()
        _AB.clear_subgoal_abstract!()
        try
            _ab_strict_mode!()
            @test _AB.max_table_subgoal_size_action() == _AB.TW_ERROR      # OUR default, unset
            s = Space()
            load_core_stdlib!(s)
            load_metta!(s, raw"(= (depth $x) ok)" * "\n")
            _AB.table_as!(:depth, :subgoal_abstract => 1)
            # a goal WITHIN the bound is untouched and must NOT trip anything
            (small, hit_small) = _AB.abstract_subgoal(
                _AB.parse_from(_AB.tokenize("(depth (s a))"), Ref(1), s.tokens))
            @test !hit_small
            # …and one OVER the bound raises, naming the tripwire, instead of abstracting
            big = _AB.parse_from(_AB.tokenize("(depth (s (s (s a))))"), Ref(1), s.tokens)
            @test_throws ArgumentError _AB.abstract_subgoal(big)

            # WARNING retries UNABSTRACTED — upstream's `sa.size = -1; goto retry`, easy to miss
            _AB.set_max_table_subgoal_size_action!(_AB.TW_WARNING)
            (g, hit) = _AB.abstract_subgoal(big)
            @test !hit && g == big            # the FULL goal is tabled, not the abstracted one

            _ab_abstract_mode!()
            (g2, hit2) = _AB.abstract_subgoal(big)
            @test hit2 && g2 != big           # only TW_ABSTRACT actually abstracts
        finally
            _ab_abstract_mode!()
            _AB.untable_all!()
            _AB.abolish_all_tables!()
            _AB.clear_subgoal_abstract!()
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

# ═════════════════════════════════════════════════════════════════════════════════════════════════
# §7.11.2 — ANSWER ABSTRACTION, `answer_abstract(N)`.
# ═════════════════════════════════════════════════════════════════════════════════════════════════
#
# 🔴 WHAT THIS BLOCK EXISTS TO CATCH IS AN INERT RESTRAINT, NOT A WRONG ANSWER SET. §7.11.2 only ever
# REMOVES or GENERALISES answers, so on a program that never blows the budget a completely dead
# implementation returns exactly the right answers — and on one that does, `warning` and
# `bounded_rationality` return the SAME ANSWER SET and differ only in a truth value. Every assertion
# below is therefore keyed to something an inert or half-built restraint gets WRONG: which TERM was
# stored, and whether it is CONDITIONAL.
#
# 📏 Every expectation is a row measured on live swipl 10.1.12 via `library(tables)`'s own readers
# (`get_returns_and_tvs/3`, `get_returns_and_dls/3`) — not derived from the C.

# the two flags this section needs, saved/restored so a failure cannot leak into the §7.11.1 block
_aa_answer_action!(a) = _AB.set_max_table_answer_size_action!(a)
_aa_reset!() = (_AB.clear_answer_abstract!(); _AB.clear_answer_delays!();
    _AB.clear_all_restraints!(); _AB.clear_answer_count_restraints!();
    _AB.set_max_table_answer_size!(-1);
    _AB.set_max_table_answer_size_action!(_AB.TW_ERROR))

# a branching answer: f(g(h(a)), k(l(m(b)))) — the shape a depth-limit implementation gets wrong
_aa_branch() = Expression(
    Atom[Sym(:f),
        Expression(Atom[Sym(:g), Expression(Atom[Sym(:h), Sym(:a)])]),
        Expression(
            Atom[Sym(:k), Expression(Atom[Sym(:l), Expression(Atom[Sym(:m), Sym(:b)])])]
        )]
)

@testset "SWI §7.11.2 — answer abstraction" begin

    @testset "the SIZE RULE is `size_abstract` unchanged — 7 rows against a live swipl oracle" begin
        # 🔴 THE TWO SIDES KEEP DIFFERENT AMOUNTS FOR THE SAME N, and this is the assertion that
        # pins it. The subgoal trie is keyed on `Module:Goal`, the answer trie on `ret(A1..An)`; with
        # the same `{.from_depth = 2}` the walk arms one level shallower on the answer side. So:
        #     p(s(s(s(a)))) as a GOAL,    subgoal_abstract(1) -> p(s(_))
        #     s(s(s(a)))    as an ANSWER, answer_abstract(1)  ->   s(s(_))
        # Our `size_abstract` frees the top functor and re-arms per ARGUMENT, which is exactly the
        # `ret(V)` walk — so the answer side reuses it verbatim. An implementation that "corrected"
        # for the missing wrapper would be off by one on every row here.
        chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
        c4 = chain(4)                                                # s(s(s(s(a))))

        (g0, h0) = _AB.answer_size_abstract(c4, 0)                   # oracle: s(_)
        @test h0 && g0 isa Expression
        @test (g0::Expression).children[1] == Sym(:s)
        @test (g0::Expression).children[2] isa Var

        (g1, h1) = _AB.answer_size_abstract(c4, 1)                   # oracle: s(s(_))
        @test h1
        a1 = (g1::Expression).children[2]
        @test a1 isa Expression && (a1::Expression).children[2] isa Var

        (g2, h2) = _AB.answer_size_abstract(c4, 2)                   # oracle: s(s(s(_)))
        @test h2
        a2 = ((g2::Expression).children[2]::Expression).children[2]
        @test a2 isa Expression && (a2::Expression).children[2] isa Var

        # 🔴 THE LOAD-BEARING ROW: N=3 does NOT abstract, so nothing downstream may fire. A restraint
        # that marked the whole table, or abstracted "just to be safe", fails right here.
        (g3, h3) = _AB.answer_size_abstract(c4, 3)                   # oracle: UNCHANGED, tv=t
        @test !h3 && g3 == c4

        # branching, N=1: BOTH arguments get their own budget (upstream re-arms at each `Ai`'s args)
        (b1, hb1) = _AB.answer_size_abstract(_aa_branch(), 1)        # oracle: f(g(_), k(_))
        @test hb1
        bc = (b1::Expression).children
        @test (bc[2]::Expression).children[1] == Sym(:g) &&
            (bc[2]::Expression).children[2] isa Var
        @test (bc[3]::Expression).children[1] == Sym(:k) &&
            (bc[3]::Expression).children[2] isa Var

        # branching, N=2: the SHALLOWER argument survives whole, the deeper one is cut. A single
        # shared budget would have spent it all on the first argument and abstracted the second.
        (b2, hb2) = _AB.answer_size_abstract(_aa_branch(), 2)        # oracle: f(g(h(a)), k(l(_)))
        @test hb2
        bc2 = (b2::Expression).children
        @test bc2[2] == (_aa_branch()::Expression).children[2]       # g(h(a)) UNTOUCHED
        k2 = bc2[3]::Expression
        @test (k2.children[2]::Expression).children[2] isa Var       # k(l(_))

        # a non-compound answer has nothing to abstract, at any N
        (ga, ha) = _AB.answer_size_abstract(Sym(:plainatom), 1)      # oracle: UNCHANGED, tv=t
        @test !ha && ga == Sym(:plainatom)
    end

    @testset "🔴🔴 ANTI-VACUITY — the STORED TERM is the generalised one, and it is CONDITIONAL" begin
        # THE ASSERTION AN INERT RESTRAINT CANNOT SURVIVE. Measured on live swipl 10.1.12:
        #     :- table p/1 as answer_abstract(1).  q(s(s(s(a)))).  q(s(a)).  p(X) :- q(X).
        #     get_returns_and_tvs -> ret(s(s(_))) tv=u    ret(s(a)) tv=t
        #     get_returns_and_dls -> ret(s(s(_))) dl=[[radial_restraint]]   ret(s(a)) dl=[]
        # Two independent things must hold and BOTH fail if the restraint does nothing:
        #   (a) the big answer is NOT in the table — its GENERALISATION is;
        #   (b) that generalisation is UNDEFINED, with `radial_restraint` as the reason.
        _aa_reset!()
        try
            chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
            big, small = chain(3), chain(1)
            _aa_answer_action!(_AB.TW_BOUNDED_RATIONALITY)
            _AB.answer_abstract!(:p, 1)
            t = _AB.AnswerTrie()
            r_big = _AB.trie_insert_answer_restrained!(t, :p, big)
            r_small = _AB.trie_insert_answer_restrained!(t, :p, small)

            # (a) THE ORIGINAL ANSWER IS ABSENT. This is the assertion that fails when the restraint
            # is inert: an implementation that stored `big` unchanged returns the same ANSWER SET
            # as a correct one on every query that only looks at answers.
            @test !_AB.trie_contains(t, big)
            @test _AB.answer_truth_value(t, big) == :none
            @test r_big.abstracted && r_big.disposition === :conditional
            stored = r_big.stored
            @test stored !== nothing
            @test stored != big
            # …and it really is `s(s($_))`: the functor survived, the third `s` became a variable
            @test (stored::Expression).children[1] == Sym(:s)
            inner = (stored::Expression).children[2]::Expression
            @test inner.children[1] == Sym(:s) && inner.children[2] isa Var

            # (b) IT IS CONDITIONAL, AND THE REASON IS UPSTREAM'S. `dnf_residual` renders our DNF the
            # way `get_returns_and_dls/3` renders theirs, so this compares against `[[radial_restraint]]`
            # rather than against our own spelling of it.
            @test _AB.answer_is_conditional(t, stored::Atom)
            @test _AB.answer_truth_value(t, stored::Atom) == :u
            @test _AB.answer_residual_in(t, stored::Atom) == Sym(:radial_restraint)
            dnf = _AB.answer_delays(t, stored::Atom)
            @test length(dnf) == 1 && length(dnf[1]) == 1            # ONE disjunct, ONE conjunct
            @test dnf[1][1].kind == _AB.DELAY_POSITIVE               # positive, as measured upstream

            # …and the answer that FIT the budget is untouched and UNCONDITIONAL. Without this the
            # test would pass for an implementation that marked the whole table approximate.
            @test r_small.abstracted == false && r_small.disposition === :none
            @test _AB.trie_contains(t, small)
            @test _AB.answer_truth_value(t, small) == :t
            @test _AB.answer_residual_in(t, small) == Sym("True")
            @test isempty(_AB.answer_delays(t, small))
        finally
            _aa_reset!()
        end
    end

    @testset "🔴 the ACTION FLAG — default `error`, and `warning` ≠ `bounded_rationality`" begin
        # The four dispositions, each measured. `warning` and `bounded_rationality` STORE THE SAME
        # TERM and differ only in the truth value — which is precisely why the anti-vacuity assertion
        # above had to be about conditionality and not about the answer set.
        chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
        big, small = chain(3), chain(1)
        _aa_run(act) = begin
            _aa_reset!()
            _aa_answer_action!(act)
            _AB.answer_abstract!(:p, 1)
            t = _AB.AnswerTrie()
            r = _AB.trie_insert_answer_restrained!(t, :p, big)
            _AB.trie_insert_answer_restrained!(t, :p, small)
            (t, r)
        end

        _aa_reset!()
        try
            # DEFAULT IS `error`, exactly as SWI (`pl-tabling.c:9341`), and it RAISES. Our port
            # would be silently more permissive than the reference if this defaulted to storing.
            @test _AB.max_table_answer_size_action() == _AB.TW_ERROR
            _AB.answer_abstract!(:p, 1)
            @test_throws ArgumentError _AB.trie_insert_answer_restrained!(
                _AB.AnswerTrie(), :p, big
            )

            # `fail`: the oversized answer is DROPPED — under-approximates, sound the other way.
            (tf, rf) = _aa_run(_AB.TW_FAIL)
            @test rf.disposition === :drop && !rf.added && rf.stored === nothing
            @test length(_AB.trie_answers(tf)) == 1 && _AB.trie_contains(tf, small)

            # `warning`: STORES THE GENERALISED ANSWER, UNCONDITIONALLY. 🔴 And note the divergence
            # from its §7.11.1 sibling, where `warning` RETRIES UNABSTRACTED and tables the FULL
            # goal (`sa.size = -1; goto retry`, pl-tabling.c:2519). There is no retry here.
            (tw, rw) = (@test_logs (:warn,) match_mode=:any _aa_run(_AB.TW_WARNING))
            @test rw.disposition === :store && rw.added && rw.stored !== nothing
            @test rw.stored != big
            @test _AB.answer_truth_value(tw, rw.stored::Atom) == :t          # ← UNCONDITIONAL
            @test !_AB.answer_is_conditional(tw, rw.stored::Atom)

            # `bounded_rationality`: same stored term, tv=`u`. THE DISCRIMINATOR.
            (tb, rb) = _aa_run(_AB.TW_BOUNDED_RATIONALITY)
            @test rb.stored !== nothing
            @test _AB.variant_eq(rb.stored::Atom, rw.stored::Atom)           # SAME TERM as `warning`…
            @test _AB.answer_truth_value(tb, rb.stored::Atom) == :u          # …DIFFERENT truth value

            # `abstract` is a DOMAIN ERROR for this flag and legal for the subgoal one
            # (`pl-tabling.c:8871-8877`). Verified upstream:
            #     ?- set_prolog_flag(max_table_answer_size_action, abstract).
            #     ERROR: domain_error(restraint_action, abstract)
            @test_throws ArgumentError _AB.set_max_table_answer_size_action!(
                _AB.TW_ABSTRACT
            )
            @test _AB.max_table_subgoal_size_action() isa _AB.TripwireAction  # …and it IS legal there
            _AB.set_max_table_subgoal_size_action!(_AB.TW_ABSTRACT)           # no throw
        finally
            _aa_reset!()
            _ab_abstract_mode!()
        end
    end

    @testset "the GLOBAL flag, and its fallback shape (NOT §7.11.3's)" begin
        # `pred_max_table_answer_size` (`pl-tabling.c:3563-3572`) DELEGATES to the global flag when
        # the predicate has none. §7.11.3's `tripwire_answers_for_subgoal` SHORT-CIRCUITS instead — a
        # per-predicate `max_answers` suppresses the global bound entirely. Two restraints, forty
        # lines apart upstream, with genuinely different composition; collapsing them would silently
        # change which predicates a global bound reaches.
        _aa_reset!()
        try
            @test _AB.answer_abstract_for(:zz) == _AB.NO_RESTRAINT
            _AB.set_max_table_answer_size!(1)
            @test _AB.answer_abstract_for(:zz) == 1              # DELEGATES — no per-predicate value
            _AB.answer_abstract!(:zz, 3)
            @test _AB.answer_abstract_for(:zz) == 3              # per-predicate OVERRIDES
            # `restraint/4`: a NEGATIVE value REMOVES rather than stores, on both levels
            _AB.answer_abstract!(:zz, -1)
            @test _AB.answer_abstract_for(:zz) == 1              # …back to the global
            _AB.set_max_table_answer_size!(-1)
            @test _AB.answer_abstract_for(:zz) == _AB.NO_RESTRAINT
            # NO_RESTRAINT must abstract NOTHING, or the restraint is on by default
            (g, h) = _AB.answer_size_abstract(_aa_branch(), _AB.answer_abstract_for(:zz))
            @test !h && g == _aa_branch()
        finally
            _aa_reset!()
        end
    end

    @testset "🔴 `true ∨ C = true` — an unconditional derivation WINS, in EITHER order" begin
        # `update_delay_list` (`pl-tabling.c:1127-1136`) destroys an answer's `delay_info` when a
        # derivation arrives with an empty delay list ("Unconditional answer after conditional"), and
        # the duplicate path (`:3618-3628`) only merges INTO an answer that is already conditional.
        # Both halves say the same thing: an answer with ANY unconditional derivation is `t`.
        #
        # MEASURED on live swipl 10.1.12, both clause orders, `answer_abstract(1)`:
        #     q(s(s(_))). q(s(s(s(a)))).   -> ret(s(s(_))) tv=t
        #     q(s(s(s(a)))). q(s(s(_))).   -> ret(s(s(_))) tv=t
        #
        # 🔴 THE FIRST WORKING VERSION FAILED BOTH ORDERS, in opposite ways — it demoted an
        # unconditional answer to `u`, and it left a conditional one at `u` after an unconditional
        # re-derivation. The rule was written into `answer_is_conditional`'s docstring and simply not
        # implemented; a probe caught it, the docstring could not.
        _aa_reset!()
        try
            chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
            big = chain(3)                                          # abstracts to (s (s $_))
            uncond = Expression(Atom[Sym(:s), Expression(Atom[Sym(:s), _AB.freshvar("u")])])
            _aa_answer_action!(_AB.TW_BOUNDED_RATIONALITY)
            _AB.answer_abstract!(:p, 1)

            # order A: UNCONDITIONAL first, then the abstracted derivation of the same variant
            tA = _AB.AnswerTrie()
            _AB.trie_insert_answer_restrained!(tA, :p, uncond)
            @test _AB.answer_truth_value(tA, uncond) == :t
            rA = _AB.trie_insert_answer_restrained!(tA, :p, big)
            @test rA.abstracted && rA.count_action === :duplicate    # it IS the same variant
            @test _AB.answer_truth_value(tA, uncond) == :t           # …and it STAYS unconditional
            @test length(_AB.trie_answers(tA)) == 1

            # order B: the abstracted (conditional) derivation first, then an unconditional one
            tB = _AB.AnswerTrie()
            rB = _AB.trie_insert_answer_restrained!(tB, :p, big)
            @test _AB.answer_truth_value(tB, rB.stored::Atom) == :u  # conditional to begin with
            _AB.trie_insert_answer_restrained!(tB, :p, uncond)
            @test _AB.answer_truth_value(tB, rB.stored::Atom) == :t  # …CLEARED by the unconditional
            @test isempty(_AB.answer_delays(tB, rB.stored::Atom))
            @test length(_AB.trie_answers(tB)) == 1
        finally
            _aa_reset!()
        end
    end

    @testset "two conditional derivations of one answer DISJOIN — they are not two answers" begin
        # `delay_info` holds a BUFFER of `delay_set`s (`pl-tabling.h:179-184`): several derivations of
        # one answer contribute ALTERNATIVE conjunctions to one record. `Tabling.jl`'s
        # `merge_bottom_into!` docstring makes the same point about the value-level bottom, where
        # getting it wrong produced two `undefined` answers where one was correct.
        _aa_reset!()
        try
            chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
            _aa_answer_action!(_AB.TW_BOUNDED_RATIONALITY)
            _AB.answer_abstract!(:p, 1)
            t = _AB.AnswerTrie()
            r1 = _AB.trie_insert_answer_restrained!(t, :p, chain(3))   # -> (s (s $_))
            r2 = _AB.trie_insert_answer_restrained!(t, :p, chain(4))   # -> (s (s $_)) again
            @test r2.count_action === :duplicate
            @test length(_AB.trie_answers(t)) == 1                     # ONE answer, not two
            # `dnf_or` drops the repeated conjunction (`C ∨ C = C`), so the residual stays a single
            # `radial_restraint` rather than accumulating one disjunct per derivation.
            @test length(_AB.answer_delays(t, r1.stored::Atom)) == 1
            @test _AB.answer_residual_in(t, r1.stored::Atom) == Sym(:radial_restraint)
        finally
            _aa_reset!()
        end
    end

    @testset "the VALUE-level bottom and the NODE-level condition are DIFFERENT carriers" begin
        # 🔴 THE QUESTION THAT BLOCKED THIS FEATURE, ASSERTED RATHER THAN ARGUED. `Options.jl` refused
        # `answer_abstract` for needing delay lists; delay lists landed, and the premise turned out to
        # be half right in the half that matters. `undefined_with(dnf)` builds an atom that CARRIES a
        # condition and HAS NO VALUE — substituting it for the generalised answer would store "some-
        # thing here is undefined" instead of "(s (s $_)) holds conditionally", discarding the
        # generalisation, which IS the feature. So conditionality had to go on the NODE, where
        # upstream has always kept it (`delay_info` on `trie_node`, `pl-tabling.h:179-184`).
        _aa_reset!()
        try
            chain(n) = n == 0 ? Sym(:a) : Expression(Atom[Sym(:s), chain(n - 1)])
            _aa_answer_action!(_AB.TW_BOUNDED_RATIONALITY)
            _AB.answer_abstract!(:p, 1)
            t = _AB.AnswerTrie()
            r = _AB.trie_insert_answer_restrained!(t, :p, chain(3))
            stored = r.stored::Atom

            # NODE-level: the stored answer is a real VALUE, not a bottom — that is the whole point.
            @test !_AB.is_undefined(stored)
            @test _AB.answer_truth_value(t, stored) == :u
            @test isempty(_AB.delays_of(stored))      # the VALUE carries nothing…
            @test !isempty(_AB.answer_delays(t, stored))   # …the NODE carries the condition

            # VALUE-level: a WFS bottom stored as an answer reports `:u` through the SAME reader,
            # from its own DNF. A consumer never has to know which carrier applied.
            und = _AB.undefined_with(
                _AB.DelayDNF([_AB.DelaySet([_AB.delay_negative(Sym(:g))])])
            )
            @test _AB.trie_insert!(t, und)
            @test _AB.answer_truth_value(t, und) == :u
            @test _AB.answer_residual_in(t, und) == Expression(Atom[Sym(:not), Sym(:g)])
            # …and it is NOT in the node-level table, so the two never shadow each other
            @test isempty(
                get(_AB._ANSWER_DELAYS, _AB.trie_lookup!(t, und, false), _AB.DelayDNF())
            )
        finally
            _aa_reset!()
        end
    end
end
