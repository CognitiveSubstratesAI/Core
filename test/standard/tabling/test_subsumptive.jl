# test_subsumptive.jl — SWI §7.5, call subsumption. `:- table p/1 as subsumptive`.
#
# Variant tabling gives `p(a)` and `p($x)` separate tables. Subsumptive tabling answers the more
# specific call FROM the more general table. A second LOOKUP MODE over the tables we already have.
#
# ⚠️ NOT WIRED. `tabled_eval` does not consult `subsumptive_answers` yet — this gates the lookup
# semantics standalone. A green file means subsumption is correct, NOT that tabling uses it.
# `[[feedback_report_green_against_the_arrow_not_the_test_list]]`
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _SB = Eval
_sb_p(x::Atom) = Expression(Atom[Sym(:p), x])
const _SB_X = Var("x", UInt64(1))
const _SB_Y = Var("y", UInt64(2))
const _SB_Z = Var("z", UInt64(3))

@testset "SWI §7.5 subsumptive tabling — the lookup mode" begin

    @testset "subsumes/2 is ONE-WAY, and a var→var binding does NOT break it" begin
        @test _SB.subsumes(_sb_p(_SB_X), _sb_p(Sym(:a)))    # general ⊒ specific
        @test !_SB.subsumes(_sb_p(Sym(:a)), _sb_p(_SB_X))    # …and NOT the other way
        @test !_SB.subsumes(_sb_p(Sym(:a)), _sb_p(Sym(:b)))  # unrelated ground terms
        @test _SB.subsumes(_sb_p(Sym(:a)), _sb_p(Sym(:a)))  # reflexive

        # 🔴 THE CASE THE FIRST IMPLEMENTATION GOT WRONG. `p($x)` and `p($y)` are mutual variants,
        # so each subsumes the other. Testing "did any of the call's variables become BOUND" says
        # NO — a var→var binding is a RENAMING, not an instantiation. Upstream's predicate is
        # `is_most_general_term(Vars)`: still distinct FREE VARIABLES.
        @test _SB.subsumes(_sb_p(_SB_X), _sb_p(_SB_Y))

        # …and the DISTINCTNESS half of that predicate: unifying `p($x,$x)` against `p($y,$z)`
        # leaves y and z free but COLLAPSED onto one variable, so the specific term is not
        # most-general and the stored key is the MORE specific of the two.
        pp(u, v) = Expression(Atom[Sym(:pp), u, v])
        @test !_SB.subsumes(pp(_SB_X, _SB_X), pp(_SB_Y, _SB_Z))
        @test _SB.subsumes(pp(_SB_X, _SB_Y), pp(Sym(:a), Sym(:b)))
    end

    @testset "more_general_table picks a subsumer, never the exact variant" begin
        _SB.abolish_all_tables!()
        gt = _SB.answer_trie_for(_SB._variant_rename(_sb_p(_SB_X)))
        for v in (Sym(:a), Sym(:b))
            _SB.trie_insert!(gt, _sb_p(v))
        end
        _SB.set_table_status!(gt, :complete)

        g = _SB.more_general_table(_sb_p(Sym(:a)))
        @test g !== nothing && g[1] == _SB._variant_rename(_sb_p(_SB_X))

        # ⚠️ AN EXACT TABLE FOR THE CALL MUST NOT BE RETURNED AS ITS OWN SUBSUMER. Upstream never
        # reaches more_general_table/2 with one present (the variant lookup already succeeded);
        # ours is callable directly, so it excludes the variant explicitly. Without that the
        # subsumptive path would shadow the ordinary one.
        _SB.answer_trie_for(_SB._variant_rename(_sb_p(Sym(:a))))
        g2 = _SB.more_general_table(_sb_p(Sym(:a)))
        @test g2 !== nothing && g2[1] == _SB._variant_rename(_sb_p(_SB_X))

        @test _SB.more_general_table(Expression(Atom[Sym(:zz), Sym(:a)])) === nothing
        _SB.abolish_all_tables!()
    end

    @testset "subsumptive_answers filters the general table" begin
        _SB.abolish_all_tables!()
        gt = _SB.answer_trie_for(_SB._variant_rename(_sb_p(_SB_X)))
        for v in (Sym(:a), Sym(:b), Sym(:c))
            _SB.trie_insert!(gt, _sb_p(v))
        end
        _SB.set_table_status!(gt, :complete)

        @test String[string(a) for a in _SB.subsumptive_answers(_sb_p(Sym(:a)))] ==
            ["(p a)"]
        @test String[string(a) for a in _SB.subsumptive_answers(_sb_p(Sym(:b)))] ==
            ["(p b)"]
        # a call with NO subsuming table ⇒ `nothing` = FALL THROUGH to ordinary tabling, which is a
        # different answer from an empty vector (= general table exists and genuinely has no match).
        @test _SB.subsumptive_answers(Expression(Atom[Sym(:zz), Sym(:a)])) === nothing
        @test _SB.subsumptive_answers(_sb_p(Sym(:zzz))) == Atom[]
        _SB.abolish_all_tables!()
    end

    @testset "🔴 an INCOMPLETE general table must NOT be used" begin
        # Upstream's subsumptive clause requires `'$tbl_table_status'(ATrie, complete, ...)`. An
        # incomplete table's answers are still arriving, so filtering a partial set would silently
        # UNDER-ANSWER — the worst failure mode available here, because it looks like a valid answer.
        _SB.abolish_all_tables!()
        t = _SB.answer_trie_for(_SB._variant_rename(_sb_p(_SB_X)))
        for v in (Sym(:a), Sym(:b))
            _SB.trie_insert!(t, _sb_p(v))
        end
        @test _SB.table_status(t) == :fresh
        @test _SB.subsumptive_answers(_sb_p(Sym(:a))) === nothing      # fall through, do not use it

        _SB.set_table_status!(t, :complete)
        @test String[string(a) for a in _SB.subsumptive_answers(_sb_p(Sym(:a)))] ==
            ["(p a)"]
        _SB.abolish_all_tables!()
    end

    @testset "the declaration surface is per-PREDICATE" begin
        _SB.clear_subsumptive!()
        @test !_SB.is_subsumptive(:p)
        _SB.table_subsumptive!(:p)
        @test _SB.is_subsumptive(:p) && !_SB.is_subsumptive(:q)
        _SB.untable_subsumptive!(:p)
        @test !_SB.is_subsumptive(:p)
        _SB.clear_subsumptive!()
    end
end

@testset "🔴🔴 §7.5 LOST EVERY ANSWER OF A VALUE TABLE — measured, fixed 2026-08-18" begin
    # The existing testsets above hand-insert GOAL-SHAPED answers like `(p a)`, which is a shape the
    # live mirror never produces — and that is exactly how this survived. A real table stores VALUES.
    #
    # MEASURED before the fix, on the warm server:
    #     (= (f a) 1)  (= (f b) 2)   table!(:f)   driven by !(f $z)
    #     more_general_table((f a))  = (f $_v#1)      answers ["1", "2"]
    #     subsumptive_answers((f a)) = Atom[]          ← upstream gives 1
    # `Atom[]` is LOADED: this function's own contract says empty means "a complete general table
    # exists and genuinely has no answer matching this call". It was a WRONG ANSWER, not a slow path.
    #
    # CAUSE: it unified the ANSWER against the GOAL. Upstream can — a Prolog answer IS a substitution
    # over the goal skeleton — but `1` never unifies with `(f a)`. The THIRD ASSUMPTION, third time.
    _SB.untable_all!()
    _SB.abolish_all_tables!()
    try
        s = Space()
        load_core_stdlib!(s)
        load_metta!(s, raw"(= (f a) 1)" * "\n" * raw"(= (f b) 2)" * "\n")
        _SB.table!(:f)
        load_metta!(s, raw"!(f $z)" * "\n")               # drive the GENERAL variant
        goal = _SB.parse_from(_SB.tokenize("(f a)"), Ref(1), s.tokens)

        g = _SB.more_general_table(goal)
        @test g !== nothing                                # ANTI-VACUITY: the general table exists…
        @test length(_SB.trie_answers(g[2])) == 2          # …and really holds two VALUES

        got = _SB.subsumptive_answers(goal)
        @test got !== nothing
        @test !isempty(got)                                # the defect: this was Atom[]
        @test Grounded(1) in got                           # …and the right answer is present

        # 🔑 GATED PRECISION, reusing §7.11.1's soundness gate rather than repeating its mistake.
        # `f` is facts-only, so it cannot reduce into itself, so filtering by the recorded INSTANCE
        # is sound — and exact.
        exact = _SB.subsumptive_answers(goal, s)
        @test exact == Atom[Grounded(1)]                   # EXACT, as upstream
    finally
        _SB.untable_all!()
        _SB.abolish_all_tables!()
    end
end

@testset "…and a REDUCING head stays coarse rather than losing an answer" begin
    # The gate must refuse to filter where the instance is meaningless. `e` reduces into itself, so
    # a recorded instance is the goal AT THE POINT THE RULE MATCHED, not the call — the exact
    # reasoning that made the §7.11.1 filter drop answers before it was gated.
    s = Space()
    load_core_stdlib!(s)
    load_metta!(s, raw"(= (e (f a)) v)" * "\n" * raw"(= (e (f (g $x))) (e (f $x)))" * "\n")
    sr = _SB._self_reaching_heads(_SB.all_atoms(s))
    @test :e in sr                                         # detected as reducing ⇒ filter OFF
end
