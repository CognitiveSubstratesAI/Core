# test_restraints.jl — SWI §7.11.3 `max_answers`, differentialled against a LIVE SWI-Prolog.
#
# ─── WHY THE ORACLE EARNS ITS KEEP HERE ──────────────────────────────────────────────────────────
# This file exists because running the oracle CORRECTED the port. The first implementation DROPPED
# answers past the bound and documented the difference away as "generalisation needs the answer
# trie". Upstream, measured:
#
#     :- table p/1 as max_answers(2).  q(1..4).  p(X) :- q(X).
#     count => 3   ground => [1,2]   general => 1
#
# The bound does not truncate to 2 — it keeps 2 and adds ONE MAXIMALLY GENERAL answer that subsumes
# everything it stopped computing (`generalise_answer_substitution`, pl-tabling.c:3641-3654). The
# restraint turns an exact answer set into a sound OVER-approximation; dropping instead produces a
# silently INCOMPLETE one — the opposite direction, and unsound wherever absence reads as failure.
# `[[feedback_run_the_check_before_making_the_claim]]`
#
# ─── SCOPE ───────────────────────────────────────────────────────────────────────────────────────
# Restraint MECHANICS against upstream, not an end-to-end tabled query — `Restraints.jl` is not wired
# into the completion loop (that is §1.0's rewire). Green here does not mean MeTTa can run
# `:- table p/1 as max_answers(2)`.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _RS = Eval

function _rs_pairs(pl_file::AbstractString)::Dict{String,String}
    out = Dict{String,String}()
    swipl = Sys.which("swipl")
    swipl === nothing && return out
    txt = try; read(`$swipl -q $pl_file`, String); catch; return out; end
    for line in split(txt, '\n')
        m = match(r"^\s*([a-z_]+)\s*=>\s*(.+?)\s*$", line)
        m === nothing && continue
        out[m.captures[1]] = m.captures[2]
    end
    out
end

const _RS_ORACLE = normpath(joinpath(@__DIR__, "..", "..", "oracle", "tabling", "max_answers_7113.pl"))
_p(i) = Expression(Atom[Sym(:p), Grounded(i)])

"Feed 1..4 through the restraint with a per-head bound of `n`, as the oracle's program does."
function _run_bounded(head::Symbol, n::Int)
    _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
    _RS.restraint!(head, :max_answers, n)
    acc = Atom[]
    for i in 1:4
        acc, _, _ = _RS.tbl_wkl_add_answer(head, acc, _p(i))
    end
    acc
end

@testset "SWI §7.11.3 max_answers — LIVE differential vs SWI-Prolog" begin
    if Sys.which("swipl") === nothing
        @test_skip "swipl NOT ON PATH — the §7.11.3 differential did not run. NOT a pass."
    elseif !isfile(_RS_ORACLE)
        @test_skip "oracle missing: $_RS_ORACLE — the §7.11.3 differential did not run. NOT a pass."
    else
        oracle = _rs_pairs(_RS_ORACLE)
        # POSITIVE CONTROL before any comparison.
        @test sort(collect(keys(oracle))) == ["count", "general", "ground"]

        acc = _run_bounded(:p, 2)
        ground  = [a for a in acc if !((a::Expression).children[2] isa Var)]
        general = [a for a in acc if (a::Expression).children[2] isa Var]

        # 🔴 THE COUNT IS 3, NOT 2 — the assertion that caught the drop-instead-of-generalise bug.
        @test length(acc)     == parse(Int, oracle["count"])
        @test length(general) == parse(Int, oracle["general"])
        # ground answers as a SET (tabled answer order is not derivation order — oracle gave [2,1,_]).
        @test sort([string((a::Expression).children[2]) for a in ground]) ==
              sort([strip(s) for s in split(strip(oracle["ground"], ['[', ']']), ',')])
        # the table must be queryable as an APPROXIMATION, upstream's `answer_count_restraint`.
        @test _RS.answer_count_restraint(:p)
    end
end

@testset "§7.11.3 mechanics no oracle line would catch" begin
    # ── the ASYMMETRY: per-predicate is `>=`, the global flag is `==` (tripwire_answers_for_subgoal).
    # `>=` fires on the threshold answer AND every one after; `==` fires EXACTLY ONCE. Collapsing them
    # to one comparison changes how often the action runs and still passes a single-answer test.
    _RS.clear_all_restraints!()
    _RS.restraint!(:a, :max_answers, 2)
    @test _RS.tripwire_answers_for_subgoal(:a, 1) === nothing
    @test _RS.tripwire_answers_for_subgoal(:a, 2) == _RS.TW_BOUNDED_RATIONALITY
    @test _RS.tripwire_answers_for_subgoal(:a, 3) == _RS.TW_BOUNDED_RATIONALITY   # >= : again

    _RS.clear_all_restraints!()
    _RS.set_global_max_answers!(2, _RS.TW_FAIL)
    @test _RS.tripwire_answers_for_subgoal(:b, 1) === nothing
    @test _RS.tripwire_answers_for_subgoal(:b, 2) == _RS.TW_FAIL
    @test _RS.tripwire_answers_for_subgoal(:b, 3) === nothing                       # == : NOT again

    # ── `warning` ADDS THE ANSWER ANYWAY (pl-tabling.c:3660 `goto add_anyway`). Easy to implement as
    # "warn and drop", which is the `fail` action wearing the wrong name.
    _RS.clear_all_restraints!(); _RS.set_global_max_answers!(1, _RS.TW_WARNING)
    kept, added, act = (@test_logs (:warn,) match_mode=:any _RS.tbl_wkl_add_answer(:w, Atom[_p(1)], _p(2)))
    @test added && length(kept) == 2 && act == _RS.TW_WARNING

    # ── `fail` drops silently; `error` throws a resource error.
    _RS.clear_all_restraints!(); _RS.set_global_max_answers!(1, _RS.TW_FAIL)
    kept2, added2, _ = _RS.tbl_wkl_add_answer(:f, Atom[_p(1)], _p(2))
    @test !added2 && length(kept2) == 1
    _RS.clear_all_restraints!(); _RS.set_global_max_answers!(1, _RS.TW_ERROR)
    @test_throws ErrorException _RS.tbl_wkl_add_answer(:e, Atom[_p(1)], _p(2))

    # ── a NEGATIVE value REMOVES the restraint rather than storing it (boot/tabling.pl:1337-1342).
    _RS.clear_all_restraints!()
    _RS.restraint!(:n, :max_answers, 3)
    @test _RS.max_answers(:n) == 3
    _RS.restraint!(:n, :max_answers, -1)
    @test _RS.max_answers(:n) == _RS.NO_RESTRAINT

    # ── the generalised answer is added ONCE, deduped by VARIANT not by `==`. Fresh variables make
    # `(p $_g1)` and `(p $_g2)` structurally unequal, so an `==` dedup yields one general answer per
    # excess answer — measured 4 against the oracle's 3 before this was fixed.
    acc = _run_bounded(:v, 2)
    @test count(a -> (a::Expression).children[2] isa Var, acc) == 1

    # ── the two ABSTRACTION restraints are REFUSED, not silently accepted: they operate on trie terms
    # and need §1.0's answer trie. A no-op that appears to apply is the failure mode.
    @test_throws ArgumentError _RS.restraint!(:x, :subgoal_abstract, 3)
    @test_throws ArgumentError _RS.restraint!(:x, :answer_abstract, 3)
    @test_throws ArgumentError _RS.restraint!(:x, :no_such_option, 1)
    _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
end

@testset "§7.11.3 re-seated onto the ANSWER TRIE — and the duplicate-ordering fix" begin
    _run_trie(head::Symbol, n::Int, vals) = begin
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
        _RS.restraint!(head, :max_answers, n)
        t = _RS.AnswerTrie()
        acts = Any[]
        for v in vals
            (_, a) = _RS.trie_insert_restrained!(t, head, _p(v)); push!(acts, a)
        end
        (t, acts)
    end

    @testset "matches the swipl oracle through the trie" begin
        if Sys.which("swipl") === nothing || !isfile(_RS_ORACLE)
            @test_skip "swipl NOT ON PATH — the trie-path §7.11.3 differential did not run."
        else
            oracle = _rs_pairs(_RS_ORACLE)
            @test sort(collect(keys(oracle))) == ["count", "general", "ground"]   # positive control
            (t, _) = _run_trie(:p, 2, 1:4)
            as  = _RS.trie_answers(t)
            gen = [a for a in as if (a::Expression).children[2] isa Var]
            @test length(as)  == parse(Int, oracle["count"])     # 3, NOT 2
            @test length(gen) == parse(Int, oracle["general"])   # exactly one general answer
            @test _RS.answer_count_restraint(:p)                 # table marked an approximation
        end
    end

    @testset "🔴 a DUPLICATE must NOT trip the restraint" begin
        # The C reaches the tripwire only in the `else` branch of the node-exists test
        # (`pl-tabling.c:3618` vs `:3633`), so a duplicate — which does not grow the table — is
        # never a restraint event. MEASURED before the fix: at bound 2 with answers {1,2},
        # re-inserting `1` returned BOUNDED_RATIONALITY and set the approximate flag.
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
        _RS.restraint!(:q, :max_answers, 2)
        t = _RS.AnswerTrie()
        _RS.trie_insert_restrained!(t, :q, _p(1))
        _RS.trie_insert_restrained!(t, :q, _p(2))
        @test length(t) == 2 && !_RS.answer_count_restraint(:q)   # at the bound, not yet approximate

        @test _RS.trie_insert_restrained!(t, :q, _p(1)) == (false, :duplicate)
        @test !_RS.answer_count_restraint(:q)          # STILL not approximate — the whole point
        @test length(t) == 2

        # …and the Vector path now agrees, which is the regression this pins.
        _RS.clear_answer_count_restraints!()
        (kept, added, act) = _RS.tbl_wkl_add_answer(:q, Atom[_p(1), _p(2)], _p(1))
        @test act == :duplicate && !added && length(kept) == 2
        @test !_RS.answer_count_restraint(:q)
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
    end

    @testset "the general answer dedups WITHOUT _is_general_variant" begin
        # In the Vector implementation each generalisation mints fresh variables, so `==` never
        # matched and `_is_general_variant` had to be written. The trie keys variables by
        # FIRST-OCCURRENCE INDEX, so the second generalisation lands on the same node by
        # construction. Measured 4 vs the oracle's 3 before that helper existed.
        (t, _) = _run_trie(:v, 2, 1:6)                 # four answers past the bound
        @test count(a -> (a::Expression).children[2] isa Var, _RS.trie_answers(t)) == 1
        @test length(t) == 3
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
    end

    @testset "actions: warning ADDS ANYWAY, fail drops, error throws" begin
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
        _RS.set_global_max_answers!(1, _RS.TW_WARNING)
        t = _RS.AnswerTrie(); _RS.trie_insert_restrained!(t, :w, _p(1))
        (added, act) = (@test_logs (:warn,) match_mode=:any _RS.trie_insert_restrained!(t, :w, _p(2)))
        @test added && act == _RS.TW_WARNING && length(t) == 2    # `goto add_anyway`

        _RS.clear_all_restraints!(); _RS.set_global_max_answers!(1, _RS.TW_FAIL)
        t2 = _RS.AnswerTrie(); _RS.trie_insert_restrained!(t2, :f, _p(1))
        @test _RS.trie_insert_restrained!(t2, :f, _p(2)) == (false, _RS.TW_FAIL)
        @test length(t2) == 1

        _RS.clear_all_restraints!(); _RS.set_global_max_answers!(1, _RS.TW_ERROR)
        t3 = _RS.AnswerTrie(); _RS.trie_insert_restrained!(t3, :e, _p(1))
        @test_throws ErrorException _RS.trie_insert_restrained!(t3, :e, _p(2))
        _RS.clear_all_restraints!(); _RS.clear_answer_count_restraints!()
    end
end
