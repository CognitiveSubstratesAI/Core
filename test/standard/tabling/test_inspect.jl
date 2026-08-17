# test_inspect.jl — SWI `library(tables)`, the portable half. §7.12.
#
# `library(tables)` is a THIN Prolog layer (381 lines) over seven C primitives, and the answer trie
# (§1.0 step 4) is the substrate the inspection predicates need. Five primitives we had; the sixth
# (`$tbl_table_status`) landed with `AnswerTrie.status`.
#
# ⚠️ THE THREE NOT PORTED ARE NOT AN OVERSIGHT: `get_residual/2`, `get_returns_and_dls/3` and
# `get_returns_and_tvs/3` need `$tbl_answer_dl` / `$tbl_answer_update_dl` — DELAY LISTS, absent
# (§7.6.1). The split falls exactly on those two primitives, which is why it is a boundary rather
# than a judgement call.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _IN = Eval
_in_g(h::Symbol, a) = Expression(Atom[Sym(h), Grounded(a)])

@testset "library(tables) — the portable inspection half (§7.12)" begin

    @testset "get_call / get_calls / status" begin
        _IN.abolish_all_tables!(); _IN.untable_all!()
        k1 = _IN._variant_rename(_in_g(:p, 1))
        k2 = _IN._variant_rename(_in_g(:p, 2))
        k3 = _IN._variant_rename(_in_g(:q, 1))
        for (k, vals) in ((k1, (10, 20)), (k2, (30,)), (k3, (99,)))
            t = _IN.answer_trie_for(k)
            for v in vals; _IN.trie_insert!(t, Grounded(v)); end
        end
        _IN.set_table_status!(_IN.answer_trie_for(k1), :complete)

        c = _IN.get_call(_in_g(:p, 1))
        @test c !== nothing
        @test c[1] == k1 && c[3] == :complete && length(c[2]) == 2
        @test _IN.get_call(_in_g(:p, 9)) === nothing        # no table ⇒ nothing, not an empty trie

        calls = _IN.get_calls(:p)                            # the nondeterministic form
        @test length(calls) == 2
        @test Set(s for (_, _, s) in calls) == Set([:complete, :fresh])
        @test isempty(_IN.get_calls(:nosuch))
        @test _IN.tabled_heads() == [:p, :q]
        _IN.abolish_all_tables!()
    end

    @testset "get_returns, with nodes, and for a call" begin
        _IN.abolish_all_tables!()
        k = _IN._variant_rename(_in_g(:p, 1))
        t = _IN.answer_trie_for(k)
        for v in (10, 20, 30); _IN.trie_insert!(t, Grounded(v)); end

        @test String[string(a) for a in _IN.get_returns(t)] == ["10", "20", "30"]   # insertion order
        wn = _IN.get_returns_with_nodes(t)                                          # get_returns/3
        @test length(wn) == 3
        @test all(n isa _IN.TrieNode for (_, n) in wn)
        @test String[string(a) for (a, _) in wn] == ["10", "20", "30"]
        # the node IS the handle: upstream's NodeID exists so a caller can act on one answer.
        @test wn[2][2].answer == Grounded(20)

        @test String[string(a) for a in _IN.get_returns_for_call(_in_g(:p, 1))] == ["10", "20", "30"]
        @test isempty(_IN.get_returns_for_call(_in_g(:z, 1)))   # no table ⇒ empty, not an error
        _IN.abolish_all_tables!()
    end

    @testset "status accepts UPSTREAM's set and nothing else" begin
        @test _IN.table_status(_IN.AnswerTrie()) == :fresh      # created, not completed
        @test _IN.TABLE_STATUSES == (:fresh, :active, :complete, :invalid, :dynamic)
        t = _IN.AnswerTrie()
        @test _IN.table_status(_IN.set_table_status!(t, :complete)) == :complete
        @test _IN.is_complete(t)
        # a status we invented would be indistinguishable from one upstream has; refuse it.
        @test_throws ArgumentError _IN.set_table_status!(t, :bogus)
        @test_throws ArgumentError _IN.set_table_status!(t, :done)
    end

    @testset "🔴 abolish_table_pred! drops TABLES; untable! also drops the DECLARATION" begin
        # Upstream keeps these separate and so must we: `abolish_table_pred/1` invalidates the
        # subgoals and the next call RE-TABLES, while `untable/1` retracts `$tabled`/`$table_mode`
        # and clears the attributes so the predicate stops being tabled. Conflating them makes
        # "clear the cache" silently mean "stop memoising".
        _IN.abolish_all_tables!(); _IN.untable_all!()
        _IN.table!(:p)
        k = _IN._variant_rename(_in_g(:p, 1))
        _IN.trie_insert!(_IN.answer_trie_for(k), Grounded(7))
        @test :p in _IN._TABLED_HEADS
        @test count(x -> _IN.head_name(x) === :p, keys(_IN._ANSWER_TRIES)) == 1

        @test _IN.abolish_table_pred!(:p)                       # had tables ⇒ true
        @test :p in _IN._TABLED_HEADS                           # DECLARATION SURVIVES
        @test count(x -> _IN.head_name(x) === :p, keys(_IN._ANSWER_TRIES)) == 0
        @test !_IN.abolish_table_pred!(:p)                      # nothing left to drop ⇒ false

        @test _IN.untable!(:p)                                  # …and this one drops the declaration
        @test !(:p in _IN._TABLED_HEADS)
        _IN.abolish_all_tables!(); _IN.untable_all!()
    end

    @testset "abolish_all_tables! clears every table and keeps every declaration" begin
        _IN.abolish_all_tables!(); _IN.untable_all!()
        _IN.table!(:p); _IN.table!(:q)
        for h in (:p, :q)
            _IN.trie_insert!(_IN.answer_trie_for(_IN._variant_rename(_in_g(h, 1))), Grounded(1))
        end
        @test length(_IN._ANSWER_TRIES) == 2
        _IN.abolish_all_tables!()
        @test isempty(_IN._ANSWER_TRIES)
        @test :p in _IN._TABLED_HEADS && :q in _IN._TABLED_HEADS   # declarations kept
        _IN.untable_all!()
    end
end

@testset "roadmap 1.0b step 1 — the trie MIRRORS a real completed table" begin
    # Until this, `_ANSWER_TRIES` was populated only by hand in tests: `library(tables)`, §7.5's
    # `more_general_table` and §7.3/§7.11.3's trie-seated inserts were CORRECT AND UNREACHABLE from a
    # real evaluation. `tabled_eval` now mirrors completed answers into the trie.
    #
    # ⚠️ MIRROR, NOT SWITCH. `_ANSWER_TABLE` is still the read path, so this changes no behaviour —
    # it makes the trie OBSERVABLE against the live engine first. Same disable-to-prove order as the
    # resumption flip: agreement before adoption.
    _IN.untable_all!(); _IN.abolish_all_tables!()
    try
        s = Space(); load_core_stdlib!(s)
        load_metta!(s, raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n")
        _IN.table!(:fib)
        @test String[string(x) for y in load_metta!(s, "!(fib 8)\n")
                     for x in (y isa AbstractVector ? y : [y])] == ["21"]

        # ANTI-VACUITY: a run that tabled nothing would make every assertion below trivially true.
        calls = _IN.get_calls(:fib)
        @test length(calls) > 1                      # fib 8 memoises several subgoals
        @test _IN.tabled_heads() == [:fib]

        # 🔴 THE TWO STORES MUST AGREE — that is the whole point of mirroring before switching.
        for (k, t, st) in calls
            @test st == :complete                    # completion marks status, which §7.5 requires
            @test sort(String[string(a) for a in get(_IN._ANSWER_TABLE, k, Atom[])]) ==
                  sort(String[string(a) for a in _IN.get_returns(t)])
        end

        # and the inspection API reaches a REAL table, not a hand-built one
        goal = _IN._reduced_goal(_IN.parse_from(_IN.tokenize("(fib 8)"), Ref(1), s.tokens),
                                 s, _IN.Bindings())
        c = _IN.get_call(goal)
        @test c !== nothing && c[3] == :complete
        @test String[string(a) for a in _IN.get_returns(c[2])] == ["21"]
    finally
        _IN.abolish_all_tables!(); _IN.untable_all!()
    end
end
