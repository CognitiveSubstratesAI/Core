# test_answer_trie.jl — the ANSWER TRIE. Roadmap §1.0 step 4 (structure half).
#
# Gates the four properties the trie exists to provide, each of which a `Dict{Atom,Vector{Atom}}`
# cannot: structural duplicate detection, VARIANT identity, a depth-walkable path (§7.11.1/2), and a
# maintained count for the §7.11.3 restraint.
#
# ⚠️ NOT WIRED. `tabled_eval` still stores answers in `_ANSWER_TABLE`/`_PARTIAL`; nothing reads a
# trie yet. A green file means the structure is correct, NOT that tabling uses it.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _AT = Eval
_at_ex(xs...) = Expression(Atom[xs...])

@testset "answer trie — structural identity, variants, and order (§1.0 step 4)" begin

    @testset "duplicate detection is STRUCTURAL, not a scan" begin
        t = _AT.AnswerTrie()
        @test isempty(t) && length(t) == 0
        a = _at_ex(Sym(:f), Grounded(1))
        @test _AT.trie_insert!(t, a)              # new
        @test !_AT.trie_insert!(t, a)             # the same answer is NOT new
        @test length(t) == 1                      # …and did not double-count
        @test _AT.trie_contains(t, a)
        @test !_AT.trie_contains(t, _at_ex(Sym(:f), Grounded(2)))
    end

    @testset "VARIANT identity — renaming a variable does not make a new answer" begin
        t = _AT.AnswerTrie()
        vx, vy, vz = Var("x", UInt64(1)), Var("y", UInt64(2)), Var("z", UInt64(3))
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), vx, vx))
        # (f $y $y) is (f $x $x) up to renaming ⇒ the SAME node. This is what upstream's `vars`
        # argument to trie_lookup buys, and what our Vector tables needed `_is_general_variant` for.
        @test !_AT.trie_insert!(t, _at_ex(Sym(:f), vy, vy))
        @test length(t) == 1
        # …but repeated-vs-distinct variables are DIFFERENT terms, so keying must be by
        # first-occurrence INDEX and not merely "is a variable".
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), vx, vz))
        @test length(t) == 2
        # the maximally-general answer bounded_rationality inserts is all variables — it must be
        # storable and must be a variant of itself under any renaming.
        @test _AT.trie_insert!(t, _at_ex(Sym(:g), vx))
        @test !_AT.trie_insert!(t, _at_ex(Sym(:g), vy))
    end

    @testset "1 and 1.0 are DIFFERENT answers" begin
        # `1 == 1.0` in Julia, so a value-only key would conflate them. Upstream keeps them distinct
        # (standard order sorts float before int on equal value, pl-prims.c:1777).
        t = _AT.AnswerTrie()
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), Grounded(1)))
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), Grounded(1.0)))
        @test length(t) == 2
    end

    @testset "structure is keyed, not flattened text" begin
        # (f (g a)) and (f g a) flatten to the same symbols; only ARITY separates them, which is why
        # ExprKey carries it. A text-ish key would merge these two distinct answers.
        t = _AT.AnswerTrie()
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), _at_ex(Sym(:g), Sym(:a))))
        @test _AT.trie_insert!(t, _at_ex(Sym(:f), Sym(:g), Sym(:a)))
        @test length(t) == 2
    end

    @testset "answers come back in INSERTION order, not traversal order" begin
        # A trie's natural walk is key order. Answer order is user-visible, so it must be a decision
        # rather than a side effect of the data structure — `seq` is stamped at insert.
        t = _AT.AnswerTrie()
        for v in (Sym(:zeta), Sym(:alpha), Grounded(9), Sym(:mid))
            _AT.trie_insert!(t, _at_ex(Sym(:g), v))
        end
        @test String[string(a) for a in _AT.trie_answers(t)] ==
              ["(g zeta)", "(g alpha)", "(g 9)", "(g mid)"]
    end

    @testset "delete unmarks, and the count tracks it" begin
        t = _AT.AnswerTrie()
        a = _at_ex(Sym(:f), Grounded(1))
        _AT.trie_insert!(t, a)
        @test _AT.trie_delete!(t, a)
        @test length(t) == 0 && !_AT.trie_contains(t, a)
        @test !_AT.trie_delete!(t, a)             # deleting twice is not an error, and not a change
        # re-inserting after delete is NEW again — the path survives but the mark does not.
        @test _AT.trie_insert!(t, a) && length(t) == 1
    end

    @testset "registry: one trie per table, dying with its table" begin
        _AT.clear_answer_tries!()
        k1, k2 = Sym(:t1), Sym(:t2)
        @test !_AT.has_answer_trie(k1)
        t1 = _AT.answer_trie_for(k1)
        @test _AT.answer_trie_for(k1) === t1      # get!, not a fresh trie per call
        _AT.trie_insert!(_AT.answer_trie_for(k2), _at_ex(Sym(:f), Grounded(1)))
        @test length(_AT.answer_trie_for(k1)) == 0 && length(_AT.answer_trie_for(k2)) == 1
        _AT.drop_answer_trie!(k1)
        @test !_AT.has_answer_trie(k1) && _AT.has_answer_trie(k2)
        _AT.clear_answer_tries!()
        @test !_AT.has_answer_trie(k2)
    end

    @testset "untable! drops the head's trie and worklist with its table (0.3 integration)" begin
        # A surviving trie would serve answers for a predicate that is no longer tabled — the same
        # class as the stranded _DEPS entries 0.3 exists to prevent.
        _AT.untable_all!()
        key = _at_ex(Sym(:p), Grounded(1))
        _AT.table!(:p)
        _AT.trie_insert!(_AT.answer_trie_for(key), _at_ex(Sym(:p), Grounded(1)))
        _AT.wkl_add_answer!(_AT.worklist_for(key), Grounded(1))
        @test _AT.has_answer_trie(key) && _AT.has_worklist(key)
        _AT.untable!(:p)
        @test !_AT.has_answer_trie(key)
        @test !_AT.has_worklist(key)
        _AT.untable_all!()
    end
end
