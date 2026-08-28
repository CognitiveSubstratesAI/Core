# test_index.jl — the ADAPTIVE (JIT) argument-index assessment. `src/standard/Index.jl`.
#
# 🔴 THIS FILE EXISTS BECAUSE THERE IS NO UPSTREAM ORACLE FOR IT. `workflows/swipl_tabling_oracle.sh`
# grades TABLING, which is a port; the index is ours, and `pl-index.c` cannot be run against us — its
# unit of indexing is a CLAUSE with argument positions, ours is an ATOM in a store. What ports
# EXACTLY is the speedup FORMULA (pl-index.c:3004-3020), so that is what this file pins, with values
# computed by hand from the formula rather than from our own output.
#
#               #clauses * #distinct
#     speedup = ----------------------------------
#               #clauses - #var + #var * #distinct

using MeTTaCore
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test
const _IX = Eval

_fx(args...) = Expression(Atom[Sym("f"), args...])

@testset "adaptive index — the pl-index.c speedup formula" begin
    @testset "all distinct, no vars ⇒ speedup == #clauses" begin
        atoms = Atom[_fx(Sym("a"), Sym("1")), _fx(Sym("b"), Sym("2")),
                     _fx(Sym("c"), Sym("3")), _fx(Sym("d"), Sym("4"))]
        a = _IX._assess_argument(atoms, 2)
        @test a.distinct == 4
        @test a.nvar == 0
        @test a.speedup ≈ 4.0            # (4*4) / (4 - 0 + 0*4)
    end

    @testset "no distinct values ⇒ speedup == 1.0 (a flat scan; index is worthless)" begin
        atoms = Atom[_fx(Sym("a"), Sym(string(i))) for i in 1:4]
        a = _IX._assess_argument(atoms, 2)
        @test a.distinct == 1
        @test a.speedup ≈ 1.0            # (4*1) / (4 - 0 + 0*1)
    end

    @testset "vars at the position DILUTE the gain — they land in every bucket" begin
        atoms = Atom[_fx(Sym("a"), Sym("1")), _fx(Sym("b"), Sym("2")),
                     _fx(Var("x"), Sym("3")), _fx(Var("y"), Sym("4"))]
        a = _IX._assess_argument(atoms, 2)
        @test a.distinct == 2
        @test a.nvar == 2
        @test a.speedup ≈ 8 / 6          # (4*2) / (4 - 2 + 2*2)
    end

    # 🔑 THE CASE A NAIVE HEURISTIC GETS WRONG, and the reason the formula is worth porting rather
    # than approximating: BOTH positions have 4 distinct values, so a distinct-count heuristic ties
    # them. The formula does not — position 3 is a variable in 3 of 4 clauses, so its buckets each
    # hold nearly everything and its real gain is ~1.23 against position 2's 4.0.
    @testset "distinct-count TIES but the formula discriminates" begin
        atoms = Atom[
            _fx(Sym("a"), Sym("p")), _fx(Sym("b"), Var("v1")),
            _fx(Sym("c"), Var("v2")), _fx(Sym("d"), Var("v3"))]
        a2 = _IX._assess_argument(atoms, 2)
        a3 = _IX._assess_argument(atoms, 3)
        @test a2.distinct == 4 && a2.nvar == 0
        @test a3.nvar == 3                        # three clauses are var at position 3
        @test a2.speedup ≈ 4.0
        @test a3.speedup < 1.5                    # diluted to near-nothing
        best = _IX.best_index_argument(atoms, [2, 3])
        @test best !== nothing && best.argpos == 2   # ⇒ the ground position wins
    end
end

@testset "adaptive index — argument SELECTION (bestHash)" begin
    atoms = Atom[_fx(Sym("a"), Sym("p")), _fx(Sym("b"), Sym("q")),
                 _fx(Sym("c"), Sym("r")), _fx(Sym("d"), Sym("s"))]

    # 🔑 THE POINT OF THE WHOLE PORT: our FIXED `_index_key` needs child 2 concrete and gives up
    # otherwise. The adaptive layer indexes on whatever the CALL instantiated instead.
    @testset "an uninstantiated arg 1 no longer forfeits the index" begin
        pat = _fx(Var("open"), Sym("q"))          # arg1 VAR, arg2 ground
        @test _IX._index_key(pat) === nothing     # the fixed key gives up …
        inst = _IX.instantiated_positions(pat)
        @test inst == [3]                         # … while position 3 IS instantiated
        best = _IX.best_index_argument(atoms, inst)
        @test best !== nothing && best.argpos == 3
    end

    @testset "no instantiated position ⇒ no index (upstream returns false, :3068)" begin
        pat = _fx(Var("a"), Var("b"))
        @test _IX.instantiated_positions(pat) == Int[]
        @test _IX.best_index_argument(atoms, Int[]) === nothing
    end

    @testset "the head is never an adaptive candidate — it is already half of _index_key" begin
        @test !(1 in _IX.instantiated_positions(_fx(Sym("a"), Sym("b"))))
    end

    @testset "an index with no gain is declined rather than built" begin
        flat = Atom[_fx(Sym("a"), Sym("z")) for _ in 1:4]   # every position identical
        @test _IX.best_index_argument(flat, [2, 3]) === nothing
    end

    # `better_index` (pl-index.c:3026) — supersede by a MARGIN, never on a tie, or a live index
    # thrashes on noise.
    @testset "better_index requires a margin" begin
        @test _IX._better_index(4.0, 0.0)          # nothing incumbent ⇒ always better
        @test !_IX._better_index(4.0, 4.0)         # a tie does NOT supersede
        @test !_IX._better_index(4.4, 4.0)         # +10% does not clear the 1.2 margin
        @test _IX._better_index(5.0, 4.0)          # +25% does
    end
end

# ── THE LIVE PATH: indexed `match` must return EXACTLY the unindexed answers ─────────────────────
# 🔴 THE ONLY FAILURE THAT MATTERS HERE IS A SILENT ONE. A wrongly-narrowing index does not error, it
# returns FEWER answers — so this compares the indexed result against the same query run with the
# index disabled, rather than against a hand-written expectation.
@testset "JIT argument index does not change answers" begin
    s = Space(); load_core_stdlib!(s)
    for k in 1:60
        load_metta!(s, "(belief k$(k) s$(k) c$(k))\n")
    end
    load_metta!(s, "(belief k7 OTHER c99)\n")        # a SECOND atom under the same key
    load_metta!(s, raw"(belief $openvar s1 c1)" * "\n")  # var at the indexed position: matches ANY key

    ground = sort(string.(load_metta!(s, raw"!(match &self (belief k7 $s $c) $s)" * "\n")))
    @test !isempty(s.store.arg_index)                 # an index WAS built
    # the var-at-position atom must appear under every key — the `#var * #distinct` term made real
    @test length(ground) == 3                          # k7's two atoms + the open-var atom

    # …and the same query with the index dropped must agree exactly.
    empty!(s.store.arg_index); empty!(s.store.arg_tried)
    unindexed = sort(string.(load_metta!(s, raw"!(match &self (belief k7 $s $c) $s)" * "\n")))
    @test ground == unindexed

    # a key with no atoms yields nothing, not everything
    @test isempty(load_metta!(s, raw"!(match &self (belief nosuch $s $c) $s)" * "\n"))

    # MUTATION MUST INVALIDATE — a stale index is a wrong answer, not a slow one.
    load_metta!(s, raw"!(match &self (belief k7 $s $c) $s)" * "\n")   # rebuild
    @test !isempty(s.store.arg_index)
    load_metta!(s, "!(add-atom &self (belief k7 FRESH c0))\n")
    @test isempty(s.store.arg_index)                  # dropped on add
    after = load_metta!(s, raw"!(match &self (belief k7 $s $c) $s)" * "\n")
    @test length(after) == 4                          # the new atom IS visible
end
