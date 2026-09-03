# test_index_jit_oracle.jl — the ANSWER-SET half of SWI's indexing suite, ported.
#
# SOURCE: `dev-zone/swipl-devel/tests/db/test_jit.pl` (237 lines, HEAD `63240a40`), specifically
# `test(retract)` / `test(retract2)` / `test(clause)` (:101-115) and `test(remove)` ×2 (:84, :92).
#
# WHY THIS FILE EXISTS. `test_index.jl` opens with "THERE IS NO UPSTREAM ORACLE FOR IT" and pins the
# speedup FORMULA by hand. That was too strong: SWI ships an indexing suite, and while most of it is
# useless to us — **6 of ~25 tests assert DETERMINISM** (`Det == true`, `var(Det)`, `nondet`), which
# is meaningless in a multiset language — the answer-set tests are exactly our requirement.
# [[feedback_upstream_tests_are_the_first_thing_to_port]]
#
# THE UPSTREAM SHAPE, kept verbatim because it is the point: 10 clauses `d(X,X)` for X in 1..10, then
# 90 clauses `d(a,X)` for X in 11..100, then query `d(a,X)`. Argument 1 is `a` in 90 clauses and
# distinct in the other 10, so the index MUST engage, and the answer must be exactly those 90.
# Upstream asserts `Xs == Xsok` with `numlist(11,100,Xsok)`.
#
# ── ⚠️ WHAT DOES *NOT* PORT, AND WHY THE ASSERTION HERE IS DIFFERENT ─────────────────────────────
# Upstream asserts SOURCE ORDER (`Xs == Xsok`). MEASURED 2026-09-03: we answer this query in REVERSE
# source order (`100 99 … 11`). That is NOT asserted here in either direction. Reverse order is
# UNEXPLAINED, not a documented contract, and pinning unexplained behaviour as a contract is a
# mistake this repo has already made once. [[feedback_unexplained_behaviour_is_not_a_contract]]
#
# What IS asserted is the invariant that must hold whatever the order is, and it is the one that
# actually grades an INDEX: **the indexed and unindexed lanes agree EXACTLY, element for element.**
# An index is a candidate-set filter; it may not add, drop, reorder or deduplicate. That is strictly
# stronger than upstream's fixed list for our purposes, because it also catches an index that
# silently reorders. If someone later specifies an answer order, add the assertion then.
#
# THE MULTISET REQUIREMENT IS OURS, NOT UPSTREAM'S. Prolog keeps duplicate clauses, but nothing in
# test_jit.pl asserts duplicate ANSWERS survive indexing. MeTTa `(=)` is multiset, so it is asserted
# here — and it is the property SWI's own metric would happily trade away (`pl-index.c:2652`,
# `a->size == 1 -> return false`; see `Index.jl`'s header).
using MeTTaCore
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _JX = Eval

"Answers for `q` against `s`, flattened, IN THE ORDER THE ENGINE PRODUCED THEM."
function _jx_ask(s, q::AbstractString)::Vector{String}
    r = _JX.load_metta!(s, q * "\n")
    String[string(x) for y in r for x in (y isa AbstractVector ? y : [y])]
end

"Upstream's fixture: 10 self-keyed clauses, then 90 sharing key `a`."
function _jx_space()
    s = _JX.Space()
    _JX.load_core_stdlib!(s)
    for i in 1:10
        _JX.load_metta!(s, "(d $i $i)\n")
    end
    for i in 11:100
        _JX.load_metta!(s, "(d a $i)\n")
    end
    s
end

"Drop every index, so the next query is served by the raw store scan."
_jx_unindex!(s) = (empty!(s.store.index); empty!(s.store.arg_index);
    empty!(s.store.arg_tried); s)

@testset "swipl test_jit.pl — answer-set oracle for the clause index" begin

    @testset "test(retract) shape — the complete answer set, and nothing else" begin
        got = _jx_ask(_jx_space(), raw"!(match &self (d a $x) $x)")
        want = String[string(i) for i in 11:100]
        @test length(got) == 90                       # upstream: numlist(11,100)
        @test sort(got) == sort(want)                 # complete, and NO extras
        @test isempty(setdiff(got, want))             # the 10 self-keyed clauses stay out
        @test isempty(setdiff(want, got))             # …and none of the 90 is dropped
    end

    @testset "🔑 the index may not add, drop, REORDER or dedupe — indexed ≡ unindexed" begin
        # This is the assertion that actually grades an index, and it is stronger than upstream's
        # fixed list: it also fails an index that merely permutes.
        indexed = _jx_ask(_jx_space(), raw"!(match &self (d a $x) $x)")
        plain = _jx_ask(_jx_unindex!(_jx_space()), raw"!(match &self (d a $x) $x)")
        @test indexed == plain                        # element for element, order included
        @test length(indexed) == length(plain)        # …stated separately so a length bug reads clearly
    end

    @testset "DUPLICATES SURVIVE — MeTTa `(=)` is a multiset, and the index must not collapse it" begin
        # Not an upstream property. SWI's metric would rate an all-one-key argument worthless
        # (pl-index.c:2652); for us that is a legitimate multi-answer relation.
        s = _JX.Space()
        _JX.load_core_stdlib!(s)
        for _ in 1:3
            _JX.load_metta!(s, "(dup x 1)\n")
        end
        for i in 1:40                                  # bulk, so an index is worth building
            _JX.load_metta!(s, "(dup k$(i) $(i))\n")
        end
        got = _jx_ask(s, raw"!(match &self (dup x $v) $v)")
        @test got == ["1", "1", "1"]                   # three, not one
        @test length(got) == 3
    end

    @testset "a VARIABLE at the indexed position joins EVERY key — the §5-iv trap" begin
        # `pl-index.c`'s deep index drops exactly these clauses, which is why upstream only builds a
        # list index when no clause has a variable there (`var_count == 0`, :2666-2669) — a
        # precondition MeTTa cannot honour. Asserted at SCALE here; test_index.jl covers n=3.
        s = _jx_space()
        _JX.load_metta!(s, raw"(d $anykey WILD)" * "\n")
        hit_a = _jx_ask(s, raw"!(match &self (d a $x) $x)")
        hit_7 = _jx_ask(s, raw"!(match &self (d 7 $x) $x)")
        @test "WILD" in hit_a                          # visible under the fat key
        @test "WILD" in hit_7                          # …and under a thin one
        @test length(hit_a) == 91                      # 90 + the wildcard
        # and dropping the index may not change that
        s2 = _jx_space()
        _JX.load_metta!(s2, raw"(d $anykey WILD)" * "\n")
        _jx_unindex!(s2)
        @test sort(hit_a) == sort(_jx_ask(s2, raw"!(match &self (d a $x) $x)"))
    end

    @testset "test_index_1/2 — GROUNDED keys (strings, floats), not just symbols" begin
        # Upstream runs the same fixture over strings/bignums/floats to exercise the hashed-key path.
        # Ours keys a Grounded by the 64-bit hash of its value; a collision may only WIDEN the
        # candidate set, never drop a match, because `match_atoms` stays authoritative.
        for (label, mk) in ("string" => (i -> "\"s$(i)\""), "float" => (i -> string(i) * ".5"))
            s = _JX.Space()
            _JX.load_core_stdlib!(s)
            for i in 1:60
                _JX.load_metta!(s, "(g $(mk(i)) v$(i))\n")
            end
            got = _jx_ask(s, "!(match &self (g $(mk(7)) \$v) \$v)")
            @test got == ["v7"]                        # exactly the one, by a hashed key ($label)
            plain = _jx_ask(_jx_unindex!(s), "!(match &self (g $(mk(7)) \$v) \$v)")
            @test got == plain
        end
    end

    @testset "test(remove) — answers stay correct while the index MIGRATES between arguments" begin
        # Upstream grows the population so a different argument becomes the better index and asserts
        # the index moved. We assert the thing that matters downstream: the ANSWERS never change.
        s = _JX.Space()
        _JX.load_core_stdlib!(s)
        for i in 1:50
            _JX.load_metta!(s, "(m $i $i)\n")
        end
        a1 = _jx_ask(s, raw"!(match &self (m $k 30) $k)")      # instantiates position 2
        @test a1 == ["30"]
        for i in 51:125                                        # grow: position 1 becomes attractive
            _JX.load_metta!(s, "(m $i $i)\n")
        end
        a2 = _jx_ask(s, raw"!(match &self (m 30 $v) $v)")      # instantiates position 1
        @test a2 == ["30"]
        a3 = _jx_ask(s, raw"!(match &self (m $k 99) $k)")      # back to position 2, post-migration
        @test a3 == ["99"]
    end
end
