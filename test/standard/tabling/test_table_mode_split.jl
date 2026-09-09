# test_table_mode_split.jl — `table!` is PROLOG mode, `auto_table!` is METTA mode, and they answer a
# CLAUSE-LESS GOAL DIFFERENTLY ON PURPOSE. Characterized 2026-09-09.
#
# ─── WHY THIS FILE EXISTS: IT IS THE RESIDUE OF A WRONG DIAGNOSIS ────────────────────────────────
# I claimed a wrong-answer defect here — "tabling is not answer-preserving for a data-fact predicate"
# — and committed it (`b46b8c4`). It is RETRACTED. Three things were wrong:
#
#   1. THE REPRODUCTION USED A SHAPE THE TRANSLATOR NEVER EMITS. I hand-wrote `(s 2)` as a bare data
#      atom. For a TABLED predicate `translate_corpus.pl` emits `(= (s 2) True)` — a RULE — because
#      `is_data_pred/1` already excludes tabled heads (`:145`). Different shape, different experiment.
#   2. THE TRANSLATOR'S REAL ENCODING IS CORRECT. Measured on its actual output:
#          (q 1) -> []   (q 2) -> []   (q 3) -> [True]   (s 2) -> [True]
#          (tnot (s 2)) -> []          (tnot (s 3)) -> [True]
#      So p60's `q(2)` does NOT come from `tnot(s(2))`, and my root cause was void.
#   3. THE BEHAVIOUR IS NOT A DEFECT — it is the documented mode split, and I asserted the wrong
#      CONTRACT against the wrong MODE. Answer-preservation belongs to METTA mode, and it HOLDS.
#
# ⚠️ p60 IS STILL OPEN, and has now had THREE wrong causes: §0r (the call loses its binding —
# refuted by execution), §0s (NotReducible-vs-FAIL — real, guard built, measured INSUFFICIENT), and
# mine (this one). The remaining suspect is the generative clause `q(A) :- q(B), t(A,B)`, since the
# `tnot(s(A))` clause is now measured correct. Do not attribute p60 again without running the
# TRANSLATOR'S OUTPUT rather than a hand-written stand-in.
using MeTTaCore
using Test

const _TMS = MeTTaCore.Eval

function _tms(program::AbstractString, query::AbstractString; auto::Bool)
    _TMS.untable_all!()
    _TMS.abolish_all_tables!()
    sp = _TMS.Space()
    _TMS.load_core_stdlib!(sp)
    _TMS.load_metta!(sp, program)
    auto ? _TMS.auto_table!(sp) : _TMS.table!(:s)
    out = String[]
    for y in _TMS.load_metta!(sp, query)
        y isa AbstractVector ? append!(out, string.(y)) : push!(out, string(y))
    end
    sort(out)
end

@testset "table! (Prolog mode) vs auto_table! (MeTTa mode) on a clause-less goal" begin

    @testset "a bare DATA ATOM is not a CLAUSE — Prolog mode fails the goal" begin
        fact = "(s 2)\n"
        @test _tms(fact, "!(s 2)\n"; auto = false) == String[]          # no clauses ⇒ fails
        @test _tms(fact, "!(tnot (s 2))\n"; auto = false) == ["True"]   # …so tnot succeeds
    end

    @testset "METTA mode is ANSWER-PRESERVING — the contract auto_table! actually makes" begin
        fact = "(s 2)\n"
        @test _tms(fact, "!(s 2)\n"; auto = true) == ["(s 2)"]          # the goal answers with ITSELF
    end

    @testset "🔑 written as a RULE — which is what the translator emits — BOTH are correct" begin
        rule = "(= (s 2) True)\n"
        @test _tms(rule, "!(s 2)\n"; auto = false) == ["True"]
        @test _tms(rule, "!(tnot (s 2))\n"; auto = false) == String[]   # s(2) holds ⇒ tnot fails
        @test _tms(rule, "!(tnot (s 9))\n"; auto = false) == ["True"]   # s(9) absent ⇒ tnot succeeds
    end
end
