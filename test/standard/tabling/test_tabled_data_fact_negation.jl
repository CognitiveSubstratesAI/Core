# test_tabled_data_fact_negation.jl — 🔴 TABLING IS NOT ANSWER-PRESERVING FOR A DATA-FACT PREDICATE,
# and `tnot` over one returns a WRONG ANSWER. Root-caused 2026-09-09; NOT yet fixed.
#
# ─── THE DEFECT, IN SIX LINES ────────────────────────────────────────────────────────────────────
#     (s 2)                     a DATA fact, no `(=)` rule anywhere
#     !(s 2)   untabled  ->  (s 2)        the fact is visible (the goal answers with ITSELF)
#     !(s 2)   TABLED    ->  <EMPTY>      ← tabling CHANGED THE ANSWER SET
#     !(tnot (s 2))      ->  True         ← WRONG. s(2) holds, so tnot(s(2)) must FAIL.
#     !(tnot (s 9))      ->  True         correct (s(9) really is absent)
# ⇒ `tnot` cannot tell a PRESENT fact from an ABSENT one, once the predicate is tabled. Written as a
# RULE instead — `(= (s 2) True)` — every one of these is correct, so the defect is specific to
# facts. Tabling's own contract (Tabling.jl, `auto_table!` header) is "answers are identical, only
# faster"; here they are not.
#
# ─── THE MECHANISM, EXACTLY ──────────────────────────────────────────────────────────────────────
#   `_probe_no_rule` (Tabling.jl:1148) = `isempty(rule_results(key, space, Bindings()))` — it asks
#   only for `(= key X)` RULES, so a bare data atom leaves the key in `_NO_RULE`, and `tnot`
#   (Tabling.jl:2279) does `key in _NO_RULE && return ExecOk(Atom[Sym("True")])`.
#   `_NO_RULE` is not junk: under METTA mode a rule-less tabled goal answers with ITSELF, so `A` is
#   non-empty and the "provably true" test below it would wrongly call G true. The bug is that ONE
#   flag conflates two cases that look identical — goal-answers-with-itself AND no supporting fact
#   (underivable, `tnot` True ✓) vs goal-answers-with-itself AND a MATCHING DATA ATOM IS PRESENT
#   (the fact is TRUE, `tnot` must be Empty).
#   ⚠️ THIS EXACT LINE WAS ALREADY FIXED ONCE FOR THE MIRROR CASE — a head with a COMPILED
#   implementation and no space rules was reported "no rule" (see the comment at :1143). The
#   data-fact case is the same shape and was missed.
#
# ─── WHY IT MATTERS: IT IS p60 ───────────────────────────────────────────────────────────────────
#   p60:  q(A) :- u(A), tnot(s(A)).   p(A) :- u(A), tnot(q(A)).   u(2). u(3). s(2). …
#   `tnot(s(2))` wrongly succeeds ⇒ q(2) derived from nothing ⇒ `tnot(q(2))` fails ⇒ p(2), and with
#   it p(3)/p(4), are lost. ALL FOUR p60 mismatches are this one error:
#       got {q2,q3,q4,s2}   gold {p2,p3,p4,q3,q4,s2}
#   🔴 TWO EARLIER DIAGNOSES OF p60 ARE SUPERSEDED BY THIS ONE. Roadmap §0r said the generative call
#   LOSES ITS BINDING — refuted 2026-09-09 (`(r b)` in the answer set is only constructible if the
#   binding survived). Roadmap §0s said the cause is `NotReducible`-vs-FAIL — a real gap, and a
#   three-way guard for it was built and measured the same day, but with the guard in place p60's
#   result is BYTE-IDENTICAL to before. Necessary, not sufficient.
using MeTTaCore
using Test

const _TDF = MeTTaCore.Eval

function _tdf(program::AbstractString, query::AbstractString)::Vector{String}
    _TDF.untable_all!()
    _TDF.abolish_all_tables!()
    sp = _TDF.Space()
    _TDF.load_core_stdlib!(sp)
    _TDF.load_metta!(sp, program)
    out = String[]
    for y in _TDF.load_metta!(sp, query)
        y isa AbstractVector ? append!(out, string.(y)) : push!(out, string(y))
    end
    sort(out)
end

@testset "tabling a DATA-FACT predicate breaks tnot" begin

    @testset "the CONTRAST that localises it — as a RULE, everything is correct" begin
        rule = "(= (s 2) True)\n!(table! s)\n"
        @test _tdf(rule, "!(tnot (s 2))\n") == String[]        # s(2) holds ⇒ tnot FAILS
        @test _tdf(rule, "!(tnot (s 9))\n") == ["True"]        # s(9) absent ⇒ tnot succeeds
    end

    @testset "…and as a FACT, the absent case is still right" begin
        fact = "(s 2)\n!(table! s)\n"
        @test _tdf(fact, "!(tnot (s 9))\n") == ["True"]        # genuinely absent
    end

    @testset "🔴 THE DEFECT — pinned BROKEN so it goes green the day it is fixed" begin
        fact = "(s 2)\n!(table! s)\n"
        # tabling must be ANSWER-PRESERVING; untabled this answers [(s 2)], tabled it answers [].
        @test_broken _tdf(fact, "!(s 2)\n") == ["(s 2)"]
        # and the consequence: a TRUE fact read as underivable by negation.
        @test_broken _tdf(fact, "!(tnot (s 2))\n") == String[]
    end

    @testset "🔴 p60's over-derivation, reproduced without the corpus" begin
        p60 = """
        (u 2)
        (u 3)
        (s 2)
        (= (q \$a) (let \$c (match &self (u \$a) True) (tnot (s \$a))))
        !(table! q)
        !(table! s)
        """
        @test _tdf(p60, "!(q 3)\n") == ["True"]                # gold: q(3) TRUE — correct today
        @test_broken _tdf(p60, "!(q 2)\n") == String[]         # gold: q(2) FALSE — WRONG today
    end
end
