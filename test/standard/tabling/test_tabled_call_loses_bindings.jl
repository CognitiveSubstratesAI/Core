# test_tabled_call_loses_bindings.jl — 🔴 A TABLED CALL RETURNS ITS VALUE BUT NOT ITS ANSWER
# SUBSTITUTIONS, so the caller's variables come back UNBOUND. Root-caused 2026-09-09. NOT fixed.
#
# ─── THE DEFECT, AS AN A/B ───────────────────────────────────────────────────────────────────────
#     (= (g a) True) (= (g b) True)            !(let $c (g $z) $z)
#         UNTABLED -> ["a","b"]      the bindings come back
#         TABLED   -> ["$z"]         ← the variable comes back AS ITSELF
# It is NOT about the callee's head shape: a variable-headed callee that binds inside its body
# (`(= (g $x) (match &self (u $x) True))`) behaves identically — ["a","b"] untabled, ["$z"] tabled.
# The discriminator is TABLING ALONE.
#
# ─── WHY: THIS IS p60, AND IT RECONCILES TWO "MEASURED" CONTRADICTIONS ───────────────────────────
# p60 tables `q`, and its second clause translates to
#     (= (q $v0) (let $c1 (q $v1) (if … Empty (match &self (t $v0 $v1) $v1))))
# `(q $v1)` leaves `$v1` unbound, so `(match &self (t $v0 $v1) $v1)` runs over the WHOLE relation:
#     full clause body -> ["1","2","3"]        (every t fact)
#     (q 2)            -> ["1"]                DERIVED FROM NOTHING; gold says q(2) is FALSE
# and the wrong q(2) then kills p(2)/p(3)/p(4) via tnot(q(2)) — all four p60 mismatches, one cause.
#
# 🔑 THE RECONCILIATION. Roadmap §0r said the binding is lost; §0s said it survives; both ran a real
# experiment and both were right ABOUT THEIR OWN SHAPE — §0s's callee was UNTABLED, p60's is TABLED.
# The contradiction stood for eleven days because neither test named the property it depended on.
# ⚠️ I then "refuted" §0r twice on the same untabled shape, and separately blamed data-fact tabling
# (retracted, `f4441cd`). THREE wrong causes before this one; state the CALLEE'S TABLED STATUS in any
# future claim about generative calls.
#
# ─── WHAT A FIX MUST DO ──────────────────────────────────────────────────────────────────────────
# Proper SLG consumes a table by UNIFYING THE CALL with each stored answer, so the caller's variables
# bind. We return the answer's VALUE only. The answer trie already stores each answer's goal INSTANCE
# (roadmap §7.11.1), so the material is there; what is missing is threading it back to the caller.
using MeTTaCore
using Test

const _TCB = MeTTaCore.Eval

function _tcb(program::AbstractString, query::AbstractString, tabled::Vector{Symbol})
    _TCB.untable_all!()
    _TCB.abolish_all_tables!()
    sp = _TCB.Space()
    _TCB.load_core_stdlib!(sp)
    _TCB.load_metta!(sp, program)
    for t in tabled
        _TCB.table!(t)
    end
    out = String[]
    for y in _TCB.load_metta!(sp, query)
        y isa AbstractVector ? append!(out, string.(y)) : push!(out, string(y))
    end
    sort(out)
end

const _GROUND  = "(= (g a) True)\n(= (g b) True)\n"
const _VARHEAD = "(u a)\n(u b)\n(= (g \$x) (match &self (u \$x) True))\n"
const _BIND    = "!(let \$c (g \$z) \$z)\n"

@testset "a TABLED call loses its answer substitutions" begin

    @testset "UNTABLED, the bindings come back — both callee shapes" begin
        @test _tcb(_GROUND,  _BIND, Symbol[]) == ["a", "b"]
        @test _tcb(_VARHEAD, _BIND, Symbol[]) == ["a", "b"]   # head shape is NOT the discriminator
    end

    @testset "🔴 TABLED, the variable comes back AS ITSELF" begin
        @test_broken _tcb(_GROUND,  _BIND, [:g]) == ["a", "b"]
        @test_broken _tcb(_VARHEAD, _BIND, [:g]) == ["a", "b"]
    end

    @testset "🔴 p60's over-derivation, on the TRANSLATOR'S OWN OUTPUT" begin
        # verbatim from `swipl translate_corpus.pl p60.P`, not a hand-written stand-in.
        p60 = """
        (u 2)
        (u 3)
        (= (s 2) True)
        (t 2 1)
        (t 3 2)
        (t 4 3)
        (= (q \$v0) (let \$c1 (match &self (u \$v0) True) (tnot (s \$v0))))
        (= (q \$v0) (let \$c1 (q \$v1) (if (== (get-metatype \$c1) Expression) Empty (match &self (t \$v0 \$v1) \$v1))))
        """
        # ⚠️ GRADE THE WAY THE HARNESS GRADES — a goal is TRUE iff it has ANY non-undefined answer.
        # Asserting an exact value here would PIN the spurious extras: with clause 2 loaded the body
        # returns the `match` template (a NUMBER), so `(q 3)` answers ["2","True"] and `(q 4)` ["3"].
        # Those extras are the same binding-loss leaking a value; the gold set only cares true/false.
        @test !isempty(_tcb(p60, "!(q 3)\n", [:q, :s]))            # gold TRUE  — correct today
        @test !isempty(_tcb(p60, "!(q 4)\n", [:q, :s]))            # gold TRUE  — correct today
        @test isempty(_tcb(p60, "!(q 1)\n", [:q, :s]))             # gold FALSE — correct today
        @test_broken isempty(_tcb(p60, "!(q 2)\n", [:q, :s]))      # gold FALSE — DERIVED FROM NOTHING
    end
end
