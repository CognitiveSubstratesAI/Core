# test_frozen_call_decline.jl — a head the space DEFINES must never be compiled as DATA.
#
# ─── THE DEFECT THIS GATE EXISTS FOR (measured 2026-09-03) ───────────────────────────────────────
# `ANormal.jl:341` splits CALL from DATA on `is_fun`, a STATIC set, and `compile_definition` lowers
# ONE FORM — so `funs` holds ONE head. Self-recursion and grounded primitives lift into
# `chain (metta …)`; every CROSS-HEAD call was classified as data. In `let`-value position the bound
# variable then unified with the UNEVALUATED TERM:
#
#     fl  ❌  (= (fl $n) (function (unify $ix (upto 0 $n) (return (map-atom $ix $x (fib $x))) …
#
# and because `map-atom`'s list parameter is typed `Expression`, it deconsed that raw term as data
# and the HEAD SYMBOL LEAKED INTO THE ANSWER:  !(f2 5) ⟹ ((+ upto 1) 1 6)   want (1 2 3 4 5 6).
#
# 🔴 THE REASON THIS IS A GATE AND NOT A NOTE: the lane reported `compiled=3, fell_back=0,
# exhausted=[]`. Accepted, nothing refused, budget untouched — a WRONG ANSWER with every status
# field green. No existing differential caught it because no corpus program passed a
# recursively-built list to an `Expression`-typed stdlib parameter.
# [[feedback_oracle_inherits_corpus_coverage]]
#
# ⚠️ WHAT IS ASSERTED HERE IS THE REFUSAL, NOT A REPAIR. `compile_definition` now DECLINES such a
# clause, and the caller loads the source form so the interpreter answers it. The real fix is
# PeTTa's: register every `(= (F …) _)` in a whole-program pre-pass so the call resolves instead of
# freezing (`docs/architecture/CROSS_ENGINE_COMPILERS.md` §2). When that lands, the ANSWER assertions
# below must all still hold and the `fell_back` ones become the thing to revisit — deliberately, by
# reading this comment, not by deleting a red line.
using MeTTaCore
using Test

const _FZ = MeTTaCore.Eval

"Answers for `program` through the compiled lane, as (query => sorted answers)."
function _fz_compiled(program::AbstractString; max_steps::Int = 512_000)
    r = MeTTaCore.compile_run(program; max_steps = max_steps)
    (answers = Dict(q => sort(collect(a)) for (q, a) in r.answers),
        compiled = r.compiled, fell_back = r.fell_back, exhausted = r.exhausted)
end

"Interpreter oracle over the same forms, in order, in one Space."
function _fz_interp(program::AbstractString)
    sp = _FZ.Space()
    _FZ.load_core_stdlib!(sp)
    out = Dict{String, Vector{String}}()
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        res = _FZ.load_metta!(sp, bang ? "!" * f : f)
        bang && (out[String(f)] = sort(String[string(x) for y in res
                                              for x in (y isa AbstractVector ? y : [y])]))
    end
    out
end

const _FZ_BASE = """
(= (fib \$n) (if (< \$n 2) \$n (+ (fib (- \$n 1)) (fib (- \$n 2)))))
(= (upto \$k \$n) (if (> \$k \$n) () (let \$rest (upto (+ \$k 1) \$n) (cons-atom \$k \$rest))))
"""

@testset "frozen cross-head call — refused, not miscompiled" begin

    @testset "the ANSWER is right, which is the only thing that finally matters" begin
        prog = _FZ_BASE *
               "(= (fib-list \$n) (let \$ix (upto 0 (- \$n 1)) (map-atom \$ix \$x (fib \$x))))\n" *
               "!(fib-list 0)\n!(fib-list 1)\n!(fib-list 6)\n!(fib-list 10)\n"
        c = _fz_compiled(prog)
        i = _fz_interp(prog)
        # DIFFERENTIAL FIRST — the interpreter is the oracle, not a literal I typed.
        for q in keys(i)
            @test c.answers[q] == i[q]
        end
        # …and pinned, because a differential where BOTH sides regress passes silently.
        @test c.answers["(fib-list 0)"] == ["()"]
        @test c.answers["(fib-list 6)"] == ["(0 1 1 2 3 5)"]
        @test c.answers["(fib-list 10)"] == ["(0 1 1 2 3 5 8 13 21 34)"]
        # NOT an empty answer group. This is what regressed, and `<EMPTY>` is what it looked like.
        @test all(!isempty, values(c.answers))
        # NOT a budget overrun — the whole point is that this defect was NOT exhaustion.
        @test isempty(c.exhausted)
    end

    @testset "the offending definition DECLINES; its neighbours still compile" begin
        prog = _FZ_BASE *
               "(= (fib-list \$n) (let \$ix (upto 0 (- \$n 1)) (map-atom \$ix \$x (fib \$x))))\n" *
               "!(fib-list 6)\n"
        c = _fz_compiled(prog)
        @test c.fell_back == 1      # exactly `fib-list`
        @test c.compiled == 2       # `fib` and `upto` are unaffected
    end

    @testset "the LEAKED HEAD SYMBOL is gone — the corruption, not just the emptiness" begin
        # Before the guard this answered `((+ upto 1) 1 6)`: `upto` deconsed as data, in the answer.
        prog = _FZ_BASE *
               "(= (f2 \$n) (let \$ix (upto 0 \$n) (map-atom \$ix \$x (+ \$x 1))))\n!(f2 5)\n"
        c = _fz_compiled(prog)
        @test c.answers["(f2 5)"] == ["(1 2 3 4 5 6)"]
        @test !any(a -> occursin("upto", a), c.answers["(f2 5)"])
        @test c.answers["(f2 5)"] == _fz_interp(prog)["(f2 5)"]
    end

    @testset "a DATA head is not a function — those bindings must still COMPILE" begin
        # The guard's predicate is "can I PROVE this is a function?", never "is this unknown?".
        # `Cons`/`Pair` have no rules, so they are data and must cost no coverage.
        for (prog, want) in [
            ("(= (mk \$x) (let \$y (Cons \$x Nil) \$y))\n!(mk 7)\n"    => "(Cons 7 Nil)"),
            ("(= (mk2 \$x) (let \$y (Pair \$x \$x) \$y))\n!(mk2 7)\n"  => "(Pair 7 7)"),
        ]
            c = _fz_compiled(prog)
            @test c.fell_back == 0                     # COMPILED, not rescued by fallback
            @test only(values(c.answers)) == [want]
        end
    end

    @testset "ARITY is part of the question — the `S` counterexample" begin
        # `b1_equal_chain.metta` defines `S` as the SKI combinator at arity 3 and USES it as a Peano
        # constructor at arity 1. A NAME-keyed guard would refuse the arity-1 binding as a "known
        # function" and cost coverage on a clause that was always correct. `Tabling._rules_of` is
        # name-keyed, which is exactly why this guard does not reuse it.
        prog = "(= (S \$x \$y \$z) (\$x \$z (\$y \$z)))\n" *
               "(= (peano \$n) (let \$y (S \$n) \$y))\n!(peano 4)\n"
        c = _fz_compiled(prog)
        @test c.fell_back == 0                          # arity 1 ≠ arity 3 ⇒ DATA ⇒ still compiled
        @test c.answers["(peano 4)"] == ["(S 4)"]
    end

    @testset "the defect is not `let`-specific — an `if` ARM freezes the same way" begin
        # `translate_expr` returns the same frozen term for a branch arm, so the guard walks nested
        # goals (`all_goals`) rather than only top-level ones.
        prog = _FZ_BASE *
               "(= (pick \$b \$n) (if \$b (upto 0 \$n) ()))\n!(pick True 3)\n!(pick False 3)\n"
        c = _fz_compiled(prog)
        i = _fz_interp(prog)
        @test c.answers["(pick True 3)"] == i["(pick True 3)"]
        @test c.answers["(pick False 3)"] == i["(pick False 3)"]
        @test c.answers["(pick True 3)"] == ["(0 1 2 3)"]
    end
end
