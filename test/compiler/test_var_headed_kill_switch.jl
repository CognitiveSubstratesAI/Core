# test_var_headed_kill_switch.jl — a VARIABLE-HEADED rule invalidates every compiled clause.
#
# THE DEFECT (measured 2026-09-03, fixed 2026-09-07). `(= ($f $x) …)` can fire on a call to ANY head.
# The compiled lane made its call/data decisions without accounting for that, so a compiled head
# answered WITHOUT the rule while the interpreter answered WITH it:
#
#     (= (g 1) one)
#     (= ($f $x) (caught $f $x))
#
#     COMPILED     !(g 1) -> one                  !(h 2) -> (h 2)
#     INTERPRETED  !(g 1) -> (caught g 1) | one   !(h 2) -> (caught h 2)
#
# 🔴 `fell_back == 0` IS THE SIGNATURE, and it is why this class is the worst one available: no
# error, no decline, no exhaustion — just FEWER ANSWERS, with every status field green. A guard that
# declines is safe; a guard that ACCEPTS WRONGLY is not.
#
# UPSTREAM AGREES, and named it before we measured it — MeTTaScript `eval.ts:1694-1697`:
# "A variable-headed runtime equation `(= ($f $x) …)` can fire on a call to ANY head, so nothing
# compiled can be trusted while one is loaded."
#
# ⚠️ DISTINCT FROM `_frozen_cross_head_call`. That guard is about a call FROZEN AS DATA and never
# reaches this clause — which is why widening it to follow the data (c4e0bce, 15/17 → 17/17) did not
# help here. Two different defects at the same seam.
using MeTTaCore
using Test

const _VH = MeTTaCore.Eval

"Compiled-lane answers for `program`, plus the accept/decline counts."
function _vh_compiled(program::AbstractString)
    r = MeTTaCore.compile_run(program; max_steps = 512_000)
    (answers = Dict(q => sort(collect(a)) for (q, a) in r.answers),
        compiled = r.compiled, fell_back = r.fell_back, exhausted = r.exhausted)
end

"Interpreter oracle over the same forms, in order, in one Space."
function _vh_interp(program::AbstractString)
    sp = _VH.Space()
    _VH.load_core_stdlib!(sp)
    out = Dict{String, Vector{String}}()
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        res = _VH.load_metta!(sp, bang ? "!" * f : f)
        bang && (out[String(f)] = sort(String[string(x) for y in res
                                              for x in (y isa AbstractVector ? y : [y])]))
    end
    out
end

@testset "a VARIABLE-HEADED rule gates the whole compiled lane" begin

    @testset "🔑 the ANSWERS match the interpreter — the defect was silent answer LOSS" begin
        prog = "(= (g 1) one)\n(= (\$f \$x) (caught \$f \$x))\n!(g 1)\n!(h 2)\n"
        c = _vh_compiled(prog)
        i = _vh_interp(prog)
        for q in keys(i)
            @test c.answers[q] == i[q]              # DIFFERENTIAL against the oracle, first
        end
        # …and pinned, because a differential where BOTH lanes regress passes silently.
        @test c.answers["(g 1)"] == ["(caught g 1)", "one"]   # TWO answers, not one
        @test c.answers["(h 2)"] == ["(caught h 2)"]          # the var-headed rule fires on `h` too
    end

    @testset "and it DECLINES rather than accepting — `fell_back=0` was the signature" begin
        prog = "(= (g 1) one)\n(= (\$f \$x) (caught \$f \$x))\n!(g 1)\n"
        c = _vh_compiled(prog)
        @test c.compiled == 0                        # nothing compiled while the rule is loaded
        @test c.fell_back > 0                        # …everything declined, which is the fix
        @test isempty(c.exhausted)                   # not a budget overrun
    end

    @testset "the gate LIFTS when no var-headed rule is present — no permanent coverage loss" begin
        # Without the rule, the same program compiles as before. The switch must be conditional on
        # the space's contents, not a blanket refusal.
        prog = "(= (g 1) one)\n!(g 1)\n"
        c = _vh_compiled(prog)
        @test c.compiled > 0                         # compiles again
        @test c.answers["(g 1)"] == ["one"]
    end

    @testset "a variable in an ARGUMENT is not a variable HEAD" begin
        # `(= (f $x) …)` is an ordinary rule — the head is the SYMBOL `f`. Only a head that IS a
        # variable trips the gate. Getting this wrong would decline essentially every program.
        prog = "(= (f \$x) (wrapped \$x))\n!(f 7)\n"
        c = _vh_compiled(prog)
        @test c.compiled > 0                         # NOT gated
        @test c.answers["(f 7)"] == ["(wrapped 7)"]
        @test c.answers["(f 7)"] == _vh_interp(prog)["(f 7)"]
    end

    @testset "the gate reads OWN atoms, not the loaded stdlib" begin
        # Scanning the whole space would let any var-headed rule in the stdlib zero out coverage
        # permanently. A plain program with a stdlib loaded must still compile.
        prog = "(= (h1 \$x) \$x)\n(= (h2 \$x) (h1 \$x))\n!(h2 5)\n"
        c = _vh_compiled(prog)
        @test c.compiled > 0
        @test c.answers["(h2 5)"] == ["5"]
    end
end
