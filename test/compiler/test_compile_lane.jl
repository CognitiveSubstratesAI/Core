# test_compile_lane.jl — COMPILER-PRIMARY execution must give the interpreter's answers.
#
# ─── THE ONLY ASSERTION THAT MATTERS ─────────────────────────────────────────────────────────────
# `compile_run` lowers each definition to minimal MeTTa and evaluates the IL. It is correct exactly
# when it answers what the interpreter answers on the same source. So every test here is a
# DIFFERENTIAL, and the interpreter is the oracle.
#
# ⚠️ THE TRAP THIS FILE IS SHAPED AROUND: `compile_run` falls back to source for declined definitions.
# A differential that passes because everything FELL BACK proves nothing about the compiler — it
# proves the interpreter equals itself. So the compiled cases assert `fell_back == 0`, and the
# strongest ones pass `fallback=false`, which turns a decline into an error instead of a rescue.
using MeTTaCore
using Test

const _CL_V = MeTTaCore.Eval

"Interpreter oracle: the same forms, in order, through one Space."
function _cl_interp(program::AbstractString)::Vector{Tuple{String, Vector{String}}}
    sp = _CL_V.Space(); _CL_V.load_core_stdlib!(sp)
    out = Tuple{String, Vector{String}}[]
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        res = _CL_V.load_metta!(sp, bang ? "!" * f : f)
        bang && push!(out, (String(f),
              sort(String[string(x) for y in res for x in (y isa AbstractVector ? y : [y])])))
    end
    out
end

_cl_sorted(a) = Tuple{String, Vector{String}}[(q, sort(v)) for (q, v) in a]

@testset "compile lane — compiler primary, interpreter as the IL's evaluator" begin

    @testset "DIFFERENTIAL: compiled answers == interpreter answers, with NOTHING falling back" begin
        for src in ("(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n!(f 7)\n",
                    "(= (inc \$x) (+ \$x 1))\n!(inc 41)\n",
                    "(= (h \$x) (let \$y \$x (pair \$y \$y)))\n!(h 3)\n")
            r = MeTTaCore.compile_run(src)
            @test r.fell_back == 0                        # the COMPILER produced this, not the fallback
            @test r.compiled > 0
            @test _cl_sorted(r.answers) == _cl_interp(src)
        end
    end

    @testset "fallback=false proves the compiled path alone answered" begin
        # If any definition were declined this errors instead of quietly producing the right answer.
        r = MeTTaCore.compile_run("(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n!(f 7)\n"; fallback = false)
        @test r.answers == [("(f 7)", ["7"])]
        @test r.fell_back == 0
    end

    @testset "INVARIANT 1 holds on the compiled lane too" begin
        # The defect fixed on 2026-08-08 for mc_run must not reappear here: a query may not see a
        # rule added after it. compile_run drives the same partition, so this is a regression lock.
        src = "(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n"
        r = MeTTaCore.compile_run(src)
        got = Vector{String}[sort(v) for (_, v) in r.answers]
        @test got == [["a"], ["a", "b"]]
        @test got == Vector{String}[v for (_, v) in _cl_interp(src)]
    end

    @testset "a DECLINED definition falls back to source and still answers" begin
        # Ground facts are not definitions and must not be counted as declines; a genuinely
        # uncompilable body must fall back rather than lose answers.
        src = "(edge a b)\n(= (q \$x \$y) (match &self (edge \$x \$y) (edge \$x \$y)))\n!(q a b)\n"
        r = MeTTaCore.compile_run(src)
        @test _cl_sorted(r.answers) == _cl_interp(src)     # answers preserved whatever the route
    end

    @testset "NO DOUBLE-LOADING: a compiled definition contributes once, not twice" begin
        # Loading both the IL form and the source form would not "prefer" the compiled one — MeTTa
        # dispatch yields EVERY match (Invariant 6), so answers would duplicate. This is the single
        # correctness constraint of the lane.
        src = "(= (f) one)\n!(f)\n"
        r = MeTTaCore.compile_run(src)
        @test r.answers == [("(f)", ["one"])]              # exactly one result, not ["one","one"]
    end

    @testset "multi-clause dispatch keeps ALL results" begin
        src = "(= (f 0) zero)\n(= (f \$x) other)\n!(f 0)\n"
        r = MeTTaCore.compile_run(src)
        @test _cl_sorted(r.answers) == _cl_interp(src)
        @test length(r.answers[1][2]) == 2                 # both clauses fired
    end

    @testset "empty program, and a program with no queries" begin
        @test isempty(MeTTaCore.compile_run("").answers)
        r = MeTTaCore.compile_run("(= (f) a)\n")
        @test isempty(r.answers) && r.compiled == 1
    end

    @testset "types are concrete — no Any containers" begin
        r = MeTTaCore.compile_run("(= (f) a)\n!(f)\n")
        @test r.answers isa Vector{Tuple{String, Vector{String}}}
        @test r.compiled isa Int && r.fell_back isa Int
    end
end
