# test_completion_resume.jl — completion by RESUMPTION vs RECOMPUTATION. §1.0 step 4 (loop half).
#
# ─── WHAT THIS IS ────────────────────────────────────────────────────────────────────────────────
# `_complete_resume!` is the Desouter §4.3 `completion/0` loop: take an (answers x dependencies)
# batch off a table's worklist, RESUME each suspended continuation with each answer, route results
# into the target table, repeat until no table has uncombined work. It replaces `_leader_pass`
# RECOMPUTATION — the "extension table" design the literature rejects.
#
# 🔴 IT IS OFF BY DEFAULT (`_RESUME_COMPLETION`) AND THIS FILE IS THE REASON IT STAYS OFF.
# The oracle for a rewrite of the engine core is AGREEMENT WITH THE ENGINE IT REPLACES, so this runs
# both and compares. Flipping the default belongs in the commit where that agreement covers the
# corpus — not before. `[[feedback_parity_vs_opt_in]]`
#
# ─── AND THE HONEST PART: MOST PROGRAMS DO NOT EXERCISE IT ───────────────────────────────────────
# Resumption engages only on a genuine VARIANT RE-ENTRY — the consumer branch, where a suspended
# continuation is recorded. `fib` does not qualify: `(fib (- $n 1))` reduces to a DIFFERENT variant
# key each call, so it is a plain memo with no suspension. Left recursion does qualify.
#
# So an "agreement" test over arbitrary programs is mostly VACUOUS — both paths agree because the
# resumption path never ran. Every case below therefore asserts, BEFORE comparing, whether it
# actually exercised resumption, and the file asserts that at least one case did. Without that a
# green run would mean nothing, which is the failure this session hit four separate times.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _CR = Eval

"""Run `query` under one completion strategy; return (answers, dependencies-recorded).

🔴 THE PROBE IS A CUMULATIVE COUNTER, NOT A SAMPLE OF `_DEPS`. It used to be the latter, and that
only worked because completion LEAKED its worklists and suspensions — audit finding #6, fixed
2026-08-17, where upstream frees every worklist at `'\$tbl_table_complete_all'`. Once cleanup was
correct the sample read ZERO for a run that had done real resumption work, and this file's whole
anti-vacuity argument would have inverted: a green run would again mean nothing. Counting the EVENT
instead of its residue cannot be falsified by correct cleanup."""
function _cr_run(prog::AbstractString, query::AbstractString, heads::Vector{Symbol}, resume::Bool)
    _CR.untable_all!()
    _CR._RESUME_COMPLETION[] = resume
    _CR._DEPS_RECORD[]       = resume
    deps = 0
    try
        s = Space(); load_core_stdlib!(s); load_metta!(s, prog)
        for h in heads; _CR.table!(h); end
        r = load_metta!(s, query)
        deps = _CR._DEPS_COUNT[]
        (sort(String[string(x) for y in r for x in (y isa AbstractVector ? y : [y])]), deps)
    finally
        _CR.reset_execution_flags!()   # restore the ENV default, never a literal — defaults move
        _CR.untable_all!()
    end
end

const _CR_REACH = "(edge a b)\n(edge b c)\n" *
                  raw"(= (reach $x $y) (match &self (edge $x $y) True))" * "\n" *
                  raw"(= (reach $x $y) (reach $y $x))" * "\n"
const _CR_FIB   = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n"

@testset "completion by resumption agrees with recomputation (§1.0 step 4)" begin

    @testset "the DEFAULT is RESUMPTION, and the reverse override works" begin
        # 🟢 FLIPPED 2026-08-16 after corpus-scale agreement AND a measured allocation win. This now
        # asserts the NEW default, and that `CORE_TABLING_RECOMPUTE=1` still reaches the old engine —
        # a differential you can only run one way has stopped being a differential.
        if get(ENV, "CORE_TABLING_RECOMPUTE", "") == "1"
            @test !_CR._RESUME_COMPLETION[]
            @test !_CR._DEPS_RECORD[]
        else
            @test _CR._RESUME_COMPLETION[]
            @test _CR._DEPS_RECORD[]      # both, or resumption silently completes nothing
        end
    end

    @testset "LEFT RECURSION — resumption really runs, and agrees" begin
        (a, _)  = _cr_run(_CR_REACH, "!(reach b a)\n", [:reach], false)
        (b, dp) = _cr_run(_CR_REACH, "!(reach b a)\n", [:reach], true)
        # ANTI-VACUITY FIRST: prove the resumption path had work before trusting the agreement.
        @test dp > 0
        @test a == b
        @test "True" in b
    end

    @testset "fib does NOT exercise resumption — recorded, not hidden" begin
        # `(fib (- $n 1))` reduces to a different variant key per call, so there is no variant
        # re-entry and no suspension: fib is a plain memo. Asserting the ZERO here is what stops a
        # later reader taking fib's agreement as evidence about resumption.
        (a, _)  = _cr_run(_CR_FIB, "!(fib 10)\n", [:fib], false)
        (b, dp) = _cr_run(_CR_FIB, "!(fib 10)\n", [:fib], true)
        @test a == b == ["55"]
        @test dp == 0                       # VACUOUS by construction — that is the point
    end

    @testset "the guard fires on a broken invariant, not on a large program" begin
        # `_complete_resume!`'s 1e6 batch guard exists to catch a worklist that re-offers a combined
        # pair forever. It must not be reachable by ordinary work, so assert the left-recursive case
        # completes far below it — a guard that trips on real programs is a bug, not a safety net.
        (b, dp) = _cr_run(_CR_REACH, "!(reach b a)\n", [:reach], true)
        @test dp > 0 && !isempty(b)         # completed without tripping the guard
    end
end
