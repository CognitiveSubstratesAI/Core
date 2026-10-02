# test_compiled_head_differential.jl — THE STANDING GATE FOR "WOULD THE TRIGGER CHANGE ANY ANSWER?"
#
# Runs `test/standard/conformance` TWICE over the same definitions — once interpreted, once with
# EVERY head `jit_head!`-compiled — and compares every `!` directive. The interpreter is the oracle.
#
# 🔴 WHY IT IS A GATE AND NOT A ONE-OFF MEASUREMENT. The first-call trigger compiles everything on
# first call, so "every head compiled" IS the trigger's threshold-1 configuration. Every divergence
# here is a WRONG ANSWER IN PRODUCTION the day the trigger ships. Without this gate, the next fix can
# introduce a divergence that nobody sees until then — which is exactly how
# `(= (t3 $x) (+ 1 (g $x)))` came to answer `(+ 1 6)` against the interpreter's `7` with a green
# suite for weeks: nothing had ever compared the two lanes' ANSWERS over a corpus.
#
# ─── THE 11 KNOWN DIVERGENCES ARE PINNED BY EXACT VALUE ─────────────────────────────────────────
# `chd_pins.jl` is GENERATED from a real run, not hand-written. The set must match EXACTLY, so:
#   * a NEW divergence fails the run;
#   * a PINNED divergence whose VALUE CHANGES fails too — the half a bare count would miss;
#   * a divergence that DISAPPEARS fails, which is the "Unexpectedly Passed" signal: a fix landed,
#     so regenerate the pins deliberately. 🔴 REGENERATE ONLY TO RECORD A FIX, NEVER TO MAKE A RED
#     RUN GREEN.
# Known classes, and the lane each belongs to (measured by re-running with `CODEGEN_ENABLED=false`):
#   A  6 cases  `()` vs `(())`           `help!` ×5, `pragma! type-check auto` ×1   CODEGEN
#   B  4 cases  `get-doc` AssertionFailed                                           CODEGEN
#   C  1 case   `add-atom &kb (Green $x)` writes `$x` UNSUBSTITUTED                 PLAN LANE
#   (a 12th, `import_prolog_functions_from_file`, lives in the MeTTa-Library-Pack corpus, which is
#    under `dev-zone` and so is NOT part of this in-repo gate — see the note on corpora below.)
#
# ⚠️ THE CORPUS IS IN-REPO ON PURPOSE. `~/dev-zone/MeTTa-Library-Pack` has 132 more files and found
# the 12th divergence, but dev-zone is a reference-only symlink that need not exist, and a gate that
# silently skips its corpus reports a clean pass over nothing. Run the wider sweep by hand:
#     Core/tools/warm_suite.sh file workflows/compiled_head_differential_run.jl
using Test
using MeTTaCore

include(joinpath(@__DIR__, "..", "..", "..", "workflows", "compiled_head_differential.jl"))
const CHD = CompiledHeadDifferential
include(joinpath(@__DIR__, "chd_pins.jl"))

# ⚠️ ABSOLUTE-FROM-@__DIR__, NOT CWD-RELATIVE. A corpus path resolved against the working directory
# makes the whole gate VACUOUS when the runner's directory changes, and it reports a clean pass while
# reading nothing — [[feedback_test_corpus_paths_must_anchor_not_cwd]].
const _CONF = normpath(joinpath(@__DIR__, "..", "standard", "conformance"))

@testset "compiled-head differential — every answer, interpreted vs fully compiled" begin
    # ── ANTI-VACUITY FIRST, BECAUSE A ZERO HERE IS THE FAILURE MODE ──────────────────────────────
    @test isdir(_CONF)
    # 🔴 THE LANE SWITCH MUST BE ON. `CODEGEN_ENABLED` is process-global, and MEASURED 2026-10-01 an
    # earlier probe in a shared warm daemon left it FALSE: the next run reported `native 0` and ONE
    # divergence instead of twelve — a 92% drop that reads as progress. Asserted, not assumed.
    @test MeTTaCore.CompilerEmitJulia.CODEGEN_ENABLED[]

    r = CHD.run_corpus([_CONF], 0)
    t = r.totals

    # The run must be CAPABLE of observing the defect class before its result means anything.
    @test !CHD.vacuous(t)
    @test !CHD.codegen_off()
    @test t.files == CHD_TOTALS.files                  # the corpus was really read, all of it
    @test t.answered == CHD_TOTALS.answered            # and every directive really answered
    @test t.answered == t.directives                   # none silently produced nothing
    # 🔴 FLOORS, NOT "> 0". MEASURED 2026-10-02: a swallowed `UndefVarError` made EVERY head
    # decline — `native 0, plan 0, declined 1270` — and this file would have reported ZERO
    # DIVERGENCES and passed, because a dead compiler diverges from nothing. `> 0` would have
    # caught that particular collapse; a FLOOR also catches a partial one, which is the likelier
    # shape when a guard is widened by accident. Current: 282 native, 155 plan.
    @test t.native >= 200
    @test t.plan >= 100
    # 🔴 AND A CRASH IS NOT A DECLINE. Every compile path now funnels through
    # `Eval.record_jit_error!`, so this is the assertion that a silent emitter failure cannot
    # masquerade as "that head was out of scope".
    @test t.jit_errors == 0
    @test MeTTaCore.Eval.jit_errors() == 0

    # ── THE PINNED SET, EXACTLY ──────────────────────────────────────────────────────────────────
    got = sort([(basename(d.file), d.directive, d.interp, d.compiled) for d in r.divergences],
               by = x -> (x[1], x[2]))
    pinned = sort([(p[1], p[2], p[3], p[4]) for p in CHD_PINS], by = x -> (x[1], x[2]))

    # The count first, so a mismatch reports a number rather than a wall of text.
    @test length(got) == length(pinned)

    # Then each entry BY VALUE. Reported per entry so a failure names the file and directive instead
    # of printing two whole sets — [[feedback_attribute_per_case_not_per_class]].
    for p in pinned
        @test p in got                                 # a pinned divergence VANISHED or CHANGED
    end
    for g in got
        @test g in pinned                              # a NEW or CHANGED divergence appeared
    end
end
