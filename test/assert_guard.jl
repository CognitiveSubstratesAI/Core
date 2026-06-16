# test/assert_guard.jl — silent-test guard, shared across Core test scripts.
#
# WHY. A green assert-based test is only trustworthy if its failure-detection actually FIRES.
# Two ways an assert suite silently always-passes:
#   (1) WRITTEN-BUT-NOT-FIRED — an `assertEqual` whose LHS reduces to empty/unreduced may never
#       produce a result, so a per-assert "no error" check sees nothing and passes.
#   (2) VACUOUS DETECTOR — the script's error-detection predicate (a string-absence
#       `!occursin("Error")`, or an `_errs` filter) goes vacuous when the evaluator's error
#       OUTPUT SHAPE changes — most dangerously across the Minimal vs full-Eval harnesses, where
#       the same assertions are reused but `qm` differs.
# Surfaced by the 2026-06-16 MOSES audit (docs/MOSES_AUDIT_2026-06-16.md); upstream metta-moses
# guards it in scripts/run-tests.py by comparing WRITTEN asserts (count of `!(assertEqual` lines)
# to FIRED asserts (runtime ✅ markers). Running test_moses_minimal with a working detector
# immediately exposed a real reduct divergence the full-Eval "227/227" had hidden.
#
# CONVENTION — every assert-based Core test script should do all three:
#   1. WRITTEN-VS-FIRED: run N `!(assertEqual …)` directives in one call, then
#                        `@test length(results) == N`.   (catches written-but-not-fired)
#   2. NO-FAILURES:      `@test isempty(<your error filter>(results))`.
#   3. NEGATIVE CONTROL: call `assert_harness_discriminates(qm, iserr)` ONCE per harness in setup
#                        (this file) — proves a known mismatch IS flagged and a known match is NOT,
#                        so rules 1-2 are meaningful rather than vacuous.
#
# PLN/MOSES/standard tests already satisfy rule 1 (`@test length(rs) == N`); they should add the
# rule-3 self-check. The full-Eval string-absence scripts (ECAN/types/MOSES-`aok`) carry an inline
# rule-3 control. New scripts: include this file and call assert_harness_discriminates in setup.

using Test

"""
    assert_harness_discriminates(qm, iserr; label="harness")

Negative control for an assert harness. `qm(expr::String)` runs a `!(assertEqual …)` directive
and returns the harness's result value; `iserr(result)::Bool` is the script's failure-detection
(e.g. `rs -> !isempty(_errs(rs))`, or `rs -> occursin("Error", string(rs))`). Asserts that the
harness + detector DISCRIMINATE: a known mismatch is flagged, a known match is not — so the
script's green assertions cannot be silently vacuous on this harness.
"""
function assert_harness_discriminates(qm, iserr; label = "harness")
    @testset "$label discriminates (silent-test guard)" begin
        @test !iserr(qm("!(assertEqual 1 1)"))   # known MATCH    → must NOT be flagged
        @test  iserr(qm("!(assertEqual 1 2)"))   # known MISMATCH → must be flagged (else vacuous)
    end
end
