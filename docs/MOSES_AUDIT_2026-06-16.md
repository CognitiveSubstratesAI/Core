# MOSES faithfulness audit — Core lib/MOSES vs upstream metta-moses

**Date:** 2026-06-16. **Method:** multi-agent, grounded (file:line on both sides),
adversarially verified (each finding independently re-checked; default-refuted).
**Coverage:** all 33 `lib/MOSES/*.metta` across 5 subsystems; 18 findings → **14 confirmed,
4 refuted**. Run: `wf_eea3c0a7-cf6` (25 agents).

## Verdict

**The port is faithful — no HIGH-severity code bugs.** Core is a *documented deliberate
subset* of upstream (one deme, boolean behavioral scorer, `hillclimbC` only; feature-selection,
other optimizers, and runMoses bookkeeping intentionally dropped — `run_moses.metta:7-13`).
All deferrals are on-record and internally consistent (critic: 0 uncovered files; all
absence-risks are documented simplifications). The **real weakness is the test suite**, not the code.

## The test suite is the weak link (the silent-test class)

`test_moses.jl` reports 227/227, but the confidence is softer than the count:
- **`aok` (test_moses.jl:49) gates ~212 of 227 assertions and is a STRING-ABSENCE check** —
  `!occursin("Error", …) && !occursin("AssertionFailed", …)`. It does NOT assert the result
  equals the expected value. An assert whose LHS silently reduces to empty (no comparison →
  no error string) **passes vacuously.**
- **No negative control** — no `@test !aok(<known mismatch>)` exists, so there is no proof
  `aok` can return false at all.
- **Headline end-to-end claims (M4-b/M5-b "runMoses learns OR") are commented out**
  (test_moses.jl:435) — "verified out-of-band," not executed in CI.
- Non-discriminating fallbacks: e.g. `… || occursin("1", string(...))` (test_moses.jl:41)
  passes on almost any output.

**Fix (adopt upstream's guard):** upstream `scripts/run-tests.py` cross-checks **written vs
fired** asserts — it statically counts `!(assertEqual` lines and compares to runtime `✅`
markers, flagging a mismatch as failure even on exit 0. Core should: (1) make `aok` a real
equality check (or count `!(assertEqual` in the loaded string vs non-Error results, like the
PLN tests' `@test length(rs) == N`); (2) add a negative control; (3) un-comment / actually
run the M4-b/M5-b learning claims.

## Confirmed code findings

| Sev | Kind | Where | Note |
|---|---|---|---|
| med | divergence | optimization (hillclimb) | Core moves on ANY strict score increase; upstream requires beating incumbent by **epsilon=0.5**. Same for integer scores; **DIVERGES for fractional scores — exactly what PLN probabilistic fitness produces.** Revisit when wiring PLN-MOSES. |
| med | weak-test | reduct (`andCut`, `reduce-to`) | `andCut` tested on 3 of upstream's 9 cases; `reduce-to` only on shallow (≤2 depth) examples — deep recursion paths untested. |
| med | weak-test | optimization+scoring | happy-path only: no `evaluate` ERROR branch, no tie-break (incumbent-kept-on-tie), no empty/single `neighborsOf` boundary. |
| low | bug (upstream) | tree.metta:104-115 | **Core is CORRECT** — fixes upstream's `$pareantIdx` typo (unbound var) + a use-before-bind. Core-faithful-fix of an upstream defect. |
| low | gap | tree.metta:70-79 | `getNodeById` lacks upstream's `(getNodeById Nil $id)` guard. Reachable only via malformed/out-of-range traversal. |
| low | weak-test | metapopulation.metta:37 | `selectExemplar` empty-pool path untested — `(car-atom ())` would crash where upstream returns an Error. Add a 0-element fixture. |
| low | divergence | rte_helpers.metta:76-82 | `addLiterals` drops upstream's explicit dedup; **harmless only if the backend's `union-atom` dedups**. MORK backend dedups; verify the **Minimal backend** does too (else duplicate guards). |
| low | divergence | scoring (`scoreProgram`) | bscore convention (0/-1 summed, perfect=0); deliberately not `fitness.metta`'s penalized path. Documented. |
| info | gap/divergence | tree/instance/optimization/utilities | documented deferrals (feature-selection helpers, instance conversion layer, hillclimbC-only) + dialect choices (`foldl` arg order, `concatT` vs `union-atom`) — deliberate, internally consistent. |

## PLN ↔ MOSES integration point (for the deferred coupling)

`scoring.metta:62` — `(= (compareAndScore $a $b) (if (== $a $b) 0 -1))` — the boolean
per-row scorer (consumed by `scoreRow`, scoring.metta:66-67). **PLN-uncertain fitness plugs
in here:** replace the 0/-1 step with a PLN truth-value distance (strength/confidence-weighted
divergence between predicted and expected). Note the hillclimb-epsilon divergence above will
matter once scores become fractional.

## Recommended follow-ups (priority order)
1. **Harden the MOSES test harness** (the silent-test fix above) — highest value; the green
   count currently overstates confidence.
2. Add the missing boundary/negative tests (selectExemplar empty pool, evaluate ERROR, tie-break).
3. Verify the Minimal-backend `union-atom` dedup for `addLiterals` (low risk, quick check).
4. When building PLN-MOSES: extend `compareAndScore` (scoring.metta:62) + decide the
   hillclimb epsilon for fractional scores.
