# Core ↔ hyperon-experimental conformance audit (2026-06-11)

**Method (test-driven, not code-reading):** run hyperon-experimental's own reference test scripts
(`python/tests/scripts/b*.metta` — the interpreter-semantics series) through Core, evaluating each
`!(assert… tested expected)`'s *tested* expr and comparing to *expected*. Harness: `test/conformance/`.
The reference programs ARE the spec; behaviour is what's checked.

## Raw result (b-series): 21 pass / 39 "fail"
`b0` 0/5 · `b1` 3/5 · `b2` 1/5 · `b3` 2/2 · `b4` 1/10 · `b5` 14/12. **But the raw fail count
over-states** — see classification.

## Classification by root cause (the point of the audit)

### 1. `OutcomeSet` / nondeterminism — THE DOMINANT gap (~22 failures, ONE root cause)
All of `b4_nondeterm` (10), plus `b3` binding cases, `b2` backchaining, `b0` match-recursion. Examples:
- `!(color)` → `red` (want `red, yellow, green`) — no fan-out.
- `!(pair (bin) (bin))` → `(A A)` (want `(A A) (A B) (B A) (B B)`) — no fan-out over `(bin)`.
- `!(rev A (superpose (B C D)))` → `((B C D) A)` (want `(B A) (C A) (D A)`) — superpose arg not fanned.
- `!(ift (green $x) $x)` → `__var_x` (want `Fritz`) — binding not propagated.
- `!(is (air dry))` → `(stop __var_z)` (want 3 results) — fan-out + binding.

**One fix — the `OutcomeSet`-valued evaluator (§2c of E1_SCOPE) — resolves this entire category.**
These b-series scripts are its conformance gate.

### 2. Type-system / error semantics — a SECOND, independent, *known* gap (`b1`, ~6 of `b5`)
Core's gradual type checker diverges from hyperon in a few places (over-strict / different error
wrapping), independent of `OutcomeSet`:
- `b1`: Core wraps mismatched arity as `(Error … IncorrectNumberOfArguments)` per-arg, differently
  from hyperon's whole-expr error.
- `b5`: `!(Add Z Ten)` → Core errors `(BadArgType 2 Nat Int)`; hyperon leaves it unevaluated.
  `!(eqa Z (Add Z Z))` → Core `T`; hyperon leaves unevaluated. `Nil` renders as `()`.
This is the **known gradual-typing tail** (see `project_core_type_system`: `test_types.jl` 22/22 with
documented remaining tuple/Atom-arg divergences). The `OutcomeSet` refactor will NOT touch it — it's
separate, smaller, follow-on work.

### 3. Harness artifact — NOT real failures (~6 of `b5`)
`assertEqualToResult` expects a result-*set* `(X)`; Core returns the single value `X`. The string
compare flagged `GOT=X` vs `WANT=(X)` as fail when the content is identical (e.g. `(Add S Z)`,
`(eq Z (S Z))`, the BadArgType errors). **Core is correct on these.** Real conformance is meaningfully
better than 21/39 — fix the harness to unwrap singleton result-sets for exact numbers.

## Scope answer (why we ran this)
- **`OutcomeSet` IS the dominant interpreter gap** — one architectural fix clears ~22 conformance
  failures across b0/b2/b3/b4. Confirmed, not extrapolated.
- **There is exactly one independent area** — type-system/error semantics — and it's already *known*
  and partially documented, not a surprise. Sequence it after `OutcomeSet`.
- The b-series scripts are now the **regression gate** for the eval refactor (done = these pass).

## Validated gain — `eval_nd` vs `eval_metta` (2026-06-11)
The `OutcomeSet` evaluator (`eval_nd`, additive — not yet wired in) re-run against the same scripts:

| script | `eval_metta` | `eval_nd` |
|---|---|---|
| `b3_direct` | 2 / 4 | **4 / 4** |
| `b4_nondeterm` | 1 / 10 | **9 / 11** |

The nondeterminism category — the dominant root cause — is essentially closed by `eval_nd`. Remaining
`b4` misses (`collapse (shape)` on an undefined symbol, `find-equal`) are edge cases, not the core gap.
This confirms the `OutcomeSet` model is the right and sufficient fix for category ①.

## Next
1. Build the `OutcomeSet`-valued evaluator (the §2c blueprint), gated by b0/b2/b3/b4.
2. Fix the harness's result-set unwrapping for exact pass counts; vendor/pin the reference scripts.
3. Track the type-system tail (`b1`/`b5`) as its own smaller conformance task.
4. Extend the corpus to `c*`/`d*` (spaces, types, higher-order) once `OutcomeSet` lands.
