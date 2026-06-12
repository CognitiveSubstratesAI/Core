# Adopting standard MeTTa: minimal interpreter + stdlib-in-MeTTa

**Decision (2026-06-12):** Core should adopt the *standard MeTTa architecture* — a minimal interpreter
core plus the language defined in MeTTa — not just swap its tree-walking evaluator. Verified against
hyperon-experimental source.

## The finding (verified, not asserted)

Standard MeTTa (hyperon-experimental) splits evaluation in two:

1. **A minimal interpreter core** — `lib/src/metta/interpreter.rs` implements ONLY ~11 primitive
   instructions: `eval`, `evalc`, `chain`, `function`, `return`, `unify`, `cons-atom`, `decons-atom`,
   `collapse-bind`, `superpose-bind`, `metta`. That is the entire interpreter.

2. **The language, defined IN MeTTa** — `lib/src/metta/runner/stdlib/stdlib.metta` (1421 lines) defines
   `if`, `let`, `let*`, `case`, `switch`, `collapse`, `superpose`, `and`/`or`/`not`, `match`, list ops,
   … as ordinary equalities on top of the minimal core:
   ```metta
   (= (if True  $then $else) $then)
   (= (if False $then $else) $else)
   (= (let  $pattern $atom $template) (unify $atom $pattern $template Empty))
   (= (let* $pairs $template) (chain (decons-atom $pairs) $ht (unify ($head $tail) $ht …)))
   ```
   `if`/`let`/`case`/`collapse` are NOT interpreter built-ins. (stdlib.metta:512,543,553,346,1204,1225.)

## Core's divergence (both evaluators are non-standard in shape)

| | semantics | architecture |
|---|---|---|
| `eval_metta` | non-standard (single-value, first-match, empty-match→`()`) | hardcoded forms in Julia |
| `eval_nd` | **standard OutcomeSet** (verified ≡ hyperon/CeTTa) | **still hardcoded** — `if`/`let`/`let*`/`case`/`switch`/`collapse`/`match` are Julia branches (`EvalND.jl:110-181`) |

So `eval_nd` fixed the *semantics* but kept the *wrong architecture*. "Adopt standard MeTTa" means
adopting the **minimal-core + stdlib-in-MeTTa** shape, which dissolves BOTH the evaluator duality AND
the hardcoded-special-form problem — and the SD-2/SD-3 library workarounds along with them.

**Important — `eval_nd` is NOT standard and is NOT the destination.** There is no `eval_nd` in standard
MeTTa; the standard interpreter is the 11 named instructions below. `eval_nd` is a custom monolithic
function whose only standard property is that its *result model* (a set of `(value, bindings)`) matches
what the standard `eval`/`evalc` produce. It is **scaffolding**: we reuse its machinery (unify,
env-merge, cartesian fan-out, hygiene, grounded dispatch) to BUILD the standard instructions, then
DELETE `eval_nd` itself. Neither `eval_nd` nor `eval_metta` survives.

## Target architecture

1. **Minimal OutcomeSet interpreter (Julia):** implement only the ~11 instructions. `eval_nd` already
   has the hard machinery — unify, env merge, cartesian fan-out, alpha-rename hygiene, grounded dispatch
   — so this is a *refactor down* to the instruction set, deleting the special-form switch.
2. **Port `stdlib.metta` into Core:** `if`/`let`/`let*`/`case`/`switch`/`collapse`/`superpose`/`match`/
   `and`/`or`/`not`/list-ops as MeTTa definitions (Core dialect).
3. **Retire** `eval_metta`, `eval_nd`'s special-form branches, and the library SD-2/SD-3 workarounds.

## Payoff

- Literally hyperon's architecture → conformance by construction, not by chasing divergences.
- Special forms become MeTTa: inspectable, overridable, portable, debuggable in MeTTa.
- One move collapses: eval_metta/eval_nd duality + hardcoded switch + library workarounds.

## Plan (ordered, multi-session)

- **Phase 0 — prototype:** implement the instruction set (`eval`/`chain`/`unify`/`cons-atom`/
  `decons-atom`/`function`/`return`/`collapse-bind`/`superpose-bind`); load a tiny ported stdlib
  (`if`, `let` via `unify`); PROVE `if`/`let` work as MeTTa definitions, not Julia. Gate: the frog/b3
  fixtures still pass with `if`/`let` removed from Julia.
- **Phase 1 — full stdlib:** port the rest of stdlib.metta's forms; gate on hyperon b-series + the dual
  ECAN tracker.
- **Phase 2 — libraries + flip:** migrate Core libs off the workarounds; route `run_metta` through the
  minimal interpreter.
- **Phase 3 — delete:** remove `eval_metta`, the special-form branches, and the workarounds.

This is the genuine "adopt standard MeTTa" — larger than swapping evaluators, but the correct foundation.
See `CONFORMANCE_AUDIT.md` (eval_nd ≡ reference semantics) and `E1_SCOPE.md`.
