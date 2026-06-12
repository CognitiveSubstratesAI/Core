# Adopting standard MeTTa: only grounded symbols + `=`-rule stdlib (no special-form layer)

**Decision (2026-06-12):** Core should adopt the standard MeTTa architecture as it exists in
**hyperon-experimental** (the port reference). The whole language is **typed stdlib symbols**, and there
are exactly **two** kinds of thing — no third "interpreter special-form" category.

## The model (this is all there is)

Every symbol in MeTTa's corelib has a type and is realized in exactly ONE of two ways:

1. **Grounded** — a host (Rust/Julia) function. Includes arithmetic and comparisons (`+ - * / % < == …`),
   space ops (`add-atom remove-atom get-atoms new-space match`), expression ops (`cons-atom decons-atom
   car-atom cdr-atom size-atom index-atom`), the evaluation primitives (`eval evalc chain unify function
   return collapse-bind superpose-bind metta`), and reflection (`get-type get-metatype sealed quote …`).
   These can't be expressed in pure MeTTa — they touch the host, the space, or evaluation control.

2. **`=`-rule** — defined IN MeTTa, in `stdlib.metta`, on top of the grounded set:
   ```metta
   (= (if True  $then $else) $then)
   (= (if False $then $else) $else)
   (= (let  $pattern $atom $template) (unify $atom $pattern $template Empty))
   (= (let* $pairs $template) (chain (decons-atom $pairs) $ht (unify ($head $tail) $ht …)))
   ```
   `if let let* case switch collapse superpose and or not xor foldl-atom map-atom filter-atom …` are ALL
   here — ordinary `=` rules, NOT interpreter built-ins.

**The evaluator is therefore just two rules** (this is the entire interpreter):
1. head is **grounded** → call the host function;
2. otherwise → query `(= (head args) $x)` and rewrite, nondeterministically (OutcomeSet).

There is no `if`/`let`/`case`/`collapse` logic *in the evaluator*. Those are stdlib `=` rules that get
loaded and bottom out in grounded ops. (Earlier framing called the grounded evaluation primitives an
"11-instruction interpreter core" — that's misleading: `eval`/`chain`/`unify`/`function`/`collapse-bind`/
… are just grounded stdlib symbols, same bucket as `+` and `car-atom`. They are not a separate layer.)

## Core's divergence

Both Core evaluators invented the illegitimate **third category** — they hardcode `if`/`let`/`let*`/
`case`/`switch`/`collapse`/`match` as Julia branches (`EvalND.jl:110-181`, and similarly `eval_metta`):

| | semantics | shape |
|---|---|---|
| `eval_metta` | non-standard (single-value, first-match, empty-match→`()`) | special-form switch in Julia |
| `eval_nd` | OutcomeSet (≡ hyperon/CeTTa result model) | **still** a special-form switch in Julia |

`eval_nd` is NOT standard and NOT the destination — there is no `eval_nd` in MeTTa. It's scaffolding; its
only standard property is its `(value,bindings)` result model. Reuse its machinery (unify, env-merge,
fan-out, hygiene, grounded dispatch) to build the grounded set, then DELETE both `eval_nd` and
`eval_metta`. Neither survives.

## Target = the two-rule evaluator + the two symbol categories

1. **Grounded registry (Julia):** register the corelib grounded symbols as host functions (many already
   exist in Core's grounded layer — audit against hyperon's Rust stdlib registrations).
2. **Load `stdlib.metta` (`=` rules):** port hyperon-experimental's `stdlib.metta` into Core so
   `if`/`let`/`case`/… are MeTTa, not Julia.
3. **Evaluator = grounded-dispatch + rewrite-by-`=`**, returning an OutcomeSet. Delete every special-form
   branch and both legacy evaluators; delete the SD-2/SD-3 library workarounds (correct semantics from
   the grounded core dissolves them).

## Port reference (hyperon-experimental — read these, don't re-derive)

- `lib/src/metta/runner/stdlib/stdlib.metta` — the `=`-rule symbols (1421 lines).
- `lib/src/metta/runner/stdlib/*.rs` — the grounded registrations (which symbols are host functions).
- `lib/src/metta/interpreter.rs` — the grounded evaluation primitives (`eval`/`chain`/`unify`/…).
- The corelib doc the user shared (the typed symbol list) — the authoritative surface to cover.

## Plan (ordered, multi-session)

- **Phase 0 — prototype the two-rule evaluator:** grounded-dispatch + rewrite-by-`=` returning an
  OutcomeSet; load a tiny ported stdlib (`if`, `let` via `unify`); PROVE `if`/`let` evaluate as `=` rules
  with NO `if`/`let` code in Julia. Gate: frog/b3 fixtures pass.
- **Phase 1 — full stdlib:** port the rest of `stdlib.metta`; audit the grounded registry vs hyperon;
  gate on hyperon b-series + the dual ECAN tracker.
- **Phase 2 — libraries + flip:** migrate Core libs off the SD-2/SD-3 workarounds; route `run_metta`
  through the new evaluator.
- **Phase 3 — delete:** remove `eval_metta`, `eval_nd`, the special-form branches, the workarounds.

See `CONFORMANCE_AUDIT.md` (eval_nd's result model ≡ reference) and `E1_SCOPE.md`.
