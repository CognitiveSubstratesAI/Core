# Corelib coverage map — hyperon's 138 corelib functions vs Core's Minimal

The correctness deliverable: every corelib function, marked **present / missing / divergent**, and for
present ones **faithful-by-test vs present-untested**. This is the map that makes "where are we on
faithfulness" legible.

## Method (so it's trustable, not taken on faith)
- **Names** come from hyperon's `stdlib.metta` `@doc` index (138) — used ONLY as the checklist of names.
- **Present/missing** verified against Core's *actual source* (read, not doc-trusted): Minimal's
  `TOKEN_REGISTRY` grounded ops + the minimal-metta instruction set + type/error consts +
  `stdlib.metta`/`CoreExtensions.metta` rule defs + `CoreMathOps.jl`/`CoreNumericOps.jl`.
- **Faithful vs divergent** comes from the **unit corpus** (`test/standard/unit/`, hyperon's own
  `#[test]` cases) — behavioral ground truth, not my judgment.
- **HONESTY RULE:** "present" ≠ "faithful." A present function is only *certified faithful* if the unit
  corpus tests it AND it passes. Present-but-untested functions are explicitly flagged — we do not know
  they're faithful, only that they're registered.

## Progress log
- **add-reduct / add-reducts / add-atoms** — IMPLEMENTED (ported verbatim from hyperon stdlib.metta:567-683;
  the reduce is type-driven via the `%Undefined%` arg, verified; gated in unit/stdlib_space_sugar.metta).
  Missing 31→28.
- **min-atom / max-atom** — IMPLEMENTED (CoreMathOps.jl, faithful to atom.rs); atom divergences 5→3.
- **HARNESS FIX**: test_unit.jl now loads token-aware (mirrors load_metta!/hyperon's Tokenizer), so
  `bind!`-bound spaces (&stateAB, &ns) resolve. Improved space 2→1 (state-op `&stateAB` now passes).
- **Verified-faithful against hyperon+CeTTa this pass**: `new-space` is properly isolated; `get-atoms`
  scopes correctly (the earlier "leak" was the non-token-aware harness, not the interpreter).
- **NEW divergence logged**: a `let`-local `(new-space)` does NOT thread mutations in Minimal, but hyperon
  DOES (mod.rs uses `(let $newspace (new-space) …)`). Separate fix — orthogonal to add-reduct.

## Headline numbers
- **107 / 138 present** in source · **28 / 138 missing** (was 31; add-reduct family done).
- Of present: **math 48/48 + the green atom/text cases are faithful-by-test**; the rest are
  **present-untested** (registered, behavior not yet gated) OR **divergent** (corpus fails).
- Divergences measured by the corpus baselines: atom 5, core 8, space 2, interpreter 41(provisional).

---

## A. MISSING — 31 functions (verified absent from every Minimal layer). THE WORKLIST.

| category | functions | note |
|---|---|---|
| **assert family** (7) | `assertEqualMsg` `assertEqualToResultMsg` `assertAlphaEqual` `assertAlphaEqualMsg` `assertAlphaEqualToResultMsg` `assertIncludes` `=alpha` | additive; Minimal has only `assertEqual`/`assertEqualToResult`/`assertAlphaEqualToResult` |
| **space sugar** (3) | `add-reduct` `add-reducts` `add-atoms` | additive MeTTa rules over `add-atom` (present) |
| **help / doc display** (4) | `help!` `help-param!` `help-space!` `print-mods!` | build on `get-doc` (present) + `println!` (present) |
| **module system** (5) | `register-module!` `mod-space!` `module-space-no-deps` `include` `git-module!` | `import!` is present; these are the rest of the module surface |
| **type system** (4) | `type-cast` `match-types` `match-type-or` `get-type-space` | the type-coercion/universal-guard layer |
| **control / misc** (6) | `pragma!` `noeval` `empty` `capture` `format-args` `sort-strings` | `pragma!` gates 5 of core's 8 corpus fails |
| **error/type symbols** (2) | `BadType` `ErrorType` | error markers; `BadArgType`/`SpaceType` ARE present (Minimal.jl:714/672) |

Most of A is **additive** (new grounded ops or MeTTa rules) — the safe `math`-pattern. `pragma!` and the
type-system four are the higher-touch ones.

---

## B. DIVERGENT — present but the unit corpus fails (faithfulness gaps in present functions)

| module | count | cause (from the corpus) |
|---|---|---|
| **atom** | 5 | `min-atom`/`max-atom` (fix validated, **uncommitted**, → 3); `index-atom` error message (`IndexOutOfBounds` symbol vs `"Index is out of bounds"` string); 2 bare-predicate `filter-atom` (the `chain` bug) |
| **core** | 8 | `pragma!` missing (≈5) + `case`-on-`Empty`/`unify`-in-`case` divergence (≈3) |
| **space** | 2 | `change-state!`/`get-state` behavior |
| **interpreter** | 41 (provisional) | mostly **error-representation** mismatch + the **`chain` bare-operand bug** (symptom: a free var `$X`). NOT 41 functional bugs — needs the corrected `$X`-symptom classifier to split honestly |

The two cross-cutting roots behind most of B: the **`chain` bare-computed-operand bug** (delicate,
reverted once) and **error-representation** (partly fixed by `error_atom→String`; `index-atom` message
text remains).

---

## C. FAITHFUL-BY-TEST — present AND corpus-green (certified)

- **math (48/48):** `sqrt`/`pow`/`abs`/`log`/`trunc`/`ceil`/`floor`/`round`/`sin`/`asin`/`cos`/`acos`/
  `tan`/`atan`/`isnan`/`isinf`-`math` + (with the uncommitted change) `min`/`max-atom`.
- **atom (green subset):** `car-atom` `cdr-atom` `size-atom` `index-atom`(value) `filter-atom`(eval-wrapped)
  `map-atom` `foldl-atom`.
- **text:** the parser comment/escape cases (6/6).
- **minimal-metta instructions** exercised green by the corpus: `eval` `chain`(non-bare) `unify`
  `cons-atom` `decons-atom` `function` `return` `collapse-bind` `superpose-bind` `metta`.
- (Integration-faithful, separately: the 234/234 `test_conformance.jl` corpus.)

---

## D. PRESENT-UNTESTED — registered, but NOT gated by the unit corpus (we do NOT know they're faithful)

This is the honest middle, and it's large. Present in `stdlib.metta`/Minimal but with **no `unit/*.metta`
coverage**, so faithfulness is **unverified**:
- doc system: `get-doc` `get-doc-atom` `get-doc-function` `get-doc-single-atom` `get-doc-params`
  `undefined-doc-function-type`
- control/list: `switch` `switch-internal` `let` `let*` `is-function` `for-each-in-atom` `noreduce-eq`
  `if-decons-expr` `if-error` `return-on-error` `first-from-pair` `id` `nop` `if` `or` `and` `not`
- set ops: `unique` `union` `intersection` `subtraction` `unique-atom` `union-atom` `intersection-atom`
  `subtraction-atom`
- space/state: `new-space` `add-atom` `remove-atom` `get-atoms` `new-state` `match` `bind!` `context-space`
- arithmetic/compare/bool: `+ - * / % < > <= >= ==` `xor` (some hit via other tests, not directly gated)
- type: `get-type` `get-metatype` `if-equal` `BadArgType` `SpaceType`
- quote: `quote` `unquote` (note `quote` is a RECORDED DIVERGENCE — constructor form, not NotReducible)
- io: `println!` `trace!`

**These need unit coverage before any of them can be claimed faithful.** The extraction agents covered
the modules with `#[test]` cases in atom/core/math/text/space/interpreter; the corelib functions whose
hyperon tests live elsewhere (or are MeTTa-script-only) are the untested set. Closing D = extracting the
remaining hyperon test cases for these functions into the corpus.

---

## Recorded divergences (deliberate, not bugs — from STDLIB_FAITHFULNESS_REFERENCE.md)
- **Bool** = symbols (PeTTa-faithful), not grounded — intentional.
- **`quote`** = constructor form, not `(= (quote $atom) NotReducible)` — Minimal doesn't special-case
  NotReducible rule-bodies.
- **`unify`** = hybrid (structural + a PeTTa-style space-query for `get-doc`).
- **error message** = was `Sym`, now grounded `String` (fixed `5621587`); `index-atom` text still diverges.

## What "done" on this map means
1. **A → 0**: implement the 31 missing (mostly additive).
2. **B → 0**: fix the divergences — error-message text, `case`-on-`Empty`, state-ops, and the `chain`
   bare-operand bug (the delicate one).
3. **D → tested**: extract the remaining hyperon `#[test]` cases so present-untested becomes
   faithful-by-test (or surfaces as divergent). Until D is gated, the headline "107 present" overstates
   faithfulness — present is not faithful.

## Verification provenance
Present/missing: grepped+spot-verified against `Minimal.jl`/`stdlib.metta`/`CoreExtensions.metta`/
`CoreMathOps.jl`/`CoreNumericOps.jl` this pass (the ambiguous ~18 individually re-checked at source:line).
Faithful/divergent: the `test/standard/unit/` baselines. The `@doc` index was used for names only.
