# Core ⇄ hyperon-experimental — comparison by hyperon's layer taxonomy

How hyperon organizes its stdlib (verified from `lib/src/metta/`):
- **Layer 1 — Minimal-MeTTa instructions** (`interpreter.rs`): the reduced instruction set the evaluator runs.
- **Layer 2 — Grounded operations** (`runner/stdlib/*.rs`): Rust-implemented atoms, one file per module.
- **Layer 3 — Standard-library rules** (`runner/stdlib/stdlib.metta`): MeTTa `(= …)` rules over Layers 1–2.

This sheet maps each hyperon item → Core status (✅ present · ⚠️ divergent · ❌ missing) and where it lives in Core.
Enumerated from source on both sides (hyperon `register_token`/`stdlib.metta`; Core `Minimal.jl` `TOKEN_REGISTRY`
+ `CoreMathOps.jl`/`CoreNumericOps.jl` + `stdlib.metta`/`CoreExtensions.metta`). Complements `CORELIB_COVERAGE.md`
(which is organized by *test corpus module*); this one is organized by *hyperon's implementation layer*.

> **Key cross-cutting divergence:** hyperon implements much of the assert family + several atom/control ops as
> **Layer-3 rules over a thin grounded floor**; Core implements several of them as **Layer-2 grounded ops**. This is
> an *implementation-shape* difference (⚠️), resolved this session to be architectural taste, NOT a semantic gap —
> except the measured assert multiset/message divergence (see `CORELIB_COVERAGE.md`, gated by `unit/debug.metta`).

---

## Component architecture — where the three layers sit (hyperon's build structure)

hyperon ships as a stack of Rust crates + FFI binding layers (per the official "Structure of the codebase").
The three layers below are **all internals of the single `./lib` crate**. Core is a **native-Julia reimplementation
that collapses hyperon's three rlib crates and eliminates the entire `c`+`python` FFI stack** — it is host-native
(like CeTTa, unlike hyperon's Python-via-C), so there is no foreign-language boundary to bridge.

| hyperon component | what it is | Core analog |
|---|---|---|
| `./hyperon-common` (rlib) | utility collections/refs, not MeTTa-specific | native Julia stdlib + utils (no separate unit) |
| `./hyperon-atom` (rlib) | Atom API: types, `matcher`, `iter`, `serial`, `subexpr` | `src/standard/Atoms.jl` + match/`unify` in `Minimal.jl` |
| `./lib` (rlib) | atomspace + interpreter + stdlib (= **L1/L2/L3** below) | `Minimal.jl` + `CoreMathOps`/`CoreNumericOps.jl` + `stdlib.metta`/`CoreExtensions.metta`; atomspace = MORK/PathMap `CoreSpace` |
| `./c` (libhyperonc) | C-API export via cbindgen, for non-Rust langs | — none (host-native; no FFI boundary) |
| `./python` (libhyperonpy + `hyperon`) | pybind11 proxy → C API + Python lib | — none (used directly from Julia; MeTTaJam HTTP = optional remote access) |
| `./repl` (metta_repl) | Rust REPL depending on `./lib` | `tools/repl.jl` (explicitly modeled on hyperon's `repl/` crate) |

**Takeaway:** Core ≈ hyperon's `common`+`atom`+`lib` reimplemented natively in Julia, with the `c`+`python` FFI
stack removed entirely. Everything below is the internals of that reimplemented `./lib`. (This is the PeTTa-thin /
CeTTa-peer model from `ARCHITECTURE_TARGET.md`: a native host-language reimplementation needs no C-API binding layer.)

---

## Layer 1 — Minimal-MeTTa instructions  →  Core: COMPLETE

| hyperon instruction | Core | location |
|---|---|---|
| `eval` `chain` `unify` `cons-atom` `decons-atom` `function` `return` `collapse-bind` `superpose-bind` `metta` `id` | ✅ all present | `Minimal.jl` interpreter dispatch |

Caveat: `chain` has the known **bare-computed-operand bug** (`$X` symptom) — `interpreter.metta` baseline 41 is
dominated by it. The instruction set is complete; the bug is a correctness divergence within `chain`.

---

## Layer 2 — Grounded operations (per `stdlib/*.rs` module)

### `arithmetics.rs` → ✅ complete
`+ - * / % < > <= >= == and or not` ✅ grounded (`Minimal.jl`); `xor` ✅ (Core has it as a Layer-3 rule, not
grounded — ⚠️ impl-shape); number/Bool literal tokenization ✅.

### `atom.rs` → 10/11
`get-type` `get-metatype` `size-atom` `index-atom` `unique-atom` `subtraction-atom` `intersection-atom`
`union-atom` `min-atom` `max-atom` ✅ (last two in `CoreMathOps.jl`). ❌ `get-type-space`.

### `core.rs` → 7/9
`if-equal` `nop` `match` `sealed` `==` `superpose` `_minimal-foldl-atom`(→Core grounded `foldl-atom`) ✅.
❌ `capture` · ❌ `pragma!` (gates ~5 of `core.metta`'s 8 corpus fails).

### `math.rs` → 16/18
All 16 `*-math` ops ✅ (`CoreMathOps.jl`, faithful, `unit/math.metta` 48/48). ❌ `PI` · ❌ `EXP` (constants).

### `debug.rs` → 1/3
`trace!` ✅. ❌ `print-alternatives!` · ❌ `=alpha` (grounded `AlphaEqOp`; test cases debug.rs:230-231; behind the hang).

### `string.rs` → 1/2
`println!` ✅. ❌ `format-args`.

### `space.rs` → 6/6 ✅
`new-space` `add-atom` `remove-atom` `change-state!` `get-state` `get-atoms` ✅ — but `change-state!`/`get-state`
behavior is ⚠️ divergent (`space.metta` baseline 1).

### `module.rs` → 2/5
`import!` `bind!` ✅. ❌ `include` · ❌ `mod-space!` · ❌ `print-mods!`.

### `package.rs` → 0/2
❌ `register-module!` · ❌ `git-module!`.

**Layer 2 totals: ~43 present / ~13 missing.** Missing cluster: module/package system (5), doc-display-adjacent,
`pragma!`/`capture`, `=alpha`/`print-alternatives!`, `format-args`, `PI`/`EXP`, `get-type-space`.

---

## Layer 3 — Standard-library rules (`stdlib.metta`)

### ✅ Present as faithful rules (rule in both)
`add-atoms` `add-reduct` `add-reducts` `assertIncludes`*  `car-atom` `cdr-atom` `empty`*  `filter-atom`
`first-from-pair` `for-each-in-atom` `get-doc` `get-doc-atom` `get-doc-function` `get-doc-params`
`get-doc-single-atom` `if` `if-decons-expr` `if-error` `intersection` `is-function` `let` `let*` `map-atom`
`noeval`*  `noreduce-eq` `quote`(⚠️ constructor form) `return-on-error` `subtraction` `switch` `switch-internal`
`switch-minimal` `undefined-doc-function-type` `union` `unique` `unquote`   *(\* added this session)*

### ⚠️ Divergent — hyperon = Layer-3 rule, Core = Layer-2 grounded (impl-shape; semantics ≈ same)
`assertEqual` `assertEqualToResult` `assertAlphaEqualToResult` (+ measured **multiset + message** gap, gated
`unit/debug.metta` baseline 2) · `case` · `collapse` · `atom-subst` · `foldl-atom` · `new-state`

### ❌ Missing (13)
`assert` · `assertEqualMsg` · `assertEqualToResultMsg` · `assertAlphaEqual` · `assertAlphaEqualMsg` ·
`assertAlphaEqualToResultMsg` · `help!` · `help-internal!` · `help-param!` · `help-space!` · `match-types` ·
`match-type-or` · `type-cast`

### ➕ Core-only (not in hyperon `stdlib.metta`)
`is-member` `length` `member` `xor` `zip` — Core convenience/extension rules (`CoreExtensions.metta`).

---

## Summary

| layer | hyperon items | Core present | divergent (impl/semantic) | missing |
|---|---|---|---|---|
| L1 minimal instructions | 11 | 11 | `chain` bug | 0 |
| L2 grounded ops | ~56 | ~43 | `change-state!`/`get-state` | ~13 |
| L3 stdlib rules | ~57 | ~36 faithful | ~8 (grounded-vs-rule) | 13 |

**Reading it:** the *evaluator* (L1) is complete; the *grounded floor* (L2) is mostly there minus the
module/package system and a handful of peripherals; the *rule library* (L3) is ~36 faithful + 8 shape-divergent
(grounded where hyperon rules) + 13 missing. The 13 missing L3 + 13 missing L2 ≈ the "25 missing" headline in
`CORELIB_COVERAGE.md` (different slicing of the same gap). None of the missing are exercised by the 26 integration
scripts, which is why `test_conformance.jl` is 234/234 while the function floor is incomplete.

Provenance: hyperon `lib/src/metta/{interpreter.rs, runner/stdlib/{arithmetics,atom,core,math,debug,string,space,
module,package}.rs, stdlib.metta}`; Core `src/standard/{Minimal.jl, CoreMathOps.jl, CoreNumericOps.jl, stdlib.metta,
CoreExtensions.metta}`. Counts are approximate (±a couple) where a name is both a rule and a grounded helper.
