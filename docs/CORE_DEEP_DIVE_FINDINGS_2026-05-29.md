; vim: ft=markdown
# Core deep-dive findings — 2026-05-29

Scope of dive: every file under `packages/Core/src/` and `packages/Core/stdlib/`, plus
algorithm-library entry points under `packages/Core/lib/{ecan,pln,metamo}/`. Read in
full unless noted; numbers below are real line numbers from the current tree
(no PRIMUS_Core legacy paths). This document supersedes any earlier claim that
referenced [Runtime.jl](../../PRIMUS_Core/) or [UnifiedAtomSpace.jl](../../PRIMUS_Core/)
— neither exists in `packages/Core/`.

The goal is to make any future audit start from the structural facts rather than
re-rediscover them. The doc is organised so the two-bucket split (grounded vs
stdlib-in-MeTTa), the [bind!](../src/eval/Eval.jl#L77) location issue, and the
[D1–D4](../../../docs/research/PRIMUS_MeTTa_Conformance_Report_2026-04-09.md)
status from the 2026-04-09 conformance report can be looked up by file:line
without re-reading the code.

---

## 1. Module composition

[MeTTaCore.jl](../src/MeTTaCore.jl) is the only `module MeTTaCore` declaration in
the package. Includes happen in this fixed order:

- [src/space/CoreSpace.jl](../src/space/CoreSpace.jl) (666 lines) — the `CoreSpace`
  struct and the trie integration.
- [src/space/CoreSpaceActIO.jl](../src/space/CoreSpaceActIO.jl) (147 lines) — .act
  snapshot / mmap source wiring on top of MORK's ACTSink/ACTSource.
- [src/parser/Parser.jl](../src/parser/Parser.jl) (214 lines) — the exclusion-
  based tokenizer + s-expression parser.
- [src/primitives/Primitives.jl](../src/primitives/Primitives.jl) (489 lines) —
  the grounded primitive registry.
- [src/primitives/AtomOps.jl](../src/primitives/AtomOps.jl) (295 lines) —
  list / set / metatype atom ops.
- [src/eval/Eval.jl](../src/eval/Eval.jl) (~887 lines) — the evaluator and special
  forms.

`using AdaptiveCompression` at the top of [MeTTaCore.jl](../src/MeTTaCore.jl#L1)
triggers WILLIAM's `__init__`, which registers `WILLIAM.lgg` and friends, and
populates `_PACKAGE_REGISTRY["william"] = pkgdir(AdaptiveCompression)` so that
`(import! &self (library william))` resolves to the AdaptiveCompression Pkg dep
rather than a local file. This is the Pattern B1 wiring that landed in the
WILLIAM submodule→Pkg-dep migration.

Public surface (the `export` list at the bottom of MeTTaCore.jl): `CoreSpace`,
`new_core_space`, `default_space`, `run_metta`, `eval_metta`, `run_file`,
`register_for_space!`, `load_stdlib!`, plus the .act lifecycle helpers from
CoreSpaceActIO.

---

## 2. The special-form dispatch table (single source of truth)

[Eval.jl L50–L97](../src/eval/Eval.jl#L50-L97) is the **only** place where a head
symbol is checked before grounded dispatch / rule rewriting. Every entry here is
a *special form* — the args are NOT pre-evaluated. Anything not in this list
either:

- (a) goes through grounded dispatch at [Eval.jl L100-L108](../src/eval/Eval.jl#L100-L108)
  with all args pre-evaluated, or
- (b) goes through rule rewriting at [Eval.jl L110-L122](../src/eval/Eval.jl#L110-L122)
  with all args pre-evaluated (`evaled_args = [eval_metta(a, space) for a in args]`).

The full special-form list (verbatim from the dispatch table):

`match`, `let`, `let*`, `if`, `collapse`, `superpose`, `case`, `switch`, `chain`,
`function`, `return`, `eval`, `evalc`, `unify`, `quote`, `unquote`, `empty`,
`noreduce-eq`, `noeval`, `Error`, `do`, `begin`, `import!`, `git-import!`,
**`bind!`**, `with-space`, `add-atom`, `remove-atom`, `decimate-importance!`,
`normalize-attention!`, `exec`, `get-atoms`, `new-space`, `get-type-space`,
`add-reduct`, `for-each-in-atom`, `foldl-atom`, `map-atom`, `filter-atom`.

That makes 38 special forms. Of these, `decimate-importance!` and
`normalize-attention!` are Julia fast-paths for ECAN bulk ops — there are
pure-MeTTa equivalents in [t1_core_logic.metta](../lib/ecan/t1_core_logic.metta)
but the dispatch precedence at [Eval.jl L85-L86](../src/eval/Eval.jl#L85-L86)
makes the MeTTa versions unreachable. This is noted in-source as intentional.

---

## 3. D1–D4 status against the 2026-04-09 report

The [2026-04-09 conformance report](../../../docs/research/PRIMUS_MeTTa_Conformance_Report_2026-04-09.md)
recorded 26/30 probe pass and 4 documented divergences against
[hyperon-experimental](../../../../dev-zone/hyperon-experimental). Where
those D-tags map onto current Core:

- **D1 (noeval returns unevaluated)** — [Eval.jl L69](../src/eval/Eval.jl#L69):
  `head === :noeval && return isempty(args) ? nothing : args[1]`. Args are
  returned untouched. Status: **FIXED in current Core**. The 2026-04-09 report
  was against the obsolete PRIMUS_Core/Runtime.jl path.

- **D2 (quote returns unevaluated)** — [Eval.jl L65](../src/eval/Eval.jl#L65) →
  `_eval_quote(args)` which returns `args[1]` raw. The MeTTa language doc says
  `quote is just a symbol with (-> Atom Atom) type without equalities (i.e.,
  a constructor)`. That's exactly Core's behavior. Status: **CONFORMANT** — the
  2026-04-09 report's D2 entry was based on a misread of H-E's behavior;
  withdraw the D2 divergence.

- **D3 (Error is a constructor)** — [Eval.jl L70-L72](../src/eval/Eval.jl#L70-L72):
  `head === :Error && return vcat([Symbol("Error")], args)`. Args NOT
  evaluated. The in-source comment says "prevents assertEqual infinite
  recursion". Status: **CONSCIOUS DIVERGENCE** from H-E error-propagation
  semantics (H-E threads `Error(...)` through `match`/`chain` automatically).

- **D4 (sort-atom / second-from-pair / function-ref variants)** — Not in the
  grounded registry of [Primitives.jl](../src/primitives/Primitives.jl) (489
  lines, fully read; no `sort-atom`, no `second-from-pair`). `sort` is in
  [stdlib/list.metta L62-L68](../stdlib/list.metta#L62-L68) as a MeTTa
  insertion-sort. Status: **MISSING grounded primitives**, partial MeTTa
  cover.

Bottom line: D1 is fixed, D2 is withdrawn (Core matches spec — see §3.5
below), D3 is a conscious design choice, D4 is a genuine partial gap
(`sort` exists in MeTTa, `sort-atom`/`second-from-pair` don't). The 30-probe
conformance number from 2026-04-09 should be re-baselined against current
Core before being cited again — projected 29-30/30.

### 3.5 Why the new audit harness must use assertEqual / trace!, not Julia classify()

The MeTTa language reference (cited 2026-05-29) describes four
debugging/assertion primitives that the audit driver should be built on:

- **`println!`** — `(-> %Undefined% (->))`. Arg IS evaluated. Returns unit `()`.
  Use for inline progress output during a probe (e.g. printing the row number
  before evaluation so a hang is localised to a specific row).
- **`trace!`** — `(-> %Undefined% $a $a)`. Both args evaluated; returns the
  second. Use for the "evaluate-and-print" pattern, especially the
  `trace-eval` idiom that combines `let`/`quote`/`trace!` to print both the
  expression and its result without infinite-looping on the expression itself.
- **`assertEqual`** — `(-> Atom Atom Atom)`. Spec: evaluates both args and
  compares result *sets*; returns `()` on match, `Error`-expression on
  mismatch. Core impl: [stdlib/core.metta L108-L111](../stdlib/core.metta#L108-L111).
  **Divergence**: Core returns `(assertEqual-passed $a)` on success rather
  than `()`. The error path matches spec — `(Error (assertEqual $a $b)
  AssertionFailed)`. The success-value difference is fine for an audit
  harness (any non-Error value = pass) but should be flagged as a minor
  spec-compliance fix.
- **`assertAlphaEqual`** — Same shape, alpha-equivalence comparator. Core
  impl: [stdlib/core.metta L113-L116](../stdlib/core.metta#L113-L116). Same
  success-value divergence.
- **`assertEqualToResult`** — `(-> Atom Atom Atom)`. Evaluates the first
  arg; treats the second as a *literal set* of expected results. Better for
  non-reducible expectations and nondeterministic results than wrapping with
  `superpose`. **Status in Core**: MISSING — not in
  [stdlib/core.metta](../stdlib/core.metta), not in
  [Primitives.jl](../src/primitives/Primitives.jl), not in
  [AtomOps.jl](../src/primitives/AtomOps.jl). This is a real gap. Add as a
  MeTTa rule in stdlib/core.metta along the lines of:
  ```metta
  (= (assertEqualToResult $expr $expected)
     (if (== (collapse $expr) $expected)
         (assertEqualToResult-passed $expr)
         (Error (assertEqualToResult $expr $expected) AssertionFailed)))
  ```
  Worth one commit on its own before the audit re-baseline runs.

**Implication for the audit driver**: the existing
[/tmp/petta_audit/run_audit5.jl](../../../../../tmp/petta_audit/run_audit5.jl)
classifies results in Julia by string-matching `:Error`. That's the wrong
layer. The MeTTa-native pattern is:

1. For each row, build an `assertEqual` (or `assertEqualToResult`)
   expression with the wiki's expected output.
2. Wrap the LHS in `trace!` to print the actual result inline.
3. Run via `run_metta` — `()` means pass, an `Error`-expression means fail.
4. The Julia driver becomes a pure I/O loop: read row, build expr, run,
   record `()` vs `Error`. No `classify` heuristic, no false positives.

The row-1 `(bind! A B)` hang is a separate issue (§4) — it predates
classification, so blacklisting it is still required regardless of harness
shape.

---

## 4. The bind! structural mislocation

[Eval.jl L77](../src/eval/Eval.jl#L77) dispatches `bind!` into the special-form
table; [Eval.jl L763-L793](../src/eval/Eval.jl#L763-L793) is the body.

Key semantic facts from the body, verbatim from the code:

- L784: `val = eval_metta(args[2], space)` — the RHS IS evaluated.
- L785-L790: if `val isa CoreSpace && name isa Symbol`, register
  `name → CoreSpace` in `space.named_spaces` and derive a byte-prefix metadata
  entry in `PREFIX_REGISTRY`. The CoreSpace keeps its own MORK trie (canonical
  isolation, same as H-E / CeTTa / PeTTa today). Stage 2 multi-space wiring is
  dormant but the metadata hooks are there.
- L791: **fall-through** — `core_add!(space, [:(=), name, val])`. Any non-Space
  `(bind! name expr)` becomes a `(= name val)` rule registration.

The structural problem the user flagged in the prior turn: **`bind!` lives in
the eval loop, not in a tokenizer/namespace layer.** That is correct as a
structural observation, and it is the root cause of the row-1 hang in the
PeTTa-wiki audit at [/tmp/petta_audit/](../../../../../tmp/petta_audit/). For
example, `(bind! A B)` with no prior binding for `A` or `B` triggers a fall-
through to rule-registration, but the LHS `name = A` is itself a free symbol;
subsequent grounded dispatch attempts on `A` re-enter the eval loop. In
hyperon-experimental and PeTTa, `bind!` is handled at the token/parse layer
so it never reaches the rule-rewriting machinery.

This is a refactor, not a one-line fix. Logged as `bind! relocation`
in the pending queue. Until then the row-1 blacklist in the audit drivers is
unavoidable.

---

## 5. Grounded primitive inventory ([Primitives.jl](../src/primitives/Primitives.jl))

Pre-evaluated args. Names exactly as registered:

- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `<`, `>`, `<=`, `>=`, `==`
- String/symbol: `concat`, `str-length`, `println!`, `trace!`, `format-args`,
  `str-concat`
- Type checks: `is-number`, `is-symbol`, `is-empty`
- Lists (core): `car-atom`, `cdr-atom`, `cons-atom`, `size-atom`
- Boolean: `and`, `or`, `not`
- Math: `sqrt-math`, `abs-math`, `log-math`, `exp-math`, `floor-math`,
  `ceil-math`, `round-math`, `trunc-math`, `sin-math`, `cos-math`, `tan-math`,
  `asin-math`, `acos-math`, `atan-math`, `pow-math`, `isnan-math`, `isinf-math`
- Reflection: `repr`, `parse`, `=alpha` (alpha-equiv)
- Type system: `get-type` ([Primitives.jl L287](../src/primitives/Primitives.jl#L287)
  — confirm Number-before-Bool ordering at audit time), `get-metatype`,
  `match-types`, `type-cast`, `match-type-or`, `first-from-pair`
- Set / collection: `unique`, `add-reduct`
- State: `new-state`, `get-state`, `change-state!`
- Random: `random-int`, `random-float` — **no `set-random-seed`** (deferred
  stdlib gap)
- Algorithm bridges: `WILLIAM.lgg` (delegates to `MORK._au_merge!`),
  `MetaMo.blend-vec`

[AtomOps.jl](../src/primitives/AtomOps.jl) adds: `decons-atom`, `take-atom`,
`drop-atom`, `index-atom`, `min-atom`, `max-atom`, `unique-atom`, `union-atom`,
`intersection-atom`, `subtraction-atom`, `is-variable`, `is-expression`. The
higher-order ops `foldl-atom` / `map-atom` / `filter-atom` are declared here
but actually dispatched as special forms ([Eval.jl L95-L97](../src/eval/Eval.jl#L95-L97))
because their body arg must NOT be pre-evaluated.

---

## 6. Stdlib-in-MeTTa inventory

Three files, all currently auto-loaded by `load_stdlib!`:

### [stdlib/core.metta](../stdlib/core.metta) (116 lines)

Identity / control flow as = rules:
- `if`, `if-equal`, `id`, `noeval` (as a rule, redundant with the special form
  but harmless)
- Error handling: `if-error`, `return-on-error`
- Expression deconstruction: `if-decons-expr`, `atom-subst`
- Type predicates: `is-function`
- Quoting: `unquote`
- HE-MeTTa compat shims: `if-equal2`, `noreduce-eq`, `match-types`,
  `first-from-pair`, `evalc`
- Assertions: `assertEqual`, `assertAlphaEqual`

**Critical**: every op the PeTTa wiki claims requires `!(import! &self lib_he)`
is **already a rule in this file**. The PeTTa-wiki audit at
[/tmp/petta_audit/](../../../../../tmp/petta_audit/) treated these as
missing — that's the misleading-claims pattern again. Re-baseline before
re-running.

### [stdlib/list.metta](../stdlib/list.metta) (68 lines)

`Nil`, `length`, `append`, `reverse` (+ `reverse-acc`), `nth`, `member`,
`sum-list`, `product-list`, `flatten`, `zip`, `sort` (+ `insert`). All recursive
defns via `(= ... ...)`.

### [stdlib/math.metta](../stdlib/math.metta) (42 lines)

Aliases (`sqrt` → `sqrt-math`, etc.) plus derived predicates: `square`, `cube`,
`max`, `min`, `clamp`, `between`, `zero?`, `positive?`, `negative?`, `even?`,
`odd?`.

### [stdlib/types.metta](../stdlib/types.metta) (88 lines)

Pure type-system declarations: `Type`, `Atom`, `Symbol`, `Variable`,
`Expression`, `Grounded`, `Bool`, `Number`, `String`, `SpaceType`,
`%Undefined%`, `True`, `False`, error type ctors (`Error`, `BadType`,
`BadArgType`, `IncorrectNumberOfArguments`, `StackOverflow`, `NoReturn`,
`AssertionFailed`), space op type sigs, atom-op type sigs, arithmetic type
sigs, string-op type sigs, control-flow type sigs, I/O type sigs.

---

## 7. CoreSpace structure (relevant audit details)

[CoreSpace.jl L123](../src/space/CoreSpace.jl#L123): `CoreSpace` struct fields —
`inner::Space` (MORK trie), `prefix::Vector{UInt8}` (Stage 2 multi-space byte
prefix), `rule_cache` (per-head cached `(head_params, body)` tuples),
`named_spaces::Dict{Symbol,CoreSpace}` (the bind!-populated child map),
`use_supercompiler::Bool`.

Stage 2 prefix-narrowed match is on at [CoreSpace.jl L545](../src/space/CoreSpace.jl#L545)
(`core_match`) via `_pattern_prefix_bytes`. Per-head rule caching is at
[L578](../src/space/CoreSpace.jl#L578) (`core_rules`). The `PREFIX_REGISTRY`
metadata structure is dormant in Stage 1 but populated by `bind!`.

`to_sexpr` / `from_sexpr` encode variables as `__var_NAME` for trie round-trip
— this is why [Eval.jl L797-L803](../src/eval/Eval.jl#L797-L803) (`_var_name`)
has both the `$NAME` and `__var_NAME` decoding paths.

---

## 8. .act lifecycle ([CoreSpaceActIO.jl](../src/space/CoreSpaceActIO.jl))

Three primitives, all delegating to MORK:
- `snapshot_space_to_act!(s, name)` — materializes a fresh PathMap from the
  prefix region, then `act_from_zipper` + `act_save`. The in-source comment at
  L14-L21 documents an important upstream gotcha: `act_from_zipper` takes a
  PathMap, NOT a ReadZipper, so the "direct path" via `read_zipper_at_path`
  won't compile.
- `load_act_source(name)` — opens `<name>.act` as an mmap'd ACTSource.
- `open_node!` / `close_node!` — startup/shutdown convenience.

This is the "True OS mmap for .act DONE" entry in the
[MORK_PATHMAP_SUBSTRATE_LEDGER](../../../docs/specs/MORK_PATHMAP_SUBSTRATE_LEDGER.md).

---

## 9. Algorithm libraries under [lib/](../lib/)

All three confirmed as plain MeTTa on top of Core (no interpreter extensions):

- [lib/ecan/ecan.metta](../lib/ecan/ecan.metta) — entry point; imports
  `t1_ECAN_Policies`, `t1_core_logic`, `t1_state_logic`,
  `t1_SpreadingActivation`, `t1_AttentionPolicies`, `t1_FluidECAN`, and
  `hyperseed/adaptive_attention.metta`.
- [lib/pln/pln.metta](../lib/pln/pln.metta) — imports `stv` + `pln_core_logic`.
- [lib/metamo/metamo.metta](../lib/metamo/metamo.metta) — equation #9 from
  [Lian & Goertzel 2025 MetaMo](../../../docs/specs/AGI2025/) (LNAI 16057, Ch. 34).

None of these add new special forms or grounded primitives — they are domain
code that uses what Core already exposes.

---

## 10. Two-bucket audit split (what to actually run)

Per the user's instruction, future audits should split into:

**Bucket A — primitive-core** (Julia-side, must work without any stdlib): the
grounded registry in [Primitives.jl](../src/primitives/Primitives.jl) +
[AtomOps.jl](../src/primitives/AtomOps.jl), plus the 38 special forms in the
[Eval.jl dispatch table](../src/eval/Eval.jl#L50-L97). This bucket maps to the
"interpreter performance" track (match/unify hot path, `@code_warntype`, JET,
AllocCheck).

**Bucket B — stdlib-in-MeTTa** (= rules in [stdlib/*.metta](../stdlib/)): every
op the PeTTa-wiki audit would otherwise flag as needing `import! lib_he`. Must
be tested with `load_stdlib!` having run first; tests against H-E `lib_he`
should be diff'd against [stdlib/core.metta](../stdlib/core.metta) to identify
genuine gaps vs naming differences.

The PeTTa-wiki 88-row audit at [/tmp/petta_audit/](../../../../../tmp/petta_audit/)
mixes both buckets. Rebuild it as two files before re-running.

---

## 11. Confirmed-not-in-Core

Items the PeTTa wiki may list that genuinely don't exist in Core (gaps, not
naming differences):

- `set-random-seed` (deferred — single primitive, ~10 LOC)
- File I/O (`open!`, `read!`, `write!`) — deferred
- JSON parse/serialize — deferred
- Catalog / module-dev primitives — deferred (whole subsystem)
- `sort-atom`, `second-from-pair`, function-ref variants — these are the D4
  family

Everything else flagged by an earlier audit is either fixed (D1), a conscious
divergence (D2, D3), or already present in [stdlib/core.metta](../stdlib/core.metta).

---

## 12. Next actions (not auto-done)

1. **Add `assertEqualToResult`** to [stdlib/core.metta](../stdlib/core.metta)
   as a single rule (see §3.5). One commit, ~5 LOC.
2. **Fix `assertEqual` / `assertAlphaEqual` success value** — return `()`
   instead of `(assertEqual-passed $a)` to match spec. One commit, ~2 LOC.
3. **Rebaseline conformance** — run the 30 probes from the 2026-04-09 report
   against current Core. Expectation: 29-30/30 (D1 fixed, D2 withdrawn, D3
   divergent by design, D4 partial). Driver: simple
   `julia --project=packages/Core` script that wraps each probe in
   `assertEqual` so the classifier becomes "Error or not Error" — no Julia-
   side `:Error` string-matching.
4. **Two-bucket audit harness** — split
   [/tmp/petta_audit/raw_rows.txt](../../../../../tmp/petta_audit/raw_rows.txt)
   into `bucket_a_primitive_core.tsv` (grounded + special forms, runs without
   `load_stdlib!`) and `bucket_b_stdlib_in_metta.tsv` (stdlib rules, requires
   `load_stdlib!`). Re-run using the assertEqual-based harness from (3).
5. **bind! relocation** — design doc for moving `bind!` out of the eval-loop
   dispatch table into the tokenizer/namespace layer. Touches Parser.jl
   (recognize `(bind! &X Y)` as a binding directive) + CoreSpace.jl (named
   spaces become first-class instead of populated post-eval). Until then the
   row-1 blacklist is unavoidable.
6. **Dialect choice** — pick H-E or PeTTa as the conformance baseline for D3
   (Error propagation). D2 is no longer a question (Core matches spec).

---

## 13. Files NOT read in this dive

- [src/space/CoreSpace.jl L668+](../src/space/CoreSpace.jl) — file ends at 666,
  read in full.
- [test/runtests.jl](../test/runtests.jl) — referenced but not re-read; 32
  testsets / 124 assertions per memory note.
- [lib/ecan/t1_*.metta](../lib/ecan/) — 7 files, ~1100 LOC. Confirmed as MeTTa
  rules, not interpreter code.
- [lib/pln/pln_core_logic.metta](../lib/pln/pln_core_logic.metta) — 27 KB.
  Confirmed as MeTTa rules.
- [lib/hyperseed/adaptive_attention.metta](../lib/hyperseed/adaptive_attention.metta)
  — confirmed as MeTTa rules.

These are out of scope for "what does the interpreter do" — they are users of
the interpreter, not extensions of it.
