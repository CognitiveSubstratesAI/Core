# LeaTTa proved-oracle — Core vs machine-checked MeTTa semantics

Ground-truth for `test/oracle/leatta/test_leatta_oracle.jl`. **LeaTTa** (1.0.6, hosted under
godelclaw, `~/dev-zone/LeaTTa`) is a **Lean-4 machine-checked** MeTTa/Hyperon interpreter: its
minimal interpreter + standard library run **Hyperon's own unmodified oracle corpus — 270 passing
assertions across 22 files** — and its metatheory (`MettaHyperonFull/Proofs/`) carries kernel-checked
proofs (determinism, confluence, first-argument-indexing soundness/completeness, gradual-type totality,
α-equivalence) with `0 sorry / admit / native_decide`.

## ⚠️ What that does and does not license (revised 2026-08-12)

This file used to say flatly: *"a Core⟂LeaTTa disagreement is our bug, not a difference of opinion."*
**That is too strong, and the qualification matters.**

- **Authorship.** Written mostly by **MesTTo** (139 of 143 commits; Zarathustra Goertzel has 4).
  `godelclaw` is where it is hosted, not who wrote it. Corrected after Zar pointed it out directly.
- **🔴 LeaTTa DELIBERATELY DIFFERS FROM hyperon-experimental at several points**, by its own README's
  section *"Where LeaTTa improves the current interpreter"*: HE's mutable `is_evaluated()` bit becomes
  static return-type gating; the `is_variable_op` hotfix becomes a total `isVariableHeaded` guard;
  `Rc<RefCell>` mutation becomes a pure immutable stack; the global `make_unique` counter becomes a
  threaded pure gensym; the unbounded loop becomes a fuel-bounded driver; linear rule lookup becomes
  first-argument indexing. Where Core follows HE and LeaTTa follows its improved construct, a
  disagreement IS a difference of opinion.
- **Its conformance to HE was being established, and paused.** Zar (2026-08-12): *"I think we were
  trying to verify its correctness against HE specs (while fixing HE specs). I kinda paused somewhere
  due to lower credits."* Reported recollection, hedged as stated — but it means "machine-checked
  metatheory" must not be read as "verified conformance to hyperon".

**What the gate still soundly licenses.** The oracle is CORPUS-based: hyperon's own 270 self-checking
assertions, where a pass means Core computed the value the assertion demands. The improvements above do
not change results the corpus pins, so for everything the corpus exercises the gate holds exactly as
before. The narrowed claim is: *a Core⟂LeaTTa disagreement ON A CORPUS DIRECTIVE is our bug; a
disagreement outside it may be either.* That is the same rule as `[[feedback_oracle_inherits_corpus_
coverage]]` — a proved oracle guarantees what its CORPUS exercises, not what its spec states — applied
to an oracle we had been quoting past that line.

## Oracle independence — LeaTTa and MeTTaScript are NOT independent

`dev-zone/MeTTaScript` is also **MesTTo's** (60 of 60 commits). Treating agreement between them as
corroboration would be double-counting one author's reading of MeTTa. The genuinely independent points
in the fleet are hyperon-experimental itself (the upstream), MeTTapedia's `metta-ref` (zariuq /
godelclaw — see `../mettaref/README.md`), and CeTTa.

## What's here

- `corpus/` — the 22 graded `.metta` files + `c2_spaces_kb.metta` (the `import!` module) + `EXPECTED.txt`,
  copied **verbatim** from LeaTTa's `tests/corpus/` (itself Hyperon's unmodified corpus, MIT, upstream
  commit `3f76dc4`). Each `!`-directive is a self-checking `assertEqual`-family call that evaluates to `()`
  on pass. `EXPECTED.txt` is LeaTTa's **proved golden**: `<file> <PASS> <FAIL> <TOTAL>`, every FAIL=0.
- `RUN.sh` — offline regeneration/verification (needs the LeaTTa binary; **never run in CI**). Confirms
  LeaTTa still reports `270/270`, then re-vendors the corpus + `EXPECTED.txt` into `corpus/`.
- `test_leatta_oracle.jl` — the standing test (pure Core + frozen corpus; no Lean/binary at CI time).

## The gate (design)

The corpus is self-checking and LeaTTa **proves every directive passes**, so "Core passes directive d" ≡
"Core computes the proved-correct value for d" — transitive agreement with LeaTTa's values with **no
string-diffing** (immune to render-format false positives). Per directive:

| class | meaning | gated? |
|---|---|---|
| **PASS** | result is `()` — Core matches the proved semantics | — |
| **CORE_BUG** | non-pass with no unimplemented head — Core computed a WRONG answer | **YES (must be 0)** |
| MISSING_OP | fails only because a head op is unimplemented (assert-variant, `sort-strings`, `help!`, `pragma!`) — correct MeTTa returns the call unreduced | ledger (exact baseline) |
| LEATTA_SPECIFIC | space/parallel-model ops Core lacks (`fork-space`, `hyperpose`) | ledger (exact baseline) |

`_MODULE_PATH[]` is seeded with `corpus/` so `!(import! &kb c2_spaces_kb)` resolves (the former
import!-path artifact). Current state (2026-07-08): **270 PASS + 0 MISSING_OP + 0 LEATTA_SPECIFIC = 270,
0 CORE_BUG — FULL conformance to the machine-proved corpus.** The entire family was implemented: the
`assert*Msg`/`assertAlphaEqual` variants + `assert`/`help!`/`pragma!`/`hyperpose` (stdlib rules) and
`sort-strings`/`sort-atom` + `fork-space` + `new-mork-space` (grounded primitives) — plus the `atom_types`
type-checker root fix. The known-missing / leatta sets are now empty: any head that fails to reduce
surfaces as a CORE_BUG, not a silent gap. The MISSING_OP/LEATTA counts are frozen per-file: a **drop** = a coverage win (implement the
op → update the baseline); a **rise** = a regression or a newly-unimplemented op. Either forces a
deliberate baseline update, keeping the ledger honest.

## History

The first differential (2026-07-08) found exactly one real CORE_BUG — `case` on an empty result set
(collapsed to `()` instead of matching the `Empty` clause; fixed `1ee0356`, locked by
`test_interpreter.jl`). Everything else was MISSING_OP / LEATTA_SPECIFIC / the import!-path artifact.

## Not yet wired (bigger oracle surface LeaTTa exposes)

LeaTTa also machine-checks the **Meta-MeTTa operational semantics** (arXiv 2305.17218) — the four-register
⟨i,k,w,o⟩ machine + barbed bisimulation + gas — which is the same machine our **MM2** lane implements. That
makes LeaTTa a candidate oracle for the `(=)→MM2` lowering too (`MettaHyperonFull.Operational.*` +
`Proofs/Correspondence.lean`). Not built here; see the session log.
