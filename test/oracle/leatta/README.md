# LeaTTa proved-oracle — Core vs machine-checked MeTTa semantics

Ground-truth for `test/oracle/leatta/test_leatta_oracle.jl`. **LeaTTa** (godelclaw/LeaTTa 1.0.6,
`~/JuliaAGI/dev-zone/LeaTTa`) is a **Lean-4 machine-checked** MeTTa/Hyperon interpreter: its
minimal interpreter + standard library run **Hyperon's own unmodified oracle corpus — 270 passing
assertions across 22 files** — and its metatheory (`MettaHyperonFull/Proofs/`) carries kernel-checked
proofs (determinism, confluence, first-argument-indexing soundness/completeness, gradual-type totality,
α-equivalence) with `0 sorry / admit / native_decide`. So a Core⟂LeaTTa disagreement is **our** bug, not a
difference of opinion — the strongest oracle in the fleet by provenance.

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
import!-path artifact). Current state (2026-07-08): **246 PASS + 19 MISSING_OP + 5 LEATTA_SPECIFIC = 270,
0 CORE_BUG**. The MISSING_OP/LEATTA counts are frozen per-file: a **drop** = a coverage win (implement the
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
