# Upstream tabling oracles

Ground truth for our §7 tabling port, taken from the trees we ported **from** rather than written
by us. Added 2026-08-18, after three days in which every tabling oracle was one we had authored.

## Why this directory exists

Our 15 Julia tabling test files are ~3,400 lines and they pass. But a suite only proves the absence
of the defects it can *see* (`[[feedback_oracle_must_observe_the_defect_class]]`), and ours were
written from the same reading of the C that produced the code. `test_delays.jl`, for instance, is
mostly DNF **algebra** — `dnf_and` distributes, `dnf_or` dedups — plus one end-to-end paradox.
Algebra assertions cannot see a wrong **fixpoint**.

Upstream ships oracles that can. `swipl-devel/tests/xsb/` alone holds **eleven** test directories
and **338** `*_old` gold-output files.

## What is here

| file | what |
|---|---|
| `extract_corpus.sh` | regenerates `wfs_corpus.tsv` from `swipl-devel/tests/xsb/wfs_tests` |
| `wfs_corpus.tsv` | 72 programs × (goal, subgoals, TRUE set, UNDEFINED set) |
| `verify_corpus.pl` | the three-way truth-value probe |
| `verify_corpus.sh` | runs all 72 under the live `swipl` and diffs against the gold rows |

`../../../../../workflows/swipl_tabling_oracle.sh` runs upstream's own 18 plunit tabling files
(165 tests) against the live binary.

## The corpus format

Each `pNN.P` opens with one machine-readable fact:

```prolog
query(p24, p, [p,q,r,s], [s], []).
%     name  goal  all-subgoals  TRUE-set  UNDEFINED-set
```

A subgoal in neither set is **false**. That is a complete Well-Founded Semantics conformance table,
written by the people who defined the semantics.

## Status — measured, not assumed

- **`verify_corpus.sh`: 72 agree · 0 differ.** Every gold row reproduces under live swipl 10.1.12,
  so the table is safe to grade ourselves against. (`gen.P` and `wfs_test.P` error out because they
  are the corpus generator and driver, not query programs.)
- **`swipl_tabling_oracle.sh`: 18 files, 165 tests, all green** in about a second.

## What is NOT done, stated plainly

**No program has been translated to MeTTa yet, so our engine is not yet held to any of this.** The
corpus is validated and the harness executes — against *swipl*. Translating XSB programs to our
engine is the next step and it is real work: these use propositional predicates (`p :- q, tnot(r)`)
and Prolog conjunction, neither of which maps to a MeTTa rule one-for-one.

Sequencing note from upstream itself: `tests/xsb/delay_tests/xsb_test_delay.pl` **pre-labels which
tests need the §7.6.1 simplification we deliberately did not build** — 9 are passable without it,
12 are not. Where a program needs simplification our engine will report `undefined` where the gold
row says `false`. That is a *classified* expected difference, not a regression, and the labelling
tells us which rows in advance. `gfp` (line 74) additionally shows simplification must **cascade**,
not run once — worth knowing before writing §7.6.1 rather than after.
