# Tabling / SLG — task list

**Created 2026-08-16** from a source survey of `swipl-devel`, `jetta`, `PeTTa` and `CeTTa`.
Every item cites the upstream file:line it came from and the check that decides it is done.

> **Ordering rule, recorded 2026-08-11 and re-derived 2026-08-15 after I proposed its reverse:**
> **bounds → scope → precision.** Finer invalidation before bounds and scope would *unmask* a latent
> defect rather than fix one — our coarse per-space stamp over-evicts, which is **sound by
> construction**, while precision depends on a *complete* dependency graph and a missed edge serves a
> stale answer. See `[[reference_petta_memo_library_pr165]]`.

---

## 0. BLOCKERS — these gate other work, and two are live defects

| # | item | why it blocks | verify |
|---|---|---|---|
| **0.1** | **`_pure_heads` classifies compiled IL as IMPURE.** `EmitIL` emits `(function (chain (metta …) …))`; none of `function`/`chain`/`metta`/`return`/`evalc` is in `_PURE_PRIMS`, so **every compiled head is impure**. MEASURED: `:fib` pure in source = `true`, in IL form = `false`. | **Every purity-gated feature is silently inert on the compiled lane.** `auto_table!` is the one we noticed — it is not necessarily the only one. Blocks 1.x and 3.1. | add the 6 ops; assert `:fib` pure in IL form; **then re-run the proved corpus** — `_pure_heads` also feeds `purity_may_mutate` → region splitting → Invariant 1 |
| **0.2** | 🟢 **LARGELY DONE 2026-08-16 (`21bd63b`).** Cause moved twice (the `()` and `_instr` stories were both void) before landing on the real one: **BINDERS**. `_BINDER_KEEP_FROM` (derived from the declared types — `Variable` in an argument position) + PeTTa's middle clause, shipped together because the mutation check proves either alone is unsafe. **MEASURED EFFECT ON THE REAL LIBRARIES:** PLN **17 → 3 declines** — the 13 `\|-` inference rules now COMPILE, which was this item's whole target. ECAN **1 → 14**, and **all 14 are binder-related and were previously MIS-COMPILED**: with binders off, `sum-prob-weights` emitted `(unify ($Pr $w) $pt (chain (metta (+ $acc $w) …) …))` with `$acc`/`$pt` FREE, the fold template hoisted OUT and evaluated eagerly, and `foldl-atom` handed a VALUE where it expects a TEMPLATE. ⇒ the ECAN "regression" converts silent WRONG ANSWERS into safe DECLINES. | — | **REMAINING: 3 in PLN** (`StampDisjoint`, `PLN.Derive`, `PLN.Query` — none binder-related) **and 14 in ECAN**, which now need binder-aware EMISSION: `EmitIL` has no way to express a `GCall` whose template argument is an unlowered term. That is a design question about how a template crosses into minimal MeTTa, not another predicate. |
| **0.3** | **`_TABLED_HEADS` is process-global.** `untable_all!` is the only removal. | A `compile_run` needs a `finally` to avoid changing the next caller's semantics; per-head undo would make it scoped. Feeds 2.2. | two `compile_run` calls in one process; assert the second is unaffected |

---

## 1. FROM SWI-PROLOG — `boot/tabling.pl`, `src/pl-tabling.c`

We implement **one of four modes and zero of nine attributes**: ~250 lines of code against ~8 600.

| # | item | upstream | notes / verify |
|---|---|---|---|
| **1.1** | **Mode-directed tabling** — `lattice(F/3)`, `po(F/2)` answer aggregation | `boot/tabling.pl:1455-1491`, `start_moded_tabling/5` | **THE FIRST TARGET.** §3.6.1 names the consumer in our vocabulary: *"local potentials … through a **product quantale structure** … orchestration layer manages **convergence**"* — a quantale IS a lattice, and we carry `Core/lib/quantale/`. SWI's own tests: `lattice(prob_sum_e/3)`, `lattice(shortest/3)`. **Hook is 2 sites**: `Tabling.jl` `_leader_pass` entry + the fixpoint merge (`unique(vcat(…))` = set union → lattice join). 🔴 **THE CATCH: the fixpoint test is CARDINALITY-based** (`length(_PARTIAL[m]) != n0`). Under a lattice a table keeps its SIZE while its VALUE improves (`shortest: 5→3`) ⇒ declares convergence early and returns a **wrong answer with no error**. Termination must become "did the join change the value". **Verify against a swipl oracle running the same `lattice(shortest/3)` program** — not pinned literals. |
| **1.2** | **`max_answers`** — cap answers per subgoal | `pl-tabling.c:3659` (tripwire) | The `bounds` half of the ordering rule. Cheapest real bound. |
| **1.3** | **`subgoal_abstract(N)` / `answer_abstract(N)`** — bound term depth by abstraction | `pl-tabling.c:2452`, `:3568` | Structural bound, not a memory cap. Needs the trie-side story we do not have (we use a `Dict`). |
| **1.4** | **`subsumptive` tabling** — a GENERAL call's table answers a SPECIFIC one | `boot/tabling.pl:59`, `start_subsumptive_tabling/3` | Lands in `Variant.jl`. ⚠️ upstream notes it does not combine with incremental/shared tabling. |
| **1.5** | **`incremental`** — per-table dependency invalidation | `pl-tabling.c:118` `idg_add_edge`, `:199` `idg_propagate_change`, `:3233` `falsecount` | ⚠️ **LAST, per the ordering rule.** Their trigger is the SAME as ours (lazy, checked on lookup); only GRANULARITY differs — per-table via the IDG vs our per-space `(objectid, revision)`. **What adoption buys is the dependency GRAPH, not a new strategy.** |
| **1.6** | **Mid-evaluation guard** — `permission_error` when a change hits an incomplete table | `pl-tabling.c` `state.incomplete` → `change_incomplete_error` | A soundness guard we have **no equivalent of**. Small, and independent of 1.5. |
| **1.7** | `tshared`, `monotonic`, `lazy`, `dynamic`, `opaque` | `boot/tabling.pl:338-346` | Low priority; several presuppose Prolog's dynamic-predicate model. |

---

## 2. FROM JeTTa — `jetta/backend/.../Generator.kt`, `compiler/Compiler.kt`

| # | item | upstream | notes |
|---|---|---|---|
| **2.0** | 🔴🔴 **BLOCKS 2.2 — TABLING COLLAPSES MULTIPLICITY.** `_leader_pass` merges answers with `unique(vcat(…))` — a SET — while MeTTa is MULTISET. MEASURED 2026-08-16: `(= (h) 1)` twice, `(= (k) (h))` ⇒ `!(k)` untabled `[1,1]`, tabled `[1]`. **NOT introduced by auto-tabling — explicit `table!` has always had it**; auto-tabling made it reachable on 5 corpus scripts at once (b1_equal_chain +1, b2_backchain +2, d3_deptypes +1, d4_type_prop +1, e1_kb_write +1; the PROVED corpus caught every one). ⚠️ **THE TENSION IS FUNDAMENTAL:** tabling REQUIRES set semantics to reach a fixpoint — dropping `unique` never converges. So this constrains WHICH HEADS MAY BE TABLED; it is not a merge to fix. **Upstream already guards it and we dismissed the guard:** JeTTa requires `!f.isMultivalued()` (`Generator.kt:166`), called "a downgrade" on 08-15 — wrongly, since handling multi-answer as a SET is not preserving MULTIPLICITY. PINNED by a test that asserts the DEFECT and must be UPDATED (not deleted) when a guard lands. | `Generator.kt:166` | **Decide the guard before 2.2.** Candidate signal: `length(rules[h]) > 1`, which is conservative-but-safe — it would also exclude ordinary disjoint-pattern definitions like `(= (fact 0) 1)` + `(= (fact $n) …)`, so it may be too blunt. Needs its own measurement. |
| **2.1** | **RECURSIVE requirement in `auto_table!`** ⚠️ *and see 2.0 — the multivalued guard is the harder sibling of this one* — table only heads that transitively call themselves | `Generator.kt:164-169`: *"Recursive ⇔ transitively calls itself — **bounds the cache and is where memoization pays**"* | We currently table EVERY pure user head. Memoizing a non-recursive function is pure overhead. **Independently corroborated by PeTTa #165** (*"avoid memoization for trivial functions called <20 times"*). Cheap; lands in `Purity.jl`. |
| **2.2** | **The lane split, ENFORCED BY TEST** — auto-table on the closed-world path, OFF on the open-world one | `MemoTablingTest.kt:39-41`: `tabling is off without autoTable (the REPL or JIT path)`, asserting `fib must NOT be tabled when autoTable is off` | Maps exactly onto `compile_run` (fixed program, bounded lifetime) vs the MettaJam server (`add-atom` any time, runs for days). Their justification, `Compiler.kt:184`: *"AOT is a closed world (rules fixed at compile), so memoizing … is sound **without cache invalidation**"*. Depends on **0.1** — an auto-table call on the compiled lane is INERT until `_pure_heads` learns the IL ops (tried 2026-08-15, did nothing). |

### 🛑 DO NOT ADOPT from JeTTa

- **Their purity gate.** `Generator.kt:153` `impureGrounded` is a **DENYLIST**, and it is **provably unsound**: it lists `"add-atom!"` and `"remove-atom!"` while MeTTa's operators are `add-atom` / `remove-atom` (no bang), so a function calling the real mutator passes `bodyPure` and **gets memoized**. `CompileLane.jl:35` already records this ("6 dead entries, both space mutators misspelled"); verified from source 2026-08-16. **Our whitelist fixpoint fails SAFE and is strictly better.**
- **`keyable` (INT/LONG/DOUBLE/BOOLEAN only)** and **`!isMultivalued()`**. They exist because JeTTa memoizes into a `ConcurrentHashMap` keyed on boxed primitives. Our SLG keys arbitrary atoms via `_variant_rename` and handles multi-answer, non-ground goals — adopting these would be a downgrade.
- **Compile-time wrapper emission** as the mechanism. It makes sense for an AOT target with *no runtime tabling engine*. We have one.

---

## 3. FROM PeTTa PR #165 — `lib/lib_memo.pl` (read at `0dc1198`; 799 LOC)

> **🛑 VERDICT ON FILE: DO NOT ADOPT YET**, and the 2026-08-16 SLG survey **retires most of the case** —
> its `answer-limit` IS `max_answers` (1.2), its `aggregate` enum IS `lattice`/`po` (1.1, and the SLG
> form is strictly more general), its dependency invalidation IS `incremental` (1.5).
> **#165 largely reimplements SLG features inside a system that already runs on SLG.**

| # | item | notes |
|---|---|---|
| **3.1** | **Eviction policy (LRU)** — **the ONE part with no SLG analogue** | SLG **BOUNDS** (abstraction, `max_answers`) and never evicts; #165 **EVICTS** under a memory cap. Bounding ≠ evicting. Our table is unbounded and our own header says so. Take LRU; **skip WTinyLFU** until a measurement wants it. |
| **3.2** | **Per-head `untable!(h)`** | Currently only `untable_all!`. See 0.3. |
| **3.3** | **Stats** — hits / misses / entries per head | Without it, "should this be tabled" is unanswerable. **Do this before 3.1** — otherwise the eviction policy is chosen blind. |
| **3.4** | **MeTTa-level `!(table! f)`** | `TABLE_DECL` exists in `Tabling.jl`; confirm the surface and document it. |

---

## 3.5 EXPLICIT MEMOIZATION — a THIRD option, available TODAY with zero engine work

Source: Markus Triska, *metalevel.at/prolog/memoization* (user-supplied 2026-08-16). O'Keefe's two
rules for efficiency: **"Don't do it. Don't do it again."** Tabling is option 2 automated; explicit
memoization is option 2 by hand.

**MEASURED IN PURE MeTTa, no engine change** — the `assertz` pattern as `add-atom`:

    (= (fib $n) (if (< $n 2) $n (fib-memo $n)))
    (= (fib-memo $n)
       (let $hit (collapse (match &self (fib-cache $n $v) $v))
         (if (== $hit ())
             (let $r (+ (fib (- $n 1)) (fib (- $n 2)))
               (let $_ (add-atom &self (fib-cache $n $r)) $r))
             (car-atom $hit))))

    untabled          dies at n=18 (step limit)
    EXPLICIT MEMO     fib(30) = 832040 in **571 ms**   ← works TODAY
    SLG tabling       fib(30) = 832040 in **36 ms**    ← 16x faster

The 16x is the lookup path: `match` is a space query, tabling hits a `Dict`.

**WHAT IT BUYS** — the cache is ATOMS: inspectable by `match`, dumpable, persistable to `.act`,
removable by `remove-atom`. No revision stamp, no IDG, no process-global state. `_ANSWER_TABLE` is a
`Dict` nothing can see.

🔴 **WHAT IT DOES NOT BUY, IN TRISKA'S OWN WORDS:** *"this rather ad hoc definition **does not help to
improve termination properties** of your programs"* and *"it requires modifications of the original
program… You have to manually wrap the goals"*. Tabling's suspend-on-variant is what makes
left-recursive `adjacent(X,Y) :- adjacent(Y,X)` terminate; a memo check cannot. **They are not
substitutes** — memo avoids recomputation, tabling ALSO fixes non-termination.

🔴🔴 **AND IT CARRIES THE SAME MULTIVALUED CONSTRAINT — A THIRD INDEPENDENT SOURCE FOR 2.0.** Triska's
`memo/1` wraps the goal in **`once(Goal)`**, with the condition stated explicitly: *"As long as Goal
is **semi-deterministic or deterministic**, `memo(Goal)` is equivalent to `Goal`."* So:

| source | the guard |
|---|---|
| JeTTa `Generator.kt:166` | `!f.isMultivalued()` |
| our measurement 2026-08-16 | tabling turns `[1,1]` into `[1]` |
| **Triska** | **`once(Goal)`, "semi-deterministic or deterministic"** |

⇒ **memoization of ANY kind requires single-valuedness.** An earlier note here suggested explicit
memo "gives you the choice to preserve multiplicity" — true in principle, but NOT of this pattern.

⭐ **AND A POINTER WORTH FOLLOWING BEFORE ANY 1.x WORK:** *"Scryer Prolog implements tabling via
**delimited continuations**. See **Tabling as a Library with Delimited Control**, Desouter et al."*
**Tabling as a LIBRARY, not a 9 472-line C engine** — and `Eval.jl` is already a CPS stack machine
("continuation-passing stack machine… a stack of frames… a `ret` continuation"), which is precisely
the substrate delimited control needs. That is a far closer architectural match than SWI's approach,
and it may make 1.1/1.4 much cheaper than the ~8 600-vs-250 line comparison suggests.
⚠️ NOT IN dev-zone — no Scryer clone, no local copy of the paper. Fetch both before scoping 1.x.

---

## 4. STRUCTURAL

| # | item | notes |
|---|---|---|
| **4.1** | ✅ **DONE `031a999`** — extract tabling from `Eval.jl` into `Tabling.jl` (475 lines; `Eval.jl` 2853→2385) | Mirrors SWI (`boot/tabling.pl` + `pl-tabling.c`) and CeTTa (`table_store.c`). |
| **4.2** | **`src/tabling/` subfolder**, split by PROVENANCE — `Tabling.jl` (hub: state, `table!`, attributes land here) · `Purity.jl` (MeTTa-TS: `_pure_heads`, `auto_table!`) · `Variant.jl` (SWI §7.1: keying, `_leader_pass`, `tabled_eval`; modes land here) · `WFS.jl` (SWI WFS: `_S_P!`, `_wfs_complete!`, `TNOT`) | ⚠️ WFS state is INTERLEAVED with general state, so this is not a pure line-range cut. Arguably over-split at 500 lines — the justification is that each file is where a NAMED item above lands. |

---

## Verification standard for every item

1. **A swipl differential where one is possible** — `test_wfs_swipl_differential.jl` is the model: consult real `.pl` oracle files, compare, and **skip loudly** if swipl is absent. Not pinned literals.
2. **The LeaTTa PROVED corpus** (`test_compile_lane_corpus.jl`) for anything touching purity, region splitting or emission — it caught both `\|-` attempts.
3. **`Core/bin/health` 5/5** — but see `[[feedback_primus_health_gate_obsolete]]`: it is a MeTTa front-end gate, NOT a substrate gate.
4. **A mutation check** — flip the assertion and confirm it fails. A test that cannot fail is not evidence.
