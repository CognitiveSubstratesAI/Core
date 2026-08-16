# Tabling / SLG — task list

**Created 2026-08-16** from a source survey of `swipl-devel`, `jetta`, `PeTTa` and `CeTTa`.
Every item cites the upstream file:line it came from and the check that decides it is done.

> **Ordering rule, recorded 2026-08-11 and re-derived 2026-08-15 after I proposed its reverse:**
> **bounds → scope → precision.** Finer invalidation before bounds and scope would *unmask* a latent
> defect rather than fix one — our coarse per-space stamp over-evicts, which is **sound by
> construction**, while precision depends on a *complete* dependency graph and a missed edge serves a
> stale answer. See `[[reference_petta_memo_library_pr165]]`.

---

## ⚠️ READ FIRST — THE ENGINE QUESTION IS OPEN (added 2026-08-16)

`Core/docs/tabling_delimited_control_spec.md` (Desouter et al., **tabling in under 600 lines
of Prolog** via delimited control) shows this whole roadmap may be scoped against the wrong base.

**OUR ENGINE IS THE "EXTENSION TABLE" DESIGN, WHICH THAT PAPER NAMES AND REJECTS:** `_leader_pass` is
RE-RUN each fixpoint round (`Tabling.jl:374-380, :467-473`), i.e. we recompute suspended goals rather
than resuming them. *"The approach cannot achieve satisfactory performance as suspended goals are
always re-evaluated."*

⚠️ **AN EARLIER VERSION OF THIS PREAMBLE CLAIMED THIS ALSO EXPLAINS 2.0. IT DOES NOT — RETRACTED
2026-08-16.** Recomputation does force `unique`, but **tabling is SET-SEMANTICS BY DESIGN in every
implementation**: the delimited-control paper dedups deliberately (§4.4 `store_answer/2` *"only
store it in case it has not"*) and SWI dedups structurally (`wkl_add_answer` takes a `trie_node*`
— a trie IS a set). ⇒ **2.0 is a LANGUAGE-LEVEL mismatch — tabling is set, MeTTa is multiset —
and moving the base would NOT fix it.** What recomputation actually costs is PERFORMANCE (*"suspended
goals are always re-evaluated"*) and the missing structures below.

⇒ **DECIDED 2026-08-16: the target is ALL of SWI §7, and the BASE MOVES FIRST** (§1.0). Building 7.7/7.8/7.11 on the recomputation base means building them twice.
>
> Original wording, kept because the reasoning still holds: **decide the engine question before building §1.** The gap to their design is TWO STRUCTURES and
ONE PRIMITIVE (`dependency(Source, Cont, Target)`, a worklist dequeue, and `shift`/`reset`) — and
`Eval.jl` is already a *"continuation-passing stack machine"*, which is the substrate delimited
control needs. Adding SWI's nine attributes to a recomputation engine may cost more than moving the
base and getting 2.0 for free.

---

## 0. BLOCKERS — these gate other work, and two are live defects

| # | item | why it blocks | verify |
|---|---|---|---|
| **0.1** | **`_pure_heads` classifies compiled IL as IMPURE.** `EmitIL` emits `(function (chain (metta …) …))`; none of `function`/`chain`/`metta`/`return`/`evalc` is in `_PURE_PRIMS`, so **every compiled head is impure**. MEASURED: `:fib` pure in source = `true`, in IL form = `false`. | **Every purity-gated feature is silently inert on the compiled lane.** `auto_table!` is the one we noticed — it is not necessarily the only one. Blocks 1.x and 3.1. | add the 6 ops; assert `:fib` pure in IL form; **then re-run the proved corpus** — `_pure_heads` also feeds `purity_may_mutate` → region splitting → Invariant 1 |
| **0.2** | 🟢 **LARGELY DONE 2026-08-16 (`21bd63b`).** Cause moved twice (the `()` and `_instr` stories were both void) before landing on the real one: **BINDERS**. `_BINDER_KEEP_FROM` (derived from the declared types — `Variable` in an argument position) + PeTTa's middle clause, shipped together because the mutation check proves either alone is unsafe. **MEASURED EFFECT ON THE REAL LIBRARIES:** PLN **17 → 3 declines** — the 13 `\|-` inference rules now COMPILE, which was this item's whole target. ECAN **1 → 14**, and **all 14 are binder-related and were previously MIS-COMPILED**: with binders off, `sum-prob-weights` emitted `(unify ($Pr $w) $pt (chain (metta (+ $acc $w) …) …))` with `$acc`/`$pt` FREE, the fold template hoisted OUT and evaluated eagerly, and `foldl-atom` handed a VALUE where it expects a TEMPLATE. ⇒ the ECAN "regression" converts silent WRONG ANSWERS into safe DECLINES. | — | **REMAINING: 3 in PLN** (`StampDisjoint`, `PLN.Derive`, `PLN.Query` — none binder-related) **and 14 in ECAN**, which now need binder-aware EMISSION: `EmitIL` has no way to express a `GCall` whose template argument is an unlowered term. That is a design question about how a template crosses into minimal MeTTa, not another predicate. |
| **0.3** | **`_TABLED_HEADS` is process-global.** `untable_all!` is the only removal. | A `compile_run` needs a `finally` to avoid changing the next caller's semantics; per-head undo would make it scoped. Feeds 2.2. | two `compile_run` calls in one process; assert the second is unaffected |

---

## 1. THE TARGET IS ALL OF SWI §7 — DECIDED 2026-08-16

**Build the complete tabling solution whether or not it is used immediately, so the solution is
FIXED.** User decision, taken after the measured-need objection was raised and reaffirmed. Nothing is
scoped out: 7.9 (shared) and 7.10 (constraints) are IN, on the basis that threading arrives later.

### 1.0 BASE FIRST — continuation capture, not recomputation

**This is not an optional refactor; it is what makes the rest ONE build instead of two.** See
`Core/docs/tabling_delimited_control_spec.md`. Our engine recomputes (`_leader_pass` re-run per
fixpoint round) — the "extension table" design the literature rejects. Three later items want
structures that base simply does not have:

* **7.7 incremental** and **7.8 monotonic** need to know WHICH ANSWERS ARE NEW. A
  recompute-until-no-growth loop has no notion of a new answer, only "the table got bigger".
  7.8's eager/lazy split is precisely about WHEN to propagate one.
* **7.11 restraints** — `subgoal_abstract`/`answer_abstract` operate on TRIE TERMS; we use a `Dict`.
* **7.3 mode-directed** needs the merge point AND a value-based fixpoint test.

Build: `shift`/`reset` over the CPS frame stack · `dependency(Source, Cont, Target)` · the worklist
dequeue with the left/right invariant · an answer TRIE.

> **🟢 STEP 1 of 4 LANDED 2026-08-16 — the control-flow primitives, MEASURED, NOT YET WIRED.**
> `Eval._run_plan` extracted from `interpret` (ONE driver, so `resume` cannot drift from `interpret`
> on the step cap or the finished/root discipline) · `Continuation` · `capture_continuation` (`shift`)
> · `resume_continuation` (the resume side of `delim/3`) · `Dependency(source,cont,target)` + `_DEPS`,
> cleared by `_table_reset!`. Gate: `test/standard/test_delimited_control.jl` **19/19**, in
> `runtests.jl`. Regression: health **5/5**, `test_tnot_wfs` 39/39, the swipl §7.1/§7.2 differential
> green, full suite unchanged (still EXIT 1 at the pre-existing `test_eval_one_step` ratchet,
> **57 violations before and after** — measured, not assumed).
>
> **TWO PLANNED PIECES TURNED OUT UNNECESSARY, both measured rather than argued:**
> * **No `reset`.** `reset/3` exists to delimit where a captured chain STOPS. Ours already stops —
>   `_run_plan` collects exactly the frames finishing at `prev === nothing`, so a nested `interpret`
>   call IS the delimiter. `Continuation` is the `shift` half alone.
> * **No continuation COPY.** The spec called `Frame`'s in-place mutation "THE ONE REAL CONSTRAINT";
>   it is retracted there. The whole tree has ONE `Frame` field write (`evalc_op`'s `f.atom`,
>   `Eval.jl:912`) and it is on the DISPATCHED frame, never a captured `prev`. So the paper's
>   `copy_term/2` — and the `copy_continuation/2` it lists as future work — are both moot here.
>   The `Bindings` copy IS kept, for a stated reason: `merge_bindings` trail-undoes its in-place fold
>   on every exit path (`Atoms.jl:224-252`), which is safe only single-threaded, and **7.9 is in scope**.
>
> **REMAINING in §1.0:** (2) `dependency/3` FIRING on each new answer · (3) the worklist dequeue with
> the left/right invariant · (4) the answer trie. Then the rewire of `tabled_eval` off `_leader_pass`,
> with the proved corpus + `test_tnot_wfs` + both swipl differentials as the oracle. ⚠️ **NOT a reason to move the base: roadmap 2.0.** Retracted 2026-08-16 — tabling is set-semantics
by design everywhere, so the guard is still needed after the move. The reasons are PERFORMANCE and
the three structures above.

### 1.1–1.13 the §7 surface, in dependency order

| § | feature | status | notes |
|---|---|---|---|
| **7.1** | memoizing | ✅ **HAVE** | variant tabling |
| **7.2** | avoiding non-termination | ✅ **HAVE** | suspend-on-variant (`a13af09`) |
| **7.6** | Well-Founded Semantics | ✅ **HAVE** | Van Gelder alternating fixpoint; swipl differential 13/13 |
| **7.6.1** | WFS and the toplevel | ❓ | how `undefined` surfaces to a MeTTa caller — ours returns `UNDEFINED`; confirm against SWI's toplevel residual-program printing |
| **7.5** | subsumptive tabling | ❌ | a second LOOKUP MODE over the same tables — first feature after the base. ⚠️ upstream: does not combine with incremental/shared |
| **7.11.3** | restraint: answer **count** (`max_answers`) | ❌ | `pl-tabling.c:3659` tripwire — the one restraint that ports to a `Dict` today |
| **7.11.1/2** | restraint: subgoal / answer **size** | ❌ | abstraction over trie terms ⇒ needs the base's answer trie |
| **7.3** | answer subsumption / mode-directed | ❌ | `lattice(F/3)`, `po(F/2)`. Consumer named by §3.6 in our vocabulary ("product quantale structure"); `Core/lib/quantale/` exists. 🔴 CATCH: the fixpoint test is CARDINALITY-based and a lattice breaks it silently |
| **7.7** | incremental | ❌ | IDG + `falsecount`, lazy like ours; buys per-table GRANULARITY. Consumes the base's dependency graph |
| **7.8** | monotonic (+ eager/lazy, tracking, external data) | ❌ | same graph, monotone-update variant |
| **7.4** | tabling for impure programs | ❌ | the interaction rules once the above exist. NOT our purity gate — that decides WHAT to table, this is how tabling behaves WITH impurity |
| **7.9** | shared tabling (+ abolishing) | ❌ | **IN SCOPE — threading later.** Prereq: a threading model. Julia has `Threads.@spawn`; MettaJam is the natural first consumer. Upstream's `tshared` + `abolish_shared_tables/0`. ⚠️ the paper flags NON-BACKTRACKABLE MUTATION as essential to retain answers across disjunctions — the concurrency story starts there |
| **7.10** | tabling and constraints | ❌ | **IN SCOPE.** Prereq we do not yet have: a CONSTRAINT STORE for tabling to interact with. Possible substrate — MORK's optional `z3` source (see the MM2 capability-boundary row in CODEMAP). Scope this only after a constraint story exists |
| **7.12** | predicate reference | ❌ | the API surface: per-head `untable!`, `is_tabled`, stats, `abolish_*`. Also roadmap 0.3 and 3.2 |
| **7.13** | about the implementation / status | — | our equivalent is `Core/docs/tabling_delimited_control_spec.md` + this file |

**Mid-evaluation guard** (`permission_error` when a change hits an incomplete table —
`pl-tabling.c` `state.incomplete` → `change_incomplete_error`) has no § of its own but is a soundness
guard we lack; it belongs with 7.7.


## 2. FROM JeTTa — `jetta/backend/.../Generator.kt`, `compiler/Compiler.kt`

| # | item | upstream | notes |
|---|---|---|---|
| **2.0** | 🔴🔴 **BLOCKS 2.2 — TABLING COLLAPSES MULTIPLICITY.** `_leader_pass` merges answers with `unique(vcat(…))` — a SET — while MeTTa is MULTISET. MEASURED 2026-08-16: `(= (h) 1)` twice, `(= (k) (h))` ⇒ `!(k)` untabled `[1,1]`, tabled `[1]`. **NOT introduced by auto-tabling — explicit `table!` has always had it**; auto-tabling made it reachable on 5 corpus scripts at once (b1_equal_chain +1, b2_backchain +2, d3_deptypes +1, d4_type_prop +1, e1_kb_write +1; the PROVED corpus caught every one). ⚠️ **THE TENSION IS FUNDAMENTAL:** tabling REQUIRES set semantics to reach a fixpoint — dropping `unique` never converges. So this constrains WHICH HEADS MAY BE TABLED; it is not a merge to fix. **Upstream already guards it and we dismissed the guard:** JeTTa requires `!f.isMultivalued()` (`Generator.kt:166`), called "a downgrade" on 08-15 — wrongly, since handling multi-answer as a SET is not preserving MULTIPLICITY. PINNED by a test that asserts the DEFECT and must be UPDATED (not deleted) when a guard lands. 🔴 **NOT SUPERSEDED — that claim was RETRACTED 2026-08-16.** Tabling is SET-SEMANTICS BY DESIGN in every implementation (the delimited-control paper dedups in `store_answer/2`; SWI dedups structurally via the answer trie), so the base move does NOT fix this. **2.0 is a LANGUAGE-LEVEL mismatch — tabling is set, MeTTa is multiset — and the guard is the RIGHT answer, independent of the engine.** The three converging sources are the correct response to that mismatch, not workarounds for a weak base. | `Generator.kt:166` | **Decide the guard before 2.2.** Candidate signal: `length(rules[h]) > 1`, which is conservative-but-safe — it would also exclude ordinary disjoint-pattern definitions like `(= (fact 0) 1)` + `(= (fact $n) …)`, so it may be too blunt. Needs its own measurement. |
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
