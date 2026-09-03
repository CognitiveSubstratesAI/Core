# How CeTTa, PeTTa and JeTTa compile MeTTa — and what it says about our lane

Measured 2026-09-03 by reading all three upstream trees, prompted by a `fib-list` exercise whose
compiled answer was empty in our lane and correct in every other engine. Root cause of OUR bug is in
`COMPILER_IL_STAGE.md` §5; this file is the comparison that put it in context.

Sources read: `~/dev-zone/CeTTa` (196k LOC C, HEAD `12da03b`), `~/dev-zone/PeTTa` (SWI-Prolog,
HEAD `ae66fa8`), `~/dev-zone/jetta` (Kotlin, HEAD `5cababc`, v0.8.0). ⚠️ Upstream moves — re-verify
line numbers before relying on one. [[feedback_capability_claims_expire_retest_the_premise]]

## 1. THE ONE DECISION EVERY MeTTa COMPILER MAKES

**Is this head a CALL, or is it DATA?** An interpreter never has to answer it in advance — at run
time the head either resolves or it does not. A compiler must commit earlier, and *every* engine here
gets it wrong somewhere. The differences are entirely in WHAT EACH ONE DOES WHEN IT IS UNSURE.

| engine | decides by | frozen as data when | on doubt |
|---|---|---|---|
| **PeTTa** | `fun/1`, filled by a WHOLE-PROGRAM PRE-PASS, arity-keyed via `current_predicate(F/N)` | — | **defers to run time** (`reduce/2` keeps the term when `fun(F)` fails) |
| **CeTTa** | admission bit-set of proof obligations | — | **DECLINES, and counts the decline**; interpreter stays authoritative |
| **JeTTa** | `resolved != null` from the resolver | a VARIABLE head in a constructor ARGUMENT | quotes it silently |
| **OURS** | `is_fun`, filled PER FORM ⇒ one head | a CROSS-HEAD call in `let`-VALUE position | **emits a wrong clause silently** |

That last cell is the finding. We are the only one of the four that neither defers, nor declines, nor
even quotes — we accept and miscompile. `compiled=3, fell_back=0, exhausted=[]` on a clause that
answers nothing.

## 2. WHAT TO TAKE FROM EACH

### PeTTa — the TWO-PASS pre-registration, which we already have and do not use
`filereader.pl:21-24` — `parse_form/2` registers `fun(F)` for EVERY `(= (F …) _)` before ANYTHING is
compiled. Their wiki: "two-stage compilation so definition order does not matter."

We have this: `ANormal.translate_program` computes `funs = defined_arities(program)` and its docstring
says "Collects the module's DEFINED HEADS first … the whole-module knowledge a compiler has and an
interpreter does not." **The live lane never benefits, because `CompileLane.compile_definition`
lowers ONE FORM, so `defined_arities` sees one definition.** The `is_fun` docstring already says the
name-only behaviour "was only safe by accident" for exactly this reason.

⚠️ **NOT A GREEN LIGHT.** Whole-program `is_fun` was tried and reverted 3× (`ANormal.jl:161`,
[[feedback_is_fun_static_half_alone_is_harmful]]). But the reverted experiment differed from PeTTa's
design on TWO axes that have since moved:

| | reverted 2026-08-11 | PeTTa | today |
|---|---|---|---|
| scope | whole SPACE incl. stdlib (`Eval.all_atoms(sp)`) | only heads DEFINED IN THE PROGRAM | program-scoping is available |
| key | NAME only | `arity(F,N)` | `is_fun` is ARITY-keyed now |

The arity fix landed BECAUSE of that failure — see the `S` counterexample (SKI at arity 3, Peano
constructor at arity 1) in `is_fun`'s docstring. So this is worth ONE experiment gated on the corpus
differential, not a change to just make. And PeTTa still carries the runtime half; static resolution
alone remains insufficient.

**The price PeTTa pays:** `NotReducible` does not exist in their tree — ZERO occurrences. An unknown
head is returned as data at compile time, but a KNOWN function with no matching clause is Prolog
FAILURE ⇒ `Empty`, and the atom is NOT returned. Worked around by hand-written catch-all clauses with
`(cut)`, and by `case`+`Empty` compiling to `\+` (which re-executes the key goal and discards its
bindings). Buying Prolog's engine costs MeTTa's unmatched-call semantics.

### CeTTa — DECLINE LOUDLY; the accelerator is never the authority
Default lane is a tree-walking C interpreter (`metta_eval`). Four compile lanes exist; the live one is
the **Prepared-Pure Machine** — a real IR (12 node kinds, positional slots, compile-time
`tail_position` and liveness), cached per `(space, call, language_id, …)`, evicted on failure.

The discipline is the transferable part:
* Admission = an explicit **bit-set of proof obligations** (`SINGLETON_HEAD`, `FLAT_LINEAR_LHS`,
  `RANGE_RESTRICTED_RHS`, `GROUND_CALL`, `REGISTER_*`, `CALL_POLICY_SUPPORTED`).
* **Every attempt AND every decline is a runtime counter** (`…COMPILE_ATTEMPT` / `…COMPILE_DECLINE` /
  `…ADMISSION` / `…DECLINE`), with a REASON string.
* `match_decision.h:6-12`: "its only soundness claim is that every omitted clause is structurally
  impossible … **The ordinary matcher remains semantic authority.**"
* Typed heads are deliberately EXCLUDED from acceleration until an accelerator implements their
  policy — conservatism as the default, not an afterthought.

**Their `Expression`-unreduced rule is STRUCTURAL, not a name list.** `eval.c:18384-18391` compares
the declared type against `get_meta_type(atom)`; an `ATOM_EXPR` has meta-type `Expression`, so an
`Expression`-declared parameter is returned unreduced through the SAME path as `Atom`. No per-op
special-casing. Worth comparing against how we decide the same thing.

Also: `map-atom`/`filter-atom` in their HE lane are PURE MeTTa source, same shape as ours
(`sealed`/`chain`/`decons-atom`). `foldl-atom` is a thin MeTTa wrapper over a native engine, and that
wrapper is the ONE place their compiler lane is entered for a higher-order combinator.

### JeTTa — non-determinism as a JVM TYPE
A multivalued function's return type IS `java.util.List`; that is the 4th field in `.jctx`
(`Context.kt:127-134`). Composition is a `map?`/`flat-map?` lift inserted by `CanonicalFormRewriter`
over a swappable 7-line runtime interface. Multivaluedness is inferred three ways: structurally from
non-mutually-exclusive clauses, from an interprocedural "relational callee" fixpoint, and propagated
along the call graph with explicit BARRIER functions (`collapse`, `assertEqual`, `once`, `unique`, …).

Its IR is the s-expression tree DECORATED IN PLACE — no ANF, no SSA. So is CeTTa's (no ANF anywhere in
196k lines). **We are the only one of the four with an A-normal form.** That is a real difference to
be able to justify, not a default.

## 3. BUDGETS — we are the only engine that reports overrun

| engine | default bound | on exhaustion |
|---|---|---|
| PeTTa | NONE (only `--stack_limit=8g`) | resource error |
| CeTTa | NONE (`fuel_limit = -1`, `max_stack_depth = -1`); C-stack guard 1–16 MiB | empty result set, matching HE |
| JeTTa | `MAX_REDUCTION_STEPS = 1024`, **runtime reducer only**; compiled recursion UNBOUNDED | **silent** — returns the current term |
| **OURS** | `max_steps = 512_000`, both lanes | **surfaced in `exhausted`** |

Keep this. It is the one axis where our lane is ahead of all three, and it is what let us rule the
budget OUT as the cause of the `fib-list` failure. Note CeTTa's compiled lane REFUSES to run under
bounded fuel at all (decline reason `"bounded fuel"`) — the opposite trade.

## 4. WHAT THIS ARGUES FOR, IN ORDER

1. **Make the cross-head case DECLINE instead of miscompiling.** CeTTa's counted-decline discipline is
   the cheap, safe half and needs no semantics change. A decline is recoverable — the lane already
   falls back to source. A silently wrong clause is not.
2. **Then** try program-scoped, arity-keyed `is_fun` as ONE gated experiment against the corpus
   differential. Program-scoped ≠ the whole-Space attempt that was reverted.
3. **Only then** consider the runtime `metta`-deferral half, which is what makes PeTTa's static half
   safe and which `ANormal.jl:190` already specifies.

⚠️ MEASURE COMPILED COVERAGE WITH `fallback=false`. Several cells scored as "passing" during this
investigation were DECLINES rescued by source fallback — `(= (f4 $n) (let $ix (0 1 2 3) (map-atom …)))`
among them. `compile_run`'s own docstring: "a fallback that silently rescues the result is how a
compiler comes to look complete." [[feedback_green_suite_hides_unwired_correct_code]]

## 5. ON UPSTREAM PERFORMANCE NUMBERS — do not quote them

CeTTa keeps a claims ledger (`benchmarks/paper_claims_*.tsv`, 46 claims) AND a reconciliation pass.
Many headline claims re-measure as **NO-DRIVER** — "10–100x faster than HE on shallow evaluation",
"38 percent instruction reduction", "6 ms startup" all have no runnable driver in tree. Others
CHANGED materially on re-measurement. Where PeTTa and CeTTa are both measured, each wins some:
8-queens PeTTa 0.05s vs CeTTa 8.22s; genomic backward-chaining CeTTa 32.32s vs PeTTa 55.43s; and one
row records CeTTa OOMing where PeTTa completes.

So: no cross-engine speed claim from any of these repos is citable without re-running it here.
[[feedback_upstream_number_has_a_pair_and_a_unit]]

---

# PART II — four more repos, 2026-09-03 (same day)

Read after Part I, at the user's request: `MeTTaIL`, `mettail-rust`, `rholang-rs`, `MeTTaScript`, plus
`MeTTa-Compiler` (MeTTaTron), which was NOT requested — it was noticed while listing `dev-zone` for
something else, and it is a MeTTa compiler sitting unread while we debug ours. That is the failure
the VISIBILITY PROTOCOL exists to prevent; a targeted search is not a survey.
[[feedback_targeted_search_is_not_a_survey]]

## 6. 🔴 TWO NAME COLLISIONS — neither "mettail" repo is our MeTTa-IL

**Check this before citing either repo.** Both were plausible reads of the name and both are wrong.

| repo | what it ACTUALLY is | proof |
|---|---|---|
| `mettail-rust` | a K-Framework-style **language-definition framework** (F1R3FLY-io). A `language!` proc-macro generating a parser + Ascent Datalog rewrite engine from a spec. Motivating case: rho-calculus. | `grep -rniE "metta" --include='*.rs' . \| grep -viE "mettail\|metta_il"` → **0**. `PatternTerm`/`Pattern` are closed enums with NO control-flow variant. |
| `MeTTaIL` (F1R3FLY) | **"Meta Type Talk Intermediate Language"** — Meredith's meta-language for ALGEBRAIC THEORY PRESENTATIONS. A `.module` composes theories in a lattice algebra (`/\`, `\/`, `\`, `Exports`, `Terms`, `Equations`, `Rewrites`) and elaborates to a BNFC grammar. | Its whole term language is 3 constructors — `ASTVar`, `ASTSExp`, `ASTSubst` (`metta_venus.cf:313-315`). No `chain`, no `cons-atom`, no A-normal form anywhere. |

**The thing that IS our MeTTa-IL exists upstream under a different name: "minimal MeTTa",** in LeaTTa's
`MettaHyperonFull/Minimal/Interpreter.lean` — a CPS nondeterministic stack machine, and a faithful
port of Hyperon's `interpreter.rs`.

**⇒ Our instruction set is a STRICT SUBSET of theirs: 8 of 13.**

    ours:    chain unify function return decons-atom cons-atom eval metta
    theirs:  …those 8… + evalc collapse-bind superpose-bind metta-thread capture context-space

Nothing of ours is missing upstream. INFERRED and worth testing: `GDisj`/`GFindall` are
`superpose-bind`/`collapse-bind`. That matters because LeaTTa runs Hyperon's UNMODIFIED corpus (270
assertions), so those two are the road to oracle-compatibility. Their `unify` is 4-ary
`(unify a p t e)` — ✅ so is ours, checked against today's IL dumps.

**TEXT SERIALIZATION IS VINDICATED, with the same rationale we used.** `MeTTaIL/Runtime/Sexpr.lean:5-16`:
*"gives every dialect a uniform surface syntax for free, with no per-dialect parser."* They use `$x`
for variables, as we do. Interop is nearly free. [[reference_il_text_roundtrip_is_the_wire_format]]

**⚠️ THE PROJECT RULE'S NAME COLLIDES.** "MeTTa-IL IS THE DISTRIBUTED ARTIFACT (MORK/Rholang/JAX/Rust)"
may be right about OUR artifact, but upstream the thing that goes to Rholang is a **GSLT
presentation** and the thing that goes to MORK is a **coded atom** (`MorkCodec`: 6-bit arity fields,
≤64 var slots). Neither is an instruction stream. **JAX appears NOWHERE** in either repo — the
analogue is `MeTTaIL2Matrix` (rholang → symbolic execution → automata → triangularize → GPU).
Consider "minimal-MeTTa IL" in anything published. [[feedback_mettail_is_the_distributed_artifact]]

## 7. THE CALL-vs-DATA TABLE, EXTENDED — and the one design that cannot have our bug

| engine | how it decides | on doubt |
|---|---|---|
| **PeTTa** | whole-program PRE-PASS + arity-keyed `fun/1` | defers to run time (`reduce/2` keeps the term) |
| **CeTTa** | bit-set of proof obligations | DECLINES, counted, with a reason |
| **MeTTaScript** | `hasEquations()` index lookup; **default-data** | **`BAIL`** — throws, re-runs in the interpreter |
| **JeTTa** | resolver `resolved != null` | quotes it silently |
| **MeTTaTron** | *never decides at compile time* | data — **and mutates the space**, plus a Levenshtein carve-out |
| **OURS (was)** | static set, filled PER FORM | emitted a wrong clause |
| **OURS (now)** | + `_space_defines_rule` guard | DECLINES (`4decc63`) |

### 🔴 PeTTa's pre-pass is the ONLY design that STRUCTURALLY cannot have this bug
MeTTaTron reaches OUR EXACT FAILURE SHAPE from a different direction: `(= …)` is a RUNTIME special
form (`eval/space.rs:29`) and the driver is strictly sequential (`main.rs:191`), so **rule visibility
is TEXTUALLY POSITIONAL** — a call written above its own definition silently becomes data. Same
defect, arrived at by having no pre-pass rather than by having a per-form one.

### MeTTaScript is the closest to what we should build, and it converges on today's guard
`compile.ts:94-98`, verbatim:

```ts
/** Whether `name` is defined by equations at all. Its negation is what marks a constructor, so a head
 *  this misses is compiled as inert data and never reduces. */
function hasEquations(env: MinEnv, name: string): boolean
```

That is `CompileLane._space_defines_rule` under another name — INDEPENDENT CONVERGENCE on the
predicate written today. Three things they carry that we do not:

1. **`BAIL`** (`compile.ts:130`) — a compiled node that meets a case it cannot handle faithfully
   THROWS, and the call re-runs in the interpreter. Sound because the compiled subset is
   side-effect-free. **That is our decline, but at RUN time, so it costs no coverage.**
2. **A var-headed-rule KILL SWITCH** (`eval.ts:1694-1697`): *"A variable-headed runtime equation
   `(= ($f $x) …)` can fire on a call to ANY head, so nothing compiled can be trusted while one is
   loaded."* **We have no such check. It is a real soundness hole in ANY static call/data partition,
   including the one shipped today.** ⇐ next thing to verify about our own lane.
3. **Epoch invalidation, deliberately conservative**: *"a data position can cause extra compilation,
   but a missing head can never expose stale compiled code."*

### MeTTaTron's fuzzy fallback — a genuinely novel answer, and a cautionary one
`eval/mod.rs:639-671`: an unknown head is classified by **Levenshtein distance ≤ 1** against known
rule heads. Within 1 ⇒ `Error`. Otherwise ⇒ **added to the space as a fact** and returned as data.
Two semantically opposite outcomes chosen by string similarity, and the failed call MUTATES THE
SPACE. It is name-shape-sensitive in a way our static-set bug was not: adding an unrelated definition
can flip a working program into an error.

## 8. ANF: WE ARE THE ONLY ONE OF FIVE

No A-normal form, CPS or SSA in CeTTa (196k LOC C), JeTTa, MeTTaTron (`grep` → 0; its `src/ir.rs` is a
DOCUMENTED RENAME of `SExpr`, spans kept for LSP indexing), or PeTTa (a flat goal list, never
materialized as a type). Not a reason to drop ours — but it is a design we must be able to justify
rather than assume, and no upstream corroborates it.

## 9. RHOLANG AS A TARGET — weaker than the project rule assumes

* **`rholang-rs` has NO ZAM**, confirmed BY SHAPE, not just by name: a plain PC + operand-stack
  machine, `cont_last` is a ONE-SLOT `(u32, Value)` register, no focus/path-to-root pair anywhere.
  This CONFIRMS `docs/specs/Mork/concurrent_zipper_machines_spec.md:326`, which said so from a grep;
  the shape search is the stronger version of the same claim.
* **`P | Q` compiles SEQUENTIALLY** — `compile_par` emits `P; POP; Q` (`codegen.rs:754-770`). A
  `SPAWN_ASYNC` opcode exists and codegen never emits it for `Par`.
* **No scheduler, no priority, no gas.** Nothing resembling our DISPATCH priority or its
  lexicographic-minimality argument. ⚠️ `AGENTS.md:14` advertises `drain_ready_processes` for
  ready-queue scheduling; **that function does not exist in the source.** Stale doc.
* The realistic seam is the 4-byte instruction word / public `Process { code, names, constants }` —
  NOT Rholang surface syntax. That layer discards `Name::Quote` reflection and models channels as
  `String`.
* **MeTTaTron is NOT prior art for a MeTTa→Rholang compiler.** Its Rholang codegen is marked "the old
  architecture", unimplemented (`docs/ISSUE_3_SATISFACTION.md:425-429`). The relationship is the
  INVERSE of ours: Rholang CALLS IN via a `rho:metta:compile` sysproc and gets `Par`-encoded data
  back — and a multi-result degrades to an ordinary `EList`, so even that bridge does not map MeTTa
  nondeterminism onto Rholang's `|`.

## 10. ⚠️ MeTTaTron DEPENDS ON MORK AND PATHMAP BY PATH

`Cargo.toml:64-88` — `mork`, `mork-expr`, `mork-frontend`, `pathmap`. It is a downstream CONSUMER of
the two upstreams we port. Its `Space::query_multi` rule lookup and its `exec`/`coalg`/`lookup`/
`rulify` MeTTa-level operators are a live, non-trivial usage example of MORK — worth reading before
designing anything MORK-facing.

Scale caveat before weighting it: **30 kLOC of Rust against 139 kLOC of Markdown in 250 files** (4.5:1).
Several headline claims have NO runnable driver in tree — "5-10x faster than FFI" (`README.md:610`),
"100-1000× parallel speedup" (`Cargo.toml:98`). **No benchmark anywhere compares MeTTaTron to another
MeTTa engine.** The citable artifact is `benches/e2e/e2e_throughput.rs`, not the prose.
[[feedback_upstream_number_has_a_pair_and_a_unit]]

## 11. BUDGETS, all seven engines

| engine | bound | on exhaustion |
|---|---|---|
| PeTTa | none (`--stack_limit=8g`) | resource error |
| CeTTa | none (`fuel_limit = -1`); C-stack guard 1–16 MiB | empty result set |
| mettail-rust | **NONE — Datalog runs to fixpoint** | diverge / OOM |
| rholang-rs | none found | — |
| JeTTa | 1024 steps, runtime reducer ONLY | **silent** |
| MeTTaTron | depth 1000 · cartesian 10000 · iterations 1000 | `Error` value |
| **OURS** | `max_steps = 512_000`, both lanes | **surfaced in `exhausted`** |

Ours remains the only one that REPORTS the overrun. Note MeTTaTron's are depth/width caps, not a fuel
counter — closer to a stack guard than to a budget.

## 12. WHAT TO DO WITH THIS

1. 🔴 **THE VAR-HEADED-RULE HOLE IS REAL — CONFIRMED THE SAME HOUR, and it is a SEPARATE defect from
   the frozen-call one.** MeTTaScript's kill switch pointed straight at it; one probe settled it.
   [[feedback_cheapest_disconfirming_test_first]]

   ```metta
   (= (g 1) one)
   (= ($f $x) (caught $f $x))     ; a VAR-HEADED rule — fires on a call to ANY head
   !(g 1)
   !(h 2)
   ```

   ```
   COMPILED     (g 1) -> one                    (h 2) -> (h 2)
   INTERPRETED  (g 1) -> (caught g 1) | one     (h 2) -> (caught h 2)
   ```

   `compiled=2  fell_back=0` — ACCEPTED, nothing declined. The compiled lane SILENTLY DROPS the
   var-headed rule's answers: one answer where the interpreter gives two, and an unreduced term where
   the interpreter reduces. A MISSING-ANSWER divergence, which no `fell_back` or `exhausted` field
   reports.

   NOT caused by today's guard — `_space_defines_rule` only ever DECLINES more, and this clause is
   never even reached. It is a pre-existing hole in the static call/data partition itself, and it is
   exactly what `eval.ts:1694-1697` refuses to tolerate: *"nothing compiled can be trusted while one
   is loaded."*

   The fix shape is theirs: detect any `(= ($f …) …)` in the space and decline compilation wholesale
   while one is present. Cost is unmeasured — such rules are rare, but the gate is the corpus
   differential, not this note. NOT DONE; recorded, not fixed.
2. **Consider `BAIL` over decline** — a runtime bailout costs no coverage where a compile-time decline
   does. Ours is side-effect-free in the same way theirs is, so the soundness argument transfers.
3. **`superpose-bind`/`collapse-bind`** if oracle-compatibility with Hyperon's corpus is wanted.
4. **Read MeTTaTron's MORK usage** before further MORK-facing design.
