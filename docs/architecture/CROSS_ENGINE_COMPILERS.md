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
