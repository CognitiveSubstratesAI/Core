# The compiled-head seam — `rule_results`

> **Cited BY SYMBOL, not by line.** Line numbers are a courtesy; they drift and then mislead —
> `TABLING_ROADMAP`'s banner cited `Tabling.jl:374-380` for `_leader_pass` after the lines had moved
> off the symbol, and it misled a session for two weeks. Every claim here is a symbol you can locate
> or a test that fails if it stops being true.
>
> * **the seam**: `Eval.rule_results` — the ONLY equation lookup, and the only place the compiled
>   check lives. Gate: `test/standard/test_compiled_head_seam.jl`, testset "SINGLE SITE".
> * contract: `Eval.CompiledOk` (inner constructor) / `Eval.ExecNoReduce`
> * anti-vacuity: `Eval.fired(head)` — every seam test asserts it MOVED before comparing an answer
> * coverage baseline to ratchet: `tools/lib_decline_survey.jl` (MM2 54.3%, 2026-09-02)

## 🔴 THIS DOCUMENT WAS WRONG TWICE, AND BOTH ERRORS PASSED A GREEN TEST

**Corrected 2026-09-03, by execution.** Recorded rather than quietly fixed, because the failure shape
is the point and it is the same one the tabling banner taught.

**(1) "The seam is `Eval.jl:968` (`eval_op`)" — FALSE.** There were **FIVE** inlined equation lookups,
each running the same idiom (`query(space, (= call X))` → merge into `b` → filter `is_present(mb, X)`
→ `subst(X, mb)`):

| site | lane it serves |
|---|---|
| `eval_op` | minimal lane |
| `metta_call_instr` | `metta` dispatch — **the live one for a `!(f x)` query** |
| `metta_call_step` | argument/head reduction, via `_reduce` ← `interpret_args` |
| `_leader_pass` | tabling's worker |
| `_probe_no_rule` | `_NO_RULE`, which `tnot` consults |

`eval_op` serves the MINIMAL lane only. Wiring the seam there produced a closure that **NEVER FIRED**
(`fired = 0` on every shape) while a structural test asserting "the lookup precedes the query inside
`eval_op`" passed **5/5**. A structural assertion is only as strong as the claim it encodes.

**(2) "Tabling composes with no special case" — FALSE as written.** `_leader_pass` ran its OWN query,
so a tabled compiled head never saw the closure; and `_probe_no_rule` would report "no rule" for a
head that HAS a compiled implementation — feeding `_NO_RULE` and therefore `tnot`. That is a
**negation hazard**, not a missed optimisation.

**(3) AND FOUR OF THE CHECKS WRITTEN TO VALIDATE THIS WORK WERE WEAKER THAN ONES THE CODEBASE
ALREADY HAD.** Each passed, and each confirmed the wrong thing:

| the check I wrote | what it missed | the stronger form, now used |
|---|---|---|
| `Meta.parseall` → "PARSES OK" | a docstring bound to the wrong expression; the module would not load | actually loading it (`tools/run_tests.sh`) |
| "the lookup precedes the query inside `eval_op`" — 5/5 green | described a function the live path never enters | `fired(head) > 0` |
| test 3 asserting "an `Error` appears" | a claim about the TYPE SYSTEM, not the seam; failed for a reason about my closure | compiled-vs-uncompiled DIFFERENTIAL |
| `readdir("standard")` for the anti-drift count | does not descend into `standard/tabling/`, where TWO of the five copies lived — right answer, subset scope | `walkdir` over the whole `src` tree |

⇒ the seam is now guarded by the stronger form of each. The general rule this keeps re-teaching:
**a check invented for the occasion is usually weaker than the convention already in the tree.**

## The fix: `eqnLookup` as a FUNCTION

    rule_results(call, space, b) -> Vector{Tuple{Atom, Bindings}}

**Empty vector = no rule matched.** Non-empty = the answers, each with its substitution. The
compiled-head check lives INSIDE it, once. All five sites now call it; each lane keeps its own
continuation construction, which is where they legitimately differ.

⇒ **tabling composes BY CONSTRUCTION** rather than by claim (gate: SEAM TEST 5, `table!` + `fired > 0`),
and `_probe_no_rule` is `isempty(rule_results(key, space, Bindings()))`, correct for compiled heads.

⚠️ **The contract is TWO-valued, not four.** There is deliberately no `isempty(results)` branch. A
closure whose clauses matched but produced nothing must return one **`EMPTY` result with its
bindings**, exactly as an equation whose body reduces to `Empty` does — returning zero results is
indistinguishable from "no clause matched" and would silently turn a match into NotReducible.

## The contract is BINDING-VALUED

`rule_results` merges each answer's bindings into the caller's. A closure returning bare atoms skips
that merge and yields `(pair $w schiphol)` where `(pair schiphol schiphol)` belongs — **the same root
cause as the tabling substitution defect, now seen three times in three different clothes.**

`CompiledOk`'s inner constructor asserts `length(results) == length(binds)`, making the defect shape
**unconstructible by any caller** rather than merely discouraged. ⚠️ `ExecOk(results)` (one argument)
is the trap: it yields empty `binds`. A lint on the emitter would not catch a hand-written closure.

---

## Why equation lookup, and NOT the `is_tabled` intercept (still true, and still the reason)

`tabled_eval` is spliced at `Eval.jl:1196`, the top of `metta_instr`'s dispatch. Everything below it —
minimal ops (`:1198`), types (`:1212`), `type_check_errors` (`:1226`) — is SKIPPED for a tabled head.
That is the recorded bypass defect: `!(of-same-type Green Color)` answers `T` where the interpreter
gives `(Error … BadArgType 2 Color Property)`. **A wrong answer, not a lost one.**

🔴 **A SECOND SPLICE AT `:1196` WOULD INHERIT THAT BUG VERBATIM**, and the row's own diagnosis is that
the disease is *the bypass shape itself* — anything spliced at the top of dispatch must re-implement
everything below it, and each re-implementation drifts.

**Equation lookup is the seam because a compiled head replaces `eqnLookup` and nothing else.** The Lean
formalization (`MeTTapedia Languages/MeTTa/OSLFCore/FullLanguageDef.lean`) makes `typeOf`/`cast`/
`groundedCall` PREMISES and equation lookup the step that consults the rules. At `:968`:

* types, minimal ops, grounded calls and NotReducible are **upstream by construction** —
  `metta_instr` runs them, then lowers to `(eval …)`, which reaches `eval_op` (call site `:398`).
  Nothing to hoist. **Roadmap 7.C is NOT a prerequisite** for this work.
* **tabling composes with no special case**: a tabled compiled head hits `tabled_eval` at `:1196`,
  its worker calls `interpret`, which reaches `:968` and finds the closure.

## The contract — binding-valued, tri-state

🔴 **THE SEAM IS BINDING-VALUED, NOT ATOM-VALUED.** `:968` does
`results = query(space, (= to_eval X))`, then `for qb in results, mb in merge_bindings(b, qb)` and
builds each answer as `subst(X, mb)`. A closure returning bare atoms **skips the merge** and produces
`(pair $w schiphol)` where `(pair schiphol schiphol)` belongs — the SAME root cause as the tabling
substitution defect (`test/standard/tabling/test_answer_substitution*.jl`), which has now appeared
three times in three different clothes.

```julia
struct CompiledOk            # NEW — compiled heads return THIS, never ExecOk
    results::Vector{Atom}
    binds::Vector{Bindings}
    function CompiledOk(r, b)
        length(r) == length(b) || error("CompiledOk: a result without its bindings is the ($w …) defect")
        new(r, b)
    end
end
```

⚠️ **`ExecOk(results::Vector{Atom}) = ExecOk(results, Bindings[])` (`Eval.jl:550`) IS THE TRAP.** It
yields empty `binds`, so the merge loop takes its `else` branch and calls `eval_result(res, b, …)` with
the caller's UNMERGED bindings. A lint on the emitter would not catch a hand-written closure; an inner
constructor makes the shape **unconstructible by any caller**. This defect survives a differential on
ground calls — a type check is the only thing that fails it deterministically.

Miss ⇒ `ExecNoReduce` ⇒ the existing `:979` branch returns `NOT_REDUCIBLE` (the call returns itself,
hyperon `metta_call_return`). **Not `Empty`.** Collapsing that distinction turns every unreducible call
on a compiled head into a silently dropped answer.

## Wiring — factor the MERGE, not the BRANCH

🔴 **DO NOT route compiled heads through `is_executable` / the `Grounded` branch.** Making a compiled
`Sym` head look grounded changes observable semantics — `get-metatype`, `is-function`, anything that
inspects the head.

1. factor the `ExecOk`-consuming loop (`:936-946`) into a helper taking results+binds;
2. at `:968`, **immediately before `query`**, look up `to_eval.children[1]` in the compiled table;
3. hit ⇒ call the closure ⇒ feed its `CompiledOk`/`ExecNoReduce` to that same helper;
   miss ⇒ `query` exactly as today.

One lookup added at the seam. The grounded path is untouched.

## Unit of compilation, and invalidation

**The unit is the HEAD, not the clause.** If a head has five clauses and the emitter compiles four,
shadowing it LOSES the fifth's answers. All-or-nothing per head — Invariant 6 was right, at the wrong
granularity.

**Closures never inline `match` results.** That is JeTTa's closed-space shortcut
(`[[reference_jetta_aot_jvm_compiler]]`: *"AtomSpace is a COMPILE-TIME CONSTANT … match is PRECOMPUTED"*)
and a mutable space forbids it. Every `match` inside a closure runs LIVE against the space.

⇒ **adding a FACT invalidates nothing.** Only a change to the head's own RULES does. **Key each head's
closure on a hash of that head's clause set**, never on `space.revision` — a revision key would
recompile everything on every `add-atom` and make the compiled lane slower than the interpreter on any
program that writes. Two mechanisms, two triggers, no overlap: `_ANSWER_STAMP` (`Tabling.jl:1850`,
keyed `(objectid(space), space.revision)`) gives a tabled compiled head its DATA invalidation; the
clause hash gives its RULE invalidation.

## Milestone 1 — in order, 1.2 FIRST

| # | item | why this order |
|---|---|---|
| **1.2** | seam wiring + **one hand-written closure**, no emitter | proves the delivery mechanism end-to-end in one file. The opposite of the MorkSupercompiler order. |
| 1.1 | `EmitJulia`: `GUnify`, `GCall`, `GResidual` with σ threading | now has a target already known to work |
| 1.3 | per-head clause-hash invalidation | |
| 1.4 | differential, `fallback=false`, **sorted multisets** | MeTTa is multiset; MORK traversal order is not a contract |
| 1.5 | **WorldModel unchanged** — heads dispatched, wall-clock, three coverage numbers | if heads-dispatched is 0, nothing downstream rescues it |

Milestone 2: `GBranch`, `GDisj`, `GFindall`; the residual-free number climbs.

### The three seam tests (1.2's acceptance — write them first)

1. **binding propagation** — `(= (m $u) (pair $u (reach a $u)))` compiled ⇒ `(pair schiphol schiphol)`,
   NOT `(pair $w schiphol)`. This is the defect's third appearance; see `test_answer_substitution_cyclic.jl`.
2. **unreducible call** ⇒ the call returns ITSELF (`NOT_REDUCIBLE`), not `Empty`.
3. **typed head, bad argument** ⇒ the `BadArgType` error — proves type checking stayed UPSTREAM, and
   is the case the intercept position would have got wrong.

### Three coverage numbers, always reported together

`MM2 emitted` (54.3% baseline) · `closure emitted` (will be ~100% and means little) ·
**`closure residual-free`** ← the ratchet, the honest successor to 54.3%.

## Why WorldModel is the acceptance test

Chronology (`git log --follow`): interpreter `Eval.jl` **2026-06-12**, WorldModel **2026-06-20**,
compiler `Frontend/ANormal/Emit` **2026-08-06**. The capstone runs 100% interpreter *because the
compiler did not exist when it was written* — `Interpreter` 2 refs, `compile_run` **0**. Raising
coverage changes nothing observable while the only consumer never calls the compiler.

⇒ **shadowing at the seam is the DELIVERY MECHANISM, not hygiene.** WorldModel is not ported; it keeps
calling `Interpreter`, and the seam swaps one step underneath it.
