# The compiled-head seam — `Eval.jl:968`

> **This header cites the seam and the tests, not a description of them.** Every claim below is a
> file:line you can open or a test that fails if it stops being true. Written 2026-09-02 because
> rediscovering this cost an hour twice in one session.
>
> * seam: `Core/src/standard/Eval.jl:968` (`eval_op`, defined `:926`)
> * merge template to factor: `Core/src/standard/Eval.jl:936-946`
> * contract types: `Core/src/standard/Eval.jl:546-552`
> * intercept invariant this AVOIDS: CODEMAP row 232 · `test/standard/tabling/test_intercept_position.jl`
> * coverage baseline to ratchet: `tools/lib_decline_survey.jl` (54.3%, 2026-09-02)

## Why the seam is equation lookup, and NOT the intercept

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
