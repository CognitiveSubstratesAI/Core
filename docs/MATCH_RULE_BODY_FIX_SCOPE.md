# Fix scope: `collapse-match-in-rule-body` quirk in Core's Interpreter

> **⛔ SUPERSEDED / WRONG PREMISE (2026-06-25, Core e916f9f).** This doc's root-cause theory — that
> `match` inside a rule body returns `()` (an INTERPRETER bug) — is FALSE. Live traces showed `match`
> finds atoms correctly in a rule body, and a 4-engine cross-check (Core/hyperon/CeTTa/PeTTa) proved
> 3 of 4 engines — INCLUDING hyperon, the reference — reproduce the exact ECAN-Stability symptom.
> Core is FAITHFUL. The real defect was a **library bug**: `increment-ecan-tick!` stored
> `(ECATick (+ $n 1))` UNEVALUATED, so the evaluated remove target `(ECATick N)` never matched →
> accumulation → uncollapsed-match fork → overflow. Fixed by let-binding the value before add-atom
> (Core e916f9f). Do NOT implement the interpreter changes below. Kept for the audit trail only.
> See memory `feedback_metta_rules_verify_by_oracle_not_syntax`.

**Status:** ~~scoped, not yet implemented~~ SUPERSEDED — premise disproven. **Date:** 2026-06-25.
**Why now:** this single interpreter bug is the documented root cause of the ECAN Stability blowup
(`increment-ecan-tick!`'s existence-check `(collapse (match &self (ECATick $m) found))` returns `()`
inside the rule body → never removes the old counter → `ECATick` atoms accumulate → `heartbeat!` goes
quadratic). It is also the reason for **~5 fragile library workarounds** (`find-first-number` in
`get-sti`/`get-lti`/`get-vlti`, `is-in-af?`'s free-pattern detour, the `Box`/`unbox` SD-2 dance, the
both-evaluator setter guards). Fixing it at the interpreter retires the whole class across ECAN / PLN /
MOSES / WILLIAM at once — the first concrete step of "converge on one correct engine."

## The bug
`(match &self <pattern> <template>)` evaluated **inside a rule/function body** returns `()` (or spurious
variable-name symbols) even when matching atoms exist in `&self`. The same call works at top level.
Repro (the regression test the fix must pass):
```metta
!(add-atom &self (Foo aaa))
!(match &self (Foo $x) $x)                              ; top-level → (aaa)  ✓
(= (probe) (collapse (match &self (Foo $x) $x)))
!(probe)                                                ; rule-body → ()  ✗  (must become (aaa))
```

## Canonical design — cross-checked, all three references AGREE
| impl | `match` evaluates its pattern/template args? | `&self` resolution |
|---|---|---|
| **hyperon-experimental** (Rust) | **No** — args passed unevaluated to `space.query(&pattern)` (interpreter.rs:512, stdlib/core.rs:155-167) | grounded space atom `Atom::gnd(space)` bound at tokenizer registration (stdlib/mod.rs:81-82) |
| **CeTTa** (C) | **No** — special form, args not pre-evaluated (eval.c:12470, handle_match) | dynamic **registry binding**; `&self` is *re-bound to the active space before executing code in it* (library.c:6049-6053, eval.c:5895-5923); match falls back to current space `s` |
| **PeTTa** (Prolog) | **No** — pattern stays structural; only Space + template translated (translator.pl:259-262) | dynamic Prolog functor binding to the active space (spaces.pl:60-63) |

**Invariant:** `match` is a SPECIAL FORM (pattern/template/space args UNEVALUATED), and `&self` resolves
to the **space whose code is currently executing**, re-bound dynamically per eval context.

## Core's divergence (the narrow locus)
Core already has the right primitives — `query()` (Interpreter.jl:376-395) is a clean naive-linear match
over data atoms, and `&self` is a parse-time token → `Grounded{Space}` handle (Interpreter.jl:1286-1287).
Two suspects remain (pin which during implementation — one trace each):

1. **`&self` loses the active-space binding in nested eval.** The `match` op resolves its space arg and
   **falls back to the current eval `space`** when the arg isn't a `Grounded{Space}` (Interpreter.jl:1192:
   `tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space`). If, inside a rule
   body, `&self` is substituted/evaluated to something that is NOT the persistent `Grounded{Space}` handle
   (so it falls back to a *transient* eval `space` that lacks the data atoms), the query is empty. The
   references fix this by keeping `&self` an unevaluated grounded handle (hyperon) or re-binding it to the
   active space per frame (CeTTa). **Verify:** trace which `Space` object `match` queries in `probe` vs
   top-level; confirm they differ.
2. **Wildcard/var-headed scan injects spurious matches.** `query()` also scans `space.wildcard`
   ("var-headed atoms, which can match any discriminant", line 391-392). Rule LHS heads like `(= $x …)`
   land there and match a *data* pattern, returning variable-name symbols — exactly the "spurious
   variable-name matches" `find-first-number` filters. **Verify:** check whether rule atoms / var-headed
   stdlib entries are in `space.wildcard` and matched by a data query.

## The fix (after the 2 traces)
1. Treat `match`'s space/pattern/template args as **Atom-typed (unevaluated)** end-to-end — confirm
   `interpret_args` (Interpreter.jl:970) keeps `&self` and the pattern structural in a rule body (don't
   reduce `&self` to the transient space).
2. Resolve `&self` to the **active persistent space** dynamically (thread/bind it through nested eval like
   CeTTa's "set `&self` before executing"), so the `:space` fallback never silently swaps spaces.
3. Make data-pattern `query()` **not** match rule-definition / var-headed atoms (separate the rule index
   from the data scan, or skip `(= …)`-headed and var-headed atoms for non-`=` patterns).

## Acceptance
- The repro above returns `(aaa)` from `!(probe)`.
- ECAN: `increment-ecan-tick!` keeps `ECATick` count = 1 across N ticks; `heartbeat!` step cost is
  **linear**; Stability passes → ECAN 13/13.
- Then REMOVE the now-unneeded workarounds (`find-first-number`, `is-in-af?` detour, Box/unbox) and
  confirm 234/234 conformance + the ECAN/PLN/MOSES suites still pass. Net: less code, one correct `match`.

## Effort
Small-to-medium. The references give the exact target behavior; Core's `query`/`match`-op/`&self` code is
~3 functions. Risk: the `&self`-threading touches the eval core (regression-test against 234/234 +
test_pln_ecan + the full ECAN suite). The 2 verification traces are ~30 min; the fix ~half a day with tests.
