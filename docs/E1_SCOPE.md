# E1 scope — wire Core's evaluator onto MORK's native term engine

**Status:** scoping (2026-06-11). **Goal:** make Core's *functional* evaluation use MORK's verified
byte-buffer term engine (`expr_unify` + `expr_apply`) for matching and substitution, instead of
deserializing to Julia vectors and doing Julia-structural unify / naive string `replace`. E1 is the
**de-risked, single-result** wiring; the **multi-result / `$x=$y`** work is the separate **B phase**.

---

## 1. Where we are (grounded in code)

Core already stores atoms as MORK byte-trie keys, and **exec-atoms already use MORK's engine**:
`core_calculus!` → `space_metta_calculus!` (`CoreSpace.jl:661`). That path is MORK-native and was
hardened this session (differential: 24 PASS / 0 CRASH; value-gate; SumSink; backup_tree).

The **functional eval path bypasses the engine**:

| step | current mechanism | file:line |
|---|---|---|
| eval loop | `eval_metta(expr, space)::Any` over Julia `Any` vectors, single-result | `Eval.jl:47` |
| rule fetch | `core_rules` walks trie, deserializes `(= head body)` to Julia | `CoreSpace.jl:587` |
| **match** | `core_match` walks trie → bytes→string→`from_sexpr`→Julia vectors | `CoreSpace.jl:554` |
| **unify** | `_unify`/`_unify_args` — Julia structural Dict-building, not `expr_unify` | `Eval.jl:703,753` |
| **substitute (terms)** | `_apply_bindings` — structural recursion (already hygiene-safe) | `Eval.jl:759` |
| **substitute (grounded)** | `foldl/map/filter-atom` — **naive string `replace`** ← live hygiene bug | `AtomOps.jl:164,180,195` |
| multi-result | aggregated at `match`/`superpose`/`collapse`, first-rule-wins for rewriting | `Eval.jl:478,529,544` |

MORK's surface is ready (signatures verified):
- `expr_unify(pairs::Vector{Tuple{ExprEnv,ExprEnv}}) → Dict{ExprVar,ExprEnv} | UnificationFailure` (Robinson MGU + occurs-check) — `ExprAlg.jl:212`
- `expr_apply(ez::ExprZipper, bindings, oz::ExprZipper)` — hygienic de-Bruijn substitution — `ExprAlg.jl:506`
- `space_query_multi(btm, pat_expr, effect)` — enumerate matches, `effect(bindings, bytes)::Bool` — `Space.jl:358`
- `sexpr_to_expr(str)::Expr` / `expr_serialize(bytes)::String` — `Frontend.jl:232` / `Expr.jl:252`
- types: `Expr{buf}`, `ExprEnv{n=source_id, v, offset, base}`, `ExprVar=(source_id,idx)` — `Expr.jl`

## 2. The crux design point — variable identity

MORK variables are **positional**: `(source_id, idx)`, assigned by occurrence order on parse; named
vars are anonymized (`$`/`_N`) on serialize. Core variables are **named** (`$x` / `__var_x`).

A rule `(= (f $x) (g $x))` requires the head's `$x` and the body's `$x` to be the **same** variable.
If head and body are parsed by **separate** `sexpr_to_expr` calls, each gets a fresh `NewVar idx=0` in
its own source — they will NOT be the same variable, and applying the head's binding to the body fails.

**Resolution (validate in E1.0):** parse the *whole rule expression as one `Expr`* so head and body
share one variable namespace, then operate on its sub-spans — exactly how MORK's exec-atoms already
bind pattern↔template (one exec atom = one expr). The bridge owns this name↔positional mapping; the
rest of E1 builds on it. This is the single highest-risk assumption — prove it first.

## 3. Plan (E1 = phases 0–3; B deferred)

### E1.0 — Bridge module (foundation, de-risked, unit-tested in isolation)
New `src/eval/MorkBridge.jl` providing the ergonomic "unify then apply" surface MORK lacks externally:
- `mork_unify(query::Expr, data::Expr) -> Union{Dict{ExprVar,ExprEnv}, Nothing}` (wraps ExprEnv-pair
  construction + `expr_unify`, maps `UnificationFailure`→`nothing`).
- `mork_apply(template::Expr, bindings) -> Expr` (wraps `expr_apply` + buffer/zipper plumbing).
- `mork_rule_parts(rule::Expr) -> (head::span, body::span)` over a **single** parsed rule expr, so
  variables are shared (the §2 point).
- Round-trip helpers Core↔Expr that preserve the name↔positional map for a rule.
**Verify:** unit tests for unify/apply on hand-built exprs incl. the shared-`$x` rule case, occurs-check,
and a known capture case. No Core eval changes yet. **Risk: low.** Decides §2.

### E1.1 — Hygienic grounded substitution (the live bug, high value, narrow)
Rewrite `foldl-atom`/`map-atom`/`filter-atom` (`AtomOps.jl:164,180,195`) to substitute via the bridge
(parse body once → `mork_apply` with the bound var → serialize once) **instead of `replace(body_str, …)`**.
Kills variable-capture / substring-collision / quoted-string corruption.
**Verify:** regression fixtures — a body where the var name is a substring of another symbol; a binding
whose value contains the var name; a quoted string containing the var token. **Risk: low** (3 localized
functions, no eval-loop change). Closes the §9-priority "sealed+hygiene" item.

### E1.2 — Route rule-rewriting through MORK unify+apply
In the rule-rewrite seam (`Eval.jl:185–196`), replace `_unify_args` + `_apply_bindings` with the bridge:
parse the matched rule as one Expr, `mork_unify` evaled-args against the head span, `mork_apply` to the
body span, deserialize the result back to Julia for recursive `eval_metta`. Keep eval's `Any`
representation at the boundary (convert at the unify/apply points) to de-risk; thread Exprs later as an
optimization. **Verify:** existing eval test-suite must stay green; add tests for nested/var-heavy rules.
**Risk: medium** (touches the core reduction step — gate on full suite). Depends on E1.0.

### E1.3 — Match via `space_query_multi` (drop the deserialize + Julia unify)
Replace `core_match`'s manual trie walk + per-atom `from_sexpr` + `_unify` (`CoreSpace.jl:554`,
`Eval.jl:703`) with `space_query_multi(btm, pattern_expr, effect)` — byte-level unification inside the
trie walk, returning `ExprVar` bindings directly. Uses the engine hardened this session (value-gate, etc.).
**Verify:** `core_match`/`_eval_match` tests unchanged in behavior; benchmark the round-trip removal.
**Risk: medium** (matching semantics — match against full suite + the prefix-scoped multi-space tests).
Depends on E1.0/E1.2.

### B (deferred, separate phase) — multi-result + `$x=$y`
`space_query_multi` already enumerates *all* matches; surface that as Core nondeterminism so rule
rewriting yields a stream (not first-rule-wins), and add bidirectional `$x=$y` unification binding.
**Gated on** the deep bipolar/multi-result unification being stable (the two `source_act*_two_bipolar`
fixtures + the in-memory 2-source crossed case; upstream still stabilizing). Do NOT fold into E1.

## 4. Sequencing & gates
E1.0 → (E1.1 ∥ E1.2) → E1.3. Each phase: land behind green suites, add targeted regression tests,
commit separately. E1.1 is shippable on its own (bug fix) right after E1.0. Do not start B until E1.3
is in and the bipolar-unification work is scheduled.

## 5. Out of scope for E1
Multi-result/nondeterministic rewriting, `$x=$y` binding, the optional serialize-alignment to upstream
`VARNAMES`, and the `space_metta_calculus_in_prefix!` multi-space-calculus gap (`CoreSpace.jl:667`).
