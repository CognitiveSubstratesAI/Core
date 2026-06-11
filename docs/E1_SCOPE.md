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

## 2a. VERIFIED PRIOR ART (2026-06-11) — the var bridge + storage/query integration already exist

Checking the code (not memory): the `__var_x` ↔ `$x` problem was **already solved**, deliberately and
documented, and Core↔MORK is **already integrated at the storage/query level**. This corrects §2 and §3:

- **Variable bridge — DONE.** Storage form `__var_x` (a *ground* symbol) preserves variable names that
  MORK's native `$x` would anonymize via de-Bruijn (`CoreSpace.jl:13-15`). Converters exist:
  `to_sexpr` (`$x`→`__var_x`, store), `to_sexpr_query` (`__var_x`→`$x`, wildcard for matching,
  `CoreSpace.jl:54`), `from_sexpr` (`__var_x`→`$x` on read, `:83`), `_var_name` (canonical normalizer,
  `Eval.jl:1181`). **So E1.2's "representation reconciliation" is NOT new work — reuse `to_sexpr_query`
  / `_var_name`.** (And the `__var_xy`-in-output I called a "leak" is just this storage form surfacing —
  not a hygiene bug; over-called.)
- **Integration is storage/query-level, NOT term-engine.** Verified: no `expr_unify`/`expr_apply` calls
  in Core before E1.0. Core uses MORK as store (`to_sexpr`→`space_add_all_sexpr!`), match (a deliberate
  **trie-walk**, not `space_query_multi`), and metta-calculus. This matches the PeTTa/CeTTa idiom (§6).
- **⚠️ The trie-walk for match is a DELIBERATE, documented decision (`CoreSpace.jl:446`):**
  `space_query_multi` **short-circuits arity-1 patterns** (`(, single)` returns the pattern without
  iterating), so single-pattern `(match &self pat tpl)` finds nothing — this *broke* match until the
  walk rewrite. That reason **still holds** (the arity-1 branch is live in MORK `Space.jl`). **So E1.3
  ("match via `space_query_multi`") is NOT a clean win — it would revisit a solved problem and needs a
  MORK change (handle arity-1 by iteration) or a different entry point first. Do not blindly replace
  the working walk.**

**Net:** E1.0 (the term-engine bridge) is genuinely new and additive; it interoperates with the
existing var bridge via `to_sexpr_query`. But E1.2 is smaller than billed (reuse the converters) and
E1.3 is gated on a MORK arity-1 change, not free. Respect the existing deliberate design.

## 2b. MEASURED PULL (2026-06-11) — hyperon `b3_direct.metta` + the frog/green tutorial

Tested Core against the hyperon-experimental reference (the metta-lang.dev `recursion_vars` content is
distilled from it). **Functional recursion is solid** — factorial, sum-to-n, Peano `add`, list-length,
`even?`, and `(green Fritz)→T` all match hyperon. **The gap is MeTTa's nondeterministic
query-as-evaluation over free variables**, demonstrated by two reference cases:

```
; b3_direct.metta
!(ift (green $x) $x)              ; hyperon: Fritz   | Core: __var_x   (binding not propagated)
; frog/green tutorial (verbatim)
!(if (frog $x) ($x is Frog) ($x is-not Frog))
   ; hyperon: (Fritz is Frog), (Sam is-not Frog)   | Core: (__var_x is-not Frog)   [1 result, $x unbound]
!(if (green $x) ($x is Green) ($x is-not Green))
   ; hyperon: (Fritz is Green)                      | Core: (__var_x is-not Green)
```

Building blocks all pass in Core (`(frog Fritz)→True`, `(frog Sam)→False`, `(and True False)→False`,
`(green Sam)→∅`). The failure is precisely: evaluating `(frog $x)` with `$x` free should **query** the
store, **fan out** over every binding (`$x=Fritz→True`, `$x=Sam→False`), and **thread each binding**
into the result. Core evaluates once with `$x` unbound → no fan-out, wrong `if` branch, `$x` leaks as
`__var_x`. Same root cause both places: **no binding-propagation + no multi-result stream.**

**This is the concrete, reference-backed pull for the binding/nondeterminism work** (E1's
`expr_unify`/`expr_apply` threading + B's result streams, via match-against-store). `b3_direct.metta`
and the frog/green tutorial are the **conformance fixtures**. (NB: the `__var_x` rendering is the
storage form surfacing, but the real defect is that `$x` is never bound at all.)

## 2c. THE FIX MODEL — `OutcomeSet` (triangulated across hyperon / PeTTa / CeTTa)

The root cause is one architectural mismatch, confirmed by **all three** reference MeTTa interpreters:

| impl | eval returns | nondeterminism + bindings |
|---|---|---|
| hyperon-experimental | multiple reducts | nondeterministic `interpret` loop |
| PeTTa (Prolog) | all solutions | Prolog backtracking, each with a binding env |
| **CeTTa (C)** | **`OutcomeSet`** = set of `Outcome{atom, env}` | explicit; `ResultSet` (drop bindings) at top |
| **Core (Julia)** | **single `Any`, no bindings** | ❌ neither fan-out nor binding propagation |

**CeTTa is the cleanest blueprint** (same language-agnostic shape, no Prolog magic): every evaluator
returns an `OutcomeSet` where each `Outcome` carries `(atom, bindings)`. Function application iterates
the set, threads/combines each outcome's bindings, and fans out; `eval_top` drops bindings → `ResultSet`
for the user. `metta_eval_bind` (internal, bindings-carrying) vs `metta_eval`/`ResultSet` (top, atoms).

**Port to Julia (the fix):** change Core's `eval_metta(expr)::Any` to return an outcome set —
`Vector{Tuple{value, bindings::Dict}}` (an `OutcomeSet`); `run_metta`/top-level drops bindings. The
match-and-bind at each reduction uses MORK's `expr_unify` (E1.0's bridge already gives this); fan-out
is "for each rule/fact that unifies, emit an outcome." This single change fixes the frog tutorial,
`(f (superpose x))`, `(croaks $x)`, and `(ift (green $x) $x)` together — it IS E1.2 + B unified, and it's
the *port of the interpreter's nondeterministic half* that the redesign skipped. Gate = the §2b fixtures.

## 3. Plan (E1 = phases 0–3; B deferred)

### ✅ E1.0 — Bridge module — DONE (`cda1c39`, 2026-06-11)
Shipped `src/eval/MorkBridge.jl`: `mork_unify` / `mork_apply` / `mork_rule_rewrite` (Expr + string
forms), +7 regression tests, Core suite green. **The §2 crux is RESOLVED and validated against MORK
directly:** separate-parse fails the crossed-variable case (`(q $y $x)` over `(p $x $y)` vs `(p a b)`
→ wrong `(q a b)`); parsing the whole `(= head body)` as one Expr + `ee_args!` gives the correct
`(q b a)`. Additive only — no eval path changed yet. Original plan below.


New `src/eval/MorkBridge.jl` providing the ergonomic "unify then apply" surface MORK lacks externally:
- `mork_unify(query::Expr, data::Expr) -> Union{Dict{ExprVar,ExprEnv}, Nothing}` (wraps ExprEnv-pair
  construction + `expr_unify`, maps `UnificationFailure`→`nothing`).
- `mork_apply(template::Expr, bindings) -> Expr` (wraps `expr_apply` + buffer/zipper plumbing).
- `mork_rule_parts(rule::Expr) -> (head::span, body::span)` over a **single** parsed rule expr, so
  variables are shared (the §2 point).
- Round-trip helpers Core↔Expr that preserve the name↔positional map for a rule.
**Verify:** unit tests for unify/apply on hand-built exprs incl. the shared-`$x` rule case, occurs-check,
and a known capture case. No Core eval changes yet. **Risk: low.** Decides §2.

### E1.1 — Hygienic grounded substitution — REFRAMED (tested 2026-06-11: latent, not live)
**Finding:** the string-`replace` is *provably unsafe* in isolation
(`replace(replace("(pair __var_a __var_ab)", "__var_a"→0), "__var_ab"→1)` = `(pair 0 0b)`), but 6
end-to-end adversarial cases (map/foldl with `$x`/`$xy`, `$a`/`$ab`, capturing bindings) all returned
**correct** results — current inputs dodge the landmine (lambda var vs free var land in non-colliding
forms). So E1.1 is "**harden a proven-unsafe path + de-dup onto the engine**", not "fix a firing bug".
Still earned (a proven-unsafe substitution is a real defect, and `expr_apply` removes it while
consolidating onto the verified engine) — but lower urgency than billed. Separately found a real minor
bug: free/unbound vars leak as `__var_xy` into HO-op output (a de-mangling gap). Original plan below.


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

## 6. Prior art — how PeTTa / CeTTa / our packages bridge MORK (2026-06-11 cross-check)

Cross-checked the four other MORK consumers. Two cross a language/FFI boundary to **Rust** MORK;
three are in-process Julia like Core.

| consumer | reach | uses MORK as… | term engine (`expr_unify`/`expr_apply`) |
|---|---|---|---|
| **PeTTa** (Prolog) | C FFI `libmork_ffi.so` via `LD_PRELOAD` (`run.sh`, `build.sh`) | store + **match via `dump_sexpr`** + `metta_calculus`; reduction stays in Prolog | not as a primitive (it's *inside* `dump_sexpr`) |
| **CeTTa** (C) | static C-ABI `libcetta_space_bridge.a` (`Makefile:55-66`); byte-span packets v1/v2/v3 | store + algebra (join/meet/subtract) + `query_bindings` + mm2; **unifies at the C level** | no |
| **MORKTensorNetworks** (Julia) | `using MORK` in-process; zippers on `space.btm` | trie-backed relational datastore → CSR | no |
| **FactorVSA** (Julia) | `using MORK: register_grounded!` (`MeTTaShim.jl:22`) | **grounded-function registry only** | no |
| **HMH** (Julia) | via FactorVSA; no direct MORK | — | no |

### What's NOT relevant to us (forced by their FFI boundary)
PeTTa's `.so`/`LD_PRELOAD`, CeTTa's C-ABI/`catch_unwind`/byte-span packets/synthetic var renaming,
string/byte (de)serialization — all artifacts of crossing **into Rust from another language**. Core
and MORK are the **same Julia process**, so these vanish: call `expr_unify`/`expr_apply` directly on
`Expr` objects, zero-copy. This confirms E1's premise. **The `.sh`+FFI machinery is not our concern.**

### What IS worth learning (semantic, language-independent)

1. **Nobody runs interpretation *through* MORK's term engine — and that reshapes E1.2/E1.3.** The
   universal idiom is: **match a pattern against the STORE via the query engine** (PeTTa `dump_sexpr`,
   CeTTa `query_bindings`, both = `space_query_multi` + `expr_apply`), keep the reducer in your own
   layer, and use a **grounded gateway** for foreign ops. So the validated shape of E1 is *match via
   `space_query_multi` (E1.3) + substitute via `expr_apply` (E1.1)*, **not** "swap Core's reducer out
   for MORK term-ops." Concretely, prefer **E1.3 (query the rule-space)** over E1.2's fetch-rule-then-
   `expr_unify`-term-vs-term — the latter is a path no consumer took; the rule lookup itself should be
   a query. Treat standalone `expr_unify` as an internal of the query path, not Core's main verb.

2. **Grounded objects: CeTTa `GV_FOREIGN` and FactorVSA's handle-arena CONVERGE — adopt it (new E1
   concern).** Foreign/grounded values must NOT enter the symbolic trie. The proven pattern: keep the
   Julia object in a **process-global handle-arena** (FactorVSA's `DualIndex` + `ReentrantLock`,
   `FactorVSA.jl:142`), put only a symbolic handle atom `(VecRef h)` into MORK, and register a
   **grounded handler** (`register_grounded!`, `MeTTaShim.jl:120`) that derefs the handle, computes in
   Julia, and returns a fresh handle. CeTTa does the same with `void* GV_FOREIGN` + symbol→C-fn
   dispatch (`grounded.c:207`). **Core already has `GROUNDED_REGISTRY`** (`Eval.jl:158`); when E1 moves
   terms onto byte-`Expr`s, grounded literals (numbers — the §9 "Number model" item — and any Julia
   objects) need this handle-arena treatment so they survive as byte-trie atoms. **Reuse FactorVSA's
   `DualIndex` rather than reinventing.** This belongs in E1.0's bridge or as an E1.1.5 step.

3. **Multi-result = bulk-enumerate then caller-iterate** (validates the deferred B phase). PeTTa
   returns all matches as a newline-delimited string and backtracks via `member/2`; CeTTa returns a v3
   packet with **per-factor multiplicity groups** for conjunctive `(, p1 p2 …)` queries. For B: have
   `space_query_multi` enumerate all matches, surface them as a Core stream; borrow CeTTa's per-factor
   grouping idea for conjunctive multi-result witnesses.

**Net:** the FFI bridges teach us nothing mechanical (we're in-process), but they unanimously endorse
*query-against-store + grounded-gateway* over *reducer-on-engine*, and they hand us a ready grounded-
object pattern (handle-arena) that's already implemented in-repo by FactorVSA. Fold #1 and #2 into the
plan; #3 informs B.
