<!-- vim: ft=markdown -->
# Primitive surface, stdlib duplication, and JuliaSymbolics-inspired tooling — 2026-06-10

**Status**: Analysis + roadmap. No substrate code changed by this document. Findings
are verified against source (line/grep evidence inline) or marked unverified.

**Lineage** (each builds on the prior, do not re-rediscover):
- [CORE_DEEP_DIVE_FINDINGS_2026-05-29.md](CORE_DEEP_DIVE_FINDINGS_2026-05-29.md) — structural
  facts: the three-tier dispatch, grounded inventory, stdlib inventory.
- `Core_Audit_Final_Findings.md` (external audit, 2026-06-10) — primitive surface vs the
  canonical MeTTa spec + hyperon-experimental Rust stdlib; the `unify`/`chain` correction;
  Number-model, double-registration, type-oracle findings.
- **This doc** — verifies the audit against source, adds the PeTTa/CeTTa/hyperon/JuliaSymbolics
  cross-reference, and lays out the ecosystem-tooling plan (TermInterface hinge → edge adopts).
- Related: [ATOM_TYPING_TRADEOFF.md](ATOM_TYPING_TRADEOFF.md) (the deferred typed-`Atom`
  refactor — the substrate this plan needs) and
  [ALGORITHM_LIBRARY_GOVERNANCE.md](ALGORITHM_LIBRARY_GOVERNANCE.md).

---

## 0. The one-sentence finding

Core's duplication problem (utilities reinvented per algorithm-library; grounded ops
re-parsing S-expr strings ~40×) is a **symptom of a canonical layer thinner than every
reference implementation** — PeTTa, CeTTa, and hyperon-experimental each solve it with one
comprehensive, reused layer. The durable fix is to **fill out Core's canonical layer** the
way they do, with a typed atom that implements the zero-dep `TermInterface` protocol at the
grounded boundary — which simultaneously fixes the Number-model lossiness and unlocks the
JuliaSymbolics ecosystem at the edge.

---

## 1. Verified primitive-surface findings (against source)

| Finding | Verdict | Evidence |
|---|---|---|
| three-tier dispatch (special forms → grounded → rules) is sound | TRUE | `Eval.jl` head-dispatch |
| `unify`/`chain`/`function`/`return` are special forms (1st audit's "missing" was wrong) | TRUE | `Eval.jl` `head === :chain/:function/:unify` |
| Number model routes through `Float64` | TRUE | `Primitives.jl` comparison/arith `tryparse(Float64,…)`; integral results re-integerized |
| Float64 lossiness is real | TRUE | `(/ 1 0)` → `Inf` (not `DivisionByZero`); `(== 9007199254740993 9007199254740992)` → `True` (distinct int64s collapse) |
| `xor` absent | TRUE | grep=0; it is canonical in hyperon `arithmetics.rs` |
| `sealed`, `collapse-bind`/`superpose-bind`, `metta`, `context-space`, `pragma!`, `nop`, `capture`, `get-doc`, `sort-strings`, `print-alternatives` absent | TRUE | grep=0 each |
| `cons-atom`/`car-atom`/`cdr-atom`/`size-atom` double-registered (Primitives.jl + AtomOps.jl) | TRUE | both files register all four |
| type oracles single-valued | TRUE | `_infer_type`/`_spec_types_match` first-decl-wins |
| **map-atom/filter-atom hygiene bug** | **TRUE (demonstrated)** | `(map-atom (1 2) $x (map-atom (10 20) $x $x))` → `((1 1)(2 2))`, not `((10 20)(10 20))` — naive `replace(body,"$x"=>item)` captures a same-named nested loop var |

**Nuance / where the audit overstates:** "Number model = highest leverage, widest blast
radius." For everyday small-int code (every NodeId/index in MOSES) the integerization makes
it a non-issue; the real bites are large-int identity, `/0`, and float overflow — biggest
*effort*, *narrow* bite. The cheap wins (de-dup, `xor`, hygiene) are better near-term ROI.

**Caveat:** the external audit predates this session's eval/type fixes (`460e264` bare-symbol
arity + `let` tuple-destructure; `10f3770` `_infer_type` + polymorphic checking; `get-metatype`
`__var_`). Its `get-type`/`type-cast` descriptions reflect pre-fix code.

---

## 2. Root cause: the canonical layer is under-provisioned (cross-reference)

How each reference avoids per-library duplication of utilities:

| Impl | Mechanism | `xor` | `is-member` | `clamp` | list ops |
|---|---|---|---|---|---|
| **hyperon-experimental** | Rust grounded modules (`arithmetics.rs`/`atom.rs`/`math.rs`) + one `stdlib.metta` | grounded `arithmetics.rs` | **not canonical** | not a primitive | `foldl-atom` etc. in stdlib |
| **PeTTa** (MeTTaLog) | comprehensive Prolog **host builtins** | builtin (`metta.pl:100`) | builtin (`metta.pl:146`) | once, in `lib_pln.metta` | `member`/`length`/`foldl`/`append`/`sort` all builtins |
| **CeTTa** | native C primitives + **namespaced** `lib/list.metta`/`math.metta` (`list:` module) | (native) | namespaced | — | "the normal list lane users reach for" |
| **Core** | **minimal** grounded tier + thin un-namespaced stdlib | **ABSENT** | **ABSENT** | **×5 copies** | partial |

All three references provide ONE comprehensive canonical layer (organized by domain) that
algorithm code reuses. Core's deliberately-minimal grounded tier (praised as "clean") is the
outlier — minimalism at the grounded tier *pushed* the common utilities into the libraries,
causing per-library reinvention. The fix is not minimalism vs not; it is **fill out the
stdlib tier** (it need not be grounded) to reference-level breadth.

### Verified duplication (Julia + MeTTa level)
- `clamp` defined **5×**: `stdlib/math.metta` (canonical) + `lib/ActPC-Chem` + `lib/ecan` +
  `lib/pln/stv.metta` + `lib/pln/pln_core_logic.metta` (PLN duplicates internally).
- Cross-library exact-name reinvention is otherwise SMALL (only `clamp`, `trace!`, and a few
  attention-domain fns shared ecan↔pln↔hyperseed). The other libraries are mostly domain logic.
- MOSES localized standard primitives (`xor`/`~=`/`===`/`is-member`) and reinvented stdlib
  under a `List.*` namespace (`List.length`≈`length`, `List.foldl`≈`foldl-atom`, `concatT`≈
  `append`, `removeElement`≈`subtraction-atom`). The `List.*` namespacing instinct is *correct*
  (CeTTa does `list:`); the error is making it a separate copy instead of the canonical lane.
- **Julia level (§7):** grounded callbacks re-derive the term protocol — `startswith(…,"(")`
  ×34, `strip(args…)` ×39, `_tokenise` ×27, with **zero** shared `is_expr`/`head`/`children`
  helper. `WILLIAM.lgg` is the exception (operates on `expr.buf` directly — the right altitude).

---

## 3. The category split (different fixes for different things)

hyperon is the arbiter of "canonical vs not":
1. **Canonical primitives Core must own** — `xor` (hyperon grounded). Localizing it was a flat error.
2. **MeTTaLog/PeTTa-compat shims** — `is-member`, `~=`, `!=` (NOT hyperon-canonical, but PeTTa
   builtins that MeTTaLog-sourced ports like MOSES depend on). Home: the existing
   "HE-MeTTa compatibility" section of `stdlib/core.metta`, labeled as compat.
3. **Domain utilities** — `clamp` (canonical nowhere as a primitive). Consolidate the 5 copies to one.
4. **Stdlib duplicates** — `List.*`/`concatT`/`removeElement`. Delegate to Core's `length`/
   `append`/`foldl-atom`/`subtraction-atom` (keep the namespace as thin wrappers, CeTTa-style).

---

## 4. JuliaSymbolics-inspired tooling (the §7 plan, source-verified)

`TermInterface.jl` is **zero-dependency** (~3 files); its protocol is ~10 generic functions
implemented *by extension* for any type: `isexpr` `iscall` `head` `children` `operation`
`arguments` `arity` `metadata` `maketerm`. **Metatheory depends on `TermInterface 2.0`**, and
the symbolic-math content tools (Symbolics / SymbolicUtils / SymbolicIntegration / SymbolicSMT)
all dispatch on `Symbolics.Num`. So the entire ecosystem reduces to **two adapter points**:

| Tool | Entry API | Operates on | Deps | Role |
|---|---|---|---|---|
| TermInterface | `isexpr/head/children/operation/arguments/maketerm` | *Core's atom* | **zero** | **L0 — the hinge** |
| Metatheory Rewriters | `Chain/Prewalk/Postwalk/Fixpoint/Walk` | TermInterface terms | TermInterface | L1 — re-derive natively |
| Metatheory EGraph | `EGraph/@rule/saturate!/extract!` | TermInterface terms | moderate | L1 — edge (MORK trie = native equiv) |
| Symbolics | diff / solve / linalg / `build_function` | `Num` | heavy | L3 content — edge |
| SymbolicSMT | `Constraints/issatisfiable/isprovable/resolve` | `Num` + **Z3** | heavy | L3 — verification / PLN / types |
| SymbolicIntegration | `integrate(Num,Num)` (Risch / rule-based) | `Num` + **Nemo** | heavy | L3 — calculus kernels |

**Two adapters unlock everything, only one is ever a Core dep:**
1. **Implement TermInterface for Core's atom (L0, zero-dep).** Makes Core atoms first-class in
   Metatheory's e-graphs/rewriters *for free* (Metatheory dispatches purely on the protocol).
2. **One `atom ↔ Symbolics.Num` translator (L3).** The content tools all consume `Num`, so one
   translator unlocks Symbolics + SymbolicSMT + SymbolicIntegration at the edge.

**Verdict per layer:** L0 adopt `TermInterface` + implement it (improves on the audit's
"own names" now that the package is confirmed zero-dep). L1 re-derive the Rewriters combinators
as named supercompiler strategies; EGraph as an edge adapter (MORK is the native equiv). L2
SymbolicUtils skip as a *core* dep (canonical-form premise fights MeTTa's no-auto-reduce). L3
adopt Symbolics/SMT/Integration **at the edge, per-kernel**, via the one `Num` translator —
never in the interpreter core.

---

## 5. The unification: §3.4 (Number) and §7 (term protocol) are the same refactor

Both stem from one boundary mistake: **grounded ops receive serialized strings
(`to_sexpr_atom`) and re-parse them.** A *typed atom that implements TermInterface* at the
grounded boundary fixes both at once — numbers stop round-tripping through
`tryparse(Float64,str)`, and term structure stops being recovered via `startswith("(")`.
This is exactly how the references already work (hyperon matches a Rust `Atom`/`Number` enum;
CeTTa native structs; PeTTa Prolog terms — none serialize-and-re-parse inside a grounded op).

This is the substrate [ATOM_TYPING_TRADEOFF.md](ATOM_TYPING_TRADEOFF.md) defers ("type the data
model or don't bother"). The TermInterface protocol + a `Number` variant is the *shape* of that
typed `Atom`, and it pays for itself twice (Number correctness + term de-duplication) and a
third time (free JuliaSymbolics interop at the edge).

---

## 6. Remediation roadmap (sequenced by ROI / risk)

1. **Cheap, now (low risk):** promote `xor` (canonical) to Core; add `is-member`/`~=`/`!=` to
   `stdlib/core.metta`'s HE-compat section; consolidate `clamp` ×5 → 1; delete the local copies;
   de-duplicate the double-registered list ops (keep `AtomOps`). Re-run the full suite.
2. **Structural guard:** a CI lint — fail when a `lib/**/*.metta` definition shadows a
   Core-provided name; warn on a watchlist of common utility names. (The references don't need
   this because their canonical layer is exhaustive; Core does, until its stdlib is filled out.)
3. **L0 scaffold (reviewable):** implement TermInterface for Core's atom; retrofit ~3 grounded
   ops; measure suite-green + `startswith("(")` count drop + zero added transitive deps.
4. **Scoped substrate project:** the typed-`Atom` + `Number` refactor (folds §3.4 in), retrofit
   the ~40 grounded callbacks onto the L0 interface. Guard with the 392-test suite.
5. **map-atom/filter-atom hygiene:** gensym the loop var instead of naive string-replace.
6. **Per-kernel, as needed:** the `atom↔Num` translator + L3 edge adopts (start with
   SymbolicSMT to *prove* the boolean-reduct: `isprovable(original ≡ reduced)`).
7. **Defer/skip:** SymbolicUtils (L2) as a core dep; the full Number model unless a workload
   needs large-int/`/0` correctness.

See [experiments/ecosystem_tooling/](../experiments/ecosystem_tooling/) for the proofs-of-shape
(L0 scaffold, SMT-verify-reduct, rewriter combinators) before any of this earns the load-bearing path.
