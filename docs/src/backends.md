# Execution Backends

MeTTaCore is not a single interpreter — it is a **front-end over several execution engines**, with the
long-term design routing each workload to the engine that fits its computational grain. This page
documents what Core integrates today and where the architecture is heading.

> Architectural basis: the cross-cutting spec
> [`docs/specs/execution_model_architecture.md`](https://github.com/CognitiveSubstratesAI/docs)
> ("engine-per-workload"). Status there: *decided (analysis); first step = measure before building.*

## Engine-per-workload routing

The tree-walking interpreter is the root performance cost (re-match / re-dispatch per node). The model
shrinks it to a small reflective meta-kernel and routes the hot paths to specialized engines:

| Workload | Engine | Status in Core |
|---|---|---|
| symbolic multi-leg joins / pattern matching / head dispatch | **ZAM / MORK** — the Zipper Abstract Machine (the PathMap zipper) | ✅ **integrated** (the substrate) |
| whole-program optimization (join-order, saturation, MM2 lowering) | **MorkSupercompiler** (tier-2) | ✅ **integrated** ([`sc_execute!`](@ref)) |
| backward goal-directed **tabled** recursion (SLG + well-founded negation) | **Prolog (SWI)** now → native tabling-over-ZAM later | ⏳ **exploration / spike — not wired into Core** |
| numeric / typed hot kernels | native (FabricPC / Reactant / typed-Julia) | external packages |
| meta / control tail (`function`/`return`, type-cast, reflection) | small interpreted **meta-kernel** | the current Interpreter |

```mermaid
flowchart LR
    W["Workload"] --> Q{"computational grain"}
    Q -->|"symbolic joins / match"| ZAM["ZAM / MORK zipper<br/>(integrated)"]
    Q -->|"whole-program opt"| SC["MorkSupercompiler<br/>sc_execute! (integrated)"]
    Q -->|"backward tabled recursion"| PL["Prolog SWI<br/>(spike, not wired)"]
    Q -->|"numeric / typed kernels"| NK["FabricPC / Reactant"]
    Q -->|"meta / control tail"| IK["Interpreter meta-kernel"]
```

## `mc_run` — the execution stack (verified from code)

The routing above is the *model*; [`mc_run`](@ref) (`DualTrack.jl`) is the *implementation*. Traced through
the code (not the comments), the load-bearing fact is that there is **one execution engine** —
`space_metta_calculus!`, the MM2 exec-calculus on the MORK trie. **Every** run reaches it: the Direct lane
routes there directly (`mm2_route!` → `space_metta_calculus!`, `MM2Router.jl:159`), and the MorkSupercompiler
`execute!` wraps it with whole-program stages but ends in the *same* call (`SCPipeline.jl:451`). So the MORK
execution layer is **not optional** — it is the shared engine. What is tunable is only the `execute!`
preprocessing, read straight from the `SCOptions()` constructor: `stats=true, plan=true, decompose=true,
saturate=false` by default, engaged via `supercompile=true` (Direct) or `saturate=true` (MeTTa-IL).

```mermaid
flowchart TD
    MC{{"mc_run · MM2 router<br/>dispatch by form · DualTrack.jl"}}
    MC -->|"direct"| DIR["DIRECT lane<br/>mm2_route!"]
    MC -->|"~&gt; / def / theory"| MIL["MeTTaIL lanes<br/>rewrite / pipeline / theory"]
    ITP["Interpreter · StandardMeTTa<br/>234/234 + LeaTTa 270/270<br/>(co-equal front-end + fallback)"]

    DIR --> LOW
    MIL --> LOW["lower → MM2 (exec …) atoms<br/>mm2_lower_equals · :reduction / :relational"]

    subgraph SC["MorkSupercompiler — execution layer (NOT optional)"]
      direction TB
      PRE["whole-program stages · execute! (tunable)<br/>stats · plan! · decompose (_sc_tmp) · [saturate] · [drive]"]
      ENG(["space_metta_calculus! — MM2 exec-calculus<br/>EVERY run goes through this engine"])
      PRE --> ENG
    end

    LOW -->|"default"| ENG
    LOW -. "supercompile= / saturate=" .-> PRE
    ITP -. "intended — code: scratch space today" .-> ENG

    ENG --> STORE[("MORK Space / PathMap<br/>content-addressed trie + .act")]

    classDef front fill:#eef0fe,stroke:#4f46e5,color:#312b90;
    classDef eng fill:#dff0ed,stroke:#0f766e,color:#0a4f49;
    classDef pre fill:#f2ecfd,stroke:#7c3aed,color:#4c1d95;
    classDef itp fill:#e9f5ec,stroke:#15803d,color:#0d4d24;
    classDef store fill:#e6f4f2,stroke:#0f766e,color:#0a4f49;
    class DIR,MIL,LOW front;
    class ENG eng;
    class PRE pre;
    class ITP itp;
    class STORE store;
```

The fast lane (`mc_run` + MM2 router) dispatches by form into the Direct lane or the MeTTa-IL lanes; each
lowers to MM2 `(exec …)` atoms that run on the one engine. The `execute!` stages (`plan!` / `decompose` →
`_sc_tmp` join-staging / `saturate`) are whole-program preprocessing *around* that engine, cleaned up
afterward (`_cleanup_sc_tmp!`, `SCPipeline.jl:457`). The Interpreter is a co-equal front-end and the
fallback; routing its output through the engine is the **intended** design — in the current code
(`_mc_fallback_eval`, `DualTrack.jl:32`) it evaluates on a scratch `Interpreter.Space` and does **not** yet
pass through `space_metta_calculus!` (the dashed edge). The earlier "~5–30× slower / materializes" figure was
a stale comment, not a measured property of this path — omitted here pending a benchmark.

## Lineage — what the direct lane inherited from CeTTa (and what it didn't)

Cross-checked against CeTTa's actual C source (`eval.c`, `mm2_lower.c`, `compile.c`, `main.c`). The direct
lane is often called "CeTTa-style," but the precise picture is: it stands on **shared upstream MORK +
Hyperon-minimal machinery** that CeTTa *also* uses, then extends it in ways CeTTa does not.

**Shared upstream (both Core and CeTTa inherit it — it is MORK / Hyperon, not one from the other):**

- The MM2 **exec vocabulary** `(exec <priority> <pattern> <template>)` with `I` / `ACT` / `BTM` / `O` / `+` /
  `-` / `,` is upstream MORK (`MORK/kernel/src/main.rs`, `MORK_TUTORIAL.md`) — Core's `(exec 0 (I L)(O (+R)(-L)))`
  uses exactly those tokens.
- **`space_metta_calculus!`** is the upstream `Space::metta_calculus` — the *same* fixpoint-over-trie
  exec-stepping CeTTa invokes over FFI.
- The **minimal-MeTTa interpreter** skeleton (type-driven laziness, special forms controlling their own arg
  evaluation, the grounded-vs-equation split): Core's `Interpreter.jl` mirrors CeTTa's `metta_eval` /
  `metta_call` — both trace to Hyperon's minimal-MeTTa spec. Both also **table** equation queries.

**Core extended (not present in CeTTa):**

- **Auto-compilation of `(= L R)` → MM2 exec** ([`mm2_lower_equals`](@ref), modes `:reduction` / `:relational`).
  The big one: CeTTa does **not** lower equations — it treats MM2 as a *separately authored* surface (`.mm2` /
  `--lang mm2`) where a human writes exec rules, and its `mm2_lower` maps `=` to an equality **guard**
  (`mm2_guard_eq`), not an equation→exec rewrite. Core compiles ordinary MeTTa equations onto the exec-calculus
  automatically.
- A **runtime per-form router** (`mc_run`) vs CeTTa's **static** up-front engine choice (CLI / `--lang` / suffix).
- **MM2 / MORK as the primary path with the interpreter as fallback + bisimulation oracle** — the inverse of
  CeTTa, where the tree-walk interpreter is primary and MM2 is the side surface.

**CeTTa has that the direct lane does not:** an **AOT LLVM emitter** (`compile.c`, `--compile`: emits LLVM IR
text then exits — and even that delegates back to `metta_eval` at runtime). Core does no native codegen in this
path.

So "the direct lane mirrors CeTTa" is imprecise: the piece most directly shared with CeTTa is the
**interpreter** (both are the Hyperon-minimal reducer); the direct lane itself is a **Core-original
auto-compiler of MeTTa equations onto the shared MORK MM2 substrate**.

## Three orthogonal layers — substrate vs engines vs cognitive processes

"Engine-per-workload" is a statement about the **middle** layer only. Keep three axes distinct
(collapsing them is a recurring framing error):

1. **Cognitive processes** — forward-chaining, backward-chaining (PLN demand / tabling), abduction,
   MOSES evolution, ECAN attention, concept blending. These are **distinct reasoning paradigms** that
   synergize through the shared AtomSpace (OpenCog "cognitive synergy"), **not** interchangeable
   backends. Promote them as first-class modes.
2. **Execution engines** — ZAM zipper, MorkSupercompiler, native-tabling-over-PathMap, numeric
   kernels. **Semantics-preserving** executors chosen by the γ̂ diagnostic. "Backend" is the right word
   *only here* — it's about speed, not meaning.
3. **Substrate** — MORK / PathMap: the **one** shared metagraph memory + base rewriting/query. It is
   neither a cognitive architecture nor "a backend among others"; keeping it **singular** is what makes
   the cognitive synergy possible (every process reasons over the *same* atoms).

So **Prolog** is a *backward-tabled reasoning strategy* (layer 1) best realized as *native tabling over
PathMap* (layer 2) — **not** a parallel cognitive architecture with its own store (that would fork the
substrate, which is explicitly ruled out). The positive/stratified fragment of that strategy already
runs on the forward engine (semi-naive saturation + magic-sets + stratified NAF); the only genuinely
distinct residual is **WFS recursion-through-negation**.

## MORK / ZAM — the substrate backend (integrated)

Every Core atom is a byte-path in a **MORK PathMap** trie; matching and joins run on the **ZAM (Zipper
Abstract Machine)** — the zipper traversal already implemented in PathMap, *not* a model to build. By the
Mork-theory selectivity theorem, the zipper delivers O(1) candidates to the unifier for selective
symbolic joins (where a WAM is Ω(N) per leg). Core exposes the native engine directly through the
**E1 bridge** ([`mork_unify`](@ref), [`mork_apply`](@ref), [`mork_rule_rewrite`](@ref)) and the
trie-index query `space_query_multi` — the same path the [Pattern Mining](pattern_mining/overview.md)
native count and the connectome `info_flow` workload use.

The MM2 exec-calculus (`(exec …)`) and the [MeTTa-IL lane](mettail.md) both lower onto this substrate.

## MorkSupercompiler — the optimization backend (integrated)

[`sc_execute!`](@ref) runs a program through the **tier-2 MorkSupercompiler** against the space's trie:
join-order + Rule-of-64 decomposition (tier-1 `plan!`), plus opt-in stages — error-bounded approximate
rewrite, **KBSaturation** (seminaive fixpoint — the recursive-closure engine the [MeTTa-IL lane](mettail.md)
uses via `saturate=true`), **magic-sets goal-direction** (`use_magic_sets` — a bottom-up surrogate for
top-down SLG tabling that rewrites the rules toward a query so saturation tables only goal-relevant facts;
sound for the single-predicate / self-recursive / bound-first fragment, falls back to full closure
otherwise), the §6 supercompilation driver, and MM2 lowering. Stage opt-ins live on `SCOptions` and are
reachable identically from both lanes (Direct via `supercompile=true`, MeTTa-IL via `saturate=true`).

!!! note "Materializing, not streaming"
    The supercompiler **materializes** intermediate join results as `_sc_tmp` trie atoms — measured **~5–30×
    slower than streaming** (`docs/specs/execution_model_architecture.md`: 771ms vs 24ms ≈ 32×, 2389ms vs
    504ms ≈ 4.7×). It is an *optimization/closure* layer, not the fast match path. The **streaming fast path
    is lean selective probing on the zipper (ZAM)** (`space_query_multi` / the connectome `info_flow`), which
    realizes the MORK selectivity result — **O(1) candidates vs a WAM's Ω(N) per leg** under Σγ>1
    (`Mork-theory`), an *asymptotic* advantage, not a fixed factor. Use the supercompiler for saturation and
    whole-program rewriting, not as a general query accelerator.

## Prolog — the tabled-recursion backend (exploration, not wired)

**Honest status: Prolog is not integrated into Core.** No Prolog code ships in `src/`. It is a *decided
architectural role* with a validated FFI **spike**, not a live backend.

The engine-per-workload analysis assigns Prolog exactly **one** job: **backward, goal-directed, tabled
recursion** (SLG resolution with well-founded-semantics negation) — the one workload the forward ZAM does
*not* cover. The plan is **SWI-Prolog via a `libswipl` FFI bridge now, phased to native tabling-over-ZAM
later**, so the dependency is temporary. Explicitly ruled out: *compiling everything to Prolog* (PeTTa's
model) — it would make Core permanently Prolog-bound and SWI is slow at simple predicate calls.

What exists today (in the cross-cutting `docs/specs/prolog/`, **not** in this repo):

- `prolog_mork_dual_backend_plan.md` — the dual-backend plan and phase-out path.
- `SWI-Prolog_10.1.9_ch7_tabling_spec.md` — the SLG tabling semantics (the genuine gap).
- `spike/` — a runnable FFI spike (`swipl_ffi_spike.{pl,jl}`, `PrologBackend.jl`, `test_prolog_backend.jl`, 5/5) proving the Julia ↔ SWI bridge and the adapter shape.

Before any wiring, the discipline is **measure first** — the γ̂ selectivity diagnostic determines which
workloads actually need backward tabling versus the forward zipper. That diagnostic is **built**
(`MORK/tools/zam_diagnostic.jl` — `γ̂ = −log_N(|P(p)|/N)` with the Σγ̂ regime split, self-checked) but is
a standalone REPL tool, **not yet wired** into any routing decision. Until a measured workload demands it,
Prolog stays an exploration.

!!! note "Prolog as a complementary interim engine (decision in progress)"
    The plan endorses SWI **now** → native-tabling-over-PathMap **later**. To use it as a complementary
    interim engine *without* forking the substrate, three guardrails: (1) **scope to the residual** — WFS
    recursion-through-negation only (the forward engine already covers positive/stratified); (2) **marshall,
    don't mirror** — atoms→Prolog terms per query, answers back, drop Prolog state (MORK stays the single
    source of truth); (3) **concrete exit** — retire when native WFS passes SWI's conformance set (parity)
    and γ̂ says the workload doesn't need it, else it acquires permanent lock-in. **Highest-value first step
    is the differential ORACLE, not the engine**: wire SWI as ground truth to validate native WFS against
    (the pattern that de-risked the PLN chainer via `PLNDemand.jl`), and promote oracle→engine only if a
    measured WFS workload arrives before native is ready.

!!! note "Positive-fragment coverage (what the forward engine already tables)"
    Semi-naive `saturate!` (live) + magic-sets goal-direction (opt-in) cover **positive recursive closure**
    (transitive closure / ancestor / path) — the bottom-up equivalent of top-down SLG tabling for the
    positive fragment. **Arithmetic/comparison guard premises** (`< > <= >= == != + - * / %`) are now
    EVALUATED in rule bodies (mirroring `GROUNDED_REGISTRY` so they bisimulate the MM2 calculus lane):
    comparisons filter; a 3-arg `(op a b c)` binds its output. A value-generating rule needs a bounding
    guard to terminate — an unbounded one is truncated at the round cap with a warning (the pragmatic
    stand-in for the supercompilation homeomorphic-embedding whistle). What still routes to no engine:
    **negation** of any kind (NAF, stratified, or well-founded), **relational aggregation**, and
    **incremental retraction / TMS** — the genuine residual gaps.

## The Interpreter as meta-kernel

The standard [Interpreter](mettail.md) is the live evaluator today and the conformance reference (the
spec the other lanes bisimulate against). In the target model it shrinks to the **~5% reflective
meta-kernel** — `function`/`return`, type-cast, reflection — while ZAM owns matching and the supercompiler
owns whole-program optimization. The end state is *not* "zero interpreter" but a thin reflective tail over
engine-routed hot paths.
