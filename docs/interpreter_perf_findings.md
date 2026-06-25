# Core Interpreter — Performance Findings (2026-06-25)

Whole-path + whole-package static/dynamic analysis of the **live** `StandardMeTTa.Interpreter`
(tree-walking reducer). Tools: AllocCheck, JET, BenchmarkTools — run via the warm Core REPL with
`JULIA_LOAD_PATH="@:@v#.#:@stdlib"`. Probes: `tools/jet_alloc_probe.jl`, `tools/warntype_probe.jl`,
`benchmark/ecan_perf_diag.jl`.

> **Scope:** excludes `src/eval/Eval_obsolete.jl` / `EvalND_obsolete.jl` (dead code; still `include`d and
> referenced by ~145 legacy test sites — deletion is the separate migration arc, not a perf concern).

## TL;DR

The live interpreter is **correct and type-clean** (hyperon-faithful, 234/234 conformance; no `::Any`/`Box`,
no live `Vector{Any}`). It is **allocation-heavy**, not GC-bound: reducing a trivial `(f 42)` costs **5,722
allocations**. Two structural drivers; **both are perf-only — do not touch the eval core until a workload
measurably needs the speed** (see the guardrail).

## Measured (BenchmarkTools)

| call | min time | allocs | memory |
|------|---------:|-------:|-------:|
| `metta_run (f 42)` — one trivial 2-rule reduction | 361 µs | **5,722** | **234 KB** |
| `match_atoms` | 2.2 µs | 69 | 3.5 KB |
| `subst` | 0.28 µs | 4 | 128 B |

- Cost is **allocation throughput + dispatch**, not GC pauses (`exp_gc.jl`: GC-disable = 1.0× — many tiny,
  short-lived allocs are cheap to collect but expensive to *make*).
- ECAN `heartbeat!` ≈ **~16k interpreter steps/tick** (~4.5 s/tick: naive-linear match, no JIT). Atom count
  is **flat** post-ECATick fix (`e916f9f`) — no quadratic accumulation.

## Allocation sites (AllocCheck — 675 across the reachable call tree from `metta_run`)

1. **`Bindings` Dict+Vector copy** — `src/standard/Atoms.jl:74` (`var_to_slot::Dict{Var,Int}` + slot Vector
   + backing `Memory`). Cloned per match candidate; reached via `add_var_binding` / `merge_bindings` /
   `match_atoms`. **Top alloc driver.**
2. **Reduce-step construction** — `src/standard/Interpreter.jl:105` (Frame, 78×), `:544` `_metta(atom,typ)`
   wrapping every atom in `(metta …)` per step (13×), `:678` child-array splat. The continuation reducer
   allocates a Frame + wrapper Expression + child arrays **every step** → the ~5,722-alloc driver.

## Dispatch + type analysis (JET)

**`report_opt` (runtime dispatch) — the abstract-`Atom` class.** `metta_run` = 191 reports, `match_atoms` = 49,
`subst` = 1. Every one traces to `Atom` being an abstract sum type, so `==`, `_flat` iteration, and `_occurs`
predicates dispatch dynamically (`(%::Atom == %::Atom)::Any`, `(A::Vector)[i]::Any`). **Not correctness bugs —
the same *perf* signal as above** (dispatch concentrated at the `Atom` boundary, leaves clean).
`report_package(MeTTaCore)` = 109 "possible errors" = this same `Any`-boundary class (e.g. the PathMap
`set_val_at!` chain). **Do not re-chase** (matches the earlier "137 = all false positives" finding).

**`report_call` (type errors / may-throw) — 2 reports, both assessed:**
1. `interpret_stack` (`Interpreter.jl:172`) getproperty-on-`Nothing` (`f.prev.vars`) → **FALSE POSITIVE** —
   guarded 3 lines up by `f.prev === nothing && return [(f, b)]`; after the guard `f.prev` is a `Frame`.
2. `add_var_binding` (`Atoms.jl:124`) `prev == val` typed `Union{Missing, Bool}` used in a boolean `elseif`
   → **LATENT EDGE (not a live bug).** `Base.:(==)(a::Grounded, b::Grounded) = a.value == b.value` and
   `.value::Any`, so `Any == Any` *can* return `missing`; if a grounded atom ever wraps Julia `missing`, line
   124 throws "non-boolean Missing." Never fires for normal MeTTa values (Float64 / symbols / expressions) —
   a sharp edge in the "primitives untested at edges" class, recorded not rushed (forcing `Grounded ==` to a
   strict `Bool` would fix it but changes atom-equality semantics → conformance risk; only with measured need).

## Profile (flat, self-time — `concatT(20,20)` recursion, Profile.jl)

Top self-time frames (`Overhead` column = time *at* that frame, not callees):

| self | frame | what |
|-----:|-------|------|
| 62 | `Atoms.jl:74` **`Bindings`** | Bindings construction/copy — **#1 self-time** (confirms target 1) |
| 41 | `Interpreter.jl:556` `metta_instr` | core reduce-instruction dispatch |
| 32 | `Interpreter.jl:88` `subst` | recursive substitution (Expression alloc) |
| 31 | `Interpreter.jl:363` **`rename_fresh`** | variable-freshening per stored atom in match — **new hot spot** |
| 24 | `Interpreter.jl:174/554` `interpret_stack` / `metta_instr` | reduce driver |
| 15 | `Atoms.jl:169` `_flat`, `Interpreter.jl:644` `interpret_tuple_instr` | binding flatten / tuple eval |

The profile agrees with AllocCheck/BenchmarkTools (Bindings is #1) and adds **`rename_fresh`
(`Interpreter.jl:363`)** — the match-time freshening that allocates a renamed copy of each stored atom per
query. A third, contained target alongside the two below.

## Type-stability cross-check (Aqua.jl + `@inferred`)

- **`@inferred`** — `subst`, `match_atoms`, `merge_bindings`, `add_var_binding` all return concretely-inferred
  types (STABLE). The function *interfaces* are type-stable; the JET `report_opt` dispatch is *internal*
  (`Any == Any` on grounded values, abstract-`Atom` iteration) — consistent, not contradictory.
- **Aqua.jl (project-wide)** — `ambiguities`, `unbound_args`, `piracies`, `undefined_exports`, `stale_deps`
  **all PASS**. No method ambiguities, no type piracy (our `==`/`hash` are on our own atom types), no stale
  deps.

**Verdict across 6 tools (AllocCheck · JET opt+call · BenchmarkTools · Profile · `@code_warntype` · Aqua ·
`@inferred`):** Core is type-stable and clean. The only "instability" is the **deliberate abstract-`Atom` IR
dispatch** (design choice for the sum-typed atom representation — a *perf* signal, not a defect) plus the one
latent `Grounded ==` edge above. No actionable correctness defect; the perf targets below are the only
follow-ups, gated by the guardrail.

## Cross-engine representation comparison (how the references avoid these)

Source-verified against hyperon-experimental, CeTTa, PeTTa — to separate *real divergences* from
*design trade-offs*.

| engine | `Atom` representation | dispatch | symbols | grounded eq |
|--------|----------------------|----------|---------|-------------|
| **hyperon** (Rust) | `enum Atom { Symbol, Expression, Variable, Grounded(Box<dyn>) }` — closed 4-variant (`hyperon-atom/src/lib.rs:827`) | tag match; vtable only for grounded | `UniqueString` — **interned** | `eq_gnd → bool` **strict** (lib.rs:414) |
| **CeTTa** (C) | `struct Atom { AtomKind kind; union{ground,expr} }` — flat tagged union; `GroundedKind` closed enum (`atom.h`) | `switch(kind)` | `sym_id` int — **interned** | `atom_eq → bool` **strict** (atom.c:1603) |
| **PeTTa** (Prolog) | native WAM tagged terms | WAM tag dispatch | atom table — interned | unification — strict |
| **Core** (Julia) | `abstract type Atom` + `Grounded{T}` — **open + parametric** | **dynamic dispatch** | raw `String` name | (now) `=== true` strict |

All three references use **closed sum types** → tag-switch dispatch. Core's `abstract type Atom` is the lone
*open* hierarchy → the dynamic dispatch JET flags.

**Per-issue verdict:**
- ✅ **Grounded `==` strict bool — DONE** (`Atoms.jl:50`). Both hyperon (`eq_gnd`) and CeTTa (`atom_eq`) return
  strict bool; Core's `Any==Any` (→ `Missing`) was the divergence. Fixed with `=== true`; 234/234 conformance
  + Core=hyperon=CeTTa on cross-engine `metta_xcheck`.
- ☐ **Symbol interning** — both hyperon (`UniqueString`) and CeTTa (`sym_id`) compare symbols by id, not
  string; Core compares raw `String` (the `atom_types` `Vector{Char}` churn). Reference-validated, low-risk,
  medium effort. The recommended next contained win.
- ⚠️ **Abstract-`Atom` → closed `Union`** — references use closed sum types; matching them needs
  `const Atom = Union{Sym,Var,Expression,Grounded}` (union-split = tag switch), which requires making
  `Grounded{T}` non-parametric (type-erase like hyperon's `Box<dyn>`, or a closed grounded-kind union like
  CeTTa's `GroundedKind`). Core's parametric `Grounded{T}` deliberately buys grounded **type-stability** that
  hyperon sacrifices to a vtable — a genuine trade-off, deep refactor, guardrail territory.
- ➖ **Bindings COW — not a divergence.** hyperon's `Bindings { HashMap<Var,usize>, HoleyVec }`
  (`matcher.rs:141`) is the same slot-sharing design Core already mirrors, and hyperon copies it on branching
  too. True COW would *exceed* the references — a Julia-specific optimization, not reference-mandated.

## Optimization targets

| # | target | site | risk | win |
|---|--------|------|------|-----|
| 1 | `Bindings` copy-on-write | `Atoms.jl:74` | **high** (eval-core mutation semantics) | biggest alloc cut + #1 self-time |
| 2 | reduce-step Frame/wrapper pooling | `Interpreter.jl:105/544/678` | high (continuation machine) | the 5.7k-alloc driver |
| 3 | ✅ **DONE** `rename_fresh` structural sharing — ground subtrees shared, not rebuilt | `Interpreter.jl:363` | low (immutable, ground=no vars) | 0 allocs for ground atoms (was full tree rebuild); 234/234 conformance |
| 4 | ✅ **DONE** `atom_types` grounded-type parse-cache — parse the type string once, not per lookup | `Interpreter.jl:800` | low (byte-identical, immutable) | kills the `Vector{Char}` re-parse; 234/234 |

> **Correction (measured):** the `Vector{Char}` re-parse AllocCheck flagged was a *minor* `atom_types` cost.
> With it cached, `atom_types(EQ_OP)` is still ~4,079 allocs / 175 KB — **dominated by the space query**
> `query(space, (: atom $T))`, which scans + `rename_fresh`es every `(: …)` decl per lookup. Symbol
> interning would *not* have helped this (it's not symbol comparison). The real lever is **indexing type
> declarations by subject op** (O(1) lookup vs scan) — a deeper space-index change, deferred.

## ⚠️ Guardrail — do not optimize the eval core until measured need

The interpreter is **correct and faithful**; these are **performance-only** changes with **zero functional
benefit**. `Bindings` COW touches the hottest mutation path: an un-triggered copy on a *shared* `Bindings`
causes **aliasing corruption** (one match branch silently overwrites another's variable bindings → wrong
results). Trading a correct, hyperon-faithful interpreter for speed is only justified when a workload is
**actually gated** on interpreter throughput.

**If/when implemented**, gate on: full **234-conformance** + every domain suite + the 4-engine
`workflows/metta_xcheck.sh` (the references are the only ground truth for "COW preserved semantics"). Prefer
the low-risk `atom_types` interning first.
