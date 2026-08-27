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

---

## 2026-08-18 — tool-driven sweep: Aqua · JET · AllocCheck · BenchmarkTools

Run from the global `v1.12` env (Aqua 0.8.16, JET 0.12.0, AllocCheck 0.2.6, BenchmarkTools 1.8.0)
against the probe daemon. **Two attempted optimisations were measured and REVERTED.** They are
recorded here precisely so nobody re-derives them — the failures are the useful part.

### Aqua — clean

`unbound_args` · `undefined_exports` · `stale_deps` · `deps_compat` · `project_extras` · `piracies`
all pass, and `detect_ambiguities(MeTTaCore; recursive=true)` finds **0 ambiguities, 0 pirated
methods**. For a package with many small typed methods over an abstract `Atom` hierarchy that is a
real result, not a formality.

### JET — 284 optimisation findings on the tabling hot path, one root cause

`report_opt` over the tabling entry points:

| function | findings |
|---|---|
| `_S_P!` | 108 |
| `_leader_pass` | 78 |
| `_wfs_complete!` | 45 |
| `_merge_partial` | 21 |
| `is_multivalued` | 6 |
| `_scc_root` · `_union_scc!` · `dyn_changed!` | 5 each |

Nearly all reduce to ONE cause: **`Atom` is abstract, so `==`/`hash` dispatch dynamically**, and that
propagates into every `Dict{Atom,…}`:

```
runtime dispatch detected: Base.hashindex(%86::Atom, %19::Int64)::Tuple{Int64, UInt8}
runtime dispatch detected: (%1::Atom == k::Atom)::Any
```

Tabling is Dict-heavy — `_COMPONENT`, `_PARTIAL`, `_ANSWER_TABLE`, `_IDG`, `_DYN_DEPS` — and
`_scc_root` touches `_COMPONENT` on every component query.

### Where the allocations actually are

| operation | ns | allocs | bytes |
|---|---|---|---|
| `hash(::Sym)` | 33 | **0** | 0 |
| `hash(::Var)` | 79 | **0** | 0 |
| `hash(::Expression)` flat (2 children) | 118 | **3** | 48 |
| `hash(::Expression)` nested (3, one deep) | 258 | **6** | 96 |
| `==(::Sym, ::Sym)` | 29 | **0** | 0 |
| `==(::Expression, ::Expression)` nested | 271 | **0** | 0 |
| `Dict{Atom,Int}` — 200 inserts | ~39 µs | 1000 | 19 200 |
| `Dict{Atom,Int}` — 200 lookups | ~38 µs | 800 | 12 800 |

**`hash(::Expression)` costs ~1.5 allocations per child** — a boxed `UInt64` per element, because the
children are `Vector{Atom}` and each element's `hash` is a dynamic dispatch. `==` is allocation-free,
so equality is NOT the problem; hashing is. That is 4 allocations per Dict lookup.

### 🛑 TWO FIXES TRIED, BOTH REVERTED — DO NOT REDO

1. **Annotating the return types** (`==(::Sym,::Sym)::Bool`, `hash(::Sym,::UInt)::UInt`, all 8
   methods). The annotations DID land — `Base.return_types(==, (Atom,Atom))` went from a widened
   result to `[Bool,Bool,Bool,Bool,Bool]` — and changed **nothing**: `_scc_root` still reported 5
   findings, Dict allocations were identical (1000/800). The dispatch is the *method lookup* on an
   abstract key type; knowing the return type does not remove it.
2. **Folding `hash(::Expression)`** into an explicit loop with a `::UInt`-asserted accumulator,
   instead of `hash(a.children, h)`. **Strictly worse**: 4 allocs flat (from 3), 10 nested (from 6),
   Dict inserts 1400 (from 1000). The `::UInt` assert on a dynamic call boxes, and the manual loop
   loses Base's optimised array-hash path.

**What would actually work is a memoised hash field on `Expression`** — computed once at
construction, so the per-child dispatch is paid once per term rather than once per Dict operation.
That is a change to a core struct, and this session measured what those cost (Revise strands a
`const` container typed on a changed struct in the old world age; Revise #1116). Not attempted.
Treat it as the next real lever, with `[[reference_core_interpreter_perf_findings]]`'s standing rule:
no eval-core change without a measured need. The need is now measured; the change still is not.

### `Any` sweep

`src/` had exactly ONE genuine `Any`: `LibPolicy.jl`'s `_POLICY_SPACES = Dict{Symbol,Any}()`, which
made `policy_space(::Symbol)` infer `Any` although `new_core_space()` returns a concrete `CoreSpace`.
Fixed; `policy_space` now infers `CoreSpace`. Remaining grep hits in `src/` are docstrings quoting
JET output. `test/` still has four (`test_frame_agnostic_ret.jl` ×3, `test_tripwires.jl` ×1) — at
least one looks deliberate (it stores a deliberately-hidden `Any` to prove the frame-agnostic return
path handles it), so they want reading, not a sweep.

---

## 2026-08-27 — `match` has no index at all; `query`'s index has a gate

⚠️ **THIS SECTION WAS WRONG ON FIRST WRITING AND IS CORRECTED IN PLACE.** The first draft attributed a
measured 8.9× to `_index_key` failing on a fact-query pattern. `match` never calls `_index_key`. The
measurement is real; the cause was not. Both are recorded below, because the wrong version is the one
a reader will independently re-derive.

### THE TWO QUERY PATHS ARE DIFFERENT CODE, AND ONLY ONE IS INDEXED

| primitive | entry | uses `index`/`wildcard`/`bucket_trie`? | records IDG dep? |
|---|---|---|---|
| `match` (MeTTa's query primitive) | `_match_pat` (`Eval.jl:2485`) | **NO — never** | **no** |
| `(=)` rule lookup / `(:)` type lookup | `query` (`Eval.jl:1016`) | yes, when the key is concrete | `dyn_read!(k)` |

```julia
function _match_pat(space::Space, pat::Atom, b0::Bindings)::Vector{Bindings}
    out = Bindings[]
    for atom in all_atoms(space), mb in match_atoms(subst(pat, b0), rename_fresh(atom))
        append!(out, merge_bindings(b0, mb))
    end
    out
end
```

**Unconditional full scan of `all_atoms`, for every pattern, ground or not.** No key, no bucket, no
trie, no early return — there is nothing to gate. `Eval.jl:805` already lists `_match_pat` among the
~9 sites that reach `.atoms` directly. `all_atoms(s) = s.store.atoms` is a bare field read.

⇒ **The three acceleration structures serve `(=)`/`(:)` lookup only. MeTTa's actual query primitive
is not accelerated by any of them.** That is the finding; "the trie is behind a gate" was the
first draft's framing and it is wrong for `match`.

### What the 8.9× actually measured

`:7702`, min-of-20, single process, `!(match &self (belief …) …)`:

| n | `(belief $k $s $c)` var arg 1 | `(belief k1 $s $c)` ground arg 1 |
|---|---|---|
| 200 | 16.84 µs/atom | 5.73 |
| 1000 | 12.98 | 3.21 |
| 4000 | **15.49** | **1.74** |

Both go through `_match_pat`, so **both are O(N) scans of the same atoms**. The gap is not
indexed-vs-unindexed — it is **early-reject vs full-bind per atom**: a ground argument lets
`match_atoms` reject a non-matching atom at position 2, while the variable form must bind, merge and
discard. The falling µs/atom in the right column is cheaper per-atom work, not fewer atoms.

⇒ **Do not cite 8.9× as an indexing result.** It is a per-atom constant-factor result on an
unindexed scan. The indexing opportunity for `match` is that it has *no* index — a different and
larger claim, unmeasured.

### `query`'s gate — real, but it is the SUBJECT that must be discriminable

All five `query` call sites build `(= subj $X)` or `(: subj $T)`:

    Tabling.jl:1038  Eval.jl:1092  Eval.jl:1585  Eval.jl:1767  Eval.jl:2120

so `children[1]` is always `=` or `:`, and `_index_key` turns on `_idx_head(subj)`. It returns
`nothing` — full scan + `dyn_read!(nothing)` — for exactly three subject kinds:

1. a `Var`
2. a **`Grounded`** (verified by execution: `_idx_head(Grounded(42)) → nothing`)
3. an `Expression` with a non-`Sym` head (compound head)

The comment at `:1023` calls this case *"(var head) … (rare)"*. The pattern's head is never a
variable — it is always `=` or `:`. The phrase is wrong and it propagated into CODEMAP row 241 and
into the `_DYN_ALL` docstring.

### §7.7 over-invalidation — measured, and one thing left OPEN

`dyn_read!` has exactly **two** call sites (`Eval.jl:1024`, `Tabling.jl:1294`). `_match_pat` is not
one of them, so a `match` records no dependency at all.

Measured with `CORE_TABLING_IDG=1`, two tables differing only in whether argument 1 is ground, then a
mutation with an unrelated head:

| table | body pattern | recorded in | after `!(add-atom &self (other x y))` |
|---|---|---|---|
| `rd_var` | `(fact $z $w)` | **`_DYN_ALL`** | **invalid = true** — discarded |
| `rd_gnd` | `(fact a $w)` | `_DYN_DEPS` only | invalid = false — kept |

Real over-invalidation: a table discarded by a mutation that cannot affect it.

🟢 **NO SOUNDNESS BUG.** Adding `(fact a 3)` invalidated the table and re-derivation returned
`[3, 1]`, identical to untabled ground truth. `_DYN_ALL` over-invalidates rather than under-
invalidating, exactly as it commits to.

🔴 **OPEN — do not guess this.** A second probe whose `rd_gnd` differed *only* in its result template
(`$w` instead of `True`) DID land in `_DYN_ALL`. Hypothesis: the grounded result issues `(= 1 $X)`,
whose subject is a `Grounded` ⇒ `nothing`. **The controlled test REFUTED it** — both `(= (g) 42)` and
`(= (g) foo)` left `_DYN_ALL` empty. So what routes `dyn_read!(nothing)` there is still unknown, and
**how much over-invalidation an indexing change would remove has no number.**

### ⚠️ SCOPE — THIS IS NOT AN INTERPRETER-ONLY FINDING

**The compiled lane runs on the same store.** `Emit.jl:283`: *"Compiled IL does NOT bypass SLG —
`compile_run` builds `Eval.Space()` (`CompileLane.jl:43,395,459`), so arrow-5 output inherits
tabling."* `Frontend.jl` agrees: `table!`/`auto_table!`/`untable_all!` are *"the single control
surface for **both lanes**."*

| lane | store | `_index_key` gate | SLG |
|---|---|---|---|
| interpreter | `Eval.Space()` | yes | yes |
| **compiled IL (arrow 5)** | **`Eval.Space()` — the same object** | **yes, identical** | yes, inherited |
| MM2 / MORK (arrow 6) | MORK trie | **its OWN gate — see below** | **no tabling** |

⇒ Everything below applies to **compiled output too**. Do not propose "just use the compiler" as a
fix; it lands on the identical gate.

🔴 **AND MORK IS NOT THE ESCAPE — ITS TRIE HAS THE SAME DEFECT, ALREADY MEASURED.** `190fe73`
(`bench(store): Phase 2 — MORK-trie matching vs interpreter Julia-Dict index`, benchmark/store_match_scaling.jl),
min-of-7, N ∈ {200, 2000, 20000}:

| | shape | scaling | @ N=20k |
|---|---|---|---|
| (A) interp `query` | Dict discriminant | **O(1)** | ~4 µs ← the live path |
| (D) `core_match` | **nested** `(= (f a) $b)` — OUR layout | **O(N)** | **181 ms** |
| (E) `core_match` | **flat** `(rule f a $b)` — Ben's layout | **O(1)** | ~8 µs |

> *"Our nested `(= (f a) body)` shape defeats the trie's prefix-narrowing (`_pattern_prefix_bytes`
> pins only flat top-level constants, so a nested head gives pinned=1 < 2 → full scan) and is O(N):
> 181 ms/lookup at N=20k vs 4 µs, ~46,000× slower. **Store rules head-first and the trie is O(1) at
> the interpreter's order.**"*

⇒ 🔴 **THE TWO ENGINES FAIL ON OPPOSITE SHAPES — so the two fixes are COMPLEMENTARY, not
alternatives.** Work the key derivation through by hand:

| query shape | interpreter `_index_key` | MORK prefix-pin |
|---|---|---|
| **rule lookup** `(= (f a) $b)` — NESTED | `(:(=), :f)` — concrete ⇒ **O(1), ~4 µs** | pins 1 < 2 ⇒ **O(N), 181 ms** |
| **non-discriminable subject** `(= <Var/Grounded/compound-head> $X)` | `_idx_head` ⇒ `nothing` ⇒ **O(N)** | n/a |
| **`match`** `(belief $k $s $c)` | ⚠️ **never reaches `query`** — `_match_pat` full-scans regardless | flat + ground head ⇒ fine |

The interpreter is *good* at the nested rule lookup MORK chokes on, Its own weak spots are a non-discriminable
**subject** in `(=)`/`(:)` lookup, and `match`, which is unindexed outright. Neither fix subsumes the other:

* **head-first layout** (MORK's recorded fix, re-deriving OmegaClaw MORK_DATA_MODEL.md §4 "most
  selective stable field first") addresses the NESTED rule lookup. It does **nothing** for `match`,
  which consults no index at all.
* **`pl-index.c` adaptive indexing** addresses a non-discriminable SUBJECT in `query`, by
  selecting a different argument to index on. It does nothing for MORK's prefix pinning, and
  nothing for `match` until `match` consults an index at all.

⇒ Pick by which query shape actually dominates your workload, and do not let one be argued as
covering the other. `190fe73`'s 46,000× is the rule-lookup shape in the other
engine; the 8.9× above is neither — it is a constant factor inside an unindexed `match` scan.

**Not "we lack a discrimination trie".** We have three acceleration structures (`Eval.jl:662` —
"THE STORE IS NOT JUST `atoms`"): `index` (2-symbol Dict), `wildcard` (scanned every query), and
`bucket_trie` — a lazy per-bucket discrimination trie, promoted at `_TRIE_MIN_BUCKET = 16`. The trie
exists and is correct.

### ⚠️ The trie's KEYS ARE MORK'S `Expr` ENCODING — not CeTTa's, not bespoke

The comment at `:902` cites CeTTa for the **promotion threshold** (16) and for the per-bucket
substitution-tree *idea*. That is not where the KEY comes from, and conflating the two misdirects the
fix. `_Tok` (`:903-916`) + `_flat_tokens!` (`:925`) are MORK's tag encoding:

| MORK (`MORK/src/expr/ExprAlg.jl`) | ours (`Eval.jl`) | |
|---|---|---|
| `ExprArity` | `_KEXPR(arity)` | both **arity-prefixed, pre-order** |
| `ExprSymbol` | `_KSYM(hash(name))` | |
| `ExprNewVar` + `ExprVarRef` | `_KVAR` | **collapsed** — De Bruijn back-reference dropped |
| — | `_KGND(hash(value))` | ours only; upstream MORK has zero grounding |

Collapsing `NewVar`/`VarRef` is exactly why the trie cannot enforce cross-position variable
consistency and must return a superset — that is a consequence of the key choice, not an oversight.

It is **unreachable whenever `_index_key` yields `nothing`** — and it is not on `match`'s path at all.
`Eval.jl:1023`:

```julia
k = _index_key(pattern)
if k === nothing      # comment: "non-discriminable pattern (var head) → full scan (rare)"
    for stored in all_atoms(space) ... end
    return out        # ← early return: index bucket AND bucket_trie both skipped
end
```

`_index_key` (:759) needs a **concrete pair** `(outer-head, 2nd-child-head)`. It returns `nothing`
in three cases; the comment names one of them and calls it rare. The third is `children[2]`'s head
not being concrete — i.e. `(belief $k $s $c)`: **head `belief` fully concrete, variable in argument
1**. Not a var head, and not rare — but this governs `(=)`/`(:)` lookup, NOT `match`.

⚠️ **The comment misdescribes its own condition**, and the phrase "var head" propagated from it into
CODEMAP row 241 and from there into a session's analysis twice before the source was opened.

### The implied fix

**The store uses TWO different key derivations, and the coarse one is the anomaly:**

| | key | behaviour when a position is non-concrete |
|---|---|---|
| `bucket_trie` | `_flat_tokens` — a **prefix-structured MORK token stream** | degrades: wildcard that position, keep walking |
| `index` | `_idx_head` → `Tuple{Symbol,Symbol}` — a **conjunctive pair** | fails atomically ⇒ `nothing` ⇒ full scan |

⇒ **Do NOT add a head-only fallback key** — that reinvents a prefix as a special case.

📜 **HISTORY, CHECKED 2026-08-27 — `pl-index.c` was NEVER adopted, and nothing index-related was
ever removed.** Across Core/MORK/PathMap: zero commits mention `pl-index`; `MAX_MULTI_INDEX`,
`MAXINDEXDEPTH`, `jiti`, `find_multi_argument_hash`, `hashDefinition` have never existed in any tree;
`--diff-filter=D` finds no deleted index file. `_index_key`/`_idx_head` appear only in `b980b69`
(2026-06-17, *"first-argument index for Space.query (the Control half)"*) and `53b6fcb`;
`bucket_trie`/`_TRIE_MIN_BUCKET` only in `2435f42` (2026-07-01, *"per-bucket discrimination trie …
CeTTa borrows"*) and `d9f6116`.

🔴 **AND THE INDEX IS OURS, NOT A PROLOG PORT — do not let the NAME imply provenance.** `b980b69`
names its models: *"hyperon's real GroundingSpace, CeTTa, and the legacy CoreSpace ALL index (**trie
/ eq_idx / rule_cache**)"*. It cites SWI-Prolog **nowhere**. The only Prolog trace in the index code
is `:691`'s *"the 'Control' half of Algorithm=Logic+Control"* — Kowalski's slogan, a framing, not a
source. Every SWI reference in `Eval.jl` is in the TABLING block (`:1272` — *"tabling/ mirrors
swipl-devel's own section boundaries (boot/tabling.pl + src/pl-tabling.c)"*).

| | provenance | oracle |
|---|---|---|
| tabling | genuine port, mirrors swipl's own file boundaries | swipl differential, 18 files / 165 tests, green |
| **indexing** | **ours**, modelled on hyperon/CeTTa/CoreSpace | **NONE** |

⚠️ **CONSEQUENCE: the SWI differential does NOT cover the index.** It is an addition above upstream,
so a `pl-index.c` adoption — or any `_index_key` change — **cannot be validated by the existing
oracle and needs its own** (cf. the standing rule that additions above upstream need their own
oracle). Budget that; it is not free.

⇒ We never adopted ANY level of Prolog indexing. This is not a do-not-redo.

🎯 **THE ADOPTION TARGET IS `pl-index.c`, FROM THE TREE WE ALREADY TOOK SLG FROM.** We ported
SWI-Prolog's `pl-tabling.c` and left its clause indexing behind. SWI does **JIT argument-selection
indexing**:

    #define MAX_MULTI_INDEX  4    /* hash up to 4 arguments TOGETHER */
    #define MAXINDEXDEPTH    7    /* index NESTED positions, 7 deep */

plus `find_multi_argument_hash`, `hashDefinition`, `jiti_tried`, `MSG_JIT_DELINDEX` — indexes built
**on demand** from observed call patterns and **deleted** when they stop paying. When an argument is
uninstantiated (`:587`, `:1796` — exactly our `(belief $k $s $c)`) it **selects a different
argument** rather than giving up. Ours is fixed `(head, arg1-head)`, one argument, one level, no JIT,
and **fails atomically**. We already run a green differential oracle against this codebase (18 files
/ 165 tests, `workflows/swipl_tabling_oracle.sh`).

⚠️ **ONLY HALF OF SWI'S PAYOFF TRANSFERS — scope it before building.** In a WAM, indexing buys (a)
fewer candidate clauses to unify, and (b) the `deterministic` VM register (`pl-wam.c:2449`, *"Last
clause has been found deterministically"*, set via `firstClause`/`nextClause`) so **no choice point
is created**. Our SLG is the ZAM-compatible one — delimited control, **zero choice points** — so (b)
has nothing to buy. **We would get the candidate narrowing; we do not get the determinism win.**
(Do not price it at the 8.9× above — that is a per-atom constant factor inside an unindexed
`match`, not a candidate-count result. The narrowing is UNMEASURED.) Whether an SLG analogue of (b) exists (knowing a call has a single answer source, so it need
not suspend) is OPEN and unmeasured.

📌 `pl-zip.c` is **NOT** a zipper — it is ZIP-archive support (`zip_open_archive`, `SopenZIP`,
minizip `zipFile`/`unzFile`, `HAVE_MMAP`) for saved states and `.qlf` resources. A false friend with
PathMap's trie cursor; checked 2026-08-27 so nobody re-checks.

Touches `_index_key`, `add_atom!`, `remove_atom!` and the `wildcard` invariant (atoms in `wildcard`
are checked on *every* query precisely because they can match any discriminant; prefix keying changes
which atoms need to live there, and that must be re-derived, not assumed).

This satisfies the guardrail above: the need is now **measured**. The change is not made.

### Cross-check: JeTTa (`~/dev-zone/jetta`, source-read)

`runtime/…/space/DiscriminationTrie.kt` (162 lines), wired at `SpaceImpl.kt:27`, 4 tests. **One
global trie**, incremental, walked per query — its own docstring: *"a single structural index
maintained incrementally over the whole space, walked per query — the inverse of building a
per-pattern index by scanning."* A query variable costs **one `skipOneSubterm`** and the walk
continues; wildcards work both directions (stored var = `varChild`, query var = skip one subterm).
So the pair-key failure mode cannot arise there — there is no pair.

🟢 **Independent convergence worth trusting:** both implementations retrieve a **superset** and keep
exact matching downstream (ours: "match_atoms stays authoritative"; theirs: "no false negatives",
exact check in `IndexerImpl.matchAndCapture`). Both cite Vampire/CeTTa lineage. Two codebases
arriving at the same contract separately is good evidence the contract is right.

🔴 **Retracted: the "0.27 → 0.007 µs/atom" JeTTa figure is unfounded.** It appears in CODEMAP row 241
and **nowhere in JeTTa's tree** (grepped `.kt`/`.md`/`.txt`). Do not quote it. The only defensible
number available is our internal 8.9× — which measures per-atom cost inside an
unindexed scan, not retrieval, so it is not comparable to a trie-probe figure either. **There is no
sound ours-vs-JeTTa number yet.**

📌 **Not done, and genuinely different:** JeTTa serializes indices **at compile time** —
`<Name>.indices/index-NNNN.jtsi`, packed indices for statically-known patterns, ~15–20× compressed,
shipped beside the `.class`. Their partial-evaluation bet applied to indexing. We rebuild at add-time
on every run, and our compile lane already knows the query patterns. Recorded as an observation; it
is a large change and nothing has been measured for it.


---

## 2026-08-27 (b) — global-env tool sweep, and a REFUTED closed-sum theory

Tools from `~/.julia/environments/v1.12` (JET · AllocCheck · BenchmarkTools · Aqua · Cthulhu ·
JuliaFormatter), run against `query` with a 400-rule bucket so the discrimination trie is active.

### Fixed: the last `Any` in `src/`

`bucket_trie::Dict{Tuple{Symbol,Symbol}, Any}` was the ONLY genuine `Any` in `Core/src` — every
other grep hit is prose (docstrings quoting JET output, or comments asserting "never `Vector{Any}`").
The stored value is always `(_TNode, IdDict{Atom,Int})`, concrete; it was `Any` purely because
`_TNode` was declared ~250 lines BELOW `VectorStore` and so was not nameable. The **type
declarations** (`_Tok`, `_TNode`, the `_K*` consts) are now hoisted above `AbstractStore`; the
functions stayed where they were. `_bucket_candidates`' `entry::Tuple{…}` assert is gone — the field
carries the type.

MEASURED: `_bucket_candidates` lowered statements mentioning `Any` **2 of 61 → 0 of 59**.
Allocations **unchanged at 513**, which is the honest signal: this is type precision, not speed.
⚠️ The wall-clock numbers (115 µs before, 32 µs after) are from **DIFFERENT PROCESSES** and are
therefore NOT a claim — same-process is the only comparison that counts here, and there isn't one.

### 🛑 REFUTED, DO NOT REDO: "make `Atom` a closed `Union` to kill the dynamic dispatch"

JET reports ~40 runtime dispatches under `query`, all on `Atom`-typed values —
`hashindex(::Atom,…)`, `(::Atom == ::Atom)`, `match_atoms(pattern, ::Atom)` ×4, `rename_fresh(::Atom)`.
The grammar (`docs/specs/metta grammar/metta_language_spec.md` §1.1) says

    ATOM ::= SYMBOL | VARIABLE | GROUNDED | EXPRESSION ;

a CLOSED four-case sum — and `Atoms.jl:23`'s own comment already calls it "a typed sum-type (Julia's
faithful equivalent of hyperon's `enum Atom`)" while implementing it as an OPEN `abstract type`. The
obvious inference is that a small `Union` would let the compiler union-split and dispatch statically.

**Tested in a faithful model (multi-method, both shapes, same process): IT DOES NOT.**

| | JET errors | min time |
|---|---|---|
| `abstract type` + 4 methods | 2 | 3020 ns |
| closed `Union` + same 4 methods | **2 — identical** | 2522 ns |

**1.2×, and the dispatches remain.** Union splitting is bounded (4 cases by default); `match_atoms`
takes TWO atom-typed arguments, so a split would need 4×4 = 16 combinations and is abandoned. A
first, simpler model (single method) showed NO dispatch at all in either shape — that model was wrong
because with one method there is nothing to dispatch on, and its result should not be cited.

⇒ The abstract/`Union` distinction is NOT the lever. This does not overturn the standing guardrail
above; it strengthens it. The documented lever remains a memoised hash field on `Expression`, still
not attempted. `Grounded{T}`'s parametricity is a further obstacle to any Union rewrite (a bare
`Grounded` arm is a `UnionAll`) and was not even reached before the theory failed on simpler grounds.

### Idiom survey (multiple dispatch / broadcasting / piping / comprehensions / display)

Already idiomatic: **comprehensions 137 uses**, `@view` 13, destructuring throughout, and **10
`Base.show` methods** (`Sym`/`Var`/`Expression`/`Grounded`/`Space`/`Delay`/`WFSBottom`/`Operation`/
`StateCell`) — which is why `println` debugging is readable at all.

Deliberately absent, and correctly so:
* **piping `|>` (0) / composition `∘` (1)** — every closure construction allocates in Julia
  (recorded at 8.4× from the leapfrog port; `::F` does not fix it). `query` already allocates 513×
  per call; routing it through pipes would add to that. Absence here is a choice, not a gap.
* **broadcasting (0)** — atoms are heterogeneous trees, not numeric arrays. Not applicable.
* **multiple dispatch** — `_idx_head`/`_tok`/`_flat_tokens!` use `isa`-chains where dispatch is the
  idiom. With an abstract `Atom` the call is dynamic either way, and a predictable `isa` branch may
  beat dynamic dispatch. Converting would be more idiomatic and possibly SLOWER; it needs a
  measurement first, and the Union experiment above suggests the payoff is small.
