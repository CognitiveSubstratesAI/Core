# Core Grounded Numeric Ops — the MeTTa↔Julia numeric adapter (spec)

**Status:** spec (gate before build). **Target:** `src/standard/CoreNumericOps.jl` — grounded ops on the
StandardMeTTa.Minimal engine.

> **NOT a numpy reimplementation.** Julia's `LinearAlgebra` / `Statistics` / broadcasting **are** the numerics
> (≥ numpy), free, stdlib-only. This layer is the thin grounded-op **ADAPTER** that marshals MeTTa atoms ↔
> Julia arrays and encodes upstream's conventions (ddof, rounding). The numeric line in each op is one token;
> the *adapter* (atom-unwrap → native-call → atom-rewrap, NaN→`ExecNoReduce`) is the layer. "NumPy"/`numpy`
> below names upstream's `helpers.py` usage — the conformance *source* — never a thing we build.

## 1. Purpose & architecture

hyperon-experimental = **standard MeTTa (logic) + Python/numpy (numeric backend)**, bridged by `py-call`.
Core's faithful analog = **Minimal + `stdlib.metta` (the 234/234 faithful core) + a Julia grounded numeric
backend**. Julia *is* Core's numpy (native arrays, broadcasting, `LinearAlgebra` — no FFI). Algorithm ports
call grounded numeric ops exactly as upstream calls `py-call` into numpy; the *symbolic* logic stays MeTTa.

This supersedes both (a) upstream's `py-call` (needs Python) and (b) the pure-MeTTa reimplementations in
`lib/metamo/helpers.metta` (the `cons-atom`-recursion that caused the bug-class + the 11-min→7.66s blowup).

**This file specs the numeric-ops adapter only** (the ops mirroring upstream's numpy usage). It is *not*
the universal migration unlock — see §6.

## 2. Scope boundary

- **IN (this spec):** numpy array/scalar math — the numeric subset of MetaMo's `core/helpers.py`.
- **OUT — stays MeTTa:** symbolic logic (appraisal/decision/governance/matching); structural list logic
  (`member` → `CoreExtensions.metta`, the MeTTa-rule analog).
- **OUT — separate future grounded tiers (named in §6, NOT built here):** RNG (`random.*`), time/IO/logging,
  selection (`getTopK`/`choice`), LLM+embeddings (`gpt_*`/`semantic_similarity`).

## 3. Conformance gate policy

Run upstream's `MetaMo/core/tests/helpers_test.metta` expected values against the Julia layer. **Per-op
policy** (a single global epsilon is wrong — see `std` vs `softmax`):

- **Replicate upstream's *convention*, then tight-match.** Where `helpers.py` rounds (`std`→2 digits,
  `vector_add`→8, `round_number/list`→d), the Julia op rounds the *same way*; then compare at ε=1e-9.
- **ddof=0 (population).** `np.var`/`np.std` default to population denominator (N). Julia `Statistics.var`/`std`
  default to **sample (N-1)** — MUST write `var(v; corrected=false)`, `std(v; corrected=false)`, or the gate
  fails definitionally (no epsilon saves it). Verified: `(variance (1.0 2.0))→0.25` (pop), not 0.5 (sample).
- **softmax/normalize/etc. (no upstream rounding):** ε=1e-10 (numpy-vs-Julia transcendental ulps are
  *information*, not bugs, at this scale).
- **Empty-input semantics are part of the spec** (e.g. `norm ()→0.0`, `sum ()→0.0`, `product ()→1.0`,
  `softmax ()→()`, `normalizeVector ()→()`).
- **Indexing is 0-based** (numpy) for index ops (`mean_at_indices`, `boost_at_indices`).

## 4. Op surface — Tier A (pure numpy; build first)

`v` = Vector{Float64}. MeTTa name ← `helpers.py` fn. ✓test = value in `helpers_test.metta`; ⊘ = NO test
(hand-derived expected REQUIRED before trusting).

| MeTTa op | Julia impl | convention | conformance |
|---|---|---|---|
| `listDifference a b` | `a .- b` (shape-check) | — | ✓ `(7 6 13)(4 5 6)→(3.0 1.0 7.0)`, `()()→()` |
| `norm v` | `LinearAlgebra.norm(v)`, `()→0.0` | L2 | ✓ `(3 4)→5.0`, `()→0.0` |
| `calculateNormDifference a b` | `sum(abs2, a .- b)` | **sum-of-sq, NOT sqrt** | ✓ `(1 2 3)(4 5 6)→27.0`, `()()→0.0` |
| `normalizeVector v` | `n=norm(v); n>0 ? v./n : v` | — | ✓ `(3 4)→(0.6 0.8)`, `()→()` |
| `sum v` | `Float64(sum(v))`, `()→0.0` | — | ✓ `(1 2 3 4)→10.0`, `()→0.0`, `(1)→1.0` |
| `product v` | `Float64(prod(v))`, `()→1.0` | — | ✓ `(1 2 3 4)→24.0`, `()→1.0` |
| `mean v` | `Statistics.mean(v)` | — | ✓ `(1 2 3 4)→2.5` |
| `variance v` | `var(v; corrected=false)` | **ddof=0** | ✓ `(1 2 3 4)→1.25`, `(1.0 2.0)→0.25`, `(2 2 2)→0.0` |
| `std v` | `round(std(v; corrected=false), digits=2)` | **ddof=0 + round-2** | ✓ `(1 2 3 4)→1.12` |
| `dotProduct a b` | `LinearAlgebra.dot(a,b)` (shape-check), `()()→0.0` | — | ✓ `(1 2 3)(4 5 6)→32.0`, `(1 0)(0 1)→0.0` |
| `softmax v` | `e=exp.(v.-maximum(v)); s=sum(e); s==0 ? () : e./s` | stable, no round | ✓ `(1 2 3)→(0.0900305… 0.2447284… 0.6652409…)` |
| `roundNum x d` | `round(x, digits=d)` | — | ✓ `(2.67777 2)→2.68`, `(0.0 2)→0.0` |
| `split v n` | `np.split`-equiv (n equal sections; errors if not divisible) | — | ✓ `(1 2 3 4) 2→((1 2)(3 4))`, `… 4→((1)(2)(3)(4))` |
| `vectorAdd a b` | `round.(a .+ b, digits=8)` | **round-8** | ⊘ derive: `(1 2)(0.5 0.5)→(1.5 2.5)` |
| `averageArrays a b` | `(a .+ b) ./ 2` | — | ⊘ derive: `(0 0)(1 1)→(0.5 0.5)` |
| `clipVector v lo hi` | `clamp.(v, lo, hi)` | — | ⊘ derive: `(0.2 1.5 -0.3) 0 1→(0.2 1.0 0.0)` |
| `scaleArray v s` | `v .* s` | — | ⊘ derive: `(0.5 1 2) 10→(5.0 10.0 20.0)` |
| `positivePart x` | `max(0.0, x)` | — | ⊘ derive: `-0.4→0.0` |
| `roundList v d` | `round.(v, digits=d)` | — | ⊘ derive |
| `absNumber x` | `abs(x)` | scalar (dup of CoreExt `abs`) | ⊘ |
| `expNumber x` | `exp(x)` | scalar (dup of CoreExt `exp`) | ⊘ |
| `sigmoidNumber x` | `1/(1+exp(-x))` | — | ⊘ derive: `0.0→0.5` |
| `meanAtIndices v idx` | `mean(v[i+1 for i in idx])` | **0-based idx**, `()→0.0` | ⊘ derive: `(0.2 0.4 0.6 0.8)(1 3)→0.6` |

## 5. Tier B (MetaMo composites) & Tier C (matrix) — DEFER / decide per-op

- **Tier B — numpy+MetaMo logic** (`weightedAverageArrays`, `blendArrays`, `boostAtIndices`,
  `projectGoalsToSafe`, `parallelMergeGoals/Modulators`, `probeVector`): some are numpy (`blendArrays`,
  `weightedAverageArrays` → Tier A-style); others encode MetaMo semantics (`boostAtIndices`,
  `projectGoalsToSafe`, `parallelMerge*`) → keep as MeTTa *or* MetaMo-specific grounded, NOT general numpy.
  Decide each by "is this numpy, or MetaMo logic?" Read each body in `helpers.py` before classifying.
- **Tier C — matrix** (`matrixIsSquare`, `matrixVectorDot`, `identityMatrix`): low priority (MetaMo is
  vector-centric). Build only if a port needs them.
- **NOT numpy** (`io_bridge.*`, `metta_bridge.*`): I/O + MeTTa bridges → other tiers / stay MeTTa.

## 6. Economics correction — numpy is MetaMo's unlock, NOT the universal one

Union of py-calls across the 4 packages → **they do not share a numeric surface**:
- **MetaMo** → genuinely numpy (~33 fns). This layer is *for* it.
- **metta-moses** → `random.{randint,random,seed}`, `operator.xor`, `round`, `str`, `float` → **seedable RNG +
  bit-ops + coercion**. numpy buys it ~nothing.
- **metta-attention** → `random.choice`, `time.{time,sleep}`, CSV logging, `getTopK` → **RNG + clock + IO +
  selection**.
- **conceptBlending** → `gpt_agents.gpt_*` (9 LLM calls), `semantic_similarity`, `importlib`/`getattr` →
  **LLM + embeddings + Python reflection** — NOT locally reimplementable; likely defer/last.

**Distinct future grounded tiers** (name now so the next package's blocker isn't a run-3 surprise):
1. **Stochastic** — *seedable, reproducible* RNG grounded into MeTTa. Real design Q: where does the seed
   live (state atom?), how does determinism interact with Minimal's eval order? (MOSES + attention.)
2. **Time/IO/logging** — effectful grounded ops; same "effects in a pure rewriter" question as `add-atom`.
3. **Selection** — `getTopK`/`choice` (structural+numeric).
4. **LLM + embeddings** — external-service integration (Anthropic SDK / embeddings in Julia); conceptBlending.

## 7. Build mechanics

- **The ops are THIN PASS-THROUGHS to native Julia, NOT reimplementations.** Julia *is* numpy here:
  `LinearAlgebra.norm/dot`, `Statistics.mean/std/var`, broadcasting (`.+`, `.*`, `clamp.`, `exp.`). Deps are
  **stdlib only** (`LinearAlgebra`, `Statistics`) — no numerics package, no numeric code. The numerics are free.
- **The LAYER is the marshalling shim, not the math.** Build ONE shared helper (the vector analog of
  `CoreExtensions.jl`'s `_ext_unop`/`_ext_binop`): unwrap `Vector{Atom}` of `Grounded(Number)` → `Vector{Float64}`,
  call native Julia, **re-wrap** the result (`Grounded(5.0)` / a `Grounded`-children Expression), with the
  not-a-number / wrong-shape fallthrough to `ExecNoReduce` (stay symbolic). That shim — written once, reused
  across all array ops — IS the work; `norm(v)` in the middle is trivial. There is no point in evaluation where
  a bare `Vector{Float64}` exists outside the op, so the boundary is irreducible (and it's what keeps
  "Minimal = faithful core + named extensions" a checkable invariant — see §7 gate).
- **File:** new `src/standard/CoreNumericOps.jl` (NOT crammed into `CoreExtensions.jl`'s scalar tier), `include`d
  in `Minimal.jl` after `CoreExtensions.jl`, registering into Minimal's **`TOKEN_REGISTRY`** (additive).
- **Registry reconciliation — DECISION (made, not defaulted):** Minimal-facing numeric grounded ops register
  into `TOKEN_REGISTRY`; that is the ONE numeric-grounded discipline going forward. FactorVSA's shim into the
  *legacy MORK* `GROUNDED_REGISTRY` is **TRANSITIONAL** — a temporary artifact of FactorVSA predating the
  Minimal migration; when FactorVSA itself migrates onto Minimal it gets a Minimal-facing registration. NOT
  two registries by design. CoreNumericOps establishes `TOKEN_REGISTRY` as the target *deliberately*, not by accident.
- **Interface:** op names match the ports' calls (`vectorAdd`/`norm`/…) so a port's
  `(= (vectorAdd …) (py-call …))` becomes the grounded op; symbolic code above is untouched.
- **Boundary gate (like 234/234 for the faithful core):** the array layer's gate = passing
  `helpers_test.metta` (per-op tolerance, §3). Run it with the layer loaded; that proves numpy-equivalence.
- **Argument marshalling:** MeTTa expression `(1 2 3)` ↔ `Vector{Float64}`; result `Vector` ↔ MeTTa
  expression. Non-numeric / wrong-shape args ⇒ `ExecNoReduce` (stay symbolic), mirroring CoreExtensions.

## 8. Worklist before build

1. Tier A ops with ✓test → implement + gate against the value.
2. Tier A ops with ⊘ (no test) → **derive the expected from the UPSTREAM Python convention** (read the
   `helpers.py` body + a throwaway numpy snippet), **NEVER from the Julia output** — a ⊘ op checked against a
   self-derived value proves nothing (circular). If it can't be derived independently of the implementation,
   mark the op **untrusted**, not green. Add the derived values to a Core `helpers_test`-equivalent.
3. **Rounding-point / composition check.** `helpers_test`'s leaf tests can't catch a *composition-order*
   rounding difference (a rounded op — `std`/`vectorAdd`/`roundNum` — feeding another numeric op downstream).
   Before calling rounding "done," confirm no rounded op feeds a downstream numeric op in the ports' call graph;
   if one does, the rounding point matters for composition, not just the leaf test.
4. Tier B → read each `helpers.py` body, classify numpy-vs-MetaMo-logic, route accordingly.
5. Do NOT build Tiers RNG/Time/Selection/LLM here — they're named §6 tiers for the other packages.
