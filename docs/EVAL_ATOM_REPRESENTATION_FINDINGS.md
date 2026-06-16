# Findings — eval-atom representation vs content-addressed storage

**Status: findings note, NOT a decision.** Records an investigation and explicitly
*declines* to commit to a target architecture, because the premise that would justify
one (the seam is a cost) is unmeasured. Written 2026-06-16.

## What was observed

- Core **stores** atoms content-addressed in MORK: atoms ↔ S-expression strings ↔
  byte-trie paths (`MeTTaCore.jl` header; `MORK.Space` is the atom store).
- Core **evaluates** on typed recursive Julia structs — `Sym / Var / Expression /
  Grounded` (`src/standard/Atoms.jl`). The structs are lifted from the trie for eval
  and lowered back as strings.
- There is therefore a **lift/lower seam** (trie path/string ↔ struct) at the eval
  boundary.
- The struct representation has exactly **one** concrete symptom: `hash`/`==`/`show`
  on an `Expression` recurse over structure (`Atoms.jl:49,53`), so a *deeply nested*
  atom overflows the native stack. **It does not fire on current workloads** — PLN
  atoms are flat; no profile shows the seam costing anything. The seam has **no
  measured cost** today.

## The discriminating question — is the struct-eval / handle-storage split deliberate or incidental?

**Answered: deliberate.**

- `MeTTaCore.jl` design principles state it outright: *"MeTTa atoms are S-expression
  strings ↔ MORK byte-paths **(no UUID atoms)**"* — a conscious rejection of the
  id/handle atom model at the eval layer — and lists it under *"per MeTTa spec +
  **CeTTa**/Mettatron/hyperon cross-check."* CeTTa's id-based model was **in view**.
- The establishing commits state the reason: *"typed Atom + Bindings + matcher —
  **faithful port of hyperon/CeTTa (no Any)**"* (`61f23f3`); *"minimal eval …
  **(faithful, idiomatic Julia)**"* (`165b763`). The recursive typed struct **is** the
  faithfulness + readability + no-`Any` mechanism.

⇒ "storage content-addressed, eval struct-based" is a **layered** design (scalable
substrate underneath, faithful/readable evaluator on top), made for two different
reasons. **The seam is a layer boundary, not debt.**

## Options considered and rejected

- **hash-consing-lite** (cache a content hash on the `Expression` struct): rejected as
  off-pattern. It caches identity on the ephemeral eval-half struct, adds a stale-cache
  sync invariant (`Expression.children` is mutable; hyperon exposes `children_mut`), and
  patches the *symptom* (the hash overflow) while the layer boundary stays. Band-aid.
- **eval-on-content-handles / id-based evaluator** (the CeTTa model): NOT a target.
  It would *reverse* the stated "no UUID atoms" principle, not "finish" anything. The
  mechanism is buildable — FactorVSA ships content-addressed identity over MORK
  (`FVSA_EMBED`, `DualIndex`, `HandleRef`), and CeTTa runs a full id-based evaluator —
  but *buildable ≠ warranted*. Core's authors knew it was buildable (they cite CeTTa)
  and chose structs for faithfulness/readability. **FactorVSA's `(VecRef h)` handles
  reference opaque heavy payloads (vectors/codebooks) that can't be strings; it keeps
  eval atoms as strings — so it is consistent with this layering, not a precedent
  against it.**

## The measured trigger that would reopen this

Only a workload that makes the seam *cost* something:
- memoization-by-content-id needed under co-working load (PLN/ECAN/MOSES re-evaluating
  shared subexpressions over one metagraph), **or**
- lift/parse/unparse showing up in a profile, **or**
- a real workload that produces deep atoms (the hash overflow actually fires).

At that point, adopting an id-based eval would be a **deliberate reversal of a stated
design principle** requiring its own justification and ADR — not a debt-paydown. Until
then: no change; the layered design stands.
