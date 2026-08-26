<!-- vim: ft=markdown -->
# experiments/ecosystem_tooling

Proofs-of-shape for the JuliaSymbolics-inspired tooling plan. Nothing here is on the
load-bearing path yet — each experiment must demonstrate its claim (and keep the 392-test
suite green) before any of it is promoted into `src/`/`stdlib/`.

**Design doc**: [docs/PRIMITIVE_SURFACE_AND_ECOSYSTEM_TOOLING_2026-06-10.md](../../docs/PRIMITIVE_SURFACE_AND_ECOSYSTEM_TOOLING_2026-06-10.md)
**References** (read, not vendored as core deps): `~/dev-zone/{TermInterface,Metatheory,SymbolicUtils,SymbolicIntegration,SymbolicSMT}.jl`

## The two adapter points (the whole plan in one line)
1. **L0** — implement the zero-dep `TermInterface` protocol for Core's atom → Metatheory works for free.
2. **L3** — one `atom ↔ Symbolics.Num` translator → Symbolics + SymbolicSMT + SymbolicIntegration at the edge.

## Experiments (status)

| # | Experiment | Claim to prove | Status |
|---|---|---|---|
| E1 | **L0 TermInterface scaffold** | implement `isexpr/head/children/operation/arguments/maketerm` for Core's atom; retrofit ~3 grounded ops; suite stays green; `startswith("(")` count drops; `TermInterface` adds 0 transitive deps | TODO |
| E2 | **SMT-verify the boolean-reduct** | translate `reduce-to` in/out to Symbolics boolean; `isprovable(orig ≡ reduced)` over the tree-test cases → an independent oracle for M6, stronger than example tests | TODO |
| E3 | **Rewriter combinators** | re-derive `Chain`/`Prewalk`/`Postwalk`/`Fixpoint` as native supercompiler strategies; show `reduce-to` = `Fixpoint(applyReduce)` and `removeAndNodesFromGuards` = a `Postwalk` (the reduct engine already hand-rolls these) | TODO |
| E4 | **Metatheory edge interop** | once E1 lands, run a Metatheory `@rule`/e-graph rewrite over Core atoms with no per-type adapter (protocol-only) | TODO |

## Why these, in this order
- **E1 first** — it's the hinge; everything else (E3 reuse, E4 interop) follows, and it's the
  measurable proof that "one canonical interface" beats ~40 ad-hoc parses.
- **E2 early + standalone** — highest immediate value: it hardens the M6 reduct engine I just
  finished with an independent SMT oracle, and validates the L3 edge-adopt pattern (Z3 stays at
  the edge, never a core dep). Does NOT require E1.
- **E3** — pays back into the existing reduct/MOSES code (stop hand-rolling traversal).
- **E4** — the interop payoff that L0 unlocks for free.

## Guardrails
- Reference packages are **read for shape**, re-derived natively / adopted at the edge — never
  added to Core's `Project.toml` except `TermInterface` (confirmed zero-dep), and even that only
  after E1 proves the de-duplication win.
- Heavy deps (Z3 via SymbolicSMT, Nemo via SymbolicIntegration) live behind per-kernel edge
  adapters, never in the interpreter core. Per [ATOM_TYPING_TRADEOFF.md](../../docs/ATOM_TYPING_TRADEOFF.md),
  the typed-`Atom` substrate that E1 prototypes is a deferred, deliberate refactor — E1 is the
  proof-of-shape, not the commitment.
