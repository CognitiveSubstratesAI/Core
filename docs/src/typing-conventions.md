# MeTTa type declarations — when (and when not) to type

MeTTa is **gradually typed**: type declarations are *optional*. Undeclared atoms have type
`%Undefined%`, type-checking is opt-in (`get-type` / `type-cast` / `match-types`), and there is
**no automatic checking pass**. So adding `(: …)` declarations buys little static safety unless
you also *invoke* the checkers — it is mostly documentation and `get-type` recognition.

How heavily to type a file therefore depends entirely on **which tier the file is in**. Getting
this wrong in either direction is a common mistake (Core over-typed `lib/pln/pln_factor_graph.metta`
and reverted it — see the case study below).

## The tier rule

| Tier | Examples | Convention |
| --- | --- | --- |
| **stdlib / prelude / grounded-op / FFI-binding** | `src/standard/stdlib.metta`; hyperon `stdlib.metta`; CeTTa `stdlib.metta`/`mork.metta` | **Fully typed.** Every grounded/built-in op gets a `(: op (-> …))` signature — the signature *is* the doc + type-check surface for an op with no `(= …)` rule. |
| **domain-algorithm library** | `lib/pln/`, `lib/ecan/`, `lib/quantale/`, MOSES | **Light / bare.** Bare symbolic constructors; reuse built-in types; at most a few pure numeric-helper signatures. **No custom data types** unless the algorithm *is* about types. |

### Why — the evidence

Cross-checked against the official MeTTa spec, hyperon-experimental, and CeTTa (2026-06):

- **Official spec:** declarations are presented as optional infrastructure; the spec's own
  examples are mostly bare `(= …)` rewrites. Explicit `(: …)` appears *selectively* (e.g. `(: if
  (-> Bool Atom Atom $t))`, where the meta-type `Atom` on the branches is evaluation-control-
  load-bearing — not cosmetic).
- **hyperon-experimental:** the stdlib (`stdlib.metta`, 1421 lines) declares **2 custom types**
  (`ErrorType`, `SpaceType`); everything else is arrow signatures over built-ins. Real modules
  (`json.metta`, `skel.metta`) type their *functions* but add **0–1** custom types. Domain *logic*
  (`b4_nondeterm.metta`, the ML-integration sandboxes) ships **untyped, bare**.
- **CeTTa:** heavy typing lives only in `stdlib.metta` (prelude) and `mork.metta` (FFI handle
  layer). Real domain libs are nearly type-free — `lib_pln.metta` is **6 decls / 84 rules**
  (numeric helpers only); `clist.metta` defines `ClistNil`/`ClistCons` and pattern-matches them
  yet declares **zero** types.
- **Density norm:** domain-algorithm libraries sit at **~0–7 %** declaration density
  (decls : rules). hyperon/CeTTa stdlib and the dependent-type `chaining` repo are the only
  high-density bodies — and those are stdlib or *about* types.

## Guidance for a new domain-algorithm library (`lib/**`)

1. **Use bare symbolic constructors** — `(stv s c)`, `(dtv μ n)`, `(dpair a b)`. Do not mint
   `(: STV Type)` / `(: dtv (-> Number Number DTV))`. (Lowercase `stv` matches the upstream
   PLN-for-PeTTa representation.)
2. **Reuse built-in types** — `Number`, `Bool`, `Atom`, `Expression`, `Symbol`. Never wrap a
   built-in in a parallel custom type.
3. **Optionally** sign a few *pure numeric helpers* `(-> Number Number)` (CeTTa `lib_pln` style)
   — purely as arity/domain documentation. This is the upper bound for a domain lib.
4. **Declare a custom `(: MyType Type)` + typed constructors only when the algorithm is *about*
   types** — typed pattern dispatch, GADT/dependent proof-search, Peano depth bounds. Numeric
   propagation, attention spreading, program evolution are **not** — leave them bare.
5. Per-function signatures and exhaustive accessor types are **non-idiomatic** for this tier and
   give no checked safety (gradual typing, no auto-pass). Skip them.

## When typing IS load-bearing

Type **only** where it changes behaviour or is the algorithm's substance:

- **Evaluation control** — declaring a function argument as meta-type `Atom` (vs an evaluated
  type) stops MeTTa pre-evaluating it. This is the `if` case; it is semantic, not cosmetic.
- **Grounded / stdlib ops** — sign them in `stdlib.metta`. Core's comparison and math ops
  (`< > <= >= sqrt log max min exp abs pow clamp`) were `%Undefined%`, a faithfulness gap vs
  CeTTa/PeTTa; they are now typed (`Number → Bool` / `Number → Number`), which the conformance
  matrix confirms is safe and which backs any library signature that flows through them.
- **GADT / dependent dispatch** — declare the type hierarchy; the types drive the computation.

## Case study: `lib/pln/pln_factor_graph.metta`

The PLN factor-graph layer (numeric demand propagation — *not* about types) was given a full
typing pass: 16 custom data types + ~46 function/accessor signatures (~38 % density). The
cross-check above showed this applied the **stdlib tier's** convention to a **domain lib**, 5× the
~7 % sibling norm. It was reverted to bare constructors. The one part kept was the **`stdlib.metta`
op typing** — that genuinely belongs to the stdlib tier and closed a real gap. The lesson:
*match the file's tier; for a domain lib, bare is correct.*
