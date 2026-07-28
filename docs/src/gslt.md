# GSLT Theory Algebra

The GSLT theory front-end (`src/standard/GSLT.jl`) is the *real* MeTTa-IL bulk (per F1R3FLY/MeTTaIL's
`GSLT/.module` representation): MeTTa-IL theories are built **compositionally** from parts. Theories
flatten to a set of rewrites that feed the [MeTTa-IL Lane](mettail.md).

PRIMUS-native s-expr surface (the GSLT BNF term `Mult . Elem ::= "(" Elem "*" Elem ")"` becomes the
type-sig `(: Mult (-> Elem Elem Elem))` — the s-expr *is* the syntax):

```
(theory NAME ()|(extends P)|(union A B)
  (params (p P) …)
  (terms …) (equations …) (rewrites …) (replacements (=> Old New) …))
```

## The theory algebra

[`theory_flatten`](@ref) resolves the algebra into the complete terms/equations/rewrites:

- **Extension** — `(extends P)`: inherit `P`'s content, then add this theory's.
- **Union** — `(union A B …)`: merge all parents (e.g. a Rig = additive CommutativeMonoid ∪ multiplicative Monoid).
- **Replacement** — `(replacements (=> Old New))`: whole-token constructor rename across the inherited content (substring-guarded).
- **Parameterization** — `(params (p P))`: a theory generic over its parameter theories; `p` defaults to `P`
  and is overridable at instantiation via [`theory_instantiate`](@ref).

Validated against the canonical upstream `UnivAlg.module` hierarchy (EmptySet → Monoid → CommutativeMonoid
/ Group → Rig), reproducing its constructor and equation sets exactly.

## Running a theory

[`theory_run!`](@ref) flattens a theory's rewrites and runs them on native MORK (with `saturate=true` for
recursive closure). [`theory_rewrites`](@ref) returns the flattened rewrite set; [`parse_theory`](@ref) /
[`load_theories`](@ref) parse the surface.

## Equation orientation

[`theory_orient_equations`](@ref) orients equations into rewrites where provably terminating: the RHS must
have strictly fewer function symbols **and** no variable may occur more often in the RHS than in the LHS
(non-duplication). Both halves are load-bearing — the symbol count is a measure on the *rule*, and
substitution multiplies each variable's instance, so a duplicating rule such as `(= (f (h $x)) (g $x $x))`
grows the term (`|Lσ| = 2 + |t|` vs `|Rσ| = 1 + 2|t|`) even though the rule itself shrinks. Non-duplication
subsumes the older "no new variables" test. Unit/simplification laws orient; commutativity / associativity /
distributivity are **flagged** (they need AC-matching or an LPO/KBO reduction order — the deeper follow-on).
Oriented rewrites feed [`metta_il_normalize`](@ref).
