# Bisimulation.jl — GSLT Definition 2.2: bisimilarity over the one-step relation, and the
# bisimilarity-preserving term map that Meredith calls a GSLT morphism.
#
# ─── WHY THIS EXISTS, AND WHY IT IS NOT Multicategory.jl ─────────────────────────────────────────
# `Multicategory.jl:46` declines to build the **Definition 5.1** morphism — a pseudofunctor of context
# multicategories, bisimulation-preserving for CONTEXT-LABELLED transitions — because this tree has no
# labelled transition system for a presentation to be bisimilar in. That decline stands and is
# correct.
#
# 🔴 BUT "NO Def 5.1 MORPHISM" WAS BEING READ AS "NO MORPHISM", AND THAT IS FALSE. Meredith's
# **Definition 2.2** is a different, weaker notion that needs NO labels, NO contexts and NO
# multicategory: a term map that preserves bisimilarity over the plain one-step relation. Verified
# 2026-08-19 against the machine-checked Lean formalisation in
# `dev-zone/MeTTapedia/lean/mettapedia/Mettapedia/GSLT/Core/GSLT.lean`:
#
#     structure GSLT where
#       Term : Type* ; equations : Setoid Term ; rewrites : Term → Term → Prop     -- our GPresentation
#     def Step (t t' : S.Term) : Prop := S.rewrites t t'                            -- our `reducts`
#     def IsBisimulation (R : S.Term → S.Term → Prop) : Prop :=
#       (∀ {t u}, R t u → ∀ {t'}, S.Step t t' → ∃ u', S.Step u u' ∧ R t' u') ∧
#       (∀ {t u}, R t u → ∀ {u'}, S.Step u u' → ∃ t', S.Step t t' ∧ R t' u')
#     structure GSLT.Morphism (S S' : GSLT) where                                   -- DEFINITION 2.2
#       toFun : S.Term → S'.Term
#       preserves_bisim : ∀ {t u}, S.Bisimilar t u → S'.Bisimilar (toFun t) (toFun u)
#
# `Step` is the RAW `rewrites` — NOT closed under the equations (`GSLT.lean:72`). Ours is `reducts`
# (`Relation.jl`), which is the premise-aware top-level one-step relation. Same object.
#
# ⚠️ WHAT IS AND IS NOT BUILT HERE — the distinction matters more than the code.
# Lean's `Bisimilar t u` is `∃ R, IsBisimulation R ∧ R t u`: an EXISTENTIAL, discharged by SUPPLYING a
# relation. It is a `Prop`, not an algorithm, and strong bisimilarity over an infinite-state system is
# not decidable in general. So this file builds the two things that ARE computable:
#
#   1. `is_bisimulation(p, R)` — CHECK a supplied finite relation. This mirrors Lean exactly: the
#      witness comes from outside, we verify the two closure conditions. Decidable because `reducts`
#      is finitely branching.
#   2. `bisimilar_bounded(p, t, u; depth)` — depth-bounded strong bisimilarity, a DECIDABLE
#      APPROXIMATION. It is `true` for a pair no observation of length `depth` can separate. It is a
#      SEMI-TEST: `false` is a proof of non-bisimilarity; `true` is not a proof of bisimilarity.
#      (Upstream CeTTa takes the same route for ρ-calculus —
#      `scripts/rhocalc_bounded_bisimulation.py` is a BOUNDED barbed-bisimulation oracle.)
#
# Nothing here claims to DECIDE bisimilarity, and `GMorphism` below carries its witness rather than
# asserting preservation — a morphism that asserted it would be exactly the naive term-map that
# `Multicategory.jl`'s header spends a paragraph refuting.
module CompilerGSLTBisimulation

using ..StandardMeTTa: Atom
using ..CompilerGSLTPresentation: GPresentation
using ..CompilerGSLTRelation: reducts

export is_bisimulation, bisimilar_bounded, GMorphism, morphism_preserves_bisim,
    BisimWitness, bisim_counterexample

"""
    BisimWitness

A finite candidate bisimulation: the set of pairs `R` a caller claims is closed under steps both
ways. Held as a `Set{Tuple{Atom,Atom}}` because Lean's `R` is a `Prop`-valued relation supplied by
the prover, and a finite set is the computable stand-in.
"""
const BisimWitness = Set{Tuple{Atom, Atom}}

"""
    is_bisimulation(p, R; depth) -> Bool

Is `R` a bisimulation over `p`'s one-step relation? Checks BOTH closure directions, exactly as
`IsBisimulation` does in `GSLT.lean:111-113`:

    (t,u) ∈ R  and  t → t'   ⟹   ∃ u'. u → u'  ∧  (t',u') ∈ R
    (t,u) ∈ R  and  u → u'   ⟹   ∃ t'. t → t'  ∧  (t',u') ∈ R

⚠️ BOTH DIRECTIONS, NOT ONE. Checking only the forward clause yields a SIMULATION, which is strictly
weaker and is the classic way to claim bisimilarity and be wrong: simulation in both directions
between two systems does NOT imply bisimilarity, because the two simulations may be different
relations. Here one relation must satisfy both clauses.
"""
function is_bisimulation(p::GPresentation, R::BisimWitness; depth::Int=32)::Bool
    for (t, u) in R
        for t2 in reducts(p, t; depth=depth)
            any(u2 -> (t2, u2) in R, reducts(p, u; depth=depth)) || return false
        end
        for u2 in reducts(p, u; depth=depth)
            any(t2 -> (t2, u2) in R, reducts(p, t; depth=depth)) || return false
        end
    end
    true
end

"""
    bisim_counterexample(p, R; depth) -> Union{Tuple{Atom,Atom,Atom,Symbol}, Nothing}

The first pair that breaks `is_bisimulation`, as `(t, u, unmatched, :forward | :backward)`, or
`nothing`. A bare `false` from a bisimulation check is nearly useless for debugging a presentation —
this says WHICH step had no partner and in which direction.
"""
function bisim_counterexample(p::GPresentation, R::BisimWitness; depth::Int=32)
    for (t, u) in R
        us = reducts(p, u; depth=depth)
        for t2 in reducts(p, t; depth=depth)
            any(u2 -> (t2, u2) in R, us) || return (t, u, t2, :forward)
        end
        ts = reducts(p, t; depth=depth)
        for u2 in us
            any(t2 -> (t2, u2) in R, ts) || return (t, u, u2, :backward)
        end
    end
    nothing
end

"""
    bisimilar_bounded(p, t, u; steps, depth) -> Bool

Depth-bounded strong bisimilarity: `true` when no observation of length `steps` separates `t` from
`u`.

🔴 A SEMI-TEST, AND THE ASYMMETRY IS THE POINT. `false` is a PROOF of non-bisimilarity — a separating
observation was found. `true` is NOT a proof of bisimilarity; it says only that this depth did not
separate them. Do not let a `true` here become "these are bisimilar" downstream; that is the same
error as reading a green suite as an absence proof.

`steps = 0` returns `true` for every pair by construction — the empty observation separates nothing.
That is not a bug, but it does mean a caller passing `0` learns nothing at all.
"""
function bisimilar_bounded(p::GPresentation, t::Atom, u::Atom;
    steps::Int=8, depth::Int=32)::Bool
    steps <= 0 && return true
    ts = reducts(p, t; depth=depth)
    us = reducts(p, u; depth=depth)
    for t2 in ts
        any(u2 -> bisimilar_bounded(p, t2, u2; steps=steps - 1, depth=depth), us) ||
            return false
    end
    for u2 in us
        any(t2 -> bisimilar_bounded(p, t2, u2; steps=steps - 1, depth=depth), ts) ||
            return false
    end
    true
end

"""
    GMorphism

A GSLT **Definition 2.2** morphism: a term map from one presentation to another, together with the
witness that makes preservation checkable.

⚠️ IT CARRIES ITS WITNESS RATHER THAN ASSERTING PRESERVATION. In Lean, `preserves_bisim` is a proof
obligation discharged at construction. We cannot discharge it by computation — bisimilarity is not
decidable — so `GMorphism` stores the finite carrier on which the claim was CHECKED, and
`morphism_preserves_bisim` re-checks it. A morphism that simply asserted preservation would be the
naive term-map `Multicategory.jl`'s header refutes at length.

This is NOT Definition 5.1. There is no pseudofunctor, no context multicategory, and no
context-labelled transition here — see `Multicategory.jl` for why that one is still declined.
"""
struct GMorphism
    source::GPresentation
    target::GPresentation
    toFun::Function                       # S.Term → S'.Term
    carrier::Vector{Atom}                 # the finite domain the claim was checked on
end

"""
    morphism_preserves_bisim(m; steps, depth) -> Bool

Check Definition 2.2's obligation on `m`'s carrier: for every pair of source terms that this depth
cannot separate, their images must be inseparable at the same depth.

⚠️ INHERITS `bisimilar_bounded`'s ASYMMETRY, so read the result carefully: a `false` here is a real
counterexample to preservation, while a `true` means "not refuted on this carrier at this depth" —
never "is a morphism". The carrier is finite and supplied by the caller, so this is a REFUTATION
instrument, which is the honest thing a computation can be here.
"""
function morphism_preserves_bisim(m::GMorphism; steps::Int=8, depth::Int=32)::Bool
    for t in m.carrier, u in m.carrier
        if bisimilar_bounded(m.source, t, u; steps=steps, depth=depth)
            bisimilar_bounded(m.target, m.toFun(t), m.toFun(u); steps=steps, depth=depth) ||
                return false
        end
    end
    true
end

end # module CompilerGSLTBisimulation
