# Relation.jl — PREMISED rewrites actually fire. The conditional-rewrite step.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). NO Figure-2 arrow.
#
# 🔴 THIS IS AN ADDITION ABOVE UPSTREAM'S EXECUTABLE LAYER, AND IT IS MARKED AS ONE.
# Everything in `Reduce.jl` and `Context.jl` is a port of Lean that `lake build MeTTaIL` checks. This
# file is not. Upstream states the conditional-rewrite semantics as a PROP and stops:
#
#     Relation.lean:33   inductive Reduces (p : Presentation) : AST → AST → Prop
#     Relation.lean:41   inductive PremisesHold (p : Presentation) : List Hyp → … → Prop
#     Normal.lean:17     "completeness in the presence of premised (conditional) rules is part of the
#                         conditional-rewrite work"                                    ← i.e. UNDONE
#
# So `applyBaseRewrite` returns `none` for a premised rule and `oneStep` never fires one. What follows
# is the EXECUTABLE READING of that Prop — not new semantics. Each clause below cites the constructor
# it discharges, and the correspondence is the thing to check, not the code.
#
# ⚠️ AND BECAUSE IT IS AN ADDITION, IT NEEDS ITS OWN ORACLE — a port inherits upstream's proofs, an
# addition inherits nothing. The oracle is the interpreter differential in
# `test_mettail_presentation.jl`: `chain` is the case this file exists for, and `Eval.bare_eval` is
# what says whether it now agrees. Before this file, that differential asserted a DISAGREEMENT.
#
# ─── WHERE THE PROP IS NOT DIRECTLY EXECUTABLE, AND WHAT WAS DECIDED ─────────────────────────────
#   1. `Reduces` and `PremisesHold` are MUTUALLY recursive with no measure that decreases: a premise
#      is discharged by a reduction, which may itself have premises. As a Prop that is fine; as a
#      function it may not terminate. Bounded by an explicit `depth`, the same device `Eval.lean`
#      uses for its own non-terminating driver ("the fuel makes the driver structurally recursive
#      even when reduction may not terminate"). EXHAUSTION IS NOT SILENT — see `reducts_exhausted`.
#   2. A relation admits MANY reducts; a function must choose. It does not choose: `reducts` returns
#      all of them, as `baseReducts` already does, and only the traversal in `Context.jl` takes the
#      first. Collapsing to one here would bake the strategy into the semantics.
#   3. `PremisesHold` discharges a premise with `Reduces` — TOP-LEVEL one-step, not the context
#      closure. Kept exactly so: a premise `$A ~> $A2` asks whether the bound `$A` reduces at its
#      root, which is what makes a congruence rule the thing that walks into the subterm.
module CompilerGSLTRelation

using ..StandardMeTTa: Atom, Sym, Var, Expression
using ..CompilerGSLTPresentation:
    GPresentation, GRewriteDecl, GHyp,
    premises_of, conclusion_of
using ..CompilerGSLTReduce: Bnds, match_pat, inst
using ..CompilerGSLTContext: step_with, normalize_with

export reducts, premises_hold, apply_rewrite, cond_step, cond_normalize, reducts_exhausted

"""How deep premise discharge may nest before `reducts` gives up.

Not a tuning knob with a pretty default — a premise chain deeper than this is a rule system doing
something the two-rule presentations in this tree do not, and the right response is to raise it
deliberately at the call site, having seen `reducts_exhausted` come back true."""
const DEFAULT_DEPTH = 32

"""Set when the last `reducts`/`cond_step`/`cond_normalize` call hit the depth bound.

⚠️ A FLAG, BECAUSE THE ALTERNATIVE IS A LIE. Running out of depth and finding no rule that applies
both return an empty list, and the caller cannot tell them apart — which would make a truncated
search read as "this term is normal". `Eval.lean` has the same hazard and answers it with a separate
`IsNormal` check; `Context.jl` answers it by returning residual fuel. Here the search is recursive
and the budget is not a single counter, so it is reported out of band.

Not thread-safe, and deliberately not: this is a diagnostic for a single-threaded presentation run,
not a control signal. Anything that needs to BRANCH on exhaustion should raise the depth instead."""
const _EXHAUSTED = Ref(false)

"Whether the last reduction call hit the depth bound rather than running out of applicable rules."
reducts_exhausted()::Bool = _EXHAUSTED[]

"""
    premises_hold(p, hyps, bnds, depth) -> Vector{Bnds}

Every extension of `bnds` under which all of `hyps` hold (`PremisesHold`, Relation.lean:41).

Each premise `src ~> tgt` instantiates `src` under the CURRENT bindings, reduces it at the root, and
binds `tgt` to the reduct — then the rest are discharged under that extension. One binding set per
way the whole premise list can be satisfied; `[]` means the rule does not apply.

`PremisesHold.nil` is `bnds` unchanged; `PremisesHold.cons` is the loop body.
"""
function premises_hold(p::GPresentation, hyps::AbstractVector{GHyp}, bnds::Bnds,
    depth::Int)::Vector{Bnds}
    isempty(hyps) && return Bnds[bnds]                      # PremisesHold.nil
    h = hyps[1]
    src = inst(bnds, Var(String(h.src)))
    out = Bnds[]
    for b in _reducts_inner(p, src, depth - 1)              # Reduces p (inst bnds (.var h.src)) B
        ext = copy(bnds)
        ext[h.tgt] = b                    # (h.tgt.baseName, B) :: bnds
        append!(out, premises_hold(p, (@view hyps[2:end]), ext, depth))
    end
    out
end

"""
    apply_rewrite(p, rd, t, depth) -> Vector{Atom}

Every reduct of `t` by the single rewrite `rd`, premises discharged (`Reduces.step`,
Relation.lean:35). Empty when the conclusion's left side does not match or no premise assignment
survives.

Note the order, which is upstream's: match the CONCLUSION first, then discharge premises under those
bindings. Reversing it would discharge premises for a rule that was never going to apply.
"""
function apply_rewrite(
    p::GPresentation, rd::GRewriteDecl, t::Atom, depth::Int
)::Vector{Atom}
    lhs, rhs = conclusion_of(rd.rw)
    b = match_pat(lhs, t)
    b === nothing && return Atom[]
    hyps = premises_of(rd.rw)
    isempty(hyps) && return Atom[inst(b::Bnds, rhs)]        # the base case, same answer as Reduce.jl
    Atom[inst(b2, rhs) for b2 in premises_hold(p, hyps, b::Bnds, depth)]
end

function _reducts_inner(p::GPresentation, t::Atom, depth::Int)::Vector{Atom}
    if depth <= 0
        _EXHAUSTED[] = true
        return Atom[]
    end
    out = Atom[]
    for rd in p.rewrites
        append!(out, apply_rewrite(p, rd, t, depth))
    end
    out
end

"""
    reducts(p, t; depth) -> Vector{Atom}

Every top-level reduct of `t` under `p`, PREMISES INCLUDED — the executable reading of `Reduces`
(Relation.lean:33). The premise-aware counterpart of `Reduce.base_reducts`, and a superset of it:
where `base_reducts` skips a premised rule, this discharges it.

Clears the exhaustion flag on entry, so `reducts_exhausted()` describes THIS call.
"""
function reducts(p::GPresentation, t::Atom; depth::Int=DEFAULT_DEPTH)::Vector{Atom}
    depth > 0 || throw(ArgumentError("reducts: depth must be positive, got $depth"))
    _EXHAUSTED[] = false
    _reducts_inner(p, t, depth)
end

"""
    cond_step(p, t; depth) -> Union{Atom, Nothing}

One leftmost-outermost step with premised rules ENABLED: `Context.jl`'s traversal, `reducts` at the
root instead of `base_reducts`. The same traversal, so there is no second copy to drift from the
ported one.
"""
function cond_step(
    p::GPresentation, t::Atom; depth::Int=DEFAULT_DEPTH
)::Union{Atom, Nothing}
    _EXHAUSTED[] = false
    step_with(x -> _reducts_inner(p, x, depth), t)
end

"""
    cond_normalize(p, t; fuel, depth) -> Tuple{Atom, Int}

`Context.normalize` with premised rules enabled. Returns the term and the residual fuel, for the
reason given there: a normal form and an exhausted budget must not look alike.
"""
function cond_normalize(p::GPresentation, t::Atom; fuel::Int=1024,
    depth::Int=DEFAULT_DEPTH)::Tuple{Atom, Int}
    _EXHAUSTED[] = false
    normalize_with(x -> _reducts_inner(p, x, depth), t; fuel=fuel)
end

end # module CompilerGSLTRelation
