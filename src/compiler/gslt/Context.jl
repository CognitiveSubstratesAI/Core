# Context.jl — reduction CLOSED UNDER CONTEXT, plus the fuel-bounded normalizer over it.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). NO Figure-2 arrow. `Reduce.jl` could only
# fire a rewrite whose left side matched the WHOLE term; this is what lets a redex be found one level
# down, which is the difference between a rule system and a table lookup.
#
# ⚠️ STILL NOT A THIRD EVALUATOR. Same scope as `Reduce.jl`: this reduces PRESENTATIONS — theory data
# — never MeTTa programs. `mettail_1_0_spec.md` §5 is the boundary: "MORK is an optimal reduction
# kernel. MeTTaIL doesn't do better than optimal."
#
# ─── PORT, FROM THREE MACHINE-CHECKED LeaTTa FILES ───────────────────────────────────────────────
#   `MeTTaIL/Semantics/Context.lean`  → `one_step`, `one_step_list`   (leftmost-outermost traversal)
#   `MeTTaIL/Semantics/Normal.lean`   → `has_redex`, `has_redex_list`
#   `MeTTaIL/Semantics/Eval.lean`     → `normalize` (`eval`), `is_normal` (`IsNormal`)
# `lake build MeTTaIL` at HEAD 3885010: 660 jobs, 0 errors / 0 warnings / 0 `sorry`. Lean names are
# kept in the docstrings so a future session can diff by grepping the same identifiers.
#
# WHAT UPSTREAM PROVES, AND WHY IT IS WORTH HAVING RATHER THAN HAND-ROLLING THE SAME TRAVERSAL:
#   `oneStep_sound`                  every executable step IS a genuine `RewStep`
#   `oneStep_isSome_eq_hasRedex`     it steps EXACTLY when a redex exists — sound AND complete
#   `isNormal_iff_hasRedex_false`    "normal" means no base rewrite applies ANYWHERE, not "we stopped"
#   `eval_sound`                     every run is a real reduction sequence, not a fixpoint by luck
# The third is the one that matters in practice: without it, "reached a normal form" and "the strategy
# could not find the redex" are the same observation.
#
# ─── THE STRATEGY IS LEFTMOST-OUTERMOST, AND THAT IS A LIMITATION UPSTREAM STATES ────────────────
# Verbatim, `Context.lean`: "leftmost-outermost is sound always, and by O'Donnell's theorem it is
# normalizing for left-normal orthogonal systems such as combinatory logic; finding a normal form for
# a general system needs parallel-outermost, which is future work." So a `normalize` that stops is
# telling you this strategy found no redex — for an orthogonal system that means normal, and for a
# general one it does not. Do not read `is_normal` as "irreducible" outside that fragment.
#
# ─── PREMISED RULES ARE STILL NOT FIRED HERE, AND THAT IS ALSO UPSTREAM'S SCOPE ──────────────────
# `oneStep` calls `baseReducts`, so a congruence rule with a premise never applies — `Normal.lean`'s
# own header calls completeness under premised rules "part of the conditional-rewrite work". Firing
# them is `Relation.jl`, which is an ADDITION above upstream's executable layer and is marked as one.
# That is why the traversal below takes its root reducer as an ARGUMENT: `one_step` passes
# `base_reducts` and is the faithful port; `Relation.jl` passes a premise-discharging reducer through
# the same traversal, so there is exactly one traversal and no second copy to drift.
module CompilerGSLTContext

using ..StandardMeTTa: Atom, Sym, Var, Expression
using ..CompilerGSLTPresentation: GPresentation
using ..CompilerGSLTReduce: base_reducts

export one_step, one_step_list, has_redex, has_redex_list, normalize, is_normal,
       step_with, normalize_with

"""`(Subst body repl v)` — the reserved head, as in `Reduce.jl`. Kept in step with that file: the
traversal must descend into a `Subst`'s BODY and REPLACEMENT but never into its variable."""
const SUBST = :Subst

_is_subst(a::Atom)::Bool =
    a isa Expression && length((a::Expression).children) == 4 &&
    (a::Expression).children[1] isa Sym && ((a::Expression).children[1]::Sym).name === SUBST

"""
    step_with(root, t) -> Union{Atom, Nothing}

One LEFTMOST-OUTERMOST rewrite step, or `nothing` if no redex is reachable (`oneStep`,
Context.lean:48). `root` is the top-level reducer: given a term it returns that term's reducts, most
preferred first.

Try `root` AT THE ROOT; if it yields nothing, descend left to right into the arguments, then into the
`Subst` components. Outermost-first is not an optimisation — it is the property `oneStep_sound` is
proved against, and reordering it would silently invalidate the citation.

⚠️ WHICH CHILDREN COUNT AS ARGUMENTS — a place our AST is RICHER than Lean's, so the port has to
decide rather than copy. Lean's `.sexp l args` keeps the label OUT of the argument list: `l` is a
`String`, so upstream can neither rewrite a head nor even WRITE a compound one. Our `children[1]` can
be anything. `_arg_range` resolves it: a `Sym`/`Grounded` head is a LABEL and is skipped, exactly as
upstream skips `l`; an EXPRESSION head is a subterm — `((f a) b)` is legal MeTTa — and is traversed,
because skipping it would make a redex inside it permanently unreachable. Dropping the second case
was the tempting reading of "faithful" and it would have been a silent gap, not fidelity.
"""
function step_with(root::F, t::Atom)::Union{Atom, Nothing} where {F}
    rs = root(t)
    isempty(rs) || return rs[1]
    if _is_subst(t)
        c = (t::Expression).children
        b2 = step_with(root, c[2])
        b2 === nothing || return Expression(Atom[c[1], b2, c[3], c[4]])
        r2 = step_with(root, c[3])
        r2 === nothing || return Expression(Atom[c[1], c[2], r2, c[4]])
        return nothing
    elseif t isa Expression
        ch = (t::Expression).children
        rng = _arg_range(ch)
        isempty(rng) && return nothing
        sub = step_with_list(root, @view ch[rng])
        sub === nothing && return nothing
        out = copy(ch)
        out[rng] = sub
        return Expression(out)
    end
    nothing
end

"""The child indices that are ARGUMENTS rather than the label — see `step_with`.

A head is skipped when it is a name (`Sym`, or a `Grounded` operator, which is how a presentation of
MeTTa reads back its own operator names). It is traversed when it is an `Expression`, a shape Lean's
`String` label cannot hold."""
_arg_range(ch::Vector{Atom})::UnitRange{Int} =
    isempty(ch)                ? (1:0) :
    (ch[1] isa Expression)     ? (1:length(ch)) :
                                 (2:length(ch))

"""
    step_with_list(root, args) -> Union{Vector{Atom}, Nothing}

One step inside the FIRST reducible element, or `nothing` if all are in normal form (`oneStepList`,
Context.lean:65). Exactly one element changes — the property `oneStepList_sound` states.
"""
function step_with_list(root::F, args)::Union{Vector{Atom}, Nothing} where {F}
    for k in eachindex(args)
        a2 = step_with(root, args[k])
        a2 === nothing && continue
        out = Atom[args...]
        out[k] = a2
        return out
    end
    nothing
end

"""
    one_step(p, t) -> Union{Atom, Nothing}

The faithful `oneStep` (Context.lean:48): leftmost-outermost, BASE REWRITES ONLY. A premised rule
never fires — see the header.
"""
one_step(p::GPresentation, t::Atom)::Union{Atom, Nothing} =
    step_with(x -> base_reducts(p, x), t)

"""
    one_step_list(p, args) -> Union{Vector{Atom}, Nothing}

The faithful `oneStepList` (Context.lean:65).
"""
one_step_list(p::GPresentation, args::AbstractVector{Atom})::Union{Vector{Atom}, Nothing} =
    step_with_list(x -> base_reducts(p, x), args)

"""
    has_redex(p, t) -> Bool

Whether a BASE rewrite applies anywhere in `t` — at the root, or in any argument or `Subst` component
(`hasRedex`, Normal.lean:26).

Upstream proves `oneStep_isSome_eq_hasRedex`: this is `true` exactly when `one_step` returns a step.
Kept as a separate function anyway, because the two are written differently and a divergence between
them is the cheapest possible signal that the traversal has drifted from the port — see the
`has_redex` agreement test.
"""
function has_redex(p::GPresentation, t::Atom)::Bool
    isempty(base_reducts(p, t)) || return true
    if _is_subst(t)
        c = (t::Expression).children
        return has_redex(p, c[2]) || has_redex(p, c[3])
    elseif t isa Expression
        ch = (t::Expression).children
        return has_redex_list(p, (@view ch[_arg_range(ch)]))
    end
    false
end

"`hasRedexList` (Normal.lean) — whether any element has a redex."
has_redex_list(p::GPresentation, args)::Bool = any(a -> has_redex(p, a), args)

"""
    normalize_with(root, t; fuel) -> Tuple{Atom, Int}

Apply `step_with` until no step applies or the fuel runs out (`eval`, Eval.lean:45), returning the
term AND THE FUEL LEFT.

⚠️ THE FUEL IS RETURNED, WHICH UPSTREAM DOES NOT DO, AND IT IS THE POINT. `eval` returns only the
term, so "stopped because normal" and "stopped because the budget ran out" are indistinguishable at
the call site — and the second silently looks like a normal form. Lean recovers the distinction with
`IsNormal`, a separate decidable check; returning the residual fuel gives it directly, and `fuel > 0`
⇒ the result is normal for this strategy.
"""
function normalize_with(root::F, t::Atom; fuel::Int = 1024)::Tuple{Atom, Int} where {F}
    fuel >= 0 || throw(ArgumentError("normalize_with: fuel must be non-negative, got $fuel"))
    cur = t
    while fuel > 0
        nxt = step_with(root, cur)
        nxt === nothing && return (cur, fuel)
        cur = nxt
        fuel -= 1
    end
    (cur, 0)
end

"""
    normalize(p, t; fuel) -> Tuple{Atom, Int}

`eval` (Eval.lean:45) over BASE rewrites. See `normalize_with` for why the fuel comes back.
"""
normalize(p::GPresentation, t::Atom; fuel::Int = 1024)::Tuple{Atom, Int} =
    normalize_with(x -> base_reducts(p, x), t; fuel = fuel)

"""
    is_normal(p, t) -> Bool

`IsNormal` (Eval.lean:53): no one-step reduction applies. By `isNormal_iff_hasRedex_false` this is
exactly `!has_redex(p, t)` — for BASE rewriting, and under this strategy.
"""
is_normal(p::GPresentation, t::Atom)::Bool = one_step(p, t) === nothing

end # module CompilerGSLTContext
