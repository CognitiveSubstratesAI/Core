# Reduce.jl — the presentation ENGINE: match, substitute, instantiate, apply a rewrite.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). NO Figure-2 arrow. It makes a presentation
# EXECUTABLE, which is what turns `presentations/mettail.metta` from data nobody can falsify into
# something a differential can test.
#
# ⚠️ NOT A THIRD EVALUATOR. This reduces PRESENTATIONS — theory data — not MeTTa programs. MeTTa
# programs are reduced by MORK and by `Eval.jl`, and `mettail_1_0_spec.md` §5 is emphatic that
# "MORK is an optimal reduction kernel. MeTTaIL doesn't do better than optimal." Nothing here
# competes with that.
#
# ─── PORT, FROM `LeaTTa/MeTTaIL/Semantics/Reduce.lean` (97 lines) ────────────────────────────────
# Machine-checked: `lake build MeTTaIL` at HEAD 3885010 completes 660 jobs with 0 errors / 0 warnings
# / 0 `sorry`. Function names are kept — `matchPat`, `subst1`, `inst`, `applyBaseRewrite`,
# `baseReducts` — so a future session can diff against the Lean by grepping the same identifiers.
#
# ⚠️ WHY THIS, AND NOT "R FOR MeTTa". The plan was to port MeTTa's reduction RULES. There are none to
# port: `Operational/Semantics.lean` defines MeTTa's semantics as `def reduceAtom / smallStep? /
# runFuel` over a `State` — an ABSTRACT MACHINE, the same shape as spec §5, with only `StepKind`
# inductive. So no rule-shaped R for MeTTa exists in the normative spec OR in the Lean formalization,
# and deriving one would be authoring semantics nobody has written — in the one artifact whose entire
# value is that it is not somebody's opinion. This file is the other half instead: not MeTTa's R, but
# the engine that CONSUMES any presentation's R.
#
# ─── TWO LIMITATIONS OF *THIS FILE*, BOTH NOW ANSWERED ABOVE IT ──────────────────────────────────
# They are still true OF THIS FILE, and the tests pin them — but neither is a limitation of the
# engine any more, so do not cite them as one:
#   1. BASE REWRITES ONLY. `applyBaseRewrite` returns nothing for a `RewCtx`; premised congruence
#      rules do not fire here. `presentations/mettail.metta`'s `ChainStep` is inert AT THIS LAYER.
#      → `Relation.jl` discharges premises. That is an ADDITION above upstream's executable layer
#        (Lean leaves conditional rewriting a Prop), not a port, and carries its own oracle.
#   2. TOP LEVEL ONLY. `baseReducts` matches at the root; there is no congruence closure into
#      subterms.
#      → `Context.jl` ports `Semantics/Context.lean` (`oneStep`, leftmost-outermost) plus
#        `Normal.lean` and `Eval.lean`. Machine-checked upstream.
# So `base_reducts` remains the ROOT-LEVEL, BASE-ONLY reducer by design: it is the thing those two
# layers are built out of, and widening it here would give them nothing to be.
#
# ─── BINDERS LIVE IN THE GRAMMAR, NOT THE TERM TREE ──────────────────────────────────────────────
# Upstream, verbatim: "The `Subst` node's own variable is not a binder in the term tree (binders live
# in the grammar, not the AST), so this is plain replacement." That is why `subst1` is capture-
# UNAWARE, and why reusing `StandardMeTTa.Atom` for terms is sound: binding structure is carried by
# `ItemBind`/`ItemAbs` in Σ, never by the terms.
module CompilerGSLTReduce

using ..StandardMeTTa: Atom, Sym, Var, Expression
using ..CompilerGSLTPresentation: GPresentation, GRewriteDecl, GRewriteBody, RewBase, RewCtx

export match_pat, subst1, inst, apply_base_rewrite, base_reducts

"""Bindings from a pattern-variable name to the term it matched.

Upstream threads an assoc list; a `Dict` is equivalent here because `matchPat` only ever inserts a
name it did not already find, so no shadowing can arise."""
const Bnds = Dict{Base.Symbol, Atom}

"`(Subst body repl v)` — the reserved head standing in for LeaTTa's `AST.subst` constructor."
const SUBST = :Subst

_is_subst(a::Atom)::Bool =
    a isa Expression && length((a::Expression).children) == 4 &&
    (a::Expression).children[1] isa Sym && ((a::Expression).children[1]::Sym).name === SUBST

_varname(a::Var)::Base.Symbol = Base.Symbol(a.name)

"""
    match_pat(pattern, term, bnds) -> Union{Bnds, Nothing}

First-order matching (`AST.matchPat`, Reduce.lean:28). A pattern variable matches any subterm AND
MUST MATCH CONSISTENTLY IF IT RECURS; constructors match structurally; anything else matches only
itself.

Every `Var` in a pattern is a pattern variable. Upstream distinguishes `.var (.base v)` from a
qualified path — the latter matching only itself — but we emit no qualified variables (a dotted path
is represented as a dotted NAME), so that case has no instances here.
"""
function match_pat(pattern::Atom, term::Atom, bnds::Bnds = Bnds())::Union{Bnds, Nothing}
    if pattern isa Var
        v = _varname(pattern::Var)
        if haskey(bnds, v)
            return bnds[v] == term ? bnds : nothing     # CONSISTENCY: a recurring var must agree
        end
        out = copy(bnds); out[v] = term
        return out
    end
    if _is_subst(pattern) && _is_subst(term)
        pc = (pattern::Expression).children; tc = (term::Expression).children
        pc[4] == tc[4] || return nothing                # the substituted variable must agree
        b1 = match_pat(pc[2], tc[2], bnds)
        b1 === nothing && return nothing
        return match_pat(pc[3], tc[3], b1)
    end
    if pattern isa Expression && term isa Expression
        pc = (pattern::Expression).children; tc = (term::Expression).children
        length(pc) == length(tc) || return nothing
        b = bnds
        for k in eachindex(pc)
            b = match_pat(pc[k], tc[k], b)
            b === nothing && return nothing
        end
        return b
    end
    pattern == term ? bnds : nothing
end

"""
    subst1(v, repl, term) -> Atom

Replace variable `v` with `repl` throughout `term` (`AST.subst1`, Reduce.lean:49).

CAPTURE-UNAWARE BY DESIGN, per upstream: binders live in the grammar, so there is nothing in a term
for a substitution to capture. The `Subst` case recurses into body and replacement but leaves the
substituted variable itself alone — it is not a binder.
"""
function subst1(v::Base.Symbol, repl::Atom, term::Atom)::Atom
    if term isa Var
        return _varname(term::Var) === v ? repl : term
    elseif _is_subst(term)
        c = (term::Expression).children
        return Expression(Atom[c[1], subst1(v, repl, c[2]), subst1(v, repl, c[3]), c[4]])
    elseif term isa Expression
        return Expression(Atom[subst1(v, repl, x) for x in (term::Expression).children])
    end
    term
end

"""
    inst(bnds, term) -> Atom

Instantiate `term` with `bnds`, RESOLVING any `Subst` node (`AST.inst`, Reduce.lean:63).

The `Subst body repl w` case follows upstream exactly: if `w` is bound to a term VARIABLE, the
substitution targets that variable's name (the bound one); otherwise it targets `w` directly. Then
the instantiated replacement is substituted into the instantiated body — which is where
`(Subst P (NQuote Q) y)` in `Rholang.module`'s COMM rule actually does its work.
"""
function inst(bnds::Bnds, term::Atom)::Atom
    if term isa Var
        v = _varname(term::Var)
        return haskey(bnds, v) ? bnds[v] : term
    elseif _is_subst(term)
        c = (term::Expression).children
        w = c[4]
        target = w
        if w isa Var
            bound = get(bnds, _varname(w::Var), nothing)
            bound isa Var && (target = bound)           # target the BOUND variable, as upstream
        end
        tname = target isa Var ? _varname(target::Var) :
                target isa Sym ? (target::Sym).name : Base.Symbol(string(target))
        return subst1(tname, inst(bnds, c[3]), inst(bnds, c[2]))
    elseif term isa Expression
        return Expression(Atom[inst(bnds, x) for x in (term::Expression).children])
    end
    term
end

"""
    apply_base_rewrite(rd, t) -> Union{Atom, Nothing}

Apply a PREMISE-FREE rewrite at the top level: match its left side, instantiate its right
(`applyBaseRewrite`, Reduce.lean:87).

Returns `nothing` for a premised rule — upstream's behaviour, not a shortcut taken here. A congruence
rule needs its premise discharged, which this engine does not do.
"""
function apply_base_rewrite(rd::GRewriteDecl, t::Atom)::Union{Atom, Nothing}
    rw = rd.rw
    rw isa RewBase || return nothing                    # RewCtx ⇒ premised ⇒ not applicable here
    b = match_pat((rw::RewBase).lhs, t)
    b === nothing ? nothing : inst(b, (rw::RewBase).rhs)
end

"""
    base_reducts(p, t) -> Vector{Atom}

Every result of applying a premise-free rewrite of `p` whose left side matches `t` AT THE TOP LEVEL
(`baseReducts`, Reduce.lean:94). Order follows the presentation's rewrite order.

No congruence closure: a redex inside a subterm is not found. That is upstream's scope for this
function — `Context.one_step` is the ported closure above it, and `Relation.reducts` the
premise-aware root reducer. Call one of those unless you specifically want root-level base rewrites.
"""
function base_reducts(p::GPresentation, t::Atom)::Vector{Atom}
    out = Atom[]
    for rd in p.rewrites
        r = apply_base_rewrite(rd, t)
        r === nothing || push!(out, r)
    end
    out
end

end # module CompilerGSLTReduce
