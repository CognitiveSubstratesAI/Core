# Parse.jl — s-expression surface → `GPresentation`. G = (Σ, E, R) as something you can WRITE.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). Implements NO Figure-2 arrow — it builds
# the INPUT that "MeTTa-IL is derived from a GSLT description" presupposes.
#
# ─── THE SURFACE MIRRORS THE PORTED MODEL ────────────────────────────────────────────────────────
# `Presentation.jl` is a port of LeaTTa's machine-checked `MeTTaIL/Syntax.lean`; this is its concrete
# syntax. Upstream writes presentations two ways, neither of which transliterates into MeTTa:
#
#   Scala .module   PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc ;
#   Rust macro      Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
#                   AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
#
# Both carry CONCRETE SYNTAX (`"new" … "in" …`) because they generate parsers for a target language.
# We drop it: in MeTTa the s-expr IS the syntax, so a concrete grammar would be a second source of
# truth. Everything else is kept — including a distinction the first draft of this file collapsed:
# `(bind x C)` DECLARES a binder, `(scope x C)` marks its SCOPE.
#
#     (language Rho
#       (types Proc Name)
#       (terms
#         (: PPar (-> Proc Proc Proc))
#         (: PNew (-> (bind x Name) (scope x Proc) Proc)))   ; (Bind x Name) … (x)Proc
#       (equations
#         (equation ScopeExtrusion (fresh x Q)
#           (PPar (PNew x P) Q) (PNew x (PPar P Q))))
#       (rewrites
#         (rewrite AppCongL ((~> M0 M1)) (~> (App M0 N) (App M1 N)))))
#
# Compound categories use the arity language the port restored: `(list C)`, `(arrow A B)`,
# `(prod A B …)`. A bare symbol is `CatId`, which is all the first draft could express.
#
# ─── MALFORMED PRESENTATIONS MUST BE REJECTED ────────────────────────────────────────────────────
# Upstream ships `GSLT/src/test/module/bad/` — `RepeatLabel.module`, `ReplacementShadows.module` — so
# it treats malformed presentations as a case worth testing. It matters more here than for an
# ordinary parser: a presentation is INPUT TO A GENERATOR, so silently accepting nonsense yields a
# type system for a language that does not exist. Every check below raises, naming the offender.
module CompilerGSLTParse

using ..StandardMeTTa: Atom, Sym, Var, Expression
using ..CompilerIR: GroundedType, GROUNDED_INT, GROUNDED_FLOAT, GROUNDED_BOOL,
                    GROUNDED_STRING, GROUNDED_OPAQUE
using ..CompilerGSLTPresentation: GCat, CatId, CatList, CatArrow, CatProd,
                                  GLabel, LabelId, GItem, ItemNonTerminal, ItemAbs, ItemBind,
                                  GRule, GHyp, GRewriteBody, RewBase, RewCtx, GRewriteDecl,
                                  GEquation, GFresh, GLiteral, GPresentation, cat_name

export parse_presentation

# ── typed accessors over the grammar's Atom ─────────────────────────────────────────────────────

_is_expr(a::Atom)::Bool = a isa Expression && !isempty((a::Expression).children)

function _head(a::Atom)::Union{Base.Symbol, Nothing}
    _is_expr(a) || return nothing
    h = (a::Expression).children[1]
    h isa Sym ? (h::Sym).name : nothing
end

_args(a::Expression)::Vector{Atom} = a.children[2:end]

function _section(body::Vector{Atom}, name::Base.Symbol)::Vector{Atom}
    for f in body
        _head(f) === name && return _args(f::Expression)
    end
    Atom[]
end

_symname(a::Atom, what::AbstractString)::Base.Symbol =
    a isa Sym ? (a::Sym).name :
    error("GSLT parse: expected a symbol for $what, got $(typeof(a))")

# ── Σ: the arity language ───────────────────────────────────────────────────────────────────────

"""A category: a bare sort, or one of the compound forms the arity language is closed under.

    Term          CatId
    (list C)      CatList    — `[Proc]`, `![Vec<Proc>] as List`
    (arrow A B)   CatArrow   — the exponential; a binder's sort IS one of these
    (prod A B …)  CatProd
"""
function _parse_cat(a::Atom)::GCat
    a isa Sym && return CatId((a::Sym).name)
    h = _head(a)
    xs = _is_expr(a) ? _args(a::Expression) : Atom[]
    if h === :list
        length(xs) == 1 || error("GSLT parse: (list C) takes exactly 1 category")
        return CatList(_parse_cat(xs[1]))
    elseif h === :arrow
        length(xs) == 2 || error("GSLT parse: (arrow A B) takes exactly 2 categories")
        return CatArrow(_parse_cat(xs[1]), _parse_cat(xs[2]))
    elseif h === :prod
        isempty(xs) && error("GSLT parse: (prod …) needs at least one category")
        return CatProd(GCat[_parse_cat(x) for x in xs])
    end
    error("GSLT parse: not a category: $(a)")
end

"""One argument position of a constructor.

`(bind x C)`  DECLARES a binder — upstream `(Bind x Name)` / `^x.body`.
`(scope x C)` marks its SCOPE  — upstream `(x)Proc`.
Anything else is a plain sort argument.

The bind/scope split is upstream's `bindNTerminal`/`absNTerminal` (`Syntax.lean:75-76`); collapsing
it — as the first draft did — cannot express which body a variable scopes over when a constructor
has more than one.

⚠️ SPELLED `scope`, NOT `abs`. MeTTa resolves `abs` to a GROUNDED operation, so it never arrives as a
`Sym` and could never match here — the same trap as `==` in the equation form. Both are guarded by
`test_gslt_parse.jl`'s keyword-collision test, which audits every keyword this parser reserves
against the live registry rather than discovering collisions one at a time."""
function _parse_item(a::Atom)::GItem
    h = _head(a)
    if h === :bind || h === :scope
        xs = _args(a::Expression)
        length(xs) == 2 || error("GSLT parse: ($(h) x C) takes a variable and a category")
        v = _symname(xs[1], "bound variable of `$(h)`")
        return h === :bind ? ItemBind(v, _parse_cat(xs[2])) :
                             ItemAbs(v, ItemNonTerminal(_parse_cat(xs[2])))
    end
    ItemNonTerminal(_parse_cat(a))
end

"`(: Label (-> arg… Result))` — the type-sig form `standard/GSLT.jl` already uses."
function _parse_rule(f::Atom)::GRule
    _head(f) === :(:) || error("GSLT parse: a term must be (: Label (-> …)), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (: Label Sig) takes exactly 2 parts")
    label = _symname(xs[1], "constructor label")
    sig = xs[2]
    _head(sig) === :(->) || error("GSLT parse: signature of `$label` must be (-> … Result)")
    parts = _args(sig::Expression)
    isempty(parts) && error("GSLT parse: signature of `$label` needs at least a result category")
    GRule(LabelId(label), _parse_cat(parts[end]),
          GItem[_parse_item(p) for p in parts[1:end - 1]])
end

# ── literals — the EXTENSION; carriers validated against the real enum ──────────────────────────

const _CARRIERS = Dict{Base.Symbol, GroundedType}(
    :GROUNDED_INT    => GROUNDED_INT,   :GROUNDED_FLOAT  => GROUNDED_FLOAT,
    :GROUNDED_BOOL   => GROUNDED_BOOL,  :GROUNDED_STRING => GROUNDED_STRING,
    :GROUNDED_OPAQUE => GROUNDED_OPAQUE)

"""`(literal Sort CARRIER)`. CARRIER must be a real `GroundedType` (`compiler/IR.jl:129`).

An unrecognised name is an ERROR, not an opaque fallback: falling back to `GROUNDED_OPAQUE` on a typo
would silently produce a sort the type system treats as unanalysable."""
function _parse_literal(f::Atom)::GLiteral
    _head(f) === :literal || error("GSLT parse: expected (literal Sort CARRIER), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (literal Sort CARRIER) takes exactly 2 names")
    s = _symname(xs[1], "literal sort")
    c = _symname(xs[2], "carrier of `$s`")
    haskey(_CARRIERS, c) ||
        error("GSLT parse: `$s` names unknown carrier `$c`; expected one of " *
              join(sort!(String[String(k) for k in keys(_CARRIERS)]), ", "))
    GLiteral(s, _CARRIERS[c])
end

# ── E ───────────────────────────────────────────────────────────────────────────────────────────

function _parse_fresh(f::Atom)::GFresh
    _head(f) === :fresh || error("GSLT parse: expected (fresh x Term), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (fresh x Term) takes exactly 2 names")
    GFresh(_symname(xs[1], "fresh variable"), _symname(xs[2], "fresh-in term"))
end

"""`(equation Label (fresh …)… LHS RHS)` — leading conditions, then the two sides.

NO INNER `==` MARKER: MeTTa resolves `==` to a GROUNDED operation, never a `Sym`, so it can never be
matched as a keyword here. Measured, after a first draft that used it and rejected every well-formed
equation."""
function _parse_equation(f::Atom)::GEquation
    _head(f) === :equation || error("GSLT parse: expected (equation Label … LHS RHS), got $(f)")
    xs = _args(f::Expression)
    length(xs) >= 3 || error("GSLT parse: (equation Label … LHS RHS) needs a label and two sides")
    label = _symname(xs[1], "equation label")
    i = 2
    conds = GFresh[]
    while i <= length(xs) - 2 && _head(xs[i]) === :fresh
        push!(conds, _parse_fresh(xs[i])); i += 1
    end
    i == length(xs) - 1 ||
        error("GSLT parse: equation `$label` has unexpected forms between conditions and sides")
    GEquation(xs[end - 1], xs[end], conds)
end

# ── R ───────────────────────────────────────────────────────────────────────────────────────────

"""A premise `(~> Src Tgt)` — VARIABLES only, per upstream's `Hyp{src tgt : DottedPath}`.

`Base.Symbol("~>")`, NOT `:(~>)`: `~>` is not a Julia operator, so `:(~>)` parses as the Expr
`:(~(>))` and the comparison against a Symbol is silently ALWAYS FALSE. Measured."""
function _parse_hyp(a::Atom, ctx::AbstractString)::GHyp
    _head(a) === Base.Symbol("~>") || error("GSLT parse: $ctx must be (~> Src Tgt), got $(a)")
    xs = _args(a::Expression)
    length(xs) == 2 || error("GSLT parse: (~> Src Tgt) takes exactly 2 variables in $ctx")
    GHyp(_symname(xs[1], "premise source"), _symname(xs[2], "premise target"))
end

function _parse_conclusion(a::Atom, ctx::AbstractString)::Tuple{Atom, Atom}
    _head(a) === Base.Symbol("~>") || error("GSLT parse: $ctx must be (~> Src Tgt), got $(a)")
    xs = _args(a::Expression)
    length(xs) == 2 || error("GSLT parse: (~> Src Tgt) takes exactly 2 terms in $ctx")
    (xs[1], xs[2])
end

"""`(rewrite Label (premise…) (~> Src Tgt))` — upstream `Label . | premises |- conclusion`.

An empty premise list is an axiom; a non-empty one is a congruence rule. Built as the nested
`RewCtx`/`RewBase` spine the port uses, matching `Syntax.lean:128`."""
function _parse_rewrite(f::Atom)::GRewriteDecl
    _head(f) === :rewrite || error("GSLT parse: expected (rewrite Label (…) (~> S T)), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 3 || error("GSLT parse: (rewrite Label (premises…) (~> S T)) takes 3 parts")
    label = _symname(xs[1], "rewrite label")
    prems = xs[2]
    prems isa Expression || error("GSLT parse: premises of `$label` must be a list; use () for none")
    lhs, rhs = _parse_conclusion(xs[3], "the conclusion of `$label`")
    body::GRewriteBody = RewBase(lhs, rhs)
    for p in reverse((prems::Expression).children)
        body = RewCtx(_parse_hyp(p, "a premise of `$label`"), body)
    end
    GRewriteDecl(label, body)
end

# ── the whole presentation, with validation ─────────────────────────────────────────────────────

"Atomic category names a rule mentions — result plus every item, through compounds and binders."
function _cats_of_rule(r::GRule)::Set{Base.Symbol}
    out = Set{Base.Symbol}()
    function walk(c::GCat)
        if c isa CatId;        push!(out, (c::CatId).name)
        elseif c isa CatList;  walk((c::CatList).elem)
        elseif c isa CatArrow; walk((c::CatArrow).dom); walk((c::CatArrow).cod)
        else;                  for x in (c::CatProd).cs; walk(x); end
        end
        nothing
    end
    function witem(i::GItem)
        if i isa ItemNonTerminal;  walk((i::ItemNonTerminal).cat)
        elseif i isa ItemBind;     walk((i::ItemBind).cat)
        elseif i isa ItemAbs;      witem((i::ItemAbs).item)
        end
        nothing
    end
    walk(r.cat)
    for i in r.items; witem(i); end
    out
end

"""
    parse_presentation(a::Atom) -> GPresentation

Parse `(language NAME (types …) (literals …) (terms …) (equations …) (rewrites …))`.

Raises on a malformed presentation rather than returning a partial one.
"""
function parse_presentation(a::Atom)::GPresentation
    _head(a) === :language || error("GSLT parse: expected (language NAME …), got $(a)")
    body = _args(a::Expression)
    isempty(body) && error("GSLT parse: (language …) needs a name")
    name = _symname(body[1], "language name")
    rest = body[2:end]

    exports = GCat[_parse_cat(s) for s in _section(rest, :types)]
    lits    = GLiteral[_parse_literal(f) for f in _section(rest, :literals)]
    terms   = GRule[_parse_rule(f) for f in _section(rest, :terms)]
    eqs     = GEquation[_parse_equation(f) for f in _section(rest, :equations)]
    rews    = GRewriteDecl[_parse_rewrite(f) for f in _section(rest, :rewrites)]

    # DUPLICATE LABELS — upstream tests this (`bad/RepeatLabel.module`). Two constructors sharing a
    # label make the signature ambiguous and every generated artifact inherits the ambiguity.
    seen = Set{Base.Symbol}()
    for r in terms
        l = (r.label::LabelId).name
        l in seen && error("GSLT parse: duplicate constructor label `$l`")
        push!(seen, l)
    end
    rseen = Set{Base.Symbol}()
    for r in rews
        r.name in rseen && error("GSLT parse: duplicate rewrite label `$(r.name)`")
        push!(rseen, r.name)
    end

    # UNDECLARED CATEGORIES — walks compounds and binders, so a sort hidden inside `(list …)` or
    # `(bind …)` cannot slip through as a phantom sort in a generated type system.
    declared = Set{Base.Symbol}()
    for c in exports
        n = cat_name(c)
        n === nothing || push!(declared, n)
    end
    for r in terms
        lbl = (r.label::LabelId).name
        for s in _cats_of_rule(r)
            s in declared || error("GSLT parse: `$lbl` uses undeclared sort `$s`")
        end
    end

    # A grounded sort must be declared, unique, and NOT also constructed — a sort cannot carry two
    # incompatible sets of formation rules.
    built = Set{Base.Symbol}()
    for r in terms
        n = cat_name(r.cat); n === nothing || push!(built, n)
    end
    lseen = Set{Base.Symbol}()
    for l in lits
        l.sort in declared || error("GSLT parse: literal sort `$(l.sort)` is not in (types …)")
        l.sort in lseen && error("GSLT parse: duplicate literal declaration for `$(l.sort)`")
        l.sort in built && error("GSLT parse: `$(l.sort)` is declared grounded but also has constructors")
        push!(lseen, l.sort)
    end

    GPresentation(name, exports, lits, terms, eqs, rews, Tuple{String, GPresentation}[])
end

end # module CompilerGSLTParse
