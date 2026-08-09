# Parse.jl — s-expression surface → `GPresentation`. G = (Σ, E, R) as something you can WRITE.
#
# `Presentation.jl` gave the data model; until a presentation can be written as text it can only be
# built in Julia, which means MeTTa's own (Σ,E,R) cannot be authored as a `.metta` file and nothing
# downstream (hypercube, generated types) can ever have a real input.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). This file implements NO Figure-2 arrow — it
# builds the INPUT that "MeTTa-IL is derived from a GSLT description" presupposes, and so sits
# upstream of the one compile arrow (MeTTa → MeTTa-IL).
#
# ─── THE SURFACE, AND WHY IT LOOKS LIKE THIS ─────────────────────────────────────────────────────
# Upstream writes presentations two ways, and neither transliterates into MeTTa:
#
#   Scala .module   PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc ;
#   Rust macro      Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
#                   AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
#
# Both carry CONCRETE SYNTAX (`"new" … "in" …`) because they generate parsers for a target language.
# We drop that: in MeTTa the s-expr IS the syntax, so a concrete grammar would be a second source of
# truth. What is kept is exactly the semantic content — sorts, binding structure, freshness, premises.
#
#     (language Lambda
#       (types Term)
#       (terms
#         (: Lam (-> (bind Term Term) Term))      ; ^x.body:[Term -> Term]
#         (: App (-> Term Term Term)))
#       (equations)
#       (rewrites
#         (rewrite Beta     ()           (~> (App (Lam fun) arg) (eval fun arg)))
#         (rewrite AppCongL ((~> M0 M1)) (~> (App M0 N) (App M1 N)))))
#
# `(: Label (-> args… Result))` is the SAME type-sig form `standard/GSLT.jl` already parses, so a
# first-order theory written for that file parses here unchanged — `(bind A B)` is the only addition,
# and it appears exactly where a sort would. Extend, do not replace.
#
# ─── MALFORMED PRESENTATIONS MUST BE REJECTED ────────────────────────────────────────────────────
# Upstream ships `GSLT/src/test/module/bad/` — `RepeatLabel.module`, `ReplacementShadows.module` —
# i.e. it treats "this presentation is nonsense" as a case worth testing. It matters more here than
# for an ordinary parser: a presentation is INPUT TO A GENERATOR, so a silently-accepted malformed
# triple produces silently-wrong apparatus (a type system for a language that does not exist). Every
# check below raises, naming the offending label, rather than returning a partial presentation.
module CompilerGSLTParse

using ..StandardMeTTa: Atom, Sym, Var, Expression
using ..CompilerIR: GroundedType, GROUNDED_INT, GROUNDED_FLOAT, GROUNDED_BOOL,
                    GROUNDED_STRING, GROUNDED_OPAQUE
using ..CompilerGSLTPresentation: GSort, GBind, GArg, GCtor, GLiteral, GFresh, GEquation,
                                  GRewrite, GPresentation

export parse_presentation

# ── small typed accessors over the grammar's Atom ────────────────────────────────────────────────

_is_expr(a::Atom)::Bool = a isa Expression && !isempty((a::Expression).children)

"Head symbol of an expression, or `nothing` if it is not a symbol-headed expression."
function _head(a::Atom)::Union{Base.Symbol, Nothing}
    _is_expr(a) || return nothing
    h = (a::Expression).children[1]
    h isa Sym ? (h::Sym).name : nothing
end

_args(a::Expression)::Vector{Atom} = a.children[2:end]

"Children of the `(section …)` form with this head, or empty if the section is absent."
function _section(body::Vector{Atom}, name::Base.Symbol)::Vector{Atom}
    for f in body
        _head(f) === name && return _args(f::Expression)
    end
    Atom[]
end

_symname(a::Atom, what::AbstractString)::Base.Symbol =
    a isa Sym ? (a::Sym).name :
    error("GSLT parse: expected a symbol for $what, got $(typeof(a))")

# ── Σ ────────────────────────────────────────────────────────────────────────────────────────────

"""One argument position: a bare sort `Term`, or a binder `(bind A B)`.

`(bind A B)` is the s-expr form of upstream's `^x.body:[A -> B]` — the sort of "an A-binder scoping
a B". Anything else in argument position is an ERROR rather than a guess: silently treating an
unrecognised form as a plain sort would erase binding structure, which is the one thing this
component exists to record."""
function _parse_arg(a::Atom)::GArg
    if a isa Sym
        return GSort((a::Sym).name)
    elseif _head(a) === :bind
        xs = _args(a::Expression)
        length(xs) == 2 || error("GSLT parse: (bind A B) takes exactly 2 sorts, got $(length(xs))")
        return GBind(_symname(xs[1], "binder variable sort"), _symname(xs[2], "binder body sort"))
    end
    error("GSLT parse: argument must be a sort or (bind A B), got $(a)")
end

"`(: Label (-> arg… Result))` — the type-sig form `standard/GSLT.jl` already uses."
function _parse_ctor(f::Atom)::GCtor
    _head(f) === :(:) || error("GSLT parse: a term must be (: Label (-> …)), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (: Label Sig) takes exactly 2 parts")
    label = _symname(xs[1], "constructor label")
    sig = xs[2]
    _head(sig) === :(->) || error("GSLT parse: signature of `$label` must be (-> … Result)")
    parts = _args(sig::Expression)
    isempty(parts) && error("GSLT parse: signature of `$label` needs at least a result sort")
    GCtor(label, GArg[_parse_arg(p) for p in parts[1:end - 1]],
          _symname(parts[end], "result sort of `$label`"))
end

"""`(literal Sort CARRIER)` — declare a sort whose inhabitants come from the lexer.

CARRIER must be one of Core's real grounded types (`GroundedType`, `compiler/IR.jl:129`); an
unrecognised name is an ERROR, not an opaque fallback. Falling back to `GROUNDED_OPAQUE` on a typo
would silently produce a sort the type system treats as unanalysable — the quiet-wrong-answer shape
this parser exists to refuse."""
const _CARRIERS = Dict{Base.Symbol, GroundedType}(
    :GROUNDED_INT    => GROUNDED_INT,
    :GROUNDED_FLOAT  => GROUNDED_FLOAT,
    :GROUNDED_BOOL   => GROUNDED_BOOL,
    :GROUNDED_STRING => GROUNDED_STRING,
    :GROUNDED_OPAQUE => GROUNDED_OPAQUE)

function _parse_literal(f::Atom)::GLiteral
    _head(f) === :literal || error("GSLT parse: expected (literal Sort CARRIER), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (literal Sort CARRIER) takes exactly 2 names")
    sort = _symname(xs[1], "literal sort")
    cname = _symname(xs[2], "carrier of `$sort`")
    haskey(_CARRIERS, cname) ||
        error("GSLT parse: `$sort` names unknown carrier `$cname`; expected one of " *
              join(sort!(String[String(k) for k in keys(_CARRIERS)]), ", "))
    GLiteral(sort, _CARRIERS[cname])
end

# ── E ────────────────────────────────────────────────────────────────────────────────────────────

"`(fresh x Q)` — upstream `x # Q`, read \"x does not occur free in Q\"."
function _parse_fresh(f::Atom)::GFresh
    _head(f) === :fresh || error("GSLT parse: expected (fresh x Term), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 2 || error("GSLT parse: (fresh x Term) takes exactly 2 names")
    GFresh(_symname(xs[1], "fresh variable"), _symname(xs[2], "fresh-in term"))
end

"""`(equation Label (fresh …)… LHS RHS)` — leading freshness conditions, then the two sides.

NO INNER `==` MARKER, deliberately. MeTTa resolves `==` to a GROUNDED operation
(`Grounded{Eval.Operation}`), never to a `Sym`, so it can never be matched as a keyword here —
measured, after a first draft that used it and rejected every well-formed equation. Rather than
hunt for another token that might also be grounded, the shape carries the meaning: conditions are
the leading `(fresh …)` forms and the final two arguments are the equation's sides."""
function _parse_equation(f::Atom)::GEquation
    _head(f) === :equation || error("GSLT parse: expected (equation Label … LHS RHS), got $(f)")
    xs = _args(f::Expression)
    length(xs) >= 3 ||
        error("GSLT parse: (equation Label … LHS RHS) needs a label and two sides")
    label = _symname(xs[1], "equation label")
    i = 2
    conds = GFresh[]
    while i <= length(xs) - 2 && _head(xs[i]) === :fresh
        push!(conds, _parse_fresh(xs[i])); i += 1
    end
    i == length(xs) - 1 ||
        error("GSLT parse: equation `$label` has unexpected forms between its conditions and sides")
    GEquation(xs[end - 1], xs[end], conds)
end

# ── R ────────────────────────────────────────────────────────────────────────────────────────────

function _parse_arrow(a::Atom, ctx::AbstractString)::Tuple{Atom, Atom}
    # `Base.Symbol("~>")`, NOT `:(~>)`: `~>` is not a Julia operator, so `:(~>)` parses as the
    # Expr `:(~(>))` and the comparison against a Symbol is silently ALWAYS FALSE. Measured.
    _head(a) === Base.Symbol("~>") || error("GSLT parse: $ctx must be (~> Src Tgt), got $(a)")
    xs = _args(a::Expression)
    length(xs) == 2 || error("GSLT parse: (~> Src Tgt) takes exactly 2 terms in $ctx")
    (xs[1], xs[2])
end

"""`(rewrite Label (premise…) (~> Src Tgt))` — upstream `Label . | premises |- conclusion`.

An EMPTY premise list is an axiom (`Beta`), which is all `standard/GSLT.jl` can represent. A
non-empty one is a congruence rule, and carrying it is the point: "reduction happens inside any
context" cannot be said by a flat `(~> L R)`."""
function _parse_rewrite(f::Atom)::GRewrite
    _head(f) === :rewrite || error("GSLT parse: expected (rewrite Label (…) (~> S T)), got $(f)")
    xs = _args(f::Expression)
    length(xs) == 3 || error("GSLT parse: (rewrite Label (premises…) (~> S T)) takes 3 parts")
    label = _symname(xs[1], "rewrite label")
    prems = xs[2]
    prems isa Expression || error("GSLT parse: premises of `$label` must be a list; use () for none")
    src, tgt = _parse_arrow(xs[3], "the conclusion of `$label`")
    GRewrite(label,
             Tuple{Atom, Atom}[_parse_arrow(p, "a premise of `$label`")
                               for p in (prems::Expression).children],
             src, tgt)
end

# ── the whole presentation, with validation ──────────────────────────────────────────────────────

"""
    parse_presentation(a::Atom) -> GPresentation

Parse `(language NAME (types …) (terms …) (equations …) (rewrites …))`.

Raises on a malformed presentation rather than returning a partial one — see the file header: a
presentation is input to a generator, so accepting nonsense produces nonsense apparatus.
"""
function parse_presentation(a::Atom)::GPresentation
    _head(a) === :language || error("GSLT parse: expected (language NAME …), got $(a)")
    body = _args(a::Expression)
    isempty(body) && error("GSLT parse: (language …) needs a name")
    name = _symname(body[1], "language name")
    rest = body[2:end]

    sorts = Base.Symbol[_symname(s, "a declared sort") for s in _section(rest, :types)]
    lits  = GLiteral[_parse_literal(f) for f in _section(rest, :literals)]
    ctors = GCtor[_parse_ctor(f) for f in _section(rest, :terms)]
    eqs   = GEquation[_parse_equation(f) for f in _section(rest, :equations)]
    rews  = GRewrite[_parse_rewrite(f) for f in _section(rest, :rewrites)]

    # DUPLICATE LABELS — upstream tests this explicitly (`bad/RepeatLabel.module`). Two constructors
    # sharing a label make the signature ambiguous, and every generated artifact inherits it.
    seen = Set{Base.Symbol}()
    for c in ctors
        c.label in seen && error("GSLT parse: duplicate constructor label `$(c.label)`")
        push!(seen, c.label)
    end
    rseen = Set{Base.Symbol}()
    for r in rews
        r.label in rseen && error("GSLT parse: duplicate rewrite label `$(r.label)`")
        push!(rseen, r.label)
    end

    # UNDECLARED SORTS — a constructor mentioning a sort `types` never declared is a typo that would
    # otherwise become a phantom sort in the generated type system.
    declared = Set{Base.Symbol}(sorts)
    for c in ctors
        c.result in declared ||
            error("GSLT parse: `$(c.label)` returns undeclared sort `$(c.result)`")
        for arg in c.args
            used = arg isa GSort ? Base.Symbol[(arg::GSort).name] :
                                   Base.Symbol[(arg::GBind).var_sort, (arg::GBind).body_sort]
            for s in used
                s in declared || error("GSLT parse: `$(c.label)` uses undeclared sort `$(s)`")
            end
        end
    end

    # A GROUNDED sort must be declared, and must NOT also be constructed. Both halves matter: an
    # undeclared literal sort is a typo, and a sort that is both opaque and built from constructors
    # has two incompatible sets of formation rules — the generated type system would have to pick one.
    lseen = Set{Base.Symbol}()
    built = Set{Base.Symbol}(c.result for c in ctors)
    for l in lits
        l.sort in declared || error("GSLT parse: literal sort `$(l.sort)` is not in (types …)")
        l.sort in lseen && error("GSLT parse: duplicate literal declaration for `$(l.sort)`")
        l.sort in built &&
            error("GSLT parse: `$(l.sort)` is declared grounded but also has constructors")
        push!(lseen, l.sort)
    end

    GPresentation(name, sorts, lits, ctors, eqs, rews)
end

end # module CompilerGSLTParse
