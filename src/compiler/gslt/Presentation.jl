# Presentation.jl — a GSLT presentation as TYPED DATA: G = (Σ, E, R).
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). Implements NO Figure-2 arrow — it is the
# INPUT that "MeTTa-IL is derived from a GSLT description" presupposes, upstream of the one arrow.
#
# ─── THIS IS A PORT, NOT A DESIGN ────────────────────────────────────────────────────────────────
# Ported from `~/JuliaAGI/dev-zone/LeaTTa/MeTTaIL/Syntax.lean` (198 lines), which is MACHINE-CHECKED:
# `lake build MeTTaIL` at LeaTTa HEAD `3885010` completes 660 jobs, 444 modules, with ZERO errors,
# ZERO warnings and ZERO `sorry` (run 2026-08-09, Lean 4.31.0). That file mirrors the NORMATIVE BNFC
# grammar `MeTTaIL/GSLT/src/main/bnfc/metta_venus.cf` ("MeTTa IL: Language Syntax Definition"), so
# the lineage is grammar → Lean → here. Every type below cites its source line.
#
# ⚠️ THE FIRST VERSION OF THIS FILE WAS HAND-BUILT, and re-derived in unverified Julia a model that
# already existed machine-checked in a repo this project ALREADY DEPENDS ON — LeaTTa is Core's
# conformance oracle and prints `✓ LeaTTa proved-oracle` on every health run. It was known as a NAME
# and never opened. The hand-built version was weaker in five specific ways, each fixed here:
#   1. sorts were bare symbols         → `GCat`, the real arity language (id/list/arrow/prod)
#   2. binder and scope conflated      → `ItemBind` and `ItemAbs`, distinct as upstream
#   3. no substitution primitive       → `Subst` as a reserved head (see the AST note)
#   4. premises took arbitrary terms   → `GHyp` is variable-to-variable, as upstream
#   5. no `exports` / `references`     → both present; `Rholang.module` uses `Exports`
#
# ─── WHY `MeTTapedia`'s GSLT IS NOT MERGED IN ────────────────────────────────────────────────────
# `dev-zone/MeTTapedia` also formalizes "GSLT" in Lean (198 files under `Mettapedia/GSLT/`, actively
# developed) — but as "§2 Graph-enriched LAWVERE Theories". That is a DIFFERENT OBJECT. The deck this
# tree conforms to devotes a section to why (`gslt_mettail_summary_spec.md` §1, page 5, verbatim):
#
#     "A Lawvere theory absorbs variables into arities … That encoding is faithful for first-order
#      algebra and BREAKS EXACTLY WHERE WE NEED IT: one cannot write a binder. Every calculus here
#      has binders — λx.M, for(x←n)P, new(x,P)."
#
# Binders are the entire reason this file exists, so the two cannot be merged. MeTTapedia stays a
# CONSULTED reference for the theory we lack (51 `Cost*` files = the C monad, OSLF, bisimulation).
#
# ─── WHY `AST` IS NOT PORTED ─────────────────────────────────────────────────────────────────────
# LeaTTa's `AST = var (DottedPath) | sexp (Label) (List AST) | subst (body repl) (v)` is a THIRD term
# type; this tree already speaks `StandardMeTTa.Atom` everywhere. A second would be transliteration,
# not adoption. The correspondence is exact, and stated so it can be checked:
#
#     LeaTTa                          ours
#     var (base "x")                  Var("x")
#     var (qualified "m" (base "x"))  Var("m.x")                       — dotted path as dotted name
#     sexp (id "App") [f, a]          Expression([Sym(:App), f, a])
#     subst body repl v               Expression([Sym(:Subst), body, repl, Var(v)])
#
# The last line is not invented: `Rholang.module` writes it exactly so —
# `RComm : (PPar (PRecv y x P) (PSend x Q)) ~> (Subst P (NQuote Q) y)`. LeaTTa promotes it to a
# constructor because its `AST` has no reserved heads; an s-expr surface does not need to.
# `StandardMeTTa.Grounded` has NO LeaTTa counterpart — its term algebra is pure — and that asymmetry
# is exactly what `GLiteral` records.
#
# ─── TWO EXTENSIONS BEYOND THE PORTED SOURCE — marked, not smuggled ──────────────────────────────
# Both from `mettail-rust/macros/src/ast/language.rs`, the newer surface:
#   * `name`     — LeaTTa's `Presentation` is anonymous (its name lives in the enclosing module map),
#                  but `.module` files and the Rust macro both name theories (`name: Lambda`).
#   * `literals` — LeaTTa has no grounded sorts. MeTTa does, so its presentation cannot be pure;
#                  `ast/language.rs:455` is where upstream puts them.
#
# NOT HERE: hypercube, elaboration, lowering. LeaTTa has all three (`Semantics/Hypercube.lean` 881
# lines, `Transform/{Desugar,Monomorphize,TypeLift}.lean`); they CONSUME a presentation.
module CompilerGSLTPresentation

using ..StandardMeTTa: Atom
using ..CompilerIR: GroundedType

export GCat, CatId, CatList, CatArrow, CatProd
export GLabel, LabelId, LabelWild, LabelListE, LabelListCons, LabelListOne
export GItem, ItemTerminal, ItemNonTerminal, ItemAbs, ItemBind
export GRule, GHyp, GRewriteBody, RewBase, RewCtx, GRewriteDecl
export GEquation, GFresh, GLiteral, GPresentation
export binders_of, is_lambda_theory, rule_arity, declared_cats_used, ddl_rung, grounded_sorts
export cat_name, empty_presentation, premises_of, conclusion_of

# ── Cat — the ARITY LANGUAGE (Syntax.lean:33; BNFC `IdCat | ListOfCat | ArrowCat | ProdCat`) ─────
# Upstream: "A sort / category, i.e. an arity expression. The arity language is the generating shapes
# closed under lists, exponentials (`arrow`), and products."
#
# A bare symbol is only the `idCat` case. The hand-built version had nothing else, so list sorts
# (`[Proc]`, `![Vec<Proc>] as List`) were unwritable and a binder needed a bespoke struct instead of
# simply being `arrow`.
abstract type GCat end
struct CatId    <: GCat; name::Base.Symbol      end
struct CatList  <: GCat; elem::GCat             end
"An exponential. Upstream `^x.body:[A -> B]` is `arrow A B` — the binder's sort, not a special case."
struct CatArrow <: GCat; dom::GCat; cod::GCat   end
struct CatProd  <: GCat; cs::Vector{GCat}       end

"Name of an ATOMIC category, or `nothing` for a compound one."
cat_name(c::GCat)::Union{Base.Symbol, Nothing} = c isa CatId ? (c::CatId).name : nothing

# ── Label (Syntax.lean:60; BNFC `Id | Wild | ListE | ListCons | ListOne`) ───────────────────────
# "The list labels carry the element category of the list sort they construct."
abstract type GLabel end
struct LabelId       <: GLabel; name::Base.Symbol end
struct LabelWild     <: GLabel                    end
struct LabelListE    <: GLabel; elem::GCat        end
struct LabelListCons <: GLabel; elem::GCat        end
struct LabelListOne  <: GLabel; elem::GCat        end

# ── Item (Syntax.lean:72; BNFC `Item`) ──────────────────────────────────────────────────────────
# Upstream: "`terminal` is a literal; `nterminal` is a sort argument; `absNTerminal x it` is the
# abstraction `(x) it` with `x` bound in `it`; `bindNTerminal x c` is `(Bind x c)`. The
# `absNTerminal`/`bindNTerminal` pair encodes a higher-order (exponential) argument."
#
# 🔴 THE PAIR IS THE POINT. Conflating it was defect (2). `Rholang.module` uses BOTH in one
# constructor — `PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc` — because DECLARING a binder and
# marking its SCOPE are different acts; a single `bind(var,body)` cannot say which body a variable
# scopes over when a constructor has more than one.
abstract type GItem end
"Concrete syntax. Kept for FAITHFULNESS; our surface never emits it (in MeTTa the s-expr IS the syntax)."
struct ItemTerminal    <: GItem; text::String                  end
struct ItemNonTerminal <: GItem; cat::GCat                     end
"`(x) it` — `x` is bound within `it`."
struct ItemAbs         <: GItem; var::Base.Symbol; item::GItem end
"`(Bind x c)` — declares `x` as a binder of category `c`."
struct ItemBind        <: GItem; var::Base.Symbol; cat::GCat   end

# ── Rule (Syntax.lean:81) — a function symbol `label . cat ::= items` ───────────────────────────
# "`cat` is the output arity; the input arity is READ OFF the non-terminal items."
struct GRule
    label::GLabel
    cat::GCat
    items::Vector{GItem}
end

"Input arity — non-terminal items only. Terminals are syntax, not arguments (Syntax.lean:79-80)."
rule_arity(r::GRule)::Int = count(i -> !(i isa ItemTerminal), r.items)

# ── E (Syntax.lean:115; BNFC `EquationImpl | EquationFresh`) ────────────────────────────────────
"A freshness side condition `x # y`. LeaTTa nests these as `Equation.fresh`; we carry them as a list."
struct GFresh
    var::Base.Symbol
    term::Base.Symbol
end

"An equation of the structural congruence, guarded by zero or more freshness conditions."
struct GEquation
    lhs::Atom
    rhs::Atom
    conditions::Vector{GFresh}
end

# ── R (Syntax.lean:121-137) ─────────────────────────────────────────────────────────────────────
"""A rewrite premise `src ~> tgt` (Syntax.lean:121; BNFC `Hyp . Hypothesis`).

⚠️ OVER VARIABLES, not arbitrary terms — upstream types both fields `DottedPath`. The hand-built
version allowed any term, strictly looser than the grammar, and would have accepted premises no
upstream presentation can express."""
struct GHyp
    src::Base.Symbol
    tgt::Base.Symbol
end

"A rewrite: conclusion `lhs ~> rhs`, optionally under premises (Syntax.lean:128; `RewriteBase | RewriteContext`)."
abstract type GRewriteBody end
struct RewBase <: GRewriteBody; lhs::Atom; rhs::Atom          end
struct RewCtx  <: GRewriteBody; hyp::GHyp; rest::GRewriteBody end

"A named rewrite declaration `name : rw` (Syntax.lean:134; BNFC `RDecl`)."
struct GRewriteDecl
    name::Base.Symbol
    rw::GRewriteBody
end

"Premises of a rewrite, outermost first — the `RewCtx` spine."
function premises_of(r::GRewriteBody)::Vector{GHyp}
    out = GHyp[]
    while r isa RewCtx
        push!(out, (r::RewCtx).hyp); r = (r::RewCtx).rest
    end
    out
end

"The `lhs ~> rhs` at the base of a rewrite, under all its premises."
function conclusion_of(r::GRewriteBody)::Tuple{Atom, Atom}
    while r isa RewCtx
        r = (r::RewCtx).rest
    end
    b = r::RewBase
    (b.lhs, b.rhs)
end

# ── EXTENSION (not in LeaTTa) — grounded sorts ──────────────────────────────────────────────────
"""A GROUNDED sort: inhabitants come from the lexer, not from constructors.

NOT IN THE PORTED SOURCE. LeaTTa's term algebra is pure, so its `Presentation` has no such section.
MeTTa has grounded atoms, so its presentation cannot be pure. Taken from the newer Rust surface
(`ast/language.rs:455`), minus `pattern`/`eval`: upstream needs a regex and a decoder because it
GENERATES a parser, whereas MeTTa's own reader already lexes literals."""
struct GLiteral
    sort::Base.Symbol
    carrier::GroundedType
end

# ── The presentation (Syntax.lean:149) ──────────────────────────────────────────────────────────
"""A theory presentation: exported sorts, function symbols, equations, rewrites, references.

`references` maps a declared prefix to a sub-presentation and is what makes the type RECURSIVE.
Upstream keeps it "to mirror `BasePres` faithfully, where a literal presentation can carry
references", noting its own elaborator never populates it; kept here for the same reason.

`name` and `literals` are the two documented extensions — see the file header."""
struct GPresentation
    name::Base.Symbol                                  # EXTENSION
    exports::Vector{GCat}
    literals::Vector{GLiteral}                         # EXTENSION
    terms::Vector{GRule}
    equations::Vector{GEquation}
    rewrites::Vector{GRewriteDecl}
    references::Vector{Tuple{String, GPresentation}}
end

"Mirrors `BasePresOps.empty` (Syntax.lean:194)."
empty_presentation(name::Base.Symbol = :Empty) =
    GPresentation(name, GCat[], GLiteral[], GRule[], GEquation[], GRewriteDecl[],
                  Tuple{String, GPresentation}[])

# ── structural queries ──────────────────────────────────────────────────────────────────────────

"Every rule that binds — the part of Σ that makes it a LAMBDA theory rather than first-order."
binders_of(p::GPresentation)::Vector{GRule} =
    GRule[r for r in p.terms if any(i -> i isa ItemBind || i isa ItemAbs, r.items)]

"""Is Σ a lambda theory (Definition 2.1's "in general"), or merely first-order?

`Monoid`/`Rig` are legal first-order signatures and return `false` — which is every theory that was
in this tree before this component, and precisely why none could present MeTTa. Per the deck, a
Lawvere encoding "breaks exactly where we need it: one cannot write a binder"."""
is_lambda_theory(p::GPresentation)::Bool = !isempty(binders_of(p))

"""Which rung of the DDL ladder this presentation reaches (`gslt_mettail_summary_spec.md` §2).

    1  terms only  ⇒ algebraic data types     2  + equations ⇒ universal algebra
    3  + rewrites  ⇒ domain-specific languages ("reduction and congruence rules, as data")

Makes the distance measurable: presenting MeTTa needs rung 3 AND binders."""
function ddl_rung(p::GPresentation)::Int
    isempty(p.rewrites) || return 3
    isempty(p.equations) || return 2
    1
end

"Sorts declared grounded rather than constructed — opaque to the term algebra."
grounded_sorts(p::GPresentation)::Set{Base.Symbol} =
    Set{Base.Symbol}(l.sort for l in p.literals)

"""Every ATOMIC category name reachable from the rules, through compounds and binders alike.

A naive walk over plain arguments misses both sorts inside `(bind A B)` and the element sort inside
`[A]`, which is how a phantom sort reaches a generated type system."""
function declared_cats_used(p::GPresentation)::Set{Base.Symbol}
    used = Set{Base.Symbol}()
    function walk(c::GCat)
        if c isa CatId
            push!(used, (c::CatId).name)
        elseif c isa CatList
            walk((c::CatList).elem)
        elseif c isa CatArrow
            walk((c::CatArrow).dom); walk((c::CatArrow).cod)
        else
            for x in (c::CatProd).cs; walk(x); end
        end
        nothing
    end
    function witem(i::GItem)
        if i isa ItemNonTerminal
            walk((i::ItemNonTerminal).cat)
        elseif i isa ItemBind
            walk((i::ItemBind).cat)
        elseif i isa ItemAbs
            witem((i::ItemAbs).item)
        end
        nothing
    end
    for r in p.terms
        walk(r.cat)
        for i in r.items; witem(i); end
    end
    used
end

end # module CompilerGSLTPresentation
