# test_gslt_presentation.jl — the ported (Σ,E,R) model must express what `standard/GSLT.jl` cannot.
#
# The model is a PORT of LeaTTa's machine-checked `MeTTaIL/Syntax.lean` (`lake build MeTTaIL`: 660
# jobs, 0 errors, 0 warnings, 0 `sorry`). So the tests are the two upstream presentations that
# exercise the constructs GSLT.jl has no room for, transcribed rather than invented:
#
#   mettail-rust/languages/src/lambda.rs
#       Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
#       AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
#
#   MeTTaIL/GSLT/src/test/module/Rholang.module
#       PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc ;
#       if x # Q then ( PPar ( PNew x P ) Q ) == ( PNew x ( PPar P Q ) ) ;
#
# Several assertions here exist specifically because the FIRST, hand-built version of this model got
# them wrong; each is labelled with what it would have missed.
using MeTTaCore
using Test

const _GP = MeTTaCore.CompilerGSLTPresentation
const _SM = MeTTaCore.StandardMeTTa

_sym(s) = _SM.Sym(Base.Symbol(s))
_var(s) = _SM.Var(s)
_ex(xs...) = _SM.Expression(collect(_SM.Atom, xs))
_pres(; name = :T, exports = _GP.GCat[], lits = _GP.GLiteral[], terms = _GP.GRule[],
        eqs = _GP.GEquation[], rews = _GP.GRewriteDecl[]) =
    _GP.GPresentation(name, exports, lits, terms, eqs, rews, Tuple{String, _GP.GPresentation}[])

@testset "GSLT presentation — ported from LeaTTa Syntax.lean" begin

    @testset "Cat is an ARITY LANGUAGE, not a bare name" begin
        # Defect (1) of the hand-built model: sorts were `Symbol`, so `[Proc]` and exponentials were
        # simply unwritable, and a binder needed a bespoke struct instead of being `arrow`.
        @test _GP.cat_name(_GP.CatId(:Proc)) === :Proc
        @test _GP.cat_name(_GP.CatList(_GP.CatId(:Proc))) === nothing     # compound has no atomic name
        arrow = _GP.CatArrow(_GP.CatId(:Term), _GP.CatId(:Term))
        @test arrow isa _GP.GCat
        @test _GP.CatProd(_GP.GCat[_GP.CatId(:A), _GP.CatId(:B)]) isa _GP.GCat
        # nesting is closed: a list of arrows is a category
        @test _GP.CatList(arrow) isa _GP.GCat
    end

    @testset "BIND and ABS are distinct — Rholang uses both in one constructor" begin
        # Defect (2): one `GBind(var,body)` cannot say WHICH body a variable scopes over when a
        # constructor has several. `PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc` has both.
        pnew = _GP.GRule(_GP.LabelId(:PNew), _GP.CatId(:Proc),
                         _GP.GItem[_GP.ItemBind(:x, _GP.CatId(:Name)),
                                   _GP.ItemAbs(:x, _GP.ItemNonTerminal(_GP.CatId(:Proc)))])
        @test _GP.rule_arity(pnew) == 2
        p = _pres(exports = _GP.GCat[_GP.CatId(:Proc), _GP.CatId(:Name)], terms = _GP.GRule[pnew])
        @test _GP.is_lambda_theory(p)
        @test _GP.declared_cats_used(p) == Set(Base.Symbol[:Proc, :Name])   # BOTH, through the binder
    end

    @testset "terminals are syntax, not arguments" begin
        # `rule_arity` counts non-terminals only (Syntax.lean:79-80). Counting terminals would give
        # every constructor the wrong arity the moment concrete syntax is present.
        r = _GP.GRule(_GP.LabelId(:PNew), _GP.CatId(:Proc),
                      _GP.GItem[_GP.ItemTerminal("new"), _GP.ItemBind(:x, _GP.CatId(:Name)),
                                _GP.ItemTerminal("in"),  _GP.ItemNonTerminal(_GP.CatId(:Proc))])
        @test _GP.rule_arity(r) == 2
    end

    @testset "a FIRST-ORDER signature is legal but is NOT a lambda theory" begin
        # Monoid/Rig — every theory in this tree before this component. Per the deck, a Lawvere
        # encoding "breaks exactly where we need it: one cannot write a binder".
        mult = _GP.GRule(_GP.LabelId(:Mult), _GP.CatId(:Elem),
                         _GP.GItem[_GP.ItemNonTerminal(_GP.CatId(:Elem)),
                                   _GP.ItemNonTerminal(_GP.CatId(:Elem))])
        p = _pres(name = :Monoid, exports = _GP.GCat[_GP.CatId(:Elem)], terms = _GP.GRule[mult])
        @test isempty(_GP.binders_of(p))
        @test !_GP.is_lambda_theory(p)
        @test _GP.ddl_rung(p) == 1
    end

    @testset "PREMISED rewrites — the RewCtx spine, and premises are VARIABLES" begin
        # Defect (4): premises took arbitrary terms; upstream types both `Hyp` fields DottedPath.
        cong = _GP.GRewriteDecl(:AppCongL,
                 _GP.RewCtx(_GP.GHyp(:M0, :M1),
                   _GP.RewBase(_ex(_sym("App"), _var("M0"), _var("N")),
                               _ex(_sym("App"), _var("M1"), _var("N")))))
        beta = _GP.GRewriteDecl(:Beta,
                 _GP.RewBase(_ex(_sym("App"), _ex(_sym("Lam"), _var("fun")), _var("arg")),
                             _ex(_sym("eval"), _var("fun"), _var("arg"))))
        @test length(_GP.premises_of(cong.rw)) == 1
        @test _GP.premises_of(cong.rw)[1] == _GP.GHyp(:M0, :M1)
        @test isempty(_GP.premises_of(beta.rw))               # the only shape GSLT.jl can represent
        @test _GP.conclusion_of(cong.rw)[1] == _ex(_sym("App"), _var("M0"), _var("N"))
        # two stacked premises unwind outermost-first
        two = _GP.RewCtx(_GP.GHyp(:A, :B), _GP.RewCtx(_GP.GHyp(:C, :D), _GP.RewBase(_var("l"), _var("r"))))
        @test [h.src for h in _GP.premises_of(two)] == Base.Symbol[:A, :C]
        @test _GP.conclusion_of(two) == (_var("l"), _var("r"))
    end

    @testset "FRESHNESS — Rholang's scope-extrusion law" begin
        eq = _GP.GEquation(
            _ex(_sym("PPar"), _ex(_sym("PNew"), _var("x"), _var("P")), _var("Q")),
            _ex(_sym("PNew"), _var("x"), _ex(_sym("PPar"), _var("P"), _var("Q"))),
            _GP.GFresh[_GP.GFresh(:x, :Q)])
        @test length(eq.conditions) == 1 && eq.conditions[1].var == :x
        plain = _GP.GEquation(_ex(_sym("PDrop"), _ex(_sym("NQuote"), _var("P"))), _var("P"), _GP.GFresh[])
        @test isempty(plain.conditions)                       # alpha-swap needs no condition
    end

    @testset "the DDL rung, and the empty presentation" begin
        r = _GP.GRule(_GP.LabelId(:A), _GP.CatId(:T), _GP.GItem[])
        @test _GP.ddl_rung(_pres(terms = _GP.GRule[r])) == 1
        @test _GP.ddl_rung(_pres(terms = _GP.GRule[r],
                                 eqs = _GP.GEquation[_GP.GEquation(_var("a"), _var("b"), _GP.GFresh[])])) == 2
        @test _GP.ddl_rung(_pres(terms = _GP.GRule[r],
                                 rews = _GP.GRewriteDecl[_GP.GRewriteDecl(:R, _GP.RewBase(_var("a"), _var("b")))])) == 3
        e = _GP.empty_presentation()
        @test isempty(e.terms) && isempty(e.exports) && isempty(e.references)
    end

    @testset "types are concrete — no Any" begin
        p = _pres(exports = _GP.GCat[_GP.CatId(:T)])
        @test p.exports isa Vector{_GP.GCat}
        @test p.references isa Vector{Tuple{String, _GP.GPresentation}}   # recursive, as upstream
        @test fieldtype(_GP.GEquation, :lhs) === _SM.Atom                 # terms TYPED, not strings
        @test fieldtype(_GP.GHyp, :src) === Base.Symbol                   # premises are VARIABLES
        @test !any(t -> t === Any, fieldtypes(_GP.GPresentation))
        @test !any(t -> t === Any, fieldtypes(_GP.GRule))
    end
end
