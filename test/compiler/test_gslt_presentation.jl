# test_gslt_presentation.jl — the (Σ,E,R) data model must express what GSLT.jl cannot.
#
# The whole point of this component is three constructs `standard/GSLT.jl` has no room for: BINDERS,
# FRESHNESS conditions, and PREMISED rewrites. So the tests are built from the two upstream
# presentations that USE them, rather than from invented shapes:
#
#   mettail-rust/languages/src/lambda.rs
#       Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
#       AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
#
#   MeTTaIL/GSLT/src/test/module/Rholang.module
#       PNew . Proc ::= "new" (Bind x Name) "in" (x)Proc ;
#       if x # Q then ( PPar ( PNew x P ) Q ) == ( PNew x ( PPar P Q ) ) ;
#
# If the model can hold those two verbatim, it can hold MeTTa's own presentation, which is the point
# of building it.
using MeTTaCore
using Test

const _GP = MeTTaCore.CompilerGSLTPresentation
const _SM = MeTTaCore.StandardMeTTa

_sym(s) = _SM.Sym(Base.Symbol(s))
_var(s) = _SM.Var(s)          # Var takes a String (name, id); Sym interns a Symbol
_ex(xs...) = _SM.Expression(collect(_SM.Atom, xs))

@testset "GSLT presentation — G = (Σ, E, R)" begin

    @testset "LAMBDA: the binder upstream writes as ^x.body:[Term -> Term]" begin
        lam = _GP.GCtor(:Lam, _GP.GArg[_GP.GBind(:Term, :Term)], :Term)
        app = _GP.GCtor(:App, _GP.GArg[_GP.GSort(:Term), _GP.GSort(:Term)], :Term)
        p = _GP.GPresentation(:Lambda, Base.Symbol[:Term], _GP.GCtor[lam, app],
                              _GP.GEquation[], _GP.GRewrite[])
        @test _GP.ctor_arity(lam) == 1
        @test _GP.ctor_arity(app) == 2
        @test _GP.binders_of(p) == _GP.GCtor[lam]        # App does not bind; Lam does
        @test _GP.is_lambda_theory(p)                    # ← the property GSLT.jl can never satisfy
    end

    @testset "a FIRST-ORDER signature is legal but is NOT a lambda theory" begin
        # Monoid/Rig — every theory currently in this tree. Legal, and unable to present MeTTa.
        mult = _GP.GCtor(:Mult, _GP.GArg[_GP.GSort(:Elem), _GP.GSort(:Elem)], :Elem)
        p = _GP.GPresentation(:Monoid, Base.Symbol[:Elem], _GP.GCtor[mult],
                              _GP.GEquation[], _GP.GRewrite[])
        @test isempty(_GP.binders_of(p))
        @test !_GP.is_lambda_theory(p)
    end

    @testset "PREMISED rewrite — a congruence rule, which a flat (~> L R) cannot state" begin
        # AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N)
        cong = _GP.GRewrite(:AppCongL,
                            Tuple{_SM.Atom, _SM.Atom}[(_var("M0"), _var("M1"))],
                            _ex(_sym("App"), _var("M0"), _var("N")),
                            _ex(_sym("App"), _var("M1"), _var("N")))
        # Beta . |- (App (Lam fun) arg) ~> (eval fun arg)   — an AXIOM: no premises
        beta = _GP.GRewrite(:Beta, Tuple{_SM.Atom, _SM.Atom}[],
                            _ex(_sym("App"), _ex(_sym("Lam"), _var("fun")), _var("arg")),
                            _ex(_sym("eval"), _var("fun"), _var("arg")))
        @test length(cong.premises) == 1
        @test isempty(beta.premises)                     # the only shape GSLT.jl can represent today
        @test cong.premises[1][1] == _var("M0")
    end

    @testset "FRESHNESS — Rholang's scope-extrusion law is expressible" begin
        # if x # Q then ( PPar ( PNew x P ) Q ) == ( PNew x ( PPar P Q ) )
        eq = _GP.GEquation(
            _ex(_sym("PPar"), _ex(_sym("PNew"), _var("x"), _var("P")), _var("Q")),
            _ex(_sym("PNew"), _var("x"), _ex(_sym("PPar"), _var("P"), _var("Q"))),
            _GP.GFresh[_GP.GFresh(:x, :Q)])
        @test length(eq.conditions) == 1
        @test eq.conditions[1].var == :x && eq.conditions[1].term == :Q
        # And an UNGUARDED equation still works — alpha-swap needs no condition.
        plain = _GP.GEquation(_ex(_sym("PDrop"), _ex(_sym("NQuote"), _var("P"))), _var("P"),
                              _GP.GFresh[])
        @test isempty(plain.conditions)
    end

    @testset "sorts used are recoverable, including through binders" begin
        # A binder mentions TWO sorts (var and body); a naive walk over plain args would miss both.
        pnew = _GP.GCtor(:PNew, _GP.GArg[_GP.GBind(:Name, :Proc)], :Proc)
        p = _GP.GPresentation(:Rho, Base.Symbol[:Proc, :Name], _GP.GCtor[pnew],
                              _GP.GEquation[], _GP.GRewrite[])
        @test _GP.declared_sorts_used(p) == Set(Base.Symbol[:Proc, :Name])
    end

    @testset "types are concrete — no Any, per the standing rule and the hook" begin
        lam = _GP.GCtor(:Lam, _GP.GArg[_GP.GBind(:Term, :Term)], :Term)
        @test lam.args isa Vector{_GP.GArg}
        @test _GP.GArg === Union{_GP.GSort, _GP.GBind}       # a closed union union-splits; Any does not
        @test fieldtype(_GP.GEquation, :lhs) === _SM.Atom     # terms are TYPED, not strings
        @test fieldtype(_GP.GRewrite, :premises) === Vector{Tuple{_SM.Atom, _SM.Atom}}
        @test !any(t -> t === Any, fieldtypes(_GP.GPresentation))
    end
end
