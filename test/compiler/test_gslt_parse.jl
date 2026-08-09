# test_gslt_parse.jl — presentations must be WRITABLE, and malformed ones must be REJECTED.
#
# The positive cases are the two upstream presentations transcribed into our s-expr surface, so the
# test doubles as the proof that the surface can carry them:
#
#   mettail-rust/languages/src/lambda.rs   — binders + congruence rules
#   MeTTaIL/GSLT/src/test/module/Rholang   — freshness-guarded scope extrusion
#
# The negative cases exist because upstream ships `GSLT/src/test/module/bad/` and treats malformed
# presentations as a case worth testing. It matters more here than for an ordinary parser: a
# presentation is INPUT TO A GENERATOR, so silently accepting nonsense yields a type system for a
# language that does not exist.
using MeTTaCore
using Test

const _PP = MeTTaCore.CompilerGSLTPresentation
const _PA = MeTTaCore.CompilerGSLTParse
const _PV = MeTTaCore.Eval

"Parse concrete text the way a user would write it in a .metta file."
function _lang(src::AbstractString)
    sp = _PV.Space()
    toks = _PV.tokenize(src); i = Ref(1)
    _PA.parse_presentation(_PV.parse_from(toks, i, sp.tokens))
end

@testset "GSLT presentation — s-expr surface" begin

    @testset "LAMBDA transcribed from lambda.rs, binders and congruence intact" begin
        p = _lang("""
        (language Lambda
          (types Term)
          (terms
            (: Lam (-> (bind Term Term) Term))
            (: App (-> Term Term Term)))
          (equations)
          (rewrites
            (rewrite Beta     ()           (~> (App (Lam fun) arg) (eval fun arg)))
            (rewrite AppCongL ((~> M0 M1)) (~> (App M0 N) (App M1 N)))
            (rewrite AppCongR ((~> N0 N1)) (~> (App M N0) (App M N1)))))
        """)
        @test p.name == :Lambda
        @test p.sorts == Base.Symbol[:Term]
        @test length(p.ctors) == 2
        @test _PP.is_lambda_theory(p)                       # ← the binder survived the surface
        @test [c.label for c in _PP.binders_of(p)] == Base.Symbol[:Lam]
        @test length(p.rewrites) == 3
        @test isempty(p.rewrites[1].premises)               # Beta is an AXIOM
        @test length(p.rewrites[2].premises) == 1           # AppCongL is a CONGRUENCE rule
        @test _PP.ddl_rung(p) == 3                          # terms + rewrites ⇒ a DSL
    end

    @testset "RHOLANG's freshness-guarded scope extrusion" begin
        p = _lang("""
        (language Rho
          (types Proc Name)
          (terms
            (: PZero (-> Proc))
            (: PPar  (-> Proc Proc Proc))
            (: PNew  (-> (bind Name Proc) Proc)))
          (equations
            ; no inner `==` marker: MeTTa resolves == to a GROUNDED op, never a Sym, so it
            ; cannot be a keyword here. Conditions lead; the last two args are the two sides.
            (equation ScopeExtrusion (fresh x Q)
              (PPar (PNew x P) Q) (PNew x (PPar P Q)))
            (equation NewSwap
              (PNew x (PNew y P)) (PNew y (PNew x P))))
          (rewrites))
        """)
        @test length(p.equations) == 2
        @test length(p.equations[1].conditions) == 1        # guarded
        @test p.equations[1].conditions[1].var == :x
        @test isempty(p.equations[2].conditions)            # unguarded — alpha-swap needs no condition
        @test _PP.is_lambda_theory(p)                       # PNew binds
        @test _PP.ddl_rung(p) == 2                          # terms + equations, no rewrites
    end

    @testset "a FIRST-ORDER theory written for GSLT.jl parses UNCHANGED" begin
        # The whole point of reusing `(: Label (-> …))`: nothing existing has to move.
        p = _lang("(language Monoid (types Elem) (terms (: Mult (-> Elem Elem Elem)) (: One (-> Elem))))")
        @test !_PP.is_lambda_theory(p)
        @test _PP.ddl_rung(p) == 1                          # terms only ⇒ algebraic data types
        @test _PP.ctor_arity(p.ctors[1]) == 2 && _PP.ctor_arity(p.ctors[2]) == 0
    end

    @testset "MALFORMED presentations are REJECTED, not partially accepted" begin
        # upstream bad/RepeatLabel.module
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: A (-> T)) (: A (-> T T))))")
        # a sort `types` never declared — would become a phantom sort downstream
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> Bogus T))))")
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> T Bogus))))")
        # binder arity
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> (bind T) T))))")
        # a premise that is not a rewrite
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: A (-> T))) (rewrites (rewrite R (oops) (~> a b))))")
        # duplicate rewrite label
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: A (-> T))) (rewrites (rewrite R () (~> a b)) (rewrite R () (~> c d))))")
        # not a language at all
        @test_throws ErrorException _lang("(monoid X)")
    end

    @testset "LITERALS — grounded sorts, the sixth upstream section" begin
        # MeTTa has grounded atoms, so its presentation cannot be a pure term algebra. The carrier
        # vocabulary is Core's real `GroundedType` enum (compiler/IR.jl:129), not free-form text.
        p = _lang("""
        (language Arith
          (types Int Expr)
          (literals (literal Int GROUNDED_INT))
          (terms (: Plus (-> Expr Expr Expr))
                 (: Lit  (-> Int Expr))))
        """)
        @test length(p.literals) == 1
        @test p.literals[1].sort == :Int
        @test _PP.grounded_sorts(p) == Set(Base.Symbol[:Int])
        @test :Expr ∉ _PP.grounded_sorts(p)          # Expr is CONSTRUCTED, not grounded

        # an unknown carrier is an error, NOT a silent fall back to GROUNDED_OPAQUE
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal T GROUNDED_WIDGET)))")
        # a literal sort must be declared in (types …)
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal Undeclared GROUNDED_INT)))")
        # …and must not ALSO be constructed — two incompatible sets of formation rules
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal T GROUNDED_INT)) (terms (: A (-> T))))")
        # duplicates
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal T GROUNDED_INT) (literal T GROUNDED_STRING)))")
    end

    @testset "absent sections are empty, not an error" begin
        p = _lang("(language Bare (types T))")
        @test isempty(p.ctors) && isempty(p.equations) && isempty(p.rewrites) && isempty(p.literals)
        @test _PP.ddl_rung(p) == 1
    end

    @testset "types are concrete — no Any" begin
        p = _lang("(language Lambda (types Term) (terms (: Lam (-> (bind Term Term) Term))))")
        @test p isa _PP.GPresentation
        @test p.ctors isa Vector{_PP.GCtor}
        @test p.ctors[1].args isa Vector{_PP.GArg}
        @test p.ctors[1].args[1] isa _PP.GBind
    end
end
