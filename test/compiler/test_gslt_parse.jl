# test_gslt_parse.jl — presentations must be WRITABLE, and malformed ones must be REJECTED.
#
# Positive cases are the two upstream presentations transcribed into our s-expr surface, so the tests
# double as proof the surface carries them:
#
#   mettail-rust/languages/src/lambda.rs   — binders + congruence rules
#   MeTTaIL/GSLT/src/test/module/Rholang   — (Bind x Name) / (x)Proc, freshness-guarded extrusion
#
# Negative cases exist because upstream ships `GSLT/src/test/module/bad/`. It matters more here than
# for an ordinary parser: a presentation is INPUT TO A GENERATOR, so silently accepting nonsense
# yields a type system for a language that does not exist.
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

    @testset "LAMBDA from lambda.rs — binder, scope, and congruence survive the surface" begin
        p = _lang("""
        (language Lambda
          (types Term)
          (terms
            (: Lam (-> (bind x Term) (scope x Term) Term))
            (: App (-> Term Term Term)))
          (equations)
          (rewrites
            ; Upstream writes `Beta . |- (App (Lam fun) arg) ~> (eval fun arg)`, where `eval` is the
            ; Rust surface's built-in application. The model we PORTED is LeaTTa's, whose built-in is
            ; the `Subst` AST node (`Reduce.lean:63`), so Beta is written with that — and with `Lam`'s
            ; binder in the pattern, which its arity-2 signature above already provides for.
            (rewrite Beta     ()             (~> (App (Lam \$x \$body) \$arg) (Subst \$body \$arg \$x)))
            (rewrite AppCongL ((~> \$M0 \$M1)) (~> (App \$M0 \$N) (App \$M1 \$N)))
            (rewrite AppCongR ((~> \$N0 \$N1)) (~> (App \$M \$N0) (App \$M \$N1)))))
        """)
        @test p.name == :Lambda
        @test length(p.exports) == 1 && _PP.cat_name(p.exports[1]) === :Term
        @test length(p.terms) == 2
        @test _PP.is_lambda_theory(p)
        @test [(r.label::_PP.LabelId).name for r in _PP.binders_of(p)] == Base.Symbol[:Lam]
        @test _PP.rule_arity(p.terms[1]) == 2                     # (bind x Term) and (scope x Term)
        @test isempty(_PP.premises_of(p.rewrites[1].rw))          # Beta is an AXIOM
        @test length(_PP.premises_of(p.rewrites[2].rw)) == 1      # AppCongL is a CONGRUENCE rule
        @test _PP.premises_of(p.rewrites[2].rw)[1] == _PP.GHyp(:M0, :M1)
        @test _PP.ddl_rung(p) == 3
    end

    @testset "RHOLANG — (Bind x Name) / (x)Proc plus freshness-guarded extrusion" begin
        p = _lang("""
        (language Rho
          (types Proc Name)
          (terms
            (: PZero (-> Proc))
            (: PPar  (-> Proc Proc Proc))
            (: PNew  (-> (bind x Name) (scope x Proc) Proc)))
          (equations
            (equation ScopeExtrusion (fresh \$x \$Q)
              (PPar (PNew \$x \$P) \$Q) (PNew \$x (PPar \$P \$Q)))
            (equation NewSwap
              (PNew \$x (PNew \$y \$P)) (PNew \$y (PNew \$x \$P))))
          (rewrites))
        """)
        @test length(p.equations) == 2
        @test length(p.equations[1].conditions) == 1 && p.equations[1].conditions[1].var == :x
        @test isempty(p.equations[2].conditions)
        @test _PP.is_lambda_theory(p)
        @test _PP.ddl_rung(p) == 2
        @test _PP.declared_cats_used(p) == Set(Base.Symbol[:Proc, :Name])
    end

    @testset "COMPOUND categories — the arity language the port restored" begin
        # `[Proc]` and exponentials were unwritable before the port; a bare symbol is only CatId.
        p = _lang("(language L (types Proc) (terms (: Bundle (-> (list Proc) Proc)) (: K (-> (arrow Proc Proc) Proc))))")
        @test (p.terms[1].items[1]::_PP.ItemNonTerminal).cat isa _PP.CatList
        @test (p.terms[2].items[1]::_PP.ItemNonTerminal).cat isa _PP.CatArrow
        @test _PP.declared_cats_used(p) == Set(Base.Symbol[:Proc])   # reached THROUGH the compounds
    end

    @testset "a FIRST-ORDER theory parses unchanged" begin
        p = _lang("(language Monoid (types Elem) (terms (: Mult (-> Elem Elem Elem)) (: One (-> Elem))))")
        @test !_PP.is_lambda_theory(p)
        @test _PP.ddl_rung(p) == 1
        @test _PP.rule_arity(p.terms[1]) == 2 && _PP.rule_arity(p.terms[2]) == 0
    end

    @testset "LITERALS — grounded sorts, validated against the real enum" begin
        p = _lang("""
        (language Arith
          (types Int Expr)
          (literals (literal Int GROUNDED_INT))
          (terms (: Plus (-> Expr Expr Expr)) (: Lit (-> Int Expr))))
        """)
        @test _PP.grounded_sorts(p) == Set(Base.Symbol[:Int])
        @test :Expr ∉ _PP.grounded_sorts(p)
        @test_throws ErrorException _lang("(language X (types T) (literals (literal T GROUNDED_WIDGET)))")
        @test_throws ErrorException _lang("(language X (types T) (literals (literal Undeclared GROUNDED_INT)))")
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal T GROUNDED_INT)) (terms (: A (-> T))))")
        @test_throws ErrorException _lang(
            "(language X (types T) (literals (literal T GROUNDED_INT) (literal T GROUNDED_STRING)))")
    end

    @testset "MALFORMED presentations are REJECTED" begin
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> T)) (: A (-> T T))))")
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> Bogus T))))")
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> (list Bogus) T))))")   # via a compound
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> (bind x Bogus) T))))") # via a binder
        @test_throws ErrorException _lang("(language X (types T) (terms (: A (-> (bind x) T))))")       # binder arity
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: A (-> T))) (rewrites (rewrite R (oops) (~> a b))))")
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: A (-> T))) (rewrites (rewrite R () (~> a b)) (rewrite R () (~> c d))))")
        # UNSIGILED PATTERN VARIABLES. `X` here is a `Sym`, so the rule is GROUND: it rewrites the
        # one literal term `(f X)` and nothing else — well-formed, parsed, inert. Every rewrite in the
        # first version of `presentations/mettail.metta` had this shape. Rejected on both sides, and
        # in equations, so the surface cannot express a schema that silently is not one.
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: f (-> T T))) (rewrites (rewrite R () (~> (f Y) Y))))")
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: f (-> T T))) (rewrites (rewrite R () (~> (f \$Y) Z))))")
        @test_throws ErrorException _lang(
            "(language X (types T) (terms (: f (-> T T))) (equations (equation E (f P) P)))")
        @test_throws ErrorException _lang("(monoid X)")
    end

    @testset "KEYWORD COLLISION GUARD — every reserved word must arrive as a `Sym`" begin
        # THE RULE, DERIVED FROM THREE INSTANCES. A keyword only works if MeTTa's reader hands it back
        # as a `Sym`; if the name is a registered grounded op it arrives as `Grounded{Operation}` and
        # the head test is SILENTLY ALWAYS FALSE. That bit twice — `==` in the equation form, then
        # `abs` for the scope marker — each time surfacing as "well-formed input rejected", which
        # reads like a parser bug rather than a name collision.
        #
        # So the whole reserved set is audited here instead of collisions being found one at a time.
        # A future keyword that collides fails THIS test with its own name, at the point of choosing.
        for kw in ("language", "types", "literals", "terms", "equations", "rewrites",
                   "bind", "scope", "list", "arrow", "prod", "fresh", "equation", "rewrite",
                   "literal", "~>", "->", ":")
            sp = _PV.Space(); toks = _PV.tokenize("($kw a b)"); i = Ref(1)
            a = _PV.parse_from(toks, i, sp.tokens)
            head = a.children[1]
            @test head isa MeTTaCore.StandardMeTTa.Sym    # fails NAMING the offending keyword
        end
        # And the two known-bad names stay bad — a regression here would mean the registry changed
        # and the surface could be simplified back.
        for bad in ("==", "abs")
            sp = _PV.Space(); toks = _PV.tokenize("($bad a b)"); i = Ref(1)
            a = _PV.parse_from(toks, i, sp.tokens)
            @test !(a.children[1] isa MeTTaCore.StandardMeTTa.Sym)
        end
    end

    @testset "absent sections are empty, not an error" begin
        p = _lang("(language Bare (types T))")
        @test isempty(p.terms) && isempty(p.equations) && isempty(p.rewrites) && isempty(p.literals)
        @test _PP.ddl_rung(p) == 1
    end

    @testset "types are concrete — no Any" begin
        p = _lang("(language Lambda (types Term) (terms (: Lam (-> (bind x Term) (scope x Term) Term))))")
        @test p isa _PP.GPresentation
        @test p.terms isa Vector{_PP.GRule}
        @test p.terms[1].items isa Vector{_PP.GItem}
        @test p.terms[1].items[1] isa _PP.ItemBind
        @test p.terms[1].items[2] isa _PP.ItemAbs
    end
end
