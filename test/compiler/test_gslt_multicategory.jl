# test_gslt_multicategory.jl — the CONTEXT MULTICATEGORY of Definition 5.1.
#
# WHAT THIS DOES NOT TEST, AND WHY THAT IS THE HEADLINE. There is no morphism here. Definition 5.1
# says a morphism of GSLTs is a "pseudofunctor of context multicategories, bisimulation-preserving for
# context-labelled transitions"; this tree has no labelled transition system for a presentation, so
# the bisimulation half cannot be written. What CAN be built is the structure a morphism is a
# pseudofunctor OF — "objects … are INTERFACES …; multimorphisms are CONTEXTS; composition is
# PLUGGING" — and that is what is tested.
#
# THE LAWS ARE THE POINT. A "context" that is just a term with a marker in it proves nothing; what
# makes it a multicategory is that plugging has an identity and is associative, and that composing an
# n-ary into an m-ary gives the right arity. Those are the tests that would fail if plugging silently
# captured or renumbered wrongly — the two ways this construction actually breaks.
using MeTTaCore
using Test

const _XP = MeTTaCore.CompilerGSLTPresentation
const _XA = MeTTaCore.CompilerGSLTParse
const _XM = MeTTaCore.CompilerGSLTMulticategory
const _XV = MeTTaCore.Eval

function _xt(src::AbstractString)
    sp = _XV.Space()
    toks = _XV.tokenize(src)
    i = Ref(1)
    _XV.parse_from(toks, i, sp.tokens)
end
_xlang(src::AbstractString) = _XA.parse_presentation(_xt(src))
_xc(src::AbstractString) = _XM.GContext(_xt(src))

"Lambda, whose `Lam` is a binder — the presentation that makes `binding_stage` mean something."
const _LAM = _xlang(
    "(language Lam (types T) (terms (: Lam (-> (bind x T) (scope x T) T)) " *
    "(: App (-> T T T)) (: K (-> T))))")

@testset "GSLT context multicategory (Definition 5.1 objects + multimorphisms)" begin

    @testset "contexts and arity — DISTINCT holes, not occurrences" begin
        @test _XM.arity(_xc("(App (Hole 1) a)")) == 1
        @test _XM.arity(_xc("(App (Hole 1) (Hole 2))")) == 2
        @test _XM.arity(_xc("(App a b)")) == 0                    # a closed term is a 0-ary context

        # A context that uses ONE input twice is UNARY. Counting occurrences would make plugging
        # ill-defined — filling input 1 fills both positions, so there is one input, not two.
        @test _XM.arity(_xc("(App (Hole 1) (Hole 1))")) == 1
        @test _XM.holes_of(_xc("(App (Hole 2) (Hole 1))")) == [1, 2]   # ascending, deduplicated
    end

    @testset "plugging a TERM fills every occurrence of that hole and no other" begin
        c = _xc("(App (Hole 1) (Hole 2))")
        @test _XM.plug_term(c, 1, _xt("a")).term == _xt("(App a (Hole 2))")
        @test _XM.plug_term(_xc("(App (Hole 1) (Hole 1))"), 1, _xt("a")).term ==
            _xt("(App a a)")
        @test _XM.plug_term(c, 3, _xt("a")).term == c.term        # no such hole ⇒ unchanged
    end

    @testset "IDENTITY — the unit laws of the multicategory" begin
        id = _XM.identity_context()
        for src in
            ("(App (Hole 1) a)", "(Lam \$x (Hole 1))", "(App (Hole 1) (Hole 2))", "(K)")
            c = _xc(src)
            # plugging the identity INTO a hole changes nothing (right unit)
            isempty(_XM.holes_of(c)) && continue
            @test _XM.plug(c, _XM.holes_of(c)[1], id).term == c.term
        end
        # plugging a context into the IDENTITY returns that context (left unit)
        for src in ("(App (Hole 1) a)", "(App (Hole 1) (Hole 2))", "(K)")
            c = _xc(src)
            @test _XM.plug(id, 1, c).term == c.term
        end
    end

    @testset "COMPOSITION — arity adds correctly and holes do not collide" begin
        outer = _xc("(App (Hole 1) (Hole 2))")            # binary
        inner = _xc("(App (Hole 1) (Hole 2))")            # binary
        # plugging a 2-ary into one input of a 2-ary: 2 - 1 + 2 = 3
        comp = _XM.plug(outer, 1, inner)
        @test _XM.arity(comp) == 3
        @test length(_XM.holes_of(comp)) == 3
        @test length(unique(_XM.holes_of(comp))) == 3      # ⇐ THE COLLISION TEST

        # The inputs are 1..3 CONTIGUOUS, in the multicategory's order: `inner`'s two inputs take the
        # position the consumed hole occupied, and `outer`'s remaining input shifts up behind them.
        @test _XM.holes_of(comp) == [1, 2, 3]
        @test comp.term == _xt("(App (App (Hole 1) (Hole 2)) (Hole 3))")

        # A 0-ary inner CLOSES an input — and the SURVIVOR IS RENUMBERED TO 1, because inputs stay
        # contiguous. Expecting `(Hole 2)` here was my error, not the code's: after input 1 is
        # consumed the remaining input is the first one.
        @test _XM.arity(_XM.plug(outer, 1, _xc("(K)"))) == 1
        @test _XM.plug(outer, 1, _xc("(K)")).term == _xt("(App (K) (Hole 1))")

        @test_throws ErrorException _XM.plug(outer, 9, inner)   # no such input
    end

    @testset "ASSOCIATIVITY of plugging — the law that makes it a multicategory" begin
        # (f ∘ᵢ g) ∘ⱼ h  ==  f ∘ᵢ (g ∘ⱼ' h), for a j inside g's inputs. Checked on the terms, since
        # two contexts are equal exactly when their terms are.
        f = _xc("(App (Hole 1) (Hole 2))")
        g = _xc("(App (Hole 1) b)")
        h = _xc("(Lam \$x (Hole 1))")

        # `g`'s single input lands AT THE POSITION IT WAS PLUGGED INTO — input 1, not appended at the
        # end. Taking `holes_of(...)[end]` picked `f`'s surviving input instead and made the two sides
        # compose different things; that was a wrong test, not a broken law.
        lhs_inner = _XM.plug(f, 1, g)
        @test lhs_inner.term == _xt("(App (App (Hole 1) b) (Hole 2))")
        lhs = _XM.plug(lhs_inner, 1, h)

        rhs = _XM.plug(f, 1, _XM.plug(g, 1, h))
        @test lhs.term == rhs.term
        @test _XM.arity(lhs) == _XM.arity(rhs) == 2
    end

    @testset "INTERFACES — the sort Σ gives the position, and the binding stage" begin
        # `App`'s arguments are T, and neither is under a binder.
        i1 = _XM.interface_at(_LAM, _xc("(App (Hole 1) a)"), 1)
        @test i1.sort === :T
        @test i1.binding_stage == 0

        # `Lam`'s SECOND argument is the `(scope x T)` position — a hole there is under ONE binder.
        i2 = _XM.interface_at(_LAM, _xc("(Lam \$x (Hole 1))"), 1)
        @test i2.binding_stage == 1
        @test i2.sort === :T
        @test _XM.binding_stage(_LAM, _xc("(Lam \$x (Lam \$y (Hole 1)))"), 1) == 2   # nested binders

        # …and the BINDER position itself is stage 0 — `(bind x T)` declares, it does not scope.
        @test _XM.interface_at(_LAM, _xc("(Lam (Hole 1) b)"), 1).binding_stage == 0

        # A head Σ does not declare gives NO sort. That is information, not a failure.
        @test _XM.interface_at(_LAM, _xc("(undeclared (Hole 1))"), 1).sort === nothing

        @test_throws ErrorException _XM.interface_at(_LAM, _xc("(App a b)"), 1)   # no such hole
    end

    @testset "A CONTEXT WHOSE OCCURRENCES DISAGREE IS REJECTED" begin
        # One input, two positions, two different binding stages. A multicategory input has ONE
        # interface, so this is not a well-formed context — reported rather than resolved by picking
        # whichever occurrence the traversal happened to reach first.
        @test_throws ErrorException _XM.interface_at(
            _LAM, _xc("(App (Lam \$x (Hole 1)) (Hole 1))"), 1
        )
        # …and the agreeing case still works, so the check is not simply always-throwing.
        @test _XM.interface_at(_LAM, _xc("(App (Hole 1) (Hole 1))"), 1).binding_stage == 0
    end

    @testset "`Hole` may not also be a CONSTRUCTOR of the presentation" begin
        # Otherwise a presentation's own data would read back as holes. `context_of` is the checked
        # entry point; the bare `GContext` constructor is for terms already known to be contexts.
        bad = _xlang("(language B (types T) (terms (: Hole (-> T T))))")
        @test_throws ErrorException _XM.context_of(bad, _xt("(Hole 1)"))
        @test _XM.context_of(_LAM, _xt("(App (Hole 1) a)")) isa _XM.GContext
    end
end
