# test_gslt_reduce.jl — the presentation ENGINE. A presentation stops being data nobody can falsify
# only once something RUNS it, and these are the tests that make its rules answerable.
#
# The port is of `LeaTTa/MeTTaIL/Semantics/Reduce.lean`, so the assertions are organised around the
# five functions upstream exports — `matchPat`, `subst1`, `inst`, `applyBaseRewrite`, `baseReducts` —
# and each names the Lean line it mirrors.
#
# THREE THINGS HERE ARE PINNED BECAUSE THEY ARE GAPS, NOT FEATURES:
#   1. `apply_base_rewrite` returns `nothing` for a premised rule, so `mettail.metta`'s `ChainStep` is
#      INERT. Upstream's own scope (congruence closure lives in `Semantics/Context.lean`), but a
#      silently inert rule reads exactly like a working one, so it is asserted.
#   2. `base_reducts` matches AT THE TOP LEVEL only — a redex one level down is not found.
#   3. `subst1` is capture-UNAWARE by design ("binders live in the grammar, not the AST"). Asserted so
#      that a future capture-avoiding rewrite is a deliberate change to a failing test.
#
# AND ONE THING IS PINNED BECAUSE IT WAS A REAL DEFECT: a pattern variable must wear MeTTa's `$`
# sigil. Every rewrite in the first `mettail.metta` was written unsigiled and was therefore GROUND —
# well-formed, parsed, matched one literal term, inert. `_check_schematic` rejects that now, and the
# engine test is where it is demonstrated to matter rather than merely stated.
using MeTTaCore
using Test

const _RP = MeTTaCore.CompilerGSLTPresentation
const _RA = MeTTaCore.CompilerGSLTParse
const _RR = MeTTaCore.CompilerGSLTReduce
const _RS = MeTTaCore.StandardMeTTa
const _RV = MeTTaCore.Eval

"Parse a term the way a rule's sides are parsed — through MeTTa's reader, so `\$x` is a `Var`."
function _t(src::AbstractString)
    sp = _RV.Space()
    toks = _RV.tokenize(src)
    i = Ref(1)
    _RV.parse_from(toks, i, sp.tokens)
end

_lang_r(src::AbstractString) = _RA.parse_presentation(_t(src))

const _MPATH = joinpath(dirname(pathof(MeTTaCore)), "compiler", "gslt", "presentations",
    "mettail.metta")

@testset "GSLT reduction — the presentation engine" begin

    @testset "match_pat — first-order matching (Reduce.lean:28)" begin
        # A pattern variable matches any subterm.
        b = _RR.match_pat(_t("(App \$M \$N)"), _t("(App a (b c))"))
        @test b !== nothing
        @test b[:M] == _t("a")
        @test b[:N] == _t("(b c)")

        # …AND MUST MATCH CONSISTENTLY IF IT RECURS. This is the clause a hand-written matcher drops.
        @test _RR.match_pat(_t("(P \$X \$X)"), _t("(P a a)")) !== nothing
        @test _RR.match_pat(_t("(P \$X \$X)"), _t("(P a b)")) === nothing

        # Constructors match structurally; a differing label or arity fails.
        @test _RR.match_pat(_t("(App \$M)"), _t("(Lam a)")) === nothing
        @test _RR.match_pat(_t("(App \$M)"), _t("(App a b)")) === nothing

        # Everything else matches only itself — including a bare symbol, which is WHY the sigil
        # matters: unsigiled, `X` below is a constant and the pattern is ground.
        @test _RR.match_pat(_t("(f X)"), _t("(f X)")) !== nothing
        @test _RR.match_pat(_t("(f X)"), _t("(f a)")) === nothing

        # An empty binding set is a MATCH, not a failure — a ground pattern against itself.
        @test _RR.match_pat(_t("a"), _t("a")) == _RR.Bnds()
    end

    @testset "match_pat — the Subst node matches structurally, its variable must agree" begin
        @test _RR.match_pat(_t("(Subst \$b \$r x)"), _t("(Subst p q x)")) !== nothing
        @test _RR.match_pat(_t("(Subst \$b \$r x)"), _t("(Subst p q y)")) === nothing   # var disagrees
    end

    @testset "subst1 — plain replacement, capture-UNAWARE by design (Reduce.lean:49)" begin
        @test _RR.subst1(:x, _t("a"), _t("(f \$x (g \$x))")) == _t("(f a (g a))")
        @test _RR.subst1(:x, _t("a"), _t("(f \$y)")) == _t("(f \$y)")

        # The Subst node's own variable is NOT a binder in the term tree, so it is left alone while
        # body and replacement are rewritten through. Upstream, verbatim: "binders live in the
        # grammar, not the AST".
        @test _RR.subst1(:x, _t("a"), _t("(Subst \$x \$x x)")) == _t("(Subst a a x)")

        # CAPTURE IS NOT AVOIDED. Nothing in a term binds, so there is nothing to capture — but the
        # consequence is pinned here rather than assumed: substituting a term containing `$y` under a
        # position where `$y` also occurs does NOT rename.
        @test _RR.subst1(:x, _t("\$y"), _t("(f \$x \$y)")) == _t("(f \$y \$y)")
    end

    @testset "inst — instantiation RESOLVES Subst (Reduce.lean:63)" begin
        b = _RR.Bnds(:body => _t("(f \$x)"), :arg => _t("c"), :x => _t("\$x"))
        # (Subst body arg x) with x bound to the term variable $x ⇒ substitution targets THAT variable.
        @test _RR.inst(b, _t("(Subst \$body \$arg \$x)")) == _t("(f c)")

        # An unbound variable instantiates to itself.
        @test _RR.inst(_RR.Bnds(), _t("(f \$z)")) == _t("(f \$z)")

        # A bound pattern variable is replaced wherever it occurs, through nesting.
        @test _RR.inst(_RR.Bnds(:M => _t("a")), _t("(f (g \$M) \$M)")) == _t("(f (g a) a)")
    end

    @testset "apply_base_rewrite / base_reducts on LAMBDA — beta actually fires" begin
        # The presentation from `lambda.rs`, with LeaTTa's `Subst` built-in standing in for the Rust
        # surface's `eval`. If the sigil discipline is wrong anywhere, this testset is what fails.
        p = _lang_r(
            """
(language Lambda
  (types Term)
  (terms
    (: Lam (-> (bind x Term) (scope x Term) Term))
    (: App (-> Term Term Term)))
  (equations)
  (rewrites
    (rewrite Beta     ()             (~> (App (Lam \$x \$body) \$arg) (Subst \$body \$arg \$x)))
    (rewrite AppCongL ((~> \$M0 \$M1)) (~> (App \$M0 \$N) (App \$M1 \$N)))))
"""
        )

        beta = only(r for r in p.rewrites if r.name === :Beta)
        # (λv. (f v)) c  ⇝  (f c)
        @test _RR.apply_base_rewrite(beta, _t("(App (Lam \$v (f \$v)) c)")) == _t("(f c)")
        # The identity: (λv. v) c ⇝ c
        @test _RR.apply_base_rewrite(beta, _t("(App (Lam \$v \$v) c)")) == _t("c")
        # A non-redex yields nothing.
        @test _RR.apply_base_rewrite(beta, _t("(App f c)")) === nothing

        @test _RR.base_reducts(p, _t("(App (Lam \$v (f \$v)) c)")) == [_t("(f c)")]
        @test isempty(_RR.base_reducts(p, _t("(Lam \$v \$v)")))

        # LIMITATION 1 — a PREMISED rule never fires. AppCongL is a congruence rule and is inert.
        congl = only(r for r in p.rewrites if r.name === :AppCongL)
        @test _RR.apply_base_rewrite(congl, _t("(App (App (Lam \$v \$v) c) d)")) === nothing

        # LIMITATION 2 — TOP LEVEL ONLY. The redex below is one level down; with AppCongL inert there
        # is no congruence closure to reach it, so the term has NO reducts at all.
        @test isempty(_RR.base_reducts(p, _t("(App (App (Lam \$v \$v) c) d)")))
    end

    @testset "the SHIPPED presentation of MeTTa reduces" begin
        p = _RA.parse_presentation(_t(read(_MPATH, String)))

        fr = only(r for r in p.rewrites if r.name === :FunctionReturn)
        # (function (return X)) ⇝ X, for ANY X — which is only true because `$X` is sigiled. Before
        # the fix this rewrite matched the single literal term containing the symbol `X`.
        @test _RR.apply_base_rewrite(fr, _t("(function (return 42))")) == _t("42")
        @test _RR.apply_base_rewrite(fr, _t("(function (return (foo bar)))")) ==
            _t("(foo bar)")
        @test _RR.apply_base_rewrite(fr, _t("(function (bar baz))")) === nothing
        @test _RR.base_reducts(p, _t("(function (return a))")) == [_t("a")]

        # EVERY PREMISED RULE OF THE SHIPPED PRESENTATION IS INERT AT THIS LAYER. Asserted per-rule
        # rather than per-term, and that distinction is the lesson: this used to assert that a `chain`
        # term had no `base_reducts` at all, which stopped being true the moment `ChainSubst` — a BASE
        # rule about the same redex — was added. The claim worth keeping is about premises, not terms.
        for r in p.rewrites
            isempty(_RP.premises_of(r.rw)) && continue
            @test _RR.apply_base_rewrite(r, _t("(chain (function (return a)) \$v \$T)")) ===
                nothing
            @test _RR.apply_base_rewrite(r, _t("(function (return a))")) === nothing
        end
        @test length([r for r in p.rewrites if !isempty(_RP.premises_of(r.rw))]) == 2
    end

    @testset "an UNSIGILED pattern variable is REJECTED, not silently made ground" begin
        # The defect this check exists for, in the shape it actually occurred.
        @test_throws ErrorException _lang_r(
            "(language L (types T) (terms (: f (-> T T))) (rewrites (rewrite R () (~> (f X) X))))"
        )
        # …and the same thing on the RIGHT side, which produces a rule that discards its input.
        @test_throws ErrorException _lang_r(
            "(language L (types T) (terms (: f (-> T T))) (rewrites (rewrite R () (~> (f \$X) Y))))"
        )
        # …and in an equation.
        @test_throws ErrorException _lang_r(
            "(language L (types T) (terms (: f (-> T T))) (equations (equation E (f P) P)))"
        )
        # Sigiled, the same presentation is accepted and its rule is a real schema.
        q = _lang_r(
            "(language L (types T) (terms (: f (-> T T))) (rewrites (rewrite R () (~> (f \$X) \$X))))"
        )
        @test _RR.base_reducts(q, _t("(f anything)")) == [_t("anything")]
        # `Subst` needs no declaration — it is the ported AST's own node, not anyone's constructor.
        r = _lang_r(
            "(language L (types T) (terms (: f (-> T T T))) " *
            "(rewrites (rewrite R () (~> (f \$a \$b) (Subst \$a \$b \$a)))))"
        )
        @test length(r.rewrites) == 1
    end
end
