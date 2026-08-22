# test_gslt_context.jl — reduction closed under CONTEXT, and premised rules FIRING.
#
# Two files under test, and they sit on opposite sides of a line that matters:
#
#   `Context.jl`   a PORT of `Semantics/{Context,Normal,Eval}.lean` — machine-checked upstream, so
#                  these tests are regression locks on the transcription.
#   `Relation.jl`  an ADDITION above upstream's executable layer (upstream leaves conditional
#                  rewriting as a Prop and says so). It inherits no proof, so it is tested against
#                  BEHAVIOUR: what the rules mean, and — in `test_mettail_presentation.jl` — against
#                  the interpreter.
#
# THE FOUR PROPERTIES WORTH STATING, each because getting it wrong is silent:
#   1. LEFTMOST-OUTERMOST, in that order. Upstream's `oneStep_sound` is proved against this exact
#      traversal; a reordering still "works" on most terms and quietly voids the citation.
#   2. `has_redex` AGREES with `one_step` being non-nothing. Upstream proves it
#      (`oneStep_isSome_eq_hasRedex`); we write the two separately, so agreement is the cheapest
#      signal that the transcription has drifted.
#   3. A NORMAL FORM AND AN EXHAUSTED BUDGET MUST NOT LOOK ALIKE. `normalize` returns residual fuel
#      and `reducts_exhausted()` reports depth exhaustion, precisely so a truncated search cannot
#      read as "nothing more applies".
#   4. AN EXPRESSION HEAD IS A SUBTERM. Lean's `.sexp` label is a String and cannot hold one, so this
#      case has no upstream answer; `((f a) b)` is legal MeTTa and the redex inside must be reachable.
using MeTTaCore
using Test

const _CP = MeTTaCore.CompilerGSLTPresentation
const _CA = MeTTaCore.CompilerGSLTParse
const _CR = MeTTaCore.CompilerGSLTReduce
const _CC = MeTTaCore.CompilerGSLTContext
const _CL = MeTTaCore.CompilerGSLTRelation
const _CV = MeTTaCore.Eval

function _ct(src::AbstractString)
    sp = _CV.Space()
    toks = _CV.tokenize(src)
    i = Ref(1)
    _CV.parse_from(toks, i, sp.tokens)
end
_clang(src::AbstractString) = _CA.parse_presentation(_ct(src))

"A one-rule arithmetic-shaped theory: `(f \$X) ~> \$X`. Enough to observe WHERE a step happens."
const _UNWRAP = _clang(
    "(language Unwrap (types T) (terms (: f (-> T T)) (: g (-> T T T))) " *
    "(rewrites (rewrite R () (~> (f \$X) \$X))))")

@testset "GSLT context closure + conditional rewriting" begin

    @testset "one_step — the redex is found BELOW the root now" begin
        # `Reduce.base_reducts` sees nothing here; that is the whole reason this file exists.
        t = _ct("(g (f a) b)")
        @test isempty(_CR.base_reducts(_UNWRAP, t))
        @test _CC.one_step(_UNWRAP, t) == _ct("(g a b)")

        # …and at the root, where it must still behave exactly as before.
        @test _CC.one_step(_UNWRAP, _ct("(f a)")) == _ct("a")

        # No redex anywhere ⇒ nothing.
        @test _CC.one_step(_UNWRAP, _ct("(g a b)")) === nothing
        @test _CC.one_step(_UNWRAP, _ct("a")) === nothing
    end

    @testset "OUTERMOST first, then LEFTMOST — the order `oneStep_sound` is proved against" begin
        # OUTERMOST: the root redex wins over the one nested inside it. `(f (f a))` could step to
        # `(f a)` (root) or to `(f a)` (inner) — indistinguishable, so use a rule that keeps a marker.
        p = _clang(
            "(language O (types T) (terms (: f (-> T T)) (: h (-> T T))) " *
            "(rewrites (rewrite R () (~> (f \$X) (h \$X)))))"
        )
        @test _CC.one_step(p, _ct("(f (f a))")) == _ct("(h (f a))")     # ROOT stepped, not the inner

        # LEFTMOST: with two sibling redexes, the first argument goes first.
        @test _CC.one_step(_UNWRAP, _ct("(g (f a) (f b))")) == _ct("(g a (f b))")
    end

    @testset "an EXPRESSION head is a subterm — a case Lean's String label cannot express" begin
        # `((f a) b)`: the redex is in child 1. Skipping the head, as the literal port would, makes it
        # permanently unreachable — a silent gap, not fidelity.
        @test _CC.one_step(_UNWRAP, _ct("((f a) b)")) == _ct("(a b)")
        @test _CC.has_redex(_UNWRAP, _ct("((f a) b)"))

        # A SYMBOL head is a label and is NOT rewritten: `f` alone is not a redex of `(f $X) ~> $X`,
        # and nothing may fire on the head position of `(f a)` other than the whole-term match.
        @test _CC.one_step(_UNWRAP, _ct("f")) === nothing
    end

    @testset "the traversal descends into a Subst's body and replacement, never its variable" begin
        @test _CC.one_step(_UNWRAP, _ct("(Subst (f a) r x)")) == _ct("(Subst a r x)")
        @test _CC.one_step(_UNWRAP, _ct("(Subst b (f a) x)")) == _ct("(Subst b a x)")
        # body BEFORE replacement, as upstream orders it
        @test _CC.one_step(_UNWRAP, _ct("(Subst (f a) (f b) x)")) ==
            _ct("(Subst a (f b) x)")
        # the substituted variable is not a position — `(f a)` there would be a malformed Subst, so
        # the case that matters is that a matching NAME in slot 4 is left alone
        @test _CC.one_step(_UNWRAP, _ct("(Subst p q f)")) === nothing
    end

    @testset "has_redex AGREES with one_step — upstream's `oneStep_isSome_eq_hasRedex`" begin
        for src in
            ("(g (f a) b)", "(f a)", "(g a b)", "a", "((f a) b)", "(Subst (f a) r x)",
            "(Subst p q x)", "()", "(g (g (f a) b) c)")
            t = _ct(src)
            @test _CC.has_redex(_UNWRAP, t) == (_CC.one_step(_UNWRAP, t) !== nothing)
            @test _CC.is_normal(_UNWRAP, t) == !_CC.has_redex(_UNWRAP, t)
        end
    end

    @testset "normalize — and the residual fuel that keeps a normal form distinguishable" begin
        t, left = _CC.normalize(_UNWRAP, _ct("(g (f (f a)) (f b))"))
        @test t == _ct("(g a b)")
        @test left > 0                       # STOPPED BECAUSE NORMAL

        # Exactly three steps were available, so a budget of 3 suffices and 2 does not.
        @test _CC.normalize(_UNWRAP, _ct("(g (f (f a)) (f b))"); fuel=3) ==
            (_ct("(g a b)"), 0)
        t2, left2 = _CC.normalize(_UNWRAP, _ct("(g (f (f a)) (f b))"); fuel=2)
        @test left2 == 0
        @test t2 != _ct("(g a b)")           # STOPPED BECAUSE OUT OF FUEL — and it is visible

        # A NON-TERMINATING presentation must return, not hang. `(f $X) ~> (f (f $X))` grows forever.
        loop = _clang(
            "(language Loop (types T) (terms (: f (-> T T))) " *
            "(rewrites (rewrite R () (~> (f \$X) (f (f \$X))))))"
        )
        _, lf = _CC.normalize(loop, _ct("(f a)"); fuel=8)
        @test lf == 0
        @test_throws ArgumentError _CC.normalize(_UNWRAP, _ct("(f a)"); fuel=-1)
    end

    # ── Relation.jl — THE ADDITION. Everything below is beyond what upstream executes. ─────────────

    @testset "reducts — a PREMISED rule fires, which `base_reducts` cannot do" begin
        # Beta plus a congruence rule: `AppCong` may only fire when its premise `$M0 ~> $M1` holds,
        # i.e. when the function position itself reduces.
        p = _clang(
            """
 (language Cong
   (types T)
   (terms (: Lam (-> (bind x T) (scope x T) T)) (: App (-> T T T)))
   (equations)
   (rewrites
     (rewrite Beta    ()             (~> (App (Lam \$x \$body) \$arg) (Subst \$body \$arg \$x)))
     (rewrite AppCong ((~> \$M0 \$M1)) (~> (App \$M0 \$N) (App \$M1 \$N)))))
 """
        )
        redex = _ct("(App (Lam \$v \$v) c)")            # ⇝ c by Beta
        nested = _ct("(App (App (Lam \$v \$v) c) d)")    # AppCong's premise is the Beta step above

        @test isempty(_CR.base_reducts(p, nested))         # the OLD behaviour, still true
        @test _CL.reducts(p, nested) == [_ct("(App c d)")] # the NEW one: the premise discharged
        @test !_CL.reducts_exhausted()

        # A premise that CANNOT be discharged blocks the rule — the property that makes it conditional
        # rather than unconditional-with-extra-steps.
        @test isempty(_CL.reducts(p, _ct("(App stuck d)")))

        # And a base rule still reduces exactly as `Reduce.jl` says, through the same entry point.
        @test _CL.reducts(p, redex) == _CR.base_reducts(p, redex) == [_ct("c")]
    end

    @testset "premises_hold — one binding set per way the premises can be satisfied" begin
        p = _clang("""
        (language Multi
          (types T)
          (terms (: f (-> T T)) (: g (-> T T)) (: c (-> T T)))
          (equations)
          (rewrites
            (rewrite A ()              (~> (f \$X) \$X))
            (rewrite B ()              (~> (f \$X) (g \$X)))
            (rewrite C ((~> \$S \$T2)) (~> (c \$S) (c \$T2)))))
        """)
        # `(f a)` has TWO reducts, so C's premise holds two ways and `(c (f a))` has two reducts.
        @test length(_CL.reducts(p, _ct("(f a)"))) == 2
        rs = _CL.reducts(p, _ct("(c (f a))"))
        @test Set(rs) == Set([_ct("(c a)"), _ct("(c (g a))")])

        # premises_hold directly: bindings extend with the premise TARGET bound to the reduct.
        cdecl = only(r for r in p.rewrites if r.name === :C)
        b = _CR.match_pat(_CP.conclusion_of(cdecl.rw)[1], _ct("(c (f a))"))
        @test b !== nothing
        exts = _CL.premises_hold(p, _CP.premises_of(cdecl.rw), b, 8)
        @test length(exts) == 2
        @test all(e -> haskey(e, :T2), exts)
        @test Set(e[:T2] for e in exts) == Set([_ct("a"), _ct("(g a)")])
    end

    @testset "DEPTH EXHAUSTION IS REPORTED, not silently returned as `no rule applies`" begin
        # A congruence rule whose premise is discharged by the SAME rule one level in. Premise
        # discharge is structurally decreasing — the source is always a bound SUBTERM — so the only
        # way to exhaust the budget is a term nested deeper than it, which is exactly this.
        deep = _clang(
            "(language Deep (types T) (terms (: c (-> T T))) " *
            "(rewrites (rewrite C ((~> \$S \$T2)) (~> (c \$S) (c \$T2)))))"
        )
        nest(n) = "(c "^n * "x" * ")"^n
        @test isempty(_CL.reducts(deep, _ct(nest(8)); depth=3))
        @test _CL.reducts_exhausted()                      # ← the distinction that must survive

        # Shallow enough to finish: no rule applies at the bottom, and the flag stays DOWN.
        @test isempty(_CL.reducts(deep, _ct(nest(2)); depth=16))
        @test !_CL.reducts_exhausted()

        # Contrast: genuinely no applicable rule, at full depth. Same empty list, different flag.
        @test isempty(_CL.reducts(_UNWRAP, _ct("(g a b)")))
        @test !_CL.reducts_exhausted()

        @test_throws ArgumentError _CL.reducts(_UNWRAP, _ct("(f a)"); depth=0)
    end

    @testset "cond_step / cond_normalize — the SAME traversal, premises enabled" begin
        p = _clang("""
        (language CN
          (types T)
          (terms (: f (-> T T)) (: c (-> T T)) (: g (-> T T T)))
          (equations)
          (rewrites
            (rewrite A ()              (~> (f \$X) \$X))
            (rewrite C ((~> \$S \$T2)) (~> (c \$S) (c \$T2)))))
        """)
        # Below the root AND premised at once — neither `base_reducts` nor `reducts` alone gets there.
        t = _ct("(g (c (f a)) b)")
        @test isempty(_CL.reducts(p, t))                   # not a root redex
        @test _CC.one_step(p, t) == _ct("(g (c a) b)")     # base traversal reaches `(f a)` directly
        @test _CL.cond_step(p, t) == _ct("(g (c a) b)")    # C at `(c (f a))` is outermost ⇒ same term
        @test _CL.cond_normalize(p, _ct("(c (f a))"))[1] == _ct("(c a)")
        @test _CL.cond_normalize(p, t)[2] > 0              # reached a normal form, fuel to spare
    end
end
