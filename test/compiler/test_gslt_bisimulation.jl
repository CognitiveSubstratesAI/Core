# GSLT Definition 2.2 — bisimilarity over the one-step relation, and the bisimilarity-preserving
# term map Meredith calls a morphism.
#
# ─── WHY THIS FILE EXISTS ────────────────────────────────────────────────────────────────────────
# `Multicategory.jl:46` declines the **Definition 5.1** morphism (a pseudofunctor of context
# multicategories, bisimulation-preserving for CONTEXT-LABELLED transitions) because this tree has no
# labelled transition system for a presentation to be bisimilar in. That decline is correct and
# stands. What it does NOT mean — and was being read to mean — is that no morphism is available.
#
# Verified 2026-08-19 against the machine-checked Lean formalisation at
# `dev-zone/MeTTapedia/lean/mettapedia/Mettapedia/GSLT/Core/GSLT.lean`: **Definition 2.2** needs no
# labels, no contexts and no multicategory. Their `GSLT` is structurally our `GPresentation` (terms ·
# equations · rewrites) and their `Step` is `rewrites` RAW, not equation-closed (`GSLT.lean:72`) —
# which is our `reducts`.
#
# ⚠️ EVERY ASSERTION BELOW HAS A NEGATIVE TWIN, DELIBERATELY. A bisimulation checker that only ever
# returns `true` is indistinguishable from `f(x) = true`, and this is exactly the shape of test that
# would not notice. So each capability is pinned by a case it must ACCEPT and a case it must REJECT.

using MeTTaCore
using Test

const _BA = MeTTaCore.CompilerGSLTParse
const _BV = MeTTaCore.Eval
const _BB = MeTTaCore.CompilerGSLTBisimulation
const _BR = MeTTaCore.CompilerGSLTRelation
const _BS = MeTTaCore.StandardMeTTa

_bterm(src::AbstractString) =
    (sp=_BV.Space(); toks=_BV.tokenize(src); i=Ref(1); _BV.parse_from(toks, i, sp.tokens))
_blang(src::AbstractString) = _BA.parse_presentation(_bterm(src))

# Two unary constructors that both reduce to their argument, plus a nullary constant.
# ⚠️ Constants are NULLARY ARROWS — `(: a (-> T))`, used as the term `(a)`. `(: a T)` is rejected by
# the parser ("signature of `a` must be (-> … Result)"), which cost one probe to discover.
const _BP = _blang(
    "(language Two (types T) (terms (: f (-> T T)) (: g (-> T T)) (: a (-> T))) " *
    "(rewrites (rewrite RF () (~> (f \$X) \$X)) (rewrite RG () (~> (g \$X) \$X))))")

const _FA = _bterm("(f (a))")
const _GA = _bterm("(g (a))")
const _AA = _bterm("(a)")

@testset "GSLT Def 2.2 — bisimilarity over the one-step relation" begin

    @testset "the step relation is what Lean calls Step" begin
        # ANTI-VACUITY. Every claim below is about `reducts`; if it returned nothing, a bisimulation
        # checker would report everything bisimilar and every test here would pass for the wrong
        # reason.
        @test _BR.reducts(_BP, _FA) == _BS.Atom[_AA]
        @test _BR.reducts(_BP, _GA) == _BS.Atom[_AA]
        @test isempty(_BR.reducts(_BP, _AA))          # `(a)` is a normal form — nothing to observe
    end

    @testset "is_bisimulation ACCEPTS a genuine witness and REJECTS a broken one" begin
        # `(f (a))` and `(g (a))` both step to `(a)` and nowhere else, so this relation is closed
        # under steps in both directions.
        good = _BB.BisimWitness([(_FA, _GA), (_AA, _AA)])
        @test _BB.is_bisimulation(_BP, good)

        # 🔴 THE REJECTION IS THE LOAD-BEARING HALF. `(f (a))` steps; `(a)` does not. Pairing a redex
        # with a normal form cannot be a bisimulation, and a checker that misses this is checking
        # nothing.
        bad = _BB.BisimWitness([(_FA, _AA)])
        @test !_BB.is_bisimulation(_BP, bad)
    end

    @testset "a failure names the unmatched step AND its direction" begin
        # A bare `false` is nearly useless when debugging a presentation. The counterexample must say
        # which step had no partner and which way the matching failed.
        cx = _BB.bisim_counterexample(_BP, _BB.BisimWitness([(_FA, _AA)]))
        @test cx !== nothing
        (t, u, unmatched, dir) = cx
        @test t === _FA && u === _AA
        @test unmatched == _AA          # `(f (a)) → (a)` is the step `(a)` cannot match
        @test dir === :forward
        # …and a genuine witness yields no counterexample at all
        @test _BB.bisim_counterexample(_BP, _BB.BisimWitness([(_FA, _GA), (_AA, _AA)])) ===
            nothing
    end

    @testset "bounded bisimilarity separates what it must, and is honest about depth 0" begin
        @test _BB.bisimilar_bounded(_BP, _FA, _GA; steps=4)      # same observations
        @test !_BB.bisimilar_bounded(_BP, _FA, _AA; steps=4)     # redex vs normal form
        # 🔴 `steps = 0` IS VACUOUSLY TRUE BY CONSTRUCTION — the empty observation separates nothing.
        # Asserted rather than left implicit, because a caller passing 0 learns exactly nothing and
        # the `true` looks like a result.
        @test _BB.bisimilar_bounded(_BP, _FA, _AA; steps=0)
    end

    @testset "a Def 2.2 morphism is CHECKED, and a collapsing map is refuted" begin
        carrier = _BS.Atom[_FA, _GA, _AA]
        @test _BB.morphism_preserves_bisim(
            _BB.GMorphism(_BP, _BP, identity, carrier); steps=4
        )

        # 🔴 THE REFUTATION. A map sending `(f (a))` to `(a)` destroys an observation: the source pair
        # `((f (a)), (g (a)))` is inseparable, but their images `(a)` and `(g (a))` are not. This is
        # the naive term-map `Multicategory.jl`'s header refutes, and the checker must catch it.
        collapse(t) = string(t) == "(f (a))" ? _AA : t
        @test !_BB.morphism_preserves_bisim(
            _BB.GMorphism(_BP, _BP, collapse, carrier); steps=4
        )
    end

    @testset "this is NOT Definition 5.1, and the distinction is asserted" begin
        # Def 5.1 needs a pseudofunctor over CONTEXT MULTICATEGORIES with CONTEXT-LABELLED
        # transitions. Nothing here supplies one, and `Multicategory.jl` still declines it. Pinned so
        # that "we have a GSLT morphism" is never read as "we have Def 5.1" — the Lean side agrees the
        # context machinery cannot be derived generically (`Logic/MinimalContext.lean` introduces a
        # `HasMinimalContexts` INTERFACE instead).
        @test isdefined(MeTTaCore, :CompilerGSLTMulticategory)
        @test !isdefined(_BB, :pseudofunctor)
        @test !isdefined(_BB, :context_labelled_transition)
    end
end
