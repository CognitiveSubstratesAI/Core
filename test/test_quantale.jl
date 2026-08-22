# test_quantale.jl
# ─────────────────────────────────────────────────────────────────────────────
# Quantale foundation (lib/quantale/quantale.metta) — the commutative-quantale
# substrate every cognitive kernel shares (PLN truth, MOSES variation/weakness,
# Occam cost). Substrate-native port from PRIMUS_Core, corrected per
# docs/specs/Quantale/quantale_spec.md + docs/specs/Mork/MORK_MOSES_spec.md §9.
#
# All tests run on the Eval (the 234/234 hyperon-faithful engine) —
# same evaluator as PLN/ECAN, so the quantale lib genuinely co-works with them.
#
# Axioms checked (quantale_spec §8 checklist + §9 numeric cases):
#   Q_prob distributivity + unit            (quantale axioms)
#   Q_cost distributivity + unit            (tropical Occam)
#   Q_PLN PAIRED (n+,n-) add/product/unit   §4.4.1, §9 cases 5-6  ⭐ the real Q_PLN
#   Q_CDL ↔ Q_PLN isomorphism Φ             §4.4.2, §9 case 7
#   program-cost (total leaf count) + CoDD weakness W9   §5.5, w(h)=N·2^-σ(h)
#   weakness morphism additivity (CoDD recurrence σ(⊗ p q)=σp+σq+1)   §6.1.2
#   Axiom W1/W3 Bennett recovery: μ≡1 ⇒ w(H)=|H|   §2.8

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
include(joinpath(@__DIR__, "assert_guard.jl"))   # silent-test guard (shared convention)

const _QUANT = joinpath(@__DIR__, "..", "lib", "quantale", "quantale.metta")

_qerrs(rs) = filter(
    r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs
)

function _setup_quantale()
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(_QUANT, String))
    load_metta!(sp, "(= (c1 \$x) 1)")   # constant measure μ≡1 for Bennett weakness
    sp
end

# Negative control (silent-test guard): proves `_qerrs` + Minimal `assertEqual` DISCRIMINATE,
# so the count-guarded asserts below are not silently vacuous on this harness.
let sp = Space()
    load_core_stdlib!(sp)
    assert_harness_discriminates(
        e -> load_metta!(sp, e), rs -> !isempty(_qerrs(rs)); label="quantale/Minimal"
    )
end

@testset "Quantale foundation — Minimal-native" begin
    @testset "Q_prob (scalar [0,1], ×, max, 1) — quantale axioms" begin
        sp = _setup_quantale()
        # distributivity a×max(b,c)=max(a×b,a×c); unit a×1=a; residuum a⊸b=min(1,b/a)
        rs = load_metta!(
            sp,
            """
!(assertEqual (q-prob-times 0.5 (q-prob-join 0.25 0.75)) (q-prob-join (q-prob-times 0.5 0.25) (q-prob-times 0.5 0.75)))
!(assertEqual (q-prob-times 0.5 (q-prob-unit)) 0.5)
!(assertEqual (q-prob-resid 0.5 1.0) 1.0)
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 3
    end

    @testset "Q_cost (R≥0, +, min, 0) — tropical Occam" begin
        sp = _setup_quantale()
        # distributivity a+min(b,c)=min(a+b,a+c); unit a+0=a
        rs = load_metta!(
            sp,
            """
!(assertEqual (q-cost-times 2 (q-cost-join 3 5)) (q-cost-join (q-cost-times 2 3) (q-cost-times 2 5)))
!(assertEqual (q-cost-times 7.5 (q-cost-unit)) 7.5)
!(assertEqual (q-cost-resid 2.0 5.0) 3.0)
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 3
    end

    @testset "Q_PLN PAIRED (n+,n-) — §4.4.1 / §9 cases 5-6  ⭐" begin
        sp = _setup_quantale()
        # ⊕ adds evidence counts; ⊗ multiplies; unit (1,1); unit⊗p=p
        rs = load_metta!(
            sp,
            """
!(assertEqual (q-pln-join (ev 2.0 1.0) (ev 3.0 2.0)) (ev 5.0 3.0))
!(assertEqual (q-pln-times (ev 2.0 1.0) (ev 3.0 2.0)) (ev 6.0 2.0))
!(assertEqual (q-pln-unit) (ev 1.0 1.0))
!(assertEqual (q-pln-times (q-pln-unit) (ev 2.0 3.0)) (ev 2.0 3.0))
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 4
    end

    @testset "Q_CDL pair + Φ : Q_CDL→Q_PLN isomorphism — §4.4.2 / §9 case 7" begin
        sp = _setup_quantale()
        # CDL ⊕=(max,min), ⊗=(min,max); Φ(x,x')=(N·x,N·x'), N=5
        rs = load_metta!(
            sp,
            """
!(assertEqual (q-cdl-join (ev 1.0 4.0) (ev 3.0 2.0)) (ev 3.0 2.0))
!(assertEqual (q-cdl-times (ev 1.0 4.0) (ev 3.0 2.0)) (ev 1.0 4.0))
!(assertEqual (phi-cdl->pln 5 (ev 0.4 0.2)) (ev 2.0 1.0))
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 3
    end

    @testset "program-cost + CoDD weakness W9 — §5.5" begin
        sp = _setup_quantale()
        # total leaf count; codd-weakness w(h)=N/2^σ(h): foo→16/2=8
        rs = load_metta!(
            sp,
            """
!(assertEqual (program-cost foo) 1)
!(assertEqual (program-cost (Compose foo bar)) 3)
!(assertEqual (program-cost (f (g x))) 3)
!(assertEqual (codd-weakness foo 16) 8.0)
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 4
    end

    @testset "weakness morphism additivity — CoDD recurrence σ(⊗ p q)=σp+σq+1 (§6.1.2)" begin
        sp = _setup_quantale()
        # w : q-prog → q-cost is a morphism: cost(Compose p q) = cost(p) + cost(q) + c_compose,
        # with the Compose combinator head as unit cost (c=1). foo,bar leaves ⇒ 1+1+1=3.
        rs = load_metta!(
            sp,
            """
!(assertEqual (program-cost (q-prog-times foo bar)) (+ (q-cost-times (program-cost foo) (program-cost bar)) 1))
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 1
    end

    @testset "Axiom W1/W3 Bennett recovery — μ≡1 ⇒ w(H)=|H| (§2.8)" begin
        sp = _setup_quantale()
        # 3-element set, all 9 ordered pairs, constant measure 1 ⇒ weakness = 9 (= |H|)
        rs = load_metta!(
            sp,
            """
!(assertEqual (weakness ((P a a)(P a b)(P a c)(P b a)(P b b)(P b c)(P c a)(P c b)(P c c)) c1) 9)
"""
        )
        @test isempty(_qerrs(rs))
        @test length(rs) == 1
    end
end
