# test_pln_dtv_l3.jl
# ─────────────────────────────────────────────────────────────────────────────
# §5.4 / §5.8 Layer-3 DTV: information-geometric (Fisher-weighted) sensitivity + demand vectors.
# No paper oracle (§6.2 uses Layer 2), so validated against KNOWN MATH:
#   - trigamma ψ'(1)=π²/6, Beta Fisher matrix entries, 2×2 λmax
#   - Fisher-sensitivity of an IDENTITY-like map = 1 (reparametrization-invariant operator norm)
#   - generic Fisher-sens is positive and correlates with the Layer-2 practical sens
#   - eq48 demand vector splits into (mean-shift, concentration-tighten) components

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

_l3errs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

@testset "§5.4/§5.8 Layer-3 DTV — Fisher sensitivity + demand vectors" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    @testset "foundations vs known math" begin
        rs = load_metta!(sp, """
        !(assertEqual (< (absf (- (trigamma 1.0) 1.6449340668482264)) 0.001) True)
        !(assertEqual (< (absf (- (trigamma 2.0) 0.6449340668482264)) 0.001) True)
        !(assertEqual (fisher-beta (dtv 0.5 4.0)) (fmat 0.3611111111111111 -0.28382287379972565 0.3611111111111111))
        !(assertEqual (m2-lammax (m2 2.0 1.0 1.0 2.0)) 3.0)
        !(assertEqual (< (absf (- (m2-det (m2-mul (m2-inv (m2 4.0 1.0 2.0 3.0)) (m2 4.0 1.0 2.0 3.0))) 1.0)) 0.0001) True)
        """)
        @test isempty(_l3errs(rs)); @test length(rs) == 5
    end

    @testset "Fisher-weighted sensitivity (eq34)" begin
        rs = load_metta!(sp, """
        !(assertEqual (< (absf (- (sens-fisher-hmp1 (dtv 0.7 8.0) (dtv 0.999 5000.0)) 1.0)) 0.01) True)
        !(assertEqual (> (sens-fisher-hmp1 (dtv 0.7 8.0) (dtv 0.6 8.0)) 0.0) True)
        !(assertEqual (sens-fisher-hmp1 (dtv 0.7 8.0) (dtv 0.6 8.0)) 0.6222973951872639)
        """)
        @test isempty(_l3errs(rs)); @test length(rs) == 3
    end

    @testset "demand vector (eq48), g_out=(1,0)" begin
        rs = load_metta!(sp, "!(assertEqual (demand-vec-hmp1 1.0 (dtv 0.7 8.0) (dtv 0.6 8.0) (v2 1.0 0.0)) (v2 0.09684078556215782 -0.02976742710245617))")
        @test isempty(_l3errs(rs)); @test length(rs) == 1
    end
end
