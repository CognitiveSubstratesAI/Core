# test_pln_dtv_hist.jl
# ─────────────────────────────────────────────────────────────────────────────
# §5.1 / §5.3 histogram DTV — the exact finite representation. A histogram (w1 … wK) on a
# uniform [0,1] grid; need = normalized Shannon entropy (eq32); hist->dtv moment-matches to a
# Beta (μ,n) so a histogram premise plugs into the Layer-2/3 DTV machinery (§5.2).
# Validated against known information theory (uniform ⇒ need 1, peaked ⇒ 0) and exact moments.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

_herrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

@testset "§5.1/§5.3 histogram DTV — need (eq32) + moments + Beta projection" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_factor_graph.metta"), String))
    rs = load_metta!(sp, """
    ;; eq32 Shannon-entropy need: uniform ⇒ 1, peaked ⇒ 0
    !(assertEqual (< (absf (- (need-hist (0.25 0.25 0.25 0.25)) 1.0)) 0.0001) True)
    !(assertEqual (need-hist (1.0 0.0 0.0 0.0)) 0.0)
    !(assertEqual (< (absf (- (need-hist (0.5 0.5)) 1.0)) 0.0001) True)
    ;; moments over bin centers (k−0.5)/K: uniform mean=0.5, all-last-bin mean=0.875
    !(assertEqual (< (absf (- (hist-mean (0.25 0.25 0.25 0.25)) 0.5)) 0.0001) True)
    !(assertEqual (< (absf (- (hist-mean (0.0 0.0 0.0 1.0)) 0.875)) 0.0001) True)
    ;; §5.2 projection: (0.1 0.2 0.4 0.3) has mean exactly 0.6 → feeds need-dtv
    !(assertEqual (< (absf (- (dtv-mu (hist->dtv (0.1 0.2 0.4 0.3))) 0.6)) 0.0001) True)
    !(assertEqual (> (need-dtv (hist->dtv (0.1 0.2 0.4 0.3))) 0.0) True)
    """)
    @test isempty(_herrs(rs)); @test length(rs) == 7
end
