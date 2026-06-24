# test_pln_dtv.jl
# ─────────────────────────────────────────────────────────────────────────────
# §5 Layer-2 Distributional Truth Values (Beta DTVs in (μ,n) coords). Validated against
# the paper's §6.2 worked example (the Mammal/Lassie chain re-run with Beta DTVs):
#   p_A=Beta(19,2)=(μ,n)=(0.905,21), p_AB=(0.8,10), p_B=Beta(1,1)=(0.5,2), p_BC=(0.882,17).
# §6.2 exact intermediate values are the oracle:
#   need: A=0.047, AB=0.175, B=1.0, BC=0.069   (eq31)
#   forward μ_B = μ_A·μ_AB = 0.724              (the n_B the paper quotes as "≈12.3" is loose;
#                                                the moment-matched formula gives 12.815)
#   sensitivity at f2: ∂μ_C/∂μ_B=0.882, ∂μ_C/∂μ_BC=0.5
#   demand at f1 (boundary leaves, no threading divergence): dem_A=0.042, dem_AB=0.175
# Plus §5.7 STV-recovery: embedding an STV into a Beta and growing nc → μ→s, need→0.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa

_derrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

@testset "§5 Layer-2 DTV — Beta truth values vs §6.2 worked example" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))

    rs = load_metta!(sp, """
    ;; §5.3 need (eq31) — all four match §6.2
    !(assertEqual (need-dtv (dtv 0.9047619047619048 21.0)) 0.04700061842918985)
    !(assertEqual (need-dtv (dtv 0.8 10.0)) 0.17454545454545453)
    !(assertEqual (need-dtv (dtv 0.5 2.0)) 1.0)
    !(assertEqual (need-dtv (dtv 0.8823529411764706 17.0)) 0.06920415224913495)
    ;; §5.6 forward product (f1): μ_B = μ_A·μ_AB = 0.724 (exact); n_B moment-matched
    !(assertEqual (dtv-mu (fwd-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))) 0.7238095238095239)
    !(assertEqual (dtv-n  (fwd-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))) 12.814960629921467)
    ;; §5.4 sensitivity at f2: (spair μ_BC μ_B) = (0.882, 0.5)
    !(assertEqual (sens2-hmp-dtv (dtv 0.5 2.0) (dtv 0.8823529411764706 17.0)) (spair 0.8823529411764706 0.5))
    ;; §5.5 demand adjoint at f1 (dv=dem_B=1.0; A,AB boundary leaves) → dem_A=0.042, dem_AB=0.175
    !(assertEqual
       (adjoint2-dtv 1.0 (sens2-hmp-dtv (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0)) (dtv 0.9047619047619048 21.0) (dtv 0.8 10.0))
       (dpair 0.04155844155844156 0.17454545454545453))
    """)
    @test isempty(_derrs(rs)); @test length(rs) == 8

    # §5.7 STV-recovery limit: high nc ⇒ μ→s, need→~0 (DTV reduces to STV semantics)
    rs2 = load_metta!(sp, """
    !(assertEqual (> (dtv-mu (stv->dtv 0.9 0.999 1000.0)) 0.8999) True)
    !(assertEqual (< (dtv-mu (stv->dtv 0.9 0.999 1000.0)) 0.9001) True)
    !(assertEqual (< (need-dtv (stv->dtv 0.9 0.999 1000.0)) 0.001) True)
    """)
    @test isempty(_derrs(rs2)); @test length(rs2) == 3
end

@testset "§5 DTV demand sweep — supply + threading + DAG (vs §6.2 forward + internal consistency)" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))
    load_metta!(sp, """
    (message A (dtv 0.9047619047619048 21.0)) (message AB (dtv 0.8 10.0)) (message BC (dtv 0.8823529411764706 17.0))
    (factor f1 hmp (premises A AB) (conclusion B)) (factor f2 hmp (premises B BC) (conclusion C))
    (produces B f1) (produces C f2)
    """)
    # DTV-supply matches §6.2 forward μ_B = μ_A·μ_AB = 0.724
    rs = load_metta!(sp, "!(assertEqual (dtv-mu (supply-dtv B)) 0.7238095238095239)")
    @test isempty(_derrs(rs))
    load_metta!(sp, "!(compute-demand-field-dtv! C)")
    # internal consistency: dem(B) = the f2 adjoint at dv=1; dem(A) THREADS dem(B) as dv (not 1.0)
    rs2 = load_metta!(sp, """
    !(assertEqual (match &self (dem B \$d) \$d)
                  (dp-1 (adjoint2-dtv 1.0 (sens2-hmp-dtv (supply-dtv B) (supply-dtv BC)) (supply-dtv B) (supply-dtv BC))))
    !(assertEqual (match &self (dem A \$d) \$d)
                  (dp-1 (adjoint2-dtv (match &self (dem B \$e) \$e) (sens2-hmp-dtv (supply-dtv A) (supply-dtv AB)) (supply-dtv A) (supply-dtv AB))))
    """)
    @test isempty(_derrs(rs2)); @test length(rs2) == 2

    # DAG diamond: max-join reuse — exactly one (dem S _) atom, sweep terminates
    sp2 = Space(); load_core_stdlib!(sp2)
    load_metta!(sp2, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))
    load_metta!(sp2, """
    (message S (dtv 0.6 5.0)) (message X (dtv 0.8 5.0)) (message Y (dtv 0.7 5.0))
    (factor f1 hmp (premises S X) (conclusion P)) (factor f2 hmp (premises S Y) (conclusion Q)) (factor f0 hmp (premises P Q) (conclusion C))
    (produces P f1) (produces Q f2) (produces C f0)
    """)
    load_metta!(sp2, "!(compute-demand-field-dtv! C)")
    rs3 = load_metta!(sp2, "!(assertEqual (size-atom (collapse (match &self (dem S \$d) \$d))) 1)")
    @test isempty(_derrs(rs3))
end

@testset "§5.6 DTV term-logic — deduction sweep (forward-μ + threading + multi-hop)" begin
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))
    # forward μ = STV deduction strength on means (independently the chaining-repo formula)
    rs0 = load_metta!(sp, "!(assertEqual (fwd-mu-ded 0.8 0.7 0.9 0.85) 0.7749999999999999)")
    @test isempty(_derrs(rs0))

    # single-hop deduction demand sweep + internal consistency vs demand-quad-dtv
    load_metta!(sp, """
    (message B (dtv 0.8 8.0)) (message C (dtv 0.7 8.0)) (message AB (dtv 0.9 8.0)) (message BC (dtv 0.85 8.0))
    (factor fd deduction (premises B C AB BC) (conclusion G)) (produces G fd)
    """)
    load_metta!(sp, "!(compute-demand-field-dtv! G)")
    rs = load_metta!(sp, """
    !(assertEqual (match &self (dem B \$d) \$d)
                  (dq-1 (demand-quad-dtv 1.0 (sens-ded-dtv 0.8 0.7 0.9 0.85) (dtv 0.8 8.0)(dtv 0.7 8.0)(dtv 0.9 8.0)(dtv 0.85 8.0))))
    !(assertEqual (> (match &self (dem BC \$d) \$d) 0.0) True)
    """)
    @test isempty(_derrs(rs)); @test length(rs) == 2

    # multi-hop: deduction premise B produced by hmp → demand recurses past deduction to x1
    sp2 = Space(); load_core_stdlib!(sp2)
    load_metta!(sp2, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))
    load_metta!(sp2, """
    (message C (dtv 0.7 8.0)) (message AB (dtv 0.9 8.0)) (message BC (dtv 0.85 8.0))
    (message x1 (dtv 0.9 8.0)) (message x2 (dtv 0.8 8.0))
    (factor fd deduction (premises B C AB BC) (conclusion G)) (factor fb hmp (premises x1 x2) (conclusion B))
    (produces G fd) (produces B fb)
    """)
    load_metta!(sp2, "!(compute-demand-field-dtv! G)")
    rs2 = load_metta!(sp2, "!(assertEqual (> (match &self (dem x1 \$d) \$d) 0.0) True)")
    @test isempty(_derrs(rs2))
end

@testset "§5.6 DTV term-logic — inversion/induction/abduction/negation sweeps" begin
    function _dscen(graph, query, asserts)
        sp = Space(); load_core_stdlib!(sp)
        load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "pln", "pln_factor_graph.metta"), String))
        load_metta!(sp, graph); load_metta!(sp, "!(compute-demand-field-dtv! $query)")
        load_metta!(sp, asserts)
    end
    @testset "inversion (3-premise) demand reaches premises" begin
        rs = _dscen("(message iA (dtv 0.7 8.0)) (message iB (dtv 0.6 8.0)) (message iBA (dtv 0.8 8.0)) (factor fi inversion (premises iA iB iBA) (conclusion GI)) (produces GI fi)",
            "GI", "!(assertEqual (> (match &self (dem iA \$d) \$d) 0.0) True)\n!(assertEqual (> (match &self (dem iBA \$d) \$d) 0.0) True)")
        @test isempty(_derrs(rs)); @test length(rs) == 2
    end
    @testset "induction (5-premise) demand reaches premises" begin
        rs = _dscen("(message uA (dtv 0.7 8.0)) (message uB (dtv 0.6 8.0)) (message uC (dtv 0.5 8.0)) (message uBA (dtv 0.8 8.0)) (message uBC (dtv 0.75 8.0)) (factor fu induction (premises uA uB uC uBA uBC) (conclusion GU)) (produces GU fu)",
            "GU", "!(assertEqual (> (match &self (dem uC \$d) \$d) 0.0) True)")
        @test isempty(_derrs(rs))
    end
    @testset "abduction (5-premise) — sens_A=0 ⇒ dem aA=0, others propagate" begin
        rs = _dscen("(message aA (dtv 0.7 8.0)) (message aB (dtv 0.6 8.0)) (message aC (dtv 0.5 8.0)) (message aAB (dtv 0.8 8.0)) (message aCB (dtv 0.75 8.0)) (factor fa abduction (premises aA aB aC aAB aCB) (conclusion GA)) (produces GA fa)",
            "GA", "!(assertEqual (match &self (dem aA \$d) \$d) 0.0)\n!(assertEqual (> (match &self (dem aB \$d) \$d) 0.0) True)")
        @test isempty(_derrs(rs)); @test length(rs) == 2
    end
    @testset "negation (1-premise) demand reaches premise" begin
        rs = _dscen("(message np (dtv 0.4 8.0)) (factor fn negation (premises np) (conclusion GN)) (produces GN fn)",
            "GN", "!(assertEqual (> (match &self (dem np \$d) \$d) 0.0) True)")
        @test isempty(_derrs(rs))
    end
end
