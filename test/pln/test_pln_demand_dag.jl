# test_pln_demand_dag.jl
# ─────────────────────────────────────────────────────────────────────────────
# §4.4 MAX-JOIN: the demand sweep on a DAG (a node reached by >1 path). Generalizes
# the tree sweep (test_pln_demand_sweep.jl) — `dem-join!` upserts dem := max(old,new)
# and recursion continues past a premise only when its demand INCREASES (monotone
# relaxation → converges on DAGs).
#
# Diamond:  C <- f0(P,Q);  P <- f1(S,X);  Q <- f2(S,Y).  S is shared by f1 and f2,
# so it is reached via two paths and must (a) keep exactly ONE (dem S _) atom (upsert,
# not duplicate-add) and (b) hold the MAX of the two path demands.
#
# Goldens produced by the validated max-join sweep (warm-REPL probe, 2026-06-23):
#   dem C=1.0, dem P=0.48124999999999996, dem Q=0.85, dem S=0.3305555555555555
#   viaP=0.24062499999999998, viaQ=0.3305555555555555  → dem S == max == viaQ.
# Claim (b) is also checked structurally (dem S == max(viaP,viaQ) recomputed from the
# threaded demands) so it does not rest on the hardcoded float alone.

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa

@testset "PLN demand sweep — DAG max-join (§4.4): dedup + max-over-paths" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(
        sp,
        read(
            joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_factor_graph.metta"), String
        )
    )

    load_metta!(
        sp,
        """
(message S (stv 0.9 0.5))
(message X (stv 0.8 0.9))
(message Y (stv 0.7 0.3))
(factor f1 hmp (premises S X) (conclusion P))
(factor f2 hmp (premises S Y) (conclusion Q))
(factor f0 hmp (premises P Q) (conclusion C))
(produces P f1)
(produces Q f2)
(produces C f0)
"""
    )
    load_metta!(sp, "!(compute-demand-field! C)")

    asserts = """
    !(assertEqual (match &self (dem C \$d) \$d) 1.0)
    !(assertEqual (match &self (dem P \$d) \$d) 0.48124999999999996)
    !(assertEqual (match &self (dem Q \$d) \$d) 0.85)
    !(assertEqual (match &self (dem S \$d) \$d) 0.3305555555555555)
    !(assertEqual (size-atom (collapse (match &self (dem S \$d) \$d))) 1)
    !(assertEqual (match &self (dem S \$d) \$d)
                  (max (dp-1 (factor-demand-pair P (match &self (dem P \$e) \$e)))
                       (dp-1 (factor-demand-pair Q (match &self (dem Q \$g) \$g)))))
    """
    rs = load_metta!(sp, asserts)
    errs = filter(
        r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs
    )
    @test isempty(errs)
    @test length(rs) == 6
end
