# test_subrep.jl
# ─────────────────────────────────────────────────────────────────────────────
# SubRep Cone-Dominant Subtask (CDS) admission gate — lib/subrep/cds.metta (MVP-0).
# The option-admission stage of the §4 goal loop: admit an option only if it beats
# the baseline for EVERY motive weight in the slice (uniform improvement).
#
# Source: docs/specs/Subrep/SubRep_spec.md §2.2 (CDS), §3.2 (simplex form),
#   §11.11 (box no-LP support fn), §2.2.5 (robust margin), §11.17 (MVP-0);
#   docs/research/papers/Subrep/SubRep-Minecraft-AIRIS_v2_2.pdf §3.2 + §5.2 options;
#   reference impl ~/PRIMUS/dev-zone/subrep/certification/cds_test.py.
#
# Runs on the Interpreter (same evaluator as quantale/PLN/ECAN). Tests are
# DISCRIMINATING — each flips a real admit↔reject decision, not just non-empty
# output. Float-inexact quantities are asserted via the boolean admit (robust);
# only float-exact values are asserted directly.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.StandardMeTTa
include(joinpath(@__DIR__, "assert_guard.jl"))

const _CDS = joinpath(@__DIR__, "..", "lib", "subrep", "cds.metta")
const _PDS = joinpath(@__DIR__, "..", "lib", "subrep", "pds.metta")
const _STORE = joinpath(@__DIR__, "..", "lib", "subrep", "store.metta")
const _ATTN = joinpath(@__DIR__, "..", "lib", "subrep", "attention.metta")
const _CAT = joinpath(@__DIR__, "..", "lib", "subrep", "category.metta")
const _ANY = joinpath(@__DIR__, "..", "lib", "subrep", "anytime.metta")
const _GEN = joinpath(@__DIR__, "..", "lib", "subrep", "generators.metta")
const _MC = joinpath(@__DIR__, "..", "lib", "subrep", "motive_cone.metta")
const _EASA = joinpath(@__DIR__, "..", "lib", "subrep", "easa.metta")
const _WF = joinpath(@__DIR__, "..", "lib", "subrep", "waveformer.metta")

_serrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

function _setup_subrep()
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(_CDS, String))     # CDS gate + vector prims + vertex cone + certificate
    load_metta!(sp, read(_PDS, String))     # PDS gates (depend on cds.metta)
    load_metta!(sp, read(_STORE, String))   # atom-native certificate storage + zero-shot reuse
    load_metta!(sp, read(_ATTN, String))    # conservative attention (runtime allocation)
    load_metta!(sp, read(_CAT, String))     # §8 categorical backbone (join + CDS⊣PDS adjunction)
    load_metta!(sp, read(_ANY, String))     # §2.4 anytime gate + §2.3.7 conformal certificates
    load_metta!(sp, read(_GEN, String))     # §4 cross-paradigm generators (uniform (r̂,n̂) screening)
    load_metta!(sp, read(_MC, String))      # end-to-end: consume the MDN's (motive-cone …) atom
    load_metta!(sp, read(_EASA, String))    # §9 EASA — fuzzy-guarded chart gluing, certified
    load_metta!(sp, read(_WF, String))      # §11 Waveformer — budget-weighted attention routing
    sp
end

@testset "SubRep CDS/PDS gates + atom-native certificate storage — Minimal-native" begin
    # Negative control: prove _serrs + assertEqual DISCRIMINATE on this harness,
    # so the count-guarded asserts below cannot be silently vacuous.
    let sp = Space()
        load_core_stdlib!(sp)
        assert_harness_discriminates(e -> load_metta!(sp, e), rs -> !isempty(_serrs(rs)); label = "subrep/Minimal")
    end

    @testset "vector primitives + backed-up value (§1)" begin
        sp = _setup_subrep()
        # vdot wᵀn = 1·0.5 + 2·0.5 = 1.5 ; backed-up = 2.0 + 1.5 = 3.5 (float-exact)
        rs = load_metta!(sp, """
        !(assertEqual (vdot (1 2) (0.5 0.5)) 1.5)
        !(assertEqual (backed-up 2.0 (0.5 0.5) (1 2)) 3.5)
        !(assertEqual (vmin (0.30 0.0 -0.05)) -0.05)
        !(assertEqual (delta-n (0.5 0.0) (0.25 0.5)) (0.25 -0.5))
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 4
    end

    @testset "simplex CDS — uniform improvement over the whole cone (§3.2)" begin
        sp = _setup_subrep()
        # Minecraft §5.2 options (Δr=0): O13 TradeMenuHotkeys Δn=(…,+0.02,…) has
        # min≥0 ⟹ CDS ADMITS (paper says so); O11 TorchCorridor Δn has a −0.05
        # reputation cost ⟹ min<0 ⟹ CDS REJECTS (a single coordinate "pays").
        rs = load_metta!(sp, """
        !(assertEqual (cds-margin-simplex 0.0 (0.0 0.0 0.02 0.0 0.0 0.0)) 0.0)
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (0.0 0.0 0.02 0.0 0.0 0.0)) 0.0) True)
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (0.30 0.0 -0.05 0.0 -0.02 0.15)) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "box-cone CDS — restricting the motive slice changes admission (§11.11)" begin
        sp = _setup_subrep()
        # dn=(safety +0.30, reputation −0.05). Over the full simplex the −0.05
        # rejects; but a box that ZEROES the reputation weight ([0,0]) and keeps
        # safety ([0,1]) drops the negative term ⟹ ADMIT. CDS depends on the cone.
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (0.30 -0.05)) 0.0) False)
        !(assertEqual (cds-margin-box 0.0 (0.30 -0.05) (0.0 0.0) (1.0 0.0)) 0.0)
        !(assertEqual (cds-admit (cds-margin-box 0.0 (0.30 -0.05) (0.0 0.0) (1.0 0.0)) 0.0) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "box-cone CDS — paper §2.2.9 worked micro-example" begin
        sp = _setup_subrep()
        # Δr̂=+2.0, Δn̂_h=−0.04, W={0≤w_h≤80}: m_o = 2.0 + 80·(−0.04) = −1.2 ⟹ FAILS
        # (the roundabout's tiny per-step cost, scaled by the worst weight, sinks it).
        # Asserted via the boolean (float-inexact 80·−0.04), which is robust.
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit (cds-margin-box 2.0 (-0.04) (0.0) (80.0)) 0.0) False)
        !(assertEqual (cds-admit (cds-margin-box 2.0 (0.10) (0.0) (1.0)) 0.0) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 2
    end

    @testset "robust margin — uncertainty cushion flips a marginal admit (§2.2.5)" begin
        sp = _setup_subrep()
        # A boundary admit (m=0.0, ε=0) becomes a REJECT once model-error cushions
        # ε_r=0.01, ε_n=0.02 (k=1) are subtracted: m_rob = −0.03 < 0.
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit 0.0 0.0) True)
        !(assertEqual (cds-admit (cds-margin-robust 0.0 0.01 0.02 1.0) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 2
    end

    @testset "end-to-end: admit option vs baseline (§2.2)" begin
        sp = _setup_subrep()
        # option (r̂=1.0, n̂=(0.5 0.5)) vs baseline (0.5, (0.25 0.25)): Δr=0.5,
        # Δn=(0.25 0.25) ⟹ margin 0.75 ⟹ ADMIT. A second option whose Δn has a
        # −0.5 coordinate and only Δr=0.25 ⟹ margin −0.25 ⟹ REJECT.
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit-simplex 1.0 (0.5 0.5) 0.5 (0.25 0.25) 0.0) True)
        !(assertEqual (cds-admit-simplex 0.75 (0.5 0.0) 0.5 (0.25 0.5) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 2
    end

    @testset "general cone via vertices + auditable certificate" begin
        sp = _setup_subrep()
        # worst-case motive over explicit vertices (unit basis = the simplex) = min_i Δn_i.
        # Certificate records (gate, Δr, Δn, margin, ε, admit): CDS 0.5/(0.25 0.25) ⟹
        # margin 0.75, admit; PDS-ε 0.0/(1.0 −0.5)/ε=0.5 ⟹ margin 0.0, admit (boundary).
        rs = load_metta!(sp, """
        !(assertEqual (cds-margin-vertices 0.0 (0.30 -0.05) ((1 0) (0 1))) -0.05)
        !(assertEqual (cds-cert 0.5 (0.25 0.25) 0.0) (subrep-cert CDS 0.5 (0.25 0.25) 0.75 0.0 True))
        !(assertEqual (pds-eps-cert 0.0 (1.0 -0.5) 0.5) (subrep-cert PDS 0.0 (1.0 -0.5) 0.0 0.5 True))
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "PDS-ε — cone-budget relaxation of CDS (§3.2 Def 2 / iCog pds_test)" begin
        sp = _setup_subrep()
        # Option with a worst coordinate Δn=−0.3: CDS rejects (margin −0.3); PDS-ε
        # admits iff the ε budget covers it (ε≥0.3) and rejects when it doesn't.
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (1.0 -0.3)) 0.0) False)
        !(assertEqual (pds-eps-admit 0.0 (1.0 -0.5) 0.5) True)
        !(assertEqual (pds-eps-admit 0.0 (1.0 -0.5) 0.1) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "PDS cover — admits complementary options CDS rejects (§2.3 / §5.6)" begin
        sp = _setup_subrep()
        # Option A helps motive-1 (+1.0) but slightly hurts motive-2 (−0.3); cover =
        # unit weights w¹=(1 0), w²=(0 1) ⟹ gaps (1.0 −0.3). CDS rejects (min<0); but
        # budgeted PDS (ε=0.05, ρ=0.5, q=0.5): −0.3 is within ρ, one component clears ε,
        # coverage 1 ≥ 0.5·2 ⟹ ADMIT — the complementary-option win CDS can't see.
        rs = load_metta!(sp, """
        !(assertEqual (vlen ((1 0) (0 1))) 2)
        !(assertEqual (all-geq (1.0 -0.3) -0.5) True)
        !(assertEqual (count-geq (1.0 -0.3) 0.05) 1)
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (1.0 -0.3)) 0.0) False)
        !(assertEqual (pds-cover-admit 0.0 (1.0 -0.3) 0.0 (0 0) ((1 0) (0 1)) 0.05 0.5 0.5) True)
        !(assertEqual (pds-cover-admit 0.0 (1.0 -0.8) 0.0 (0 0) ((1 0) (0 1)) 0.05 0.5 0.5) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 6
    end

    @testset "atom-native storage + zero-shot reuse under motive shift (§5.9 / Phase 4)" begin
        sp = _setup_subrep()
        # Two certified skills stored AS ATOMS: A favours motive-1, B favours motive-2.
        load_metta!(sp, """
        !(store-admitted! skillA 0.0 (1.0 -0.2))
        !(store-admitted! skillB 0.0 (-0.2 1.0))
        """)
        # Zero-shot reuse: re-value the SAME stored atoms under shifted motive weights —
        # under motive-1 weight (1 0) skill A wins; shift to motive-2 (0 1) and B wins,
        # with NO recertification (the certificates are re-queried, not recomputed).
        rs = load_metta!(sp, """
        !(assertEqual (skill-value-by-id skillA (1 0)) 1.0)
        !(assertEqual (skill-value-by-id skillB (1 0)) -0.2)
        !(assertEqual (reuse-under-weight (1 0) 0.0) (skillA))
        !(assertEqual (reuse-under-weight (0 1) 0.0) (skillB))
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 4
    end

    @testset "conservative attention — conserved margin-proportional allocation (§10)" begin
        sp = _setup_subrep()
        # equal margins → equal conserved split (exact); the highest-margin option gets
        # the most attention; total allocation = A_total (conservation, Σ a(o)=A_total).
        rs = load_metta!(sp, """
        !(assertEqual (attention-alloc (0.0 0.0) 1.0 1.0) (0.5 0.5))
        !(assertEqual (> (car-atom (attention-alloc (1.0 0.0 -1.0) 1.0 1.0)) 0.5) True)
        !(assertEqual (within (lsum (attention-alloc (2.0 0.5 -1.0) 4.0 1.0)) 4.0 0.001) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "theoretical guarantees — join-safety + monotone persistence (§7)" begin
        sp = _setup_subrep()
        # Prop 7.1 (join-safety): a CDS-admitted option (margin ≥ 0) DOMINATES the
        # baseline backed-up value at every weight in the cone, so adding it can never
        # lower the planner's max. Option (1.0,(0.5 0.5)) vs baseline (0.5,(0.25 0.25)):
        # margin 0.75 ≥ 0 ⟹ B_o(w) ≥ B_base(w) at each tested vertex weight.
        # Prop 7.2 (monotone persistence): a TIGHTER cone W₂⊆W₁ yields a margin ≥ that of
        # W₁ — so as the MDN tightens the geometry, prior admissions persist (margins rise).
        rs = load_metta!(sp, """
        !(assertEqual (cds-admit (cds-margin-simplex 0.5 (0.25 0.25)) 0.0) True)
        !(assertEqual (>= (backed-up 1.0 (0.5 0.5) (1 0)) (backed-up 0.5 (0.25 0.25) (1 0))) True)
        !(assertEqual (>= (backed-up 1.0 (0.5 0.5) (0 1)) (backed-up 0.5 (0.25 0.25) (0 1))) True)
        !(assertEqual (>= (cds-margin-box 0.0 (0.30 -0.05) (0 0) (0.5 0.5)) (cds-margin-box 0.0 (0.30 -0.05) (0 0) (1 1))) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 4
    end

    @testset "categorical backbone — planner join + CDS⊣PDS adjunction (§8)" begin
        sp = _setup_subrep()
        # planner join ⋁_o T_o = per-state max over options' backed-up values;
        # F: box cone [0,u] → its extreme rays (axis vertices u_i·e_i);
        # CDS⊣PDS adjunction (Thm 8.8): CDS over the cone EQUALS CDS over its extreme
        # rays (inf over the box = min over the axis vertices) — so the cone test and
        # the finite vertex-cover test coincide.
        rs = load_metta!(sp, """
        !(assertEqual (transformer-join (0.5 1.2 0.8)) 1.2)
        !(assertEqual (cone-extreme-rays (1.0 0.5)) ((1.0 0) (0 0.5)))
        !(assertEqual (cds-margin-via-rays 0.0 (0.30 -0.05) (1.0 0.5)) (cds-margin-box 0.0 (0.30 -0.05) (0 0) (1.0 0.5)))
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "anytime gate (§2.4) + conformal certificates (§2.3.7)" begin
        sp = _setup_subrep()
        # §2.4 anytime: a clearly-negative cached-ray margin (over-estimate of the true
        # inf) decisively REJECTS cheaply (−0.5); an inconclusive cached margin falls
        # through to the exact box solve (−0.025 for Δn=(0.30 −0.05)).
        # §2.3.7 conformal: subtract the 0.9-quantile of calibration residuals (0.1) — a
        # margin 0.15 survives (admit), but 0.08 (within the calibration noise) is rejected.
        rs = load_metta!(sp, """
        !(assertEqual (anytime-margin 0.0 (-0.5 -0.5) ((1 0)) (0 0) (1 1) 0.1) -0.5)
        !(assertEqual (anytime-margin 0.0 (0.30 -0.05) ((1 0)) (0 0) (1 1) 0.1) (cds-margin-box 0.0 (0.30 -0.05) (0 0) (1 1)))
        !(assertEqual (quantile (0.01 0.02 0.05 0.1) 0.9) 0.1)
        !(assertEqual (>= (conformal-margin 0.15 (0.01 0.02 0.05 0.1) 0.9) 0.0) True)
        !(assertEqual (>= (conformal-margin 0.08 (0.01 0.02 0.05 0.1) 0.9) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 5
    end

    @testset "cross-paradigm generators — (r̂,n̂) screened uniformly (§4)" begin
        sp = _setup_subrep()
        # A LOGIC macro and an EVO program, each exporting an (r̂,n̂) summary, screened by
        # the SAME CDS gate. The logic macro helps both motives (admit); the evo program
        # hurts motive-2 badly (reject) — same algebra, paradigm (KIND) is metadata only.
        load_metta!(sp, """
        !(store-generator! logicMacro LOGIC 1.0 (0.5 0.5))
        !(store-generator! mosesProg EVO 0.5 (0.3 -0.4))
        """)
        rs = load_metta!(sp, """
        !(assertEqual (gen-summary logicMacro) (1.0 (0.5 0.5)))
        !(assertEqual (screen-generator logicMacro 0.5 (0.25 0.25) 0.0) True)
        !(assertEqual (screen-generator mosesProg 0.5 (0.25 0.25) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "end-to-end — Core gate consumes the MDN's (motive-cone …) atom (§2.4)" begin
        sp = _setup_subrep()
        # The FabricPC MDN learned cone for the "raid" context is exactly this atom
        # (examples/subrep_mdn.jl emits (motive-cone raid (lo 0.0 0.0) (hi 1.0 0.2))).
        # The Core gate consumes it: a safety-favouring option (helps motive-1, hurts
        # motive-2) is ADMITTED under the learned cone but REJECTED by the naive simplex
        # — the MDN's co-learned geometry, carried by the atom, enables the admission.
        load_metta!(sp, "!(store-cone! raid (0.0 0.0) (1.0 0.2))")
        rs = load_metta!(sp, """
        !(assertEqual (lookup-cone raid) ((0.0 0.0) (1.0 0.2)))
        !(assertEqual (admit-under-cone raid 0.0 (0.3 -0.2) 0.05) True)
        !(assertEqual (cds-admit (cds-margin-simplex 0.0 (0.3 -0.2)) 0.0) False)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end

    @testset "EASA — fuzzy-guarded chart gluing stays certified (§9)" begin
        sp = _setup_subrep()
        # Two CDS-certified charts (chart1 helps both motives; chart2 helps motive-1) are
        # glued by EQUAL fuzzy guards (softmax of equal scores = (0.5 0.5)) into a composite
        # (r̂,n̂). Each chart admits, AND the blended atlas admits — composition of certified
        # charts stays certified (the §9 gluing preserves the CDS certificate).
        rs = load_metta!(sp, """
        !(assertEqual (guard2 1.0 1.0 1.0) (0.5 0.5))
        !(assertEqual (easa-blend2 0.5 0.5 1.0 (0.5 0.5) 0.5 (0.5 0.25)) (0.75 (0.5 0.375)))
        !(assertEqual (cds-admit-simplex 1.0 (0.5 0.5) 0.5 (0.25 0.25) 0.0) True)
        !(assertEqual (cds-admit-simplex 0.5 (0.5 0.25) 0.5 (0.25 0.25) 0.0) True)
        !(assertEqual (easa-admit2 0.5 0.5 1.0 (0.5 0.5) 0.5 (0.5 0.25) 0.5 (0.25 0.25) 0.0) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 5
    end

    @testset "Waveformer control plane — budget-weighted attention (§11.5)" begin
        sp = _setup_subrep()
        # Two keys with EQUAL raw logits (1.0 1.0) but very different conservative-attention
        # budgets (1.0 vs 0.001): the budget routes the attention so the high-budget key
        # gets almost all the weight (> 0.99) and the negligible-budget key is suppressed
        # (anti-spam). Equal budgets → equal split (conservation Σ=1).
        rs = load_metta!(sp, """
        !(assertEqual (budget-weighted-attn (1.0 1.0) (1.0 1.0) 0.0001) (0.5 0.5))
        !(assertEqual (> (car-atom (budget-weighted-attn (1.0 1.0) (1.0 0.001) 0.0001)) 0.99) True)
        !(assertEqual (within (lsum (budget-weighted-attn (2.0 0.5 1.0) (1.0 0.5 0.2) 0.0001)) 1.0 0.001) True)
        """)
        @test isempty(_serrs(rs)); @test length(rs) == 3
    end
end
