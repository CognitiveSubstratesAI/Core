# test_pln_ecan.jl
# ─────────────────────────────────────────────────────────────────────────────
# §4.9 PLN↔ECAN co-working — "demand as backward attention".
#
# Proves PLN and ECAN are co-working cognitive algorithms over ONE faithful evaluator
# (Minimal): PLN's backward DEMAND field drives ECAN's STI via the source's damped +
# budget-normalized channel. NO Julia primitives — ECAN's normalize-attention! is native
# MeTTa (core_logic.metta), so PLN + ECAN run on the same evaluator. Libraries are
# loaded ON-DEMAND (the import! subset model, cross-checked faithful to hyperon/CeTTa/PeTTa).
#
# Golden = the closed-form §4.9 EMA (no oracle implements it; PLNDemand.jl stops at the
# demand field): STI_new = (1-ρ)·STI_old + ρ·d̂,  ρ=0.5. Binary-exact values ⇒ the float
# assert is precise, not laundered.
#   T1 EMA golden       — (1-0.5)·0.5 + 0.5·0.25 = 0.375 exactly.
#   T2 budget normalize — normalize-attention! 1000 over {1,3} → {250,750}, Σ=1000 conserved.
#   T3 demand→attention — equal init STI, higher-demand atom ends with strictly higher STI.
#   T4 bounded converge — iterate the coupling; Σ STI stays at budget (the §4.9 anti-positive-
#                         feedback property — damping + normalize bound the demand↔attention loop).
#   T5 full co-work tick — pln-attention-tick! over a real PLN graph: demand field → attention,
#                          query + premise receive STI on ONE evaluator (the integration proof).

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
include(joinpath(@__DIR__, "..", "assert_guard.jl"))   # silent-test guard (shared convention)

const _ECAN = joinpath(@__DIR__, "..", "..", "lib", "ecan", "core_logic.metta")
const _POL  = joinpath(@__DIR__, "..", "..", "lib", "ecan", "ECAN_Policies.metta")
const _FG   = joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_factor_graph.metta")
const _CPL  = joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_ecan_coupling.metta")
const _PLNCORE = joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_core_logic.metta")

_eerrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

# on-demand subset: stdlib + ECAN core/policies + §4.9 coupling (NO PLN graph)
function _setup_ecan()
    sp = Space(); load_core_stdlib!(sp)
    load_metta!(sp, read(_ECAN, String))
    load_metta!(sp, read(_POL, String))
    load_metta!(sp, read(_CPL, String))
    sp
end
# full co-work: + the PLN factor graph (for pln-attention-tick!)
_setup_full() = (sp = _setup_ecan(); load_metta!(sp, read(_FG, String)); sp)

# Negative control (silent-test guard): the PLN tests gate on `_eerrs` over the Eval harness +
# `@test length(rs) == N`. This proves `_eerrs` + the Minimal `assertEqual` actually DISCRIMINATE
# (a known mismatch is flagged, a known match is not) — so the count-guarded asserts below are not
# silently vacuous. Representative for the PLN suite (all share the Minimal `load_metta!`/`_eerrs`
# pattern). See test/assert_guard.jl.
let sp = Space()
    load_core_stdlib!(sp)
    assert_harness_discriminates(e -> load_metta!(sp, e), rs -> !isempty(_eerrs(rs)); label = "PLN/Minimal")
end

@testset "§4.9 PLN↔ECAN co-working — demand as backward attention" begin
    @testset "T1 EMA golden — STI_new=(1-ρ)·STI_old+ρ·d̂" begin
        sp = _setup_ecan()
        load_metta!(sp, "!(set-sti! A 0.5)")
        load_metta!(sp, "!(add-atom &self (dem A 0.25))")
        load_metta!(sp, "!(demand->sti! A)")
        rs = load_metta!(sp, "!(assertEqual (get-sti A) 0.375)")
        @test isempty(_eerrs(rs)); @test length(rs) == 1
    end

    @testset "T2 budget normalize — Σ STI = target, conserved" begin
        sp = _setup_ecan()
        load_metta!(sp, "!(set-sti! X 1.0)")
        load_metta!(sp, "!(set-sti! Y 3.0)")
        load_metta!(sp, "!(normalize-attention! 1000.0)")
        rs = load_metta!(sp, "!(assertEqual (get-sti X) 250.0)\n!(assertEqual (get-sti Y) 750.0)")
        @test isempty(_eerrs(rs)); @test length(rs) == 2
    end

    @testset "T3 demand→attention — higher demand ⇒ strictly higher STI" begin
        sp = _setup_ecan()
        load_metta!(sp, "!(set-sti! P 0.2)")
        load_metta!(sp, "!(set-sti! Q 0.2)")
        load_metta!(sp, "!(add-atom &self (dem P 0.8))")
        load_metta!(sp, "!(add-atom &self (dem Q 0.1))")
        load_metta!(sp, "!(couple-demand->attention!)")
        rs = load_metta!(sp, "!(assertEqual (< (get-sti Q) (get-sti P)) True)")
        @test isempty(_eerrs(rs)); @test length(rs) == 1
    end

    @testset "T4 bounded convergence — Σ STI stays at budget under iteration" begin
        sp = _setup_ecan()
        # foldl-atom is a special form — its list arg must be a bound var (eval'd), not an inline
        # call (ECAN's normalize-attention! binds via let too). Inline → unevaluated → folds nothing.
        load_metta!(sp, "(= (total-sti) (let \$ids (get-all-av-atoms) (foldl-atom \$ids 0.0 \$acc \$id (+ \$acc (get-sti \$id)))))")
        load_metta!(sp, "!(set-sti! P 0.2)")
        load_metta!(sp, "!(set-sti! Q 0.2)")
        load_metta!(sp, "!(add-atom &self (dem P 0.8))")
        load_metta!(sp, "!(add-atom &self (dem Q 0.1))")
        load_metta!(sp, "!(couple-demand->attention!)")
        load_metta!(sp, "!(couple-demand->attention!)")
        load_metta!(sp, "!(couple-demand->attention!)")
        rs = load_metta!(sp, "!(assertEqual (and (< 999.0 (total-sti)) (< (total-sti) 1001.0)) True)")
        @test isempty(_eerrs(rs)); @test length(rs) == 1
    end

    @testset "T5 full co-work tick — pln-attention-tick! demand→attention end-to-end" begin
        sp = _setup_full()
        load_metta!(sp, """
        (message A (stv 0.95 0.95)) (message AB (stv 0.99 0.80))
        (factor f1 hmp (premises A AB) (conclusion B)) (produces B f1)
        """)
        load_metta!(sp, "!(pln-attention-tick! B 0.0)")
        rs = load_metta!(sp, "!(assertEqual (< 0.0 (get-sti B)) True)\n!(assertEqual (< 0.0 (get-sti A)) True)")
        @test isempty(_eerrs(rs)); @test length(rs) == 2
    end

    # The REVERSE half of the synergy: ECAN attention → PLN inference priority.
    # PLN.Derive's PriorityRank blends confidence with STI (0.5·c + 0.5·STI/100).
    # Un-stubbed (the 0.0 get-sti stub was removed) so ECAN's real get-sti drives it.
    @testset "T6 ECAN→PLN — attention raises PriorityRank (un-stub, no shadowing)" begin
        sp = Space(); load_core_stdlib!(sp)
        load_metta!(sp, read(_ECAN, String))        # ecan core: real get-sti
        load_metta!(sp, read(_PLNCORE, String))     # PLN.Derive (get-sti stub REMOVED)
        load_metta!(sp, "!(set-sti! hi 50.0)")      # `hi` gets attention; `lo` has none (get-sti→0)
        rhi = load_metta!(sp, "!(PriorityRank (Sentence (hi (stv 0.6 0.5)) ev))")
        rlo = load_metta!(sp, "!(PriorityRank (Sentence (lo (stv 0.6 0.5)) ev))")
        @test length(rhi) == 1 && length(rlo) == 1  # single result — stub no longer shadows ECAN
        # hi = 0.5·0.5 + 0.5·(50/100) = 0.5 ; lo = 0.25 + 0 = 0.25  (attention raised priority)
        rs = load_metta!(sp, "!(assertEqual (PriorityRank (Sentence (hi (stv 0.6 0.5)) ev)) 0.5)\n!(assertEqual (PriorityRank (Sentence (lo (stv 0.6 0.5)) ev)) 0.25)")
        @test isempty(_eerrs(rs)); @test length(rs) == 2
    end
end
