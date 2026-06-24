# test_pln_forward_maps.jl
# ─────────────────────────────────────────────────────────────────────────────
# FIRST regression coverage of lib/pln's BOOK forward truth-value maps (Truth_*).
#
# Why this file exists: prior to it, lib/pln's `Truth_*` forward maps were UNTESTED
# in Core's suite — the conformance harness (test/standard/test_conformance.jl) loads
# only stdlib.metta + CoreExtensions.metta, and c3_pln_stv.metta is self-contained
# (it defines its own `TV` metarules and never calls `Truth_*`). So the entire PLN
# book forward layer carried zero regression coverage.
#
# What it pins: the BOOK contract. lib/pln is the system-of-record (PLN-book formulas,
# with weight-of-evidence confidence via Truth_c2w/Truth_w2c). The demand-driven Layer-1
# oracle (MorkSupercompiler/src/mgfw/PLNDemand.jl, the `fwd_*` maps) is the §3.4 SIMPLIFIED
# approximation the sensitivity layer rides on. They AGREE on strength, DIVERGE on
# confidence (book c2w/w2c vs §3.4 simple products):
#
#   map          | lib/pln BOOK (contract, pinned here) | §3.4 approx (oracle fwd_*)
#   ─────────────┼──────────────────────────────────────┼───────────────────────────
#   ModusPonens  | (0.7856, 0.40476)                    | (0.783, 0.68)   ← conf diverges
#   Negation     | (0.2, 0.9)                           | (0.2, 0.9)      ← agree
#   inversion    | (0.6, 0.432)                         | eq 6/12
#   Revision     | (0.769, 0.684)                       | (book-only: evidence pooling)
#
# A THIRD MP variant lives in the mgfw §15.4 lowering (HeuristicMP: strength=As*Is,
# confidence=min(Ac,Ic)*0.9) — to be aligned/documented when the demand chain is ported.
# Conjunction also has three treatments (book interval smallest/largest-intersection;
# c3's fuzzy min/min; oracle product/noisy-OR eq21) — pinned separately when consolidated.
#
# Values below are execution-derived (Core via the warm evaluator) and were each confirmed
# to pass as `assertEqual` before being committed here.

using Test
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa          # Space, load_metta!, Expression, Sym, …

@testset "PLN forward maps — book contract (lib/pln Truth_*)" begin
    sp = Space()
    load_core_stdlib!(sp)                                   # stdlib + CoreExtensions (grounds *, binary min, …)
    pln_dir = joinpath(@__DIR__, "..", "..", "lib", "pln")
    load_metta!(sp, read(joinpath(pln_dir, "stv.metta"), String))
    load_metta!(sp, read(joinpath(pln_dir, "pln_core_logic.metta"), String))

    # Each directive is `(assertEqual <book-map-call> <pinned-golden>)`; a passing assert
    # yields () and a failure yields an (Error …) expression — counted exactly as the
    # conformance harness does (test_conformance.jl:37).
    goldens = """
    !(assertEqual (Truth_Negation (stv 0.8 0.9)) (stv 0.19999999999999996 0.9))
    !(assertEqual (Truth_ModusPonens (stv 0.87 0.85) (stv 0.9 0.8)) (stv 0.7856000000000001 0.40476190476190477))
    !(assertEqual (Truth_inversion (stv 0.7 0.9) (stv 0.6 0.8)) (stv 0.6 0.432))
    !(assertEqual (Truth_Revision (stv 0.8 0.6) (stv 0.7 0.4)) (stv 0.7692307692307692 0.6842105263157895))
    """
    rs = load_metta!(sp, goldens)
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    @test isempty(errs)
    @test length(rs) == 4          # all four directives ran (guards against silent load failure)
end
