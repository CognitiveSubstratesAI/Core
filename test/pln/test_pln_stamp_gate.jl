# test_pln_stamp_gate.jl
# ─────────────────────────────────────────────────────────────────────────────
# The evidence-overlap gate (lib/pln/pln_core_logic.metta): InsertionSort canonicalises a
# stamp; StampDisjoint (:493-497) is the ONLY thing licensing Truth_Revision's `w = w1 + w2`
# (:275-282). If the gate is wrong, revision adds evidence it is not entitled to add.
#
# WHY THIS FILE EXISTS — a regression lock on a real bug that shipped unnoticed:
# `InsertionSort` called `(msort $L)`, and **`msort` was undefined repo-wide** (a single grep
# hit: its own call site), with our own working recursive impl commented out directly below.
# It silently returned the UNREDUCED term `(msort (s1 s2))`, so every derived sentence's stamp
# (built at :502 / :553) was malformed. Nothing caught it because NOTHING TESTED THIS GATE —
# hence these tests. Observed failure, both directions:
#   · derived-vs-derived: StampDisjoint((msort (s1 s2)), (msort (s3 s4))) = False on fully
#     DISJOINT evidence — both stamps contain the symbol `msort`, so every pair "overlaps" and
#     legitimate revision is blocked  ⇒ INFERENCE STARVATION.
#   · seed-vs-derived:    StampDisjoint((s1), (msort (s1 s2)))            = True although `s1`
#     is in BOTH — it is nested inside the unreduced term, so superpose never sees it. The gate
#     fails OPEN and licenses double-counting ⇒ EVIDENCE FABRICATION.
# Found by auditing our PLN against Goertzel's ωPLN law catalogue
# (docs/specs/omegaclaw/omegapln_implementation_v3_spec.md §26.2/Appendix C); the fabrication
# direction is exactly ωPLN Prop 7.1's D_dc > 0 (the same token counted m_u = 2 times).
#
# NOTE ON SCOPE: PLN.Derive (:545-567), the only consumer of this gate, currently has no
# callers — the live WorldModel goal-loop path carries no stamps at all. So these are tests of
# a CORRECT-BUT-DORMANT mechanism: they protect the gate for whoever wires it in.

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa

@testset "PLN evidence-overlap gate — stamp canonicalisation + StampDisjoint" begin
    sp = Space()
    load_core_stdlib!(sp)
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "lib", "pln", "pln_core_logic.metta"), String))

    _errs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

    # (1) InsertionSort must actually SORT — not return an unreduced term. The `msort` regression:
    #     any result still shaped `(msort …)` means the undefined call is back.
    sorts = """
    !(assertEqual (InsertionSort (3 1 2) ()) (1 2 3))
    !(assertEqual (InsertionSort (s3 s1 s2) ()) (s1 s2 s3))
    !(assertEqual (InsertionSort () ()) ())
    !(assertEqual (InsertionSort (s1) ()) (s1))
    """
    rs = load_metta!(sp, sorts)
    @test isempty(_errs(rs))
    @test length(rs) == 4

    # (2) Canonicalisation is the POINT of sorting: stamp equality must not depend on premise
    #     order, or StampDisjoint's overlap test is order-sensitive.
    rs = load_metta!(sp, "!(assertEqual (InsertionSort (s2 s1) ()) (InsertionSort (s1 s2) ()))")
    @test isempty(_errs(rs))

    # (3) A DERIVED stamp (the :553 shape) must be a flat, sorted tuple — this is the exact
    #     expression whose malformation broke the gate.
    rs = load_metta!(sp, "!(assertEqual (InsertionSort (TupleConcat (s1) (s2)) ()) (s1 s2))")
    @test isempty(_errs(rs))

    # (4) NO STARVATION — disjoint evidence must be revisable (gate says True).
    starve = """
    !(assertEqual (StampDisjoint (s1) (s2)) True)
    !(assertEqual (StampDisjoint (s1 s2) (s3 s4)) True)
    """
    rs = load_metta!(sp, starve)
    @test isempty(_errs(rs))
    @test length(rs) == 2

    # (5) NO FABRICATION — overlapping evidence must be blocked (gate says False). The
    #     seed-vs-derived row is the one that failed OPEN and let a token be counted twice.
    fabricate = """
    !(assertEqual (StampDisjoint (s1) (s1)) False)
    !(assertEqual (StampDisjoint (s1) (s1 s2)) False)
    !(assertEqual (StampDisjoint (s1 s2) (s2 s3)) False)
    """
    rs = load_metta!(sp, fabricate)
    @test isempty(_errs(rs))
    @test length(rs) == 3
end
