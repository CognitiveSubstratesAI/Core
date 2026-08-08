# test_program_regions.jl — the sequential-effects partition (MeTTa Invariant 1).
#
# ─── THE DEFECT THIS PARTITION EXISTS TO FIX (MEASURED 2026-08-08) ───────────────────────────────
#     program   (= (f) a)  !(f)  (= (f) b)  !(f)
#     oracle    !(f) → ["a"]        then  !(f) → ["a","b"]
#     compiled  !(f) → ["a","b"]    and   !(f) → ["a","b"]
# The first query was answered with a rule added LATER, because every lane entry takes the program as
# one string. `split_program_regions` is the lane-neutral partition that makes each query see only
# its textual prefix.
#
# ─── WHY THESE ASSERTIONS ARE SHAPED THIS WAY ────────────────────────────────────────────────────
# PREFIX-EXACT is a two-sided property, so a test that only pins "region 1 sees one rule" is half a
# test — it passes for a partition that never lets region 2 see region 1's rules either. Every
# ordering case below therefore asserts BOTH the narrowing and the accumulation.
#
# CONSERVATION is the strongest structural check here: flattening the regions back out must reproduce
# the original form sequence exactly. A partition can be wrong by DROPPING a form or REORDERING one,
# and neither shows up in a per-region content assertion.
#
# The ALIASING case pins an implementation trap: the loop pushes a region and then starts a new one.
# Clearing the accumulators with `empty!` instead of rebinding would silently blank every region
# already pushed, because the struct holds the same vector.
using MeTTaCore
using Test

# Predicates. `_never` isolates ordering from mutation-detection; `_mutates` is the realistic shape:
# a fail-safe classifier that reports true for anything it cannot prove inert.
const _never   = (_::AbstractString) -> false
const _always  = (_::AbstractString) -> true
_mutates(f::AbstractString) = occursin("add-atom", f) || occursin("remove-atom", f)

"Flatten regions back to the (bang, form) sequence they were built from."
function _flatten(rs::Vector{ProgramRegion})::Vector{Tuple{Bool, String}}
    out = Tuple{Bool, String}[]
    for r in rs
        for d in r.defs;    push!(out, (false, d)); end
        for q in r.queries; push!(out, (true,  q)); end
    end
    out
end

@testset "program regions — the sequential-effects partition" begin

    @testset "THE DEFECT: a rule added after a query must not reach it" begin
        rs = split_program_regions("(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n", _never)
        @test length(rs) == 2
        # region 1 sees ONLY the first rule …
        @test rs[1].defs    == ["(= (f) a)"]
        @test rs[1].queries == ["(f)"]
        # … and region 2 introduces the second. Incremental: a driver applies defs cumulatively, so
        # region 2's query sees BOTH rules. That is the other half of prefix-exactness.
        @test rs[2].defs    == ["(= (f) b)"]
        @test rs[2].queries == ["(f)"]
    end

    @testset "DEGENERACY: defs before queries ⇒ exactly ONE region (no perf cost on the common case)" begin
        rs = split_program_regions("(= (f) a)\n(= (g) b)\n!(f)\n!(g)\n", _never)
        @test length(rs) == 1
        @test rs[1].defs    == ["(= (f) a)", "(= (g) b)"]
        @test rs[1].queries == ["(f)", "(g)"]
    end

    @testset "a MUTATING query closes its own region" begin
        # The mutation must be visible to what follows, so the region ends AFTER the query that
        # performs it — the query itself is still answered against the prefix before it.
        rs = split_program_regions("(= (f) a)\n!(add-atom &self (= (f) b))\n!(f)\n", _mutates)
        @test length(rs) == 2
        @test rs[1].defs    == ["(= (f) a)"]
        @test rs[1].queries == ["(add-atom &self (= (f) b))"]   # answered BEFORE its own effect lands
        @test isempty(rs[2].defs)
        @test rs[2].queries == ["(f)"]                          # sees the mutation
    end

    @testset "a non-mutating query does NOT close a region" begin
        # Same program shape, predicate says inert ⇒ one region. This is what makes the predicate the
        # load-bearing part: it alone decides how much staging happens.
        rs = split_program_regions("(= (f) a)\n!(add-atom &self (= (f) b))\n!(f)\n", _never)
        @test length(rs) == 1
        @test length(rs[1].queries) == 2
    end

    @testset "FAIL-SAFE predicate: over-reporting costs regions, never correctness" begin
        rs = split_program_regions("(= (f) a)\n!(f)\n!(g)\n", _always)
        @test length(rs) == 2                    # one region per query
        @test rs[1].queries == ["(f)"]
        @test rs[2].queries == ["(g)"]
        @test isempty(rs[2].defs)
    end

    @testset "CONSERVATION: flattening reproduces the original form sequence exactly" begin
        for src in ("(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n",
                    "!(f)\n(= (f) a)\n!(f)\n(= (g) b)\n(= (h) c)\n!(g)\n!(h)\n",
                    "(= (f) a)\n(= (g) b)\n",
                    "!(f)\n!(g)\n!(h)\n")
            for pred in (_never, _always, _mutates)
                @test _flatten(split_program_regions(src, pred)) == mm2_split_forms(src)
            end
        end
    end

    @testset "boundary cardinalities" begin
        @test isempty(split_program_regions("", _never))
        @test isempty(split_program_regions("   \n ; just a comment\n", _never))

        only_defs = split_program_regions("(= (f) a)\n", _never)
        @test length(only_defs) == 1
        @test only_defs[1].defs == ["(= (f) a)"] && isempty(only_defs[1].queries)

        only_qs = split_program_regions("!(f)\n", _never)
        @test length(only_qs) == 1
        @test isempty(only_qs[1].defs) && only_qs[1].queries == ["(f)"]

        # A query with NO preceding definition at all — region 1 legitimately has empty defs.
        lead = split_program_regions("!(f)\n(= (f) a)\n!(f)\n", _never)
        @test length(lead) == 2
        @test isempty(lead[1].defs) && lead[1].queries == ["(f)"]
        @test lead[2].defs == ["(= (f) a)"]
    end

    @testset "comments and whitespace do not become forms" begin
        rs = split_program_regions("; leading\n(= (f) a)   ; trailing\n\n  !(f)\n; tail\n", _never)
        @test length(rs) == 1
        @test rs[1].defs    == ["(= (f) a)"]
        @test rs[1].queries == ["(f)"]
    end

    @testset "ALIASING: regions must not share their accumulator vectors" begin
        rs = split_program_regions("(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n", _never)
        @test rs[1].defs    !== rs[2].defs
        @test rs[1].queries !== rs[2].queries
        push!(rs[2].defs, "(= (f) c)")                 # touching one must not disturb the other
        @test rs[1].defs == ["(= (f) a)"]
    end

    @testset "region_program renders text a lane entry can consume" begin
        rs = split_program_regions("(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n", _never)
        @test region_program(rs[1]) == "(= (f) a)\n!(f)\n"
        @test region_program(rs[2]) == "(= (f) b)\n!(f)\n"
        # And it round-trips through the splitter, so a rendered region is a valid program.
        @test mm2_split_forms(region_program(rs[1])) == [(false, "(= (f) a)"), (true, "(f)")]
    end

    @testset "END-TO-END through mc_run: the measured defect must not reproduce" begin
        # Through `mc_run`, NOT through a primitive. The last time this defect class was probed by
        # calling `mm2_zam_answers` directly the repro came back green and a real defect was nearly
        # retracted — the bang has to be inside the program string for the lane to route it.
        #
        # The expectation is a LIVE interpreter oracle, not a pinned literal: the same forms fed
        # sequentially to one Space, which is the definition of Invariant 1. The oracle's own values
        # are then pinned too, so a broken oracle cannot quietly make this testset vacuous.
        prog = "(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n"

        oracle = Vector{String}[]
        osp = MeTTaCore.Eval.Space(); MeTTaCore.Eval.load_core_stdlib!(osp)
        for (bang, f) in mm2_split_forms(prog)
            res = MeTTaCore.Eval.load_metta!(osp, bang ? "!" * f : f)
            bang && push!(oracle,
                sort(String[string(x) for r in res for x in (r isa AbstractVector ? r : [r])]))
        end
        @test oracle == [["a"], ["a", "b"]]      # the oracle is what Invariant 1 requires

        r = mc_run(MeTTaCore.new_core_space(), "", prog)
        @test r.lane == :direct
        got = Vector{String}[sort(ans) for (_, ans) in r.results.evaluated]
        @test length(got) == 2
        @test got[1] == ["a"]                    # ← was ["a","b"]: answered with a rule added later
        @test got[2] == ["a", "b"]               # ← and the second still accumulates. Prefix-EXACT.
        @test got == oracle
    end

    @testset "END-TO-END: definitions before queries are unaffected" begin
        # The degenerate single-region case must be untouched by staging — same answers, and both
        # queries still see both rules.
        prog = "(= (f) a)\n(= (f) b)\n!(f)\n!(f)\n"
        r = mc_run(MeTTaCore.new_core_space(), "", prog)
        got = Vector{String}[sort(ans) for (_, ans) in r.results.evaluated]
        @test got == [["a", "b"], ["a", "b"]]
    end

    @testset "types are concrete — no Any containers" begin
        rs = split_program_regions("(= (f) a)\n!(f)\n", _never)
        @test rs isa Vector{ProgramRegion}
        @test rs[1].defs isa Vector{String}
        @test rs[1].queries isa Vector{String}
        @test isconcretetype(fieldtype(ProgramRegion, :defs))
        @test isconcretetype(fieldtype(ProgramRegion, :queries))
    end
end
