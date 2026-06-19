# Frequent-pattern miner (src/standard/PatternMiner.jl) — the simplified Hyperon Pattern Miner core on
# the def/match/emit surface, on the Pattern-Miner-Tutorial-MeTTa4 drink example.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "frequent-pattern miner (simplified, def/match/emit)" begin
    # the tutorial's database
    data = "(drink Alice Coke)\n(drink Bob Coke)\n(drink Alice Tea)\n(drink Bob Tea)\n(drink Carol Tea)\n(inherit Alice American)"

    @testset "support: distinct ground matches of a _-wildcard pattern" begin
        cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, data)
        @test pattern_support(cs, raw"(drink _ Coke)") == 2    # Alice, Bob
        @test pattern_support(cs, raw"(drink _ Tea)") == 3     # Alice, Bob, Carol
        @test pattern_support(cs, raw"(drink Alice _)") == 2   # Coke, Tea
        @test pattern_support(cs, raw"(drink Carol _)") == 1   # Tea only
        @test pattern_support(cs, raw"(inherit _ American)") == 1
    end

    @testset "mine_frequent: abstract (def/match/emit) → support → mark-kept (minsup 2)" begin
        cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, data)
        # abstraction stage: one-hole abstractions of (drink S O), emitted as (cand …) with `_` wildcards
        abs_pipe = raw"""
        (def abs-subj () (match (drink $s $o) (emit (cand (drink _ $o)))))
        (def abs-obj  () (match (drink $s $o) (emit (cand (drink $s _)))))
        """
        kept = Dict(mine_frequent(cs, abs_pipe, 2))
        @test kept[raw"(drink _ Tea)"]  == 3
        @test kept[raw"(drink _ Coke)"] == 2
        @test kept[raw"(drink Alice _)"] == 2
        @test kept[raw"(drink Bob _)"]   == 2
        @test !haskey(kept, raw"(drink Carol _)")   # support 1 < minsup 2 → dropped
    end
end
