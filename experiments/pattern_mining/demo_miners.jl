# Pattern mining — demo of the three approaches on the Pattern-Miner-Tutorial-MeTTa4 "drink" DB.
# Run from a WARM Core REPL:
#   cd ~/code/CognitiveSubstratesAI/Core && printf 'include("experiments/pattern_mining/demo_miners.jl"); exit()\n' | julia --project=. -i tools/repl.jl
# Code: src/standard/PatternMiner.jl (+ MeTTaIL.jl for the def/match/emit surface).
using MeTTaCore
const MC = MeTTaCore

const DRINK_DB = "(drink Alice Coke)\n(drink Bob Coke)\n(drink Alice Tea)\n(drink Bob Tea)\n(drink Carol Tea)\n(inherit Alice American)"

println("=== (1) def/match/emit frequent-pattern miner (MeTTa-IL → MM2), minsup=2 ===")
cs1 = MC.new_core_space(); MC.space_add_all_sexpr!(cs1.inner, DRINK_DB)
abs_pipe = raw"""
(def abs-subj () (match (drink $s $o) (emit (cand (drink _ $o)))))
(def abs-obj  () (match (drink $s $o) (emit (cand (drink $s _)))))
"""
for (p, n) in MC.mine_frequent(cs1, abs_pipe, 2)
    println("  $p\tsupport=$n")
end

println("\n=== (2) MORK-native prefix-locality miner (depth 2, minsup=2) ===")
cs2 = MC.new_core_space(); MC.space_add_all_sexpr!(cs2.inner, DRINK_DB)
for (p, n) in MC.mine_prefix_patterns(cs2, 2, 2)
    println("  $p\tsupport=$n")
end

println("\n=== (3) MORK-Miner §2.3 in-place counters — O(1) support reads ===")
pc = MC.prefix_counter(DRINK_DB)
for pre in [["drink"], ["drink", "Alice"], ["drink", "Carol"], ["inherit", "Alice"]]
    println("  prefix $pre\tsupport=", MC.prefix_count_support(pc, pre))
end
