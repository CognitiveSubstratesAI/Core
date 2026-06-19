# Pattern mining — (a) cross-dialect support AGREEMENT, (b) the MORK-Miner §2.3 in-place-counter SPEEDUP.
# Run from a WARM Core REPL:
#   cd ~/code/CognitiveSubstratesAI/Core && printf 'include("experiments/pattern_mining/bench_dialects_and_speedup.jl"); exit()\n' | julia --project=. -i tools/repl.jl
#
# Findings (see README.md): all four support dialects AGREE; the §2.3 in-place counter gives O(1) support,
# 145k–2.3M× faster than an O(N) scan and growing with N — the paper's "no global scans" claim demonstrated.
using MeTTaCore, Printf
const MC = MeTTaCore

const DRINK_DB = "(drink Alice Coke)\n(drink Bob Coke)\n(drink Alice Tea)\n(drink Bob Tea)\n(drink Carol Tea)\n(inherit Alice American)"

println("=== (a) four-dialect support AGREEMENT (drink DB) ===")
cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, DRINK_DB)
pc0 = MC.prefix_counter(DRINK_DB)
# (dollar-var pattern, _-wildcard pattern, prefix tokens | nothing, expected support)
cases = [(raw"(drink $x Coke)",  raw"(drink _ Coke)",  nothing,           2),
         (raw"(drink Alice $y)", raw"(drink Alice _)", ["drink","Alice"], 2),
         (raw"(inherit $x American)", raw"(inherit _ American)", nothing,  1)]
for (dollar, wild, pre, exp) in cases
    i = MC.pattern_support_interp(DRINK_DB, dollar)   # raw-MeTTa interpreter (collapse/size-atom)
    s = MC.pattern_support(cs, wild)                  # relational dump-scan
    n = MC.pattern_support_native(cs, dollar)         # MORK trie query (space_query_multi)
    c = pre === nothing ? "-" : string(MC.prefix_count_support(pc0, pre))  # §2.3 in-place counter
    ok = (i == s == n == exp) && (pre === nothing || parse(Int, c) == exp)
    @printf("  %-24s interp=%d scan=%d native=%d counter=%s  %s\n", dollar, i, s, n, c, ok ? "AGREE" : "MISMATCH")
end

println("\n=== (b) MORK-Miner §2.3 speedup: O(1) counter read vs O(N) scan ===")
function bench(nsubj)
    objs = ["Coke", "Tea", "Water", "Juice"]
    d = join(["(drink s$i $o)" for i in 1:nsubj for o in objs], "\n")
    csb = MC.new_core_space(); MC.space_add_all_sexpr!(csb.inner, d)
    pcb = MC.prefix_counter(d)                        # one-time insert pass (counters maintained at store)
    rd = () -> MC.prefix_count_support(pcb, ["drink", "s7"])   # O(1) counter read
    sc = () -> MC.prefix_support(csb, ["drink", "s7"])         # O(N) dump-scan
    rd(); sc()                                        # warmup
    tr = @elapsed for _ in 1:100000; rd(); end
    ts = @elapsed for _ in 1:10;     sc(); end
    @printf("  N=%6d | counter-read %6.3f us | scan %8.2f ms | speedup %9.0fx | support=%d\n",
            nsubj * 4, tr / 100000 * 1e6, ts / 10 * 1000, (ts / 10) / (tr / 100000), rd())
end
for n in [1000, 4000, 16000, 64000]; bench(n); end
