# Pattern mining — runnable experiments + findings

Executable experiments behind the pattern-mining documentation in
[`../../docs/src/pattern_mining/`](../../docs/src/pattern_mining/). Specs/docs describe, experiments run.
The miner code lives in [`../../src/standard/PatternMiner.jl`](../../src/standard/PatternMiner.jl)
(+ [`MeTTaIL.jl`](../../src/standard/MeTTaIL.jl) for the `def/match/emit` surface); tests in
[`../../test/test_pattern_miner.jl`](../../test/test_pattern_miner.jl) (27/27).

Run from a **warm Core REPL** (cold-start is hook-blocked):
```
cd ~/code/CognitiveSubstratesAI/Core && \
  printf 'include("experiments/pattern_mining/<file>.jl"); exit()\n' | julia --project=. -i tools/repl.jl
```

- `demo_miners.jl` — the three mining approaches on the Pattern-Miner-Tutorial-MeTTa4 "drink" DB:
  (1) `def/match/emit` frequent-pattern miner (MeTTa-IL → MM2), (2) MORK-native prefix-locality miner,
  (3) MORK-Miner §2.3 in-place counters (O(1) support).
- `bench_dialects_and_speedup.jl` — (a) cross-dialect support **agreement** (raw-MeTTa interpreter ≡
  relational dump-scan ≡ MORK trie query ≡ §2.3 counter), and (b) the **§2.3 in-place-counter speedup**
  vs an O(N) scan.

## Findings

Grounded in three Goertzel docs (`../../docs/research/papers/Mork/`): **Pattern-Miner-Tutorial-MeTTa4**
(the Hyperon Pattern Miner algorithm), **MORK-Miner** (PathMap-native, prefix-locality), **metta-magic_v2**
(framework context). Canonical references cloned to `~/dev-zone/{hyperon-miner,weighted-atom-sweep}`.

1. **§9 "three dialects" comparison.** The Scalable-MeTTa-Infrastructure §9 implements the *same* miner in
   multiple dialects to **compare the language variants** — it's a benchmark, not competing miners. We
   realized the support op in four dialects; **all agree** on the same data (the §9 methodology).

2. **MORK-Miner §2.3 speedup — the paper's claim, demonstrated.** Support is **not** a post-hoc scan/query;
   it is an **in-place counter incremented at INSERT time** along each atom's key path, read in **O(1)**.
   Counter-read is flat in N while a scan is O(N):

   | N (atoms) | O(1) counter read | O(N) scan | speedup |
   |---|---|---|---|
   | 4,000  | 0.15 µs | 21 ms  | 145,071× |
   | 16,000 | 0.12 µs | 106 ms | 847,875× |
   | 64,000 | 0.18 µs | 419 ms | 2,344,802× |

   The speedup *grows* with N — "orders of magnitude, no global scans" (MORK-Miner §2.3).

3. **Correction (honest).** A first benchmark of a post-hoc `space_query_multi`/scan was O(N) and slower; we
   briefly concluded "speedup not real." That was **our error** — the wrong mechanism (the "separate
   counting pass" §2.3 says you don't do), not the paper. Implementing the actual in-place counter vindicated
   the claim. See `feedback_deviation_from_paper_means_we_erred`.

4. **WILLIAM is the production miner.** These two miners are the educational/comparison complement; WILLIAM
   (papers-based, grounded `mine-patterns`, wired in Core) is the real frequent-subgraph engine the whitepaper
   §7.2.2 uses. Cross-validating WILLIAM against `hyperon-miner` is a separate follow-up.
