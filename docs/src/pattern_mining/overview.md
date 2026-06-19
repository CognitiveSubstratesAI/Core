# Pattern Mining — Overview

Pattern mining discovers reusable structures (templates recurring across contexts) in an Atomspace —
priming reasoning, suggesting subgoals, and compressing knowledge. MeTTaCore implements pattern mining at
several layers, deliberately, to **compare language dialects and substrate strategies** on the same
algorithm. This section documents each.

## Source material

Three Goertzel documents (under `docs/research/papers/Mork/`) ground this work:

| Document | What it is |
|---|---|
| **Pattern-Miner-Tutorial-MeTTa4** | The Hyperon Pattern Miner *algorithm*: abstract → specialize → support → expand-conjunctions → I-surprisingness |
| **MORK-Miner** | A *PathMap-native* miner: prefix-locality, seed/grow by prefix, **in-place support counters** |
| **metta-magic_v2** | Framework context (`metta_magic`/PyMeTTa); the miner is one algorithm in a broader vision |

The canonical reference implementations are cloned to `~/PRIMUS/dev-zone/`:
[`hyperon-miner`](https://github.com/trueagi-io/hyperon-miner) (the authoritative MeTTa miner) and
[`weighted-atom-sweep`](https://github.com/iCog-Labs-Dev/weighted-atom-sweep) (the Weighted Atom Sweeps
cognitive scheduler).

## The "three dialects" methodology

The Scalable-MeTTa-Infrastructure spec (§9) implements the *same* Hyperon Pattern Miner in **multiple
language dialects** in order to **compare the variants** — it is a measuring benchmark, not a set of
competing miners. The pattern miner is chosen precisely because it is algorithmically simple, lives in
the metagraph, and has a published tutorial. We follow that methodology: the support operation (the core
stream op) is realized in **four** ways that all agree on the same data — see
[Mining Dialects](dialects.md).

## WILLIAM is the production miner

MeTTaCore already ships **WILLIAM** — the papers-based frequent-subgraph miner (grounded `mine-patterns`
primitive, wired into Core), which the Hyperon whitepaper (§7.2.2) uses for template-library creation. The
miners documented here are the **educational / comparison complement**: they make the language and
substrate layers explicit and measurable. For production frequent-subgraph mining, use WILLIAM.

## API surface

All in [`src/standard/PatternMiner.jl`](https://github.com/CognitiveSubstratesAI/Core/blob/main/src/standard/PatternMiner.jl)
(the `def/match/emit` pipeline surface it builds on is in `MeTTaIL.jl`):

- **Frequent-pattern miner** (`def/match/emit` → MM2): `mine_frequent`, `pattern_support`.
- **Support dialects**: `pattern_support_interp` (raw-MeTTa), `pattern_support` (relational scan),
  `pattern_support_native` (MORK trie query).
- **MORK-native prefix miner**: `prefix_support`, `mine_prefix_patterns`, `grow_prefix`.
- **MORK-Miner §2.3 in-place counters**: `PrefixCounter`, `prefix_insert!`, `prefix_counter`,
  `prefix_count_support`.

Runnable experiments: [`experiments/pattern_mining/`](https://github.com/CognitiveSubstratesAI/Core/tree/main/experiments/pattern_mining)
(`demo_miners.jl`, `bench_dialects_and_speedup.jl`). Tests: `test/test_pattern_miner.jl` (27/27).
