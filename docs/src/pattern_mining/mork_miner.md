# MORK-Native Miner — prefix locality + in-place counters

The MORK-Miner mines **entirely inside MORK's PathMap index**, exploiting prefix-tree locality: atoms
stored as token-paths share byte-trie prefixes, so atoms with a common leading prefix are "nearby" and
likely participate in the same pattern. This avoids global scans and subgraph isomorphism.

## Prefix-locality mining

Patterns are **left-anchored prefixes** `(head t1 … tk _)` — distinct from the any-position `_` wildcards
of [the relational miner](dialects.md). Three stages, all PathMap operations:

- **Seed** — `mine_prefix_patterns(cs, depth, minsup)`: group atoms by their leading `depth` tokens, count
  atoms under each prefix, keep the frequent ones.
- **Grow** — `grow_prefix(cs, prefix, minsup)`: extend a frequent prefix one token deeper (prefix proximity).
- **Support** — the count of atoms under a prefix.

On the "drink" DB, depth 2, `minsup = 2`: `(drink Alice _):2`, `(drink Bob _):2` (`(drink Carol _):1` and
`(inherit Alice _):1` dropped).

## §2.3 in-place counters — the speedup

The MORK-Miner's key idea is that support is **not** computed by a scan or a query pass. Per §2.3:

> "Whenever a new data item is **stored**, the miner **increments an integer counter at each prefix node
> along its key path**. The support of any pattern is obtained by **reading the counter** — no separate
> matching or counting pass is required."

`PrefixCounter` realizes this: `prefix_insert!` increments a counter at every prefix of an atom's key path
at insert time; `prefix_count_support` reads support in **O(1)**.

```julia
pc = prefix_counter(data)                       # one-time storage pass (counters maintained at insert)
prefix_count_support(pc, ["drink", "Alice"])    # O(1) read → 2
```

Benchmark (`bench_dialects_and_speedup.jl`) — O(1) counter read vs an O(N) dump-scan for the same support:

| N (atoms) | O(1) counter read | O(N) scan | speedup |
|---|---|---|---|
| 4,000  | 0.15 µs | 21 ms  | **145,071×** |
| 16,000 | 0.12 µs | 106 ms | **847,875×** |
| 64,000 | 0.18 µs | 419 ms | **2,344,802×** |

The counter read is **flat in N**; the speedup *grows* with the dataset — the paper's "orders of
magnitude, no global scans," demonstrated.

## A correction worth recording

An earlier benchmark used a **post-hoc** `space_query_multi`/scan, found it O(N) and slower, and briefly
concluded the speedup "wasn't real / needed deep substrate work." That was **our error** — we had
benchmarked the wrong mechanism (the "separate counting pass" §2.3 explicitly avoids), not the paper's
algorithm. Implementing the actual in-place counter vindicated the claim. The standing lesson: when a
measured result contradicts a serious paper, assume **we** erred and find it before doubting the claim.

`space_query_multi_at` (the prefix-anchored query variant) is for the multi-space "spaces as prefixes"
scoping model — not a pattern-prefix counter — so it is not the right tool here; the in-place counter is.
