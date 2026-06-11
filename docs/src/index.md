# MeTTaCore.jl

**MeTTaCore** is the canonical standalone [MeTTa](https://metta-lang.dev) interpreter of the
[CognitiveSubstratesAI](https://github.com/CognitiveSubstratesAI) stack, running on the
[MORK](https://github.com/CognitiveSubstratesAI/MORK) byte-trie substrate. Evaluation is
eager and single-result; numbers are `Float64`. Dispatch is three-tier: special forms →
grounded operations → rule rewriting.

```julia
using MeTTaCore
space = new_core_space()
ef = e -> to_sexpr(eval_metta(from_sexpr(e), space))
register_all_primitives!(); _register_atom_ops!(ef); load_stdlib!(space)

run_metta("!(+ 2 3)", space)            # => 5
run_metta("!(import! &self (library MOSES))", space)
```

## Algorithm library

Cognitive algorithms live in `lib/` as MeTTa, loaded on demand via
`!(import! &self (library <Name>))`:

- **MOSES** — Meta-Optimizing Semantic Evolutionary Search (competent program evolution:
  representation → knob-building → boolean reduct → getCandidate → scoring → hill-climb →
  metapopulation search). End-to-end verified to learn boolean functions.
- **PLN** — Probabilistic Logic Networks core logic.
- **ECAN** — Economic Attention Networks.
- **MetaMo** — motivational framework.
- **ActPC-Chem / ActPC-Geom** — Active Predictive Coding.

## Design notes

In-repo design and architecture documents live under [`docs/`](https://github.com/CognitiveSubstratesAI/Core/tree/main/docs)
(algorithm-library governance, the primitive-surface audit, the multi-space/connectome
architecture, and per-algorithm specs). The cross-cutting research corpus and source-paper
map live in the shared `CognitiveSubstratesAI/docs` repository.

!!! note
    The API reference is a work in progress; this page will grow `@autodocs` sections as the
    public surface stabilizes.
