# `metta-ref` differential — MeTTapedia's HOL4-specified M1 reference

Ground truth and extra coverage for `test_mettaref_oracle.jl`. Vendored from **MeTTapedia**
(`~/JuliaAGI/dev-zone/MeTTapedia` @ `23bede4e`, MIT), subtree `cakeml/metta-ref`: a HOL4
specification of MeTTa "M1" with an SML reference interpreter (`sml/metta_m1.sml`) and a curated
test set.

## Why this corpus was adopted and the rest of MeTTapedia was not

MeTTapedia is a formal-theory library — Lean 4 / HOL4 / Mizar / Isabelle / Megalodon, with a
flagship Lean package covering probability, PLN, HOL, AIXI. None of that can state the properties
our compiler actually gets wrong, which are about **our own representations agreeing with each
other** (`show` being lossy; parse-equivalence being space-relative). Those are found by execution,
not by theory.

What `metta-ref` has that theory does not is **executable cases**, and they cover our thinnest area:

| | files | overlap with our existing corpora |
|---|---|---|
| `curated/` | 4 (+ `.expected` goldens) | none |
| `cetta_selected/` | 20 | none |

Fourteen of the twenty are `nondet_*_bag` — superpose, collapse, chain, case, switch, `let*`, match.
That is exactly where the compile lane is weakest: the `eval`-vs-`metta` choice in
`EmitIL._instr(::GCall)`, the `collapse` wrapper, and chain sequencing are all nondeterminism-shaped.
A proved oracle only guarantees what its **corpus** exercises, so new coverage in a weak area is worth
more than more theory over areas already covered by LeaTTa.

## The two halves license different conclusions

- **`curated/` is an ORACLE.** Its `.expected` files are goldens from the HOL4-specified M1 reference
  (`tests/run_metta_file.sml`), independent of us. A disagreement is evidence about Core.
- **`cetta_selected/` is NOT an oracle.** It ships no goldens, so it runs as a compiled-vs-interpreted
  differential — self-consistency only. A green run says the two lanes agree, not that either is right.

Comparison is **structural, not textual**: both sides are parsed to atoms and compared as multisets.
`../leatta/README.md` records why string-diffing an oracle's output is a trap (quoting, Float-vs-Int,
alpha-renaming), and this session added a fresh reason to distrust rendered text as an equality
witness — `show` is lossy for grounded strings, `Space` and `StateCell`.

The bag comparison is deliberate. The first version compared only ERROR COUNTS, the contract
`test_compile_lane_corpus.jl` uses; on this corpus that is nearly vacuous, since all twenty scripts are
error-free in both lanes (0 → 0 measured). A lane that dropped a `superpose` branch would have passed.

## Status when vendored (2026-08-12)

- curated goldens: **4/4 agree** with the M1 reference.
- cetta_selected: **24 definitions compiled, 13 fell back, 21 bags compared, zero deviations.**

## Cross-check: how the other MeTTa-IL implementations handle serialization

Recorded here because it bears directly on the wire-format work:

- **`dev-zone/mettail-rust`** keeps a typed AST throughout and guards its wire format with
  property-based tests (`languages/tests/roundtrip_tests.rs`, proptest, 500 cases). ⚠️ Read the
  BODY, not the header: the file says it tests `parse(display(t)) == t`, but
  `roundtrip_int_parse_display` only asserts `parsed.is_ok()`; the equality property it actually
  enforces is the weaker **display idempotence**, `display(parse(display(t))) == display(t)`. It also
  excludes variables and binders outright — *"moniker's Var equality semantics differ from structural
  equality after round-trip"*. So the strongest MeTTa-IL implementation available did NOT achieve
  atom-level round-trip equality either, and settled where we did: keep terms typed, and do not rely
  on the text as an identity.
- **`dev-zone/MeTTaIL`** (Scala, F1R3FLY/GSLT) parses via ANTLR/BNFC into a generated typed AST and
  interprets that; no text between phases.
