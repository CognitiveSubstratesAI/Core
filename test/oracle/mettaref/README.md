# `metta-ref` differential — MeTTapedia's HOL4-specified M1 reference

Ground truth and extra coverage for `test_mettaref_oracle.jl`. Vendored from **MeTTapedia**
(`~/dev-zone/MeTTapedia` @ `23bede4e`, MIT), subtree `cakeml/metta-ref`: a HOL4
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

## Cross-check: how four other MeTTa implementations handle the representation boundary

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

- **`dev-zone/jetta`** (Kotlin → JVM bytecode, AOT) is the closest counterpart we have: a real MeTTa
  COMPILER whose stated bet is *"partial evaluation with a runtime fallback"* and *"one code path
  shared between compile time and call time"*, verified byte-for-byte against
  `hyperon-experimental`. Two findings:

  1. **Its IR is ours — BY DESCENT, not by coincidence.** ⚠️ This entry first said "the same node set
     … independent convergence". That was wrong, and the answer was in the header of the file being
     compared: `Core/src/compiler/IR.jl:12-15` says *"The node set is JeTTa's (`dev-zone/jetta` …
     `frontend-api/src/main/kotlin/.../frontend/ir/`). JeTTa is the only MeTTa-specific compiler IR
     among our references, so it is the one to follow."* Thirty-one JeTTa citations in that file, plus
     more in `Frontend.jl`/`ANormal.jl`. So `Symbol`/`ResolvedSymbol`/`Position`/`BoundAtom`/
     `Match`/`ArrowType`/`UniqueAtomIdGenerator` matching is a DELIBERATE PORT.

     That removes the corroboration value — a copy agreeing with its source is not evidence — but it
     sharpens the useful part: we followed JeTTa's NODE SET and did NOT follow its SERIALIZER. The
     tag-per-grounded-type design below is the piece left on the table, from a source we had already
     decided to follow. (It remains evidence against SPECMAP C7's retracted "ours has NO IR", since
     that claim is about existence, not provenance.)
  2. 🔴 **Its persistence format is TAGGED BINARY, not text** — `runtime/space/SAtomSerializer.kt`:

         TAG_SYMBOL 0 · TAG_EXPRESSION 1 · TAG_VARIABLE 3 · TAG_SPECIAL 4
         TAG_GROUNDED_LONG 20 · DOUBLE 21 · STRING 22 · BOOLEAN 23 · INT 24

     A grounded string is written under its OWN tag, so it can never read back as a symbol. That is
     precisely the defect we hit: our text form distinguishes the two only by a quoting convention
     that `show` does not honour, which is why `il_text` had to be written by hand. JeTTa also gives
     `SSpecial` a tag — the construct our emitter currently DECLINES in ten places — and throws on an
     unsupported atom type rather than degrading silently, the same fail-closed stance as
     `_unroundtrippable`, but located at the serializer instead of upstream of it.

- **`dev-zone/MeTTaScript`** (TypeScript, faithful interpreter port) contributes no new corpus — its
  `corpus/` is the same hyperon set we already run through LeaTTa — but two things are worth knowing:
  `packages/fuzz/` is a grammar-driven term generator with a decoder (the machinery a randomized
  round-trip property needs), and `packages/core/src/atomlog.ts` records that a flat `Atom[]` copied
  on every `add-atom` is O(N²) — they replaced it with an append-only linked log with structural
  sharing and a lazily-built hash index. Our `Space` is also a `Vector{Atom}`; we `push!` rather than
  copy, so we do not have their bug, but their O(1)-snapshot motivation is relevant to the second
  atom store.

### What the four agree on

None of them treats rendered text as an identity. JeTTa tags bytes; MeTTaIL generates a typed AST from
a BNF grammar; mettail-rust keeps a typed AST and settles for display IDEMPOTENCE, explicitly excluding
variables and binders; MeTTaScript keeps atoms as structures and indexes them by hash. Our conclusion —
keep terms typed, remove the in-process round-trip, and write the wire serializer by hand rather than
inheriting `show` — is the same conclusion, reached the expensive way.

⇒ The concrete borrowable design is **JeTTa's tag-per-grounded-type**. Our wire form is text because
Fig-2 makes MeTTa-IL the distributed artifact, and text is legitimate there; but the LOSSY cases
(`Space`, `StateCell`, and until this session grounded strings) are exactly the cases a type tag
resolves. That is the shape to reach for when the `Atom → MORK.Expr` bridge replaces its lossy sexpr
text write path.
