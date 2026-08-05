# Core architecture target — hyperon / CeTTa / PeTTa, and where Core is headed

Purpose: one written reference for Core's target architecture, derived from a four-way comparison
of the reference MeTTa implementations. This is the "where we're going" doc; it does NOT replace the
corelib faithfulness map (the 138-function present/missing/divergent table) — that's a separate,
still-needed deliverable about *correctness*. This doc is about *structure*.

## Provenance (what was read, and how much to trust each)
- **hyperon-experimental**: structure read from source (`lib/src/metta/`, `python/hyperon/`) + the
  official "Structure of the codebase" docs. VERIFIED.
- **PeTTa**: read from source this pass — `src/{translator,spaces,metta,parser,specializer}.pl`,
  `lib/lib_he.metta`. VERIFIED.
- **CeTTa**: file/dir structure + `lib/stdlib.metta` read from source. The DEEP internals
  (`term_universe.c`, `space_match_backend.c`, the tabled evaluator, the MORK bridge) came from a
  separate research read of files on another machine — ACCEPTED AS GIVEN, not independently
  re-verified here. Flagged inline where load-bearing.
- **Core**: read from source — `src/MeTTaCore.jl` wiring, `src/standard/Minimal.jl`, the `src/` tree.
  VERIFIED.

---

## 1. The four implementations, placed correctly

| | what it actually is |
|---|---|
| **hyperon** | The reference **Rust core** (`lib` = atomspace + interpreter) + a stable **C API** (`c`/libhyperonc) + thin **language bindings** that proxy to it (Python via pybind11). One implementation, many bindings. Authoritative for the corelib spec + the test suite. |
| **CeTTa** | A **multi-language C runtime workbench** — a `--lang` front-end dispatcher (12 declared language ids; HE/MM2/rho-calc implemented) over a sophisticated substrate: AtomId-interned persistent store, a pluggable 4-engine match backend (native / native-candidate-exact / pathmap / mork), a tabled/answer-ref evaluator, an LLVM compile path, and a deep AtomId-native MORK bridge. NOT a simple sibling of Core. |
| **PeTTa** | A **MeTTa→Prolog compiler.** `translator.pl` compiles MeTTa rules into Prolog clauses (`Head :- Body`); a space is Prolog's dynamic clause DB (`assertz`/`retract`); matching = unification, nondeterminism = backtracking (`findall`/`bagof`), control = `cut`, arithmetic = `clpfd`. Thin *because* it offloads everything to the WAM. The independent reference for what's *essential* vs hyperon-idiom (`lib_he.metta`). |
| **Core** | A **native Julia reimplementation, mid-convergence.** A faithful interpreter (`standard/Minimal.jl`, passes 234/234 integration conformance) + a partial corelib (`stdlib.metta`) + a **MORK/PathMap substrate** (`space/CoreSpace.jl`, the high-performance store) + a legacy interpreter being retired (`eval/Eval.jl`/`EvalND.jl`). |

**Core's true peer is CeTTa** (both are native host-language reimplementations on a MORK substrate),
**not** hyperon's Python binding layer. PeTTa is the architectural model; hyperon is the spec.

---

## 2. THE MORK REFRAME (the correction that reorganizes everything)

MORK/PathMap is **not legacy.** Earlier framing lumped it with the old `eval_metta` interpreter and
called the whole region "legacy to retire." That was wrong:

- **Legacy** = the old `eval_metta`/`eval_nd` interpreter only. That's what `Minimal` supersedes.
- **NOT legacy** = MORK / PathMap / the space substrate. That is the **engine** — the high-performance
  storage + matching + indexing foundation, and the *target*, not the thing being retired.

The target is **`Minimal`'s faithful semantics running ON the MORK substrate**, not `Minimal` replacing
MORK. This is your own E1 plan (wire `match`/`unify`/`substitute` onto MORK's `expr_unify`/`expr_apply`/
`space_query_multi`). And it is exactly CeTTa's architecture: a faithful HE evaluator on an AtomId-
interned store with MORK as a first-class match backend.

**The unifying insight: MORK is Core's WAM.** PeTTa is thin because it compiles MeTTa onto the Prolog
engine. Core should compile/wire MeTTa onto the MORK engine the same way. So:
- The "two spaces" in Core (`Minimal`'s simple in-memory `Space` vs MORK-backed `CoreSpace`) is **not
  old-vs-new** — it's a **convergence in progress**. `Minimal`'s in-memory `Space` is a placeholder;
  MORK is the target backend.

---

## 3. Layer-by-layer comparison

| Layer | hyperon | CeTTa | PeTTa | Core (now → target) |
|---|---|---|---|---|
| Atom types | `hyperon-atom` crate | `atom.c` + AtomId-interned `term_universe` | Prolog terms | `standard/Atoms.jl` → (interned store, CeTTa-style) |
| Parser | `text.rs` | `parser.c` (+ rho/MM2 front ends) | `parser.pl` | `parser/Parser.jl` + Minimal `tokenize()` |
| Minimal-metta interpreter | `interpreter.rs` | `eval.c` (tabled, answer-ref) | **none** — compiled to Prolog | `standard/Minimal.jl` |
| Type system | `types.rs` | `lang.c`/`compile.c` | `clpfd` + Prolog | embedded in `Minimal.jl` |
| Space + matching | `hyperon-space` | `space.c` + 4-engine `space_match_backend` vtable (native/pathmap/**mork**) | Prolog dynamic DB (`assertz`/`retract`, first-arg indexed) | **MORK/PathMap `CoreSpace`** (the engine) + Minimal placeholder `Space` |
| Nondeterminism | hand-written | `SearchContext` choice-point + trail | **WAM backtracking** + `findall` | `collapse-bind`/`superpose-bind` (hand-rolled) → choice-point/trail |
| Grounded stdlib | `runner/stdlib/*.rs` | `grounded.c`/`cetta_stdlib.c` | Prolog builtins | `Minimal` ops + `CoreMathOps`/`NumpyOps` |
| Rule corelib | `stdlib.metta` | `lib/stdlib.metta` (~99) | `lib_he.metta` (independent reimpl) | `standard/stdlib.metta` (partial) |
| Runner / session | `runner/` (`MeTTa`/`RunnerState`/`Environment`) | `session.c` + `library.c` (profiles, modules) — **NOT** `runtime.c` (that's the LLVM shim) | `main.pl` | **none** (loose `load_metta!`) |
| Host API | `python/` (pybind11 proxy to C API) | `foreign.c` + `native_handle.c` | `janus` (SWI↔Python) | bare Julia exports |
| Engine offload model | core does the work | core + MORK backend | **compile to WAM** | **compile/wire to MORK** (E1) |

---

## 4. Best-of-both-worlds adoption plan — what Core takes from each

- **From hyperon** → the **corelib spec + the `#[test]` suite** (the *what* and the *gate*). The
  unit corpus (`test/standard/unit/`) is this, already adopted. Authoritative for correctness.
- **From PeTTa** → the **architecture + the essence**:
  - The **compile-to-engine model**: offload matching/resolution/backtracking/indexing to the engine
    (WAM for PeTTa, **MORK for Core** = E1). Don't re-implement them in the interpreter.
  - The **space-as-indexed-dynamic-DB** model (`assertz`/`retract` + first-arg index → MORK indexed
    `add-atom`/`remove-atom`/rule-lookup).
  - The **`cut`** primitive (committed choice; also a termination tool).
  - `lib_he.metta` as the **independent corelib reference** (what's essential vs hyperon-idiom).
- **From CeTTa** → the **substrate engineering** that makes the engine fast and faithful:
  - **AtomId-interned store with decode-on-demand** (`term_universe`) — first-class byte-form
    accessors so matching never forces full decode; compact32→wide64 online migration.
  - **Storage/match split as a vtable seam** (`space_match_backend`) where the flat native array is a
    *projection*, not the source of truth — backends own their rows (the MORK lane).
  - **Choice-point + trail search machine** (`SearchContext`/`ChoicePoint`) for nondeterminism.
  - **AtomId-native MORK bridge** (mutation = expr-bytes, queries carry a typed variable-slot map;
    text is a tracked fallback, never silent) — with a five-rung join-pushdown ladder backed by a
    provably-correct C nested-loop fallback.

---

## 5. Prolog features to adopt (grounded in what PeTTa actually uses), prioritized

1. **Indexed dynamic-DB space + indexed rule lookup** → MORK as the indexed atom store; rule lookup
   via MORK indexed query, not linear scan (E1). *Highest value — where MORK pays off.*
2. **Choice-point + trail nondeterminism engine** → replace hand-rolled `collapse-bind`/`superpose-bind`
   fan-out with a principled choice-point/trail engine (PeTTa via WAM, CeTTa via `SearchContext`).
3. **The `cut` / committed choice** → a real MeTTa control primitive (deterministic pruning +
   termination help for the step-cap problem). Concrete corelib addition.
4. **`findall`/`bagof` = collapse/superpose** → already aligned conceptually; the principled framing
   of what Core already has.
5. **`clpfd`-style constraint reasoning** → optional/advanced (relational/constrained numeric
   reasoning), low priority.

---

## 6. The synthesis (the one-line target)

**Core's target = hyperon-faithful corelib semantics, compiled/wired onto the MORK engine the way
PeTTa is onto the WAM, with CeTTa-grade substrate underneath — plus a `cut` and a principled
choice-point engine adopted from the Prolog model.** MORK is the linchpin (it plays Prolog's WAM
role), which is precisely why it is not legacy.

## 7. What this does NOT do (so it doesn't become drift)
This is the structural target. It does NOT certify the corelib is faithful — the **138-function
coverage map** (present/missing/divergent, verified against source + tests, not docs) is the separate
correctness deliverable and is still the concrete gap. Architecture is the *how to structure*;
faithfulness is the *is it correct*. Both are needed; this doc is only the first.
