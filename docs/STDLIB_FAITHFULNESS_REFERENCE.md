# MeTTa stdlib faithfulness reference — hyperon / CeTTa / PeTTa, vs Core Minimal

Source files (read directly):
- hyperon (AUTHORITATIVE): hyperon-experimental/lib/src/metta/runner/stdlib/stdlib.metta
- CeTTa:                    CeTTa/lib/stdlib.metta
- PeTTa lib_he (shim):      PeTTa/lib/lib_he.metta
- **Minimal column**: filled by reading Core/src/standard/{Minimal.jl,stdlib.metta,CoreExtensions.metta}
  directly (NOT from memory). `✓`=matches authoritative; `✗`=divergence; `⚠️`=hybrid/extension;
  `[?]`=body not yet re-read.

> The three reference columns were read on a read-only connector by the user; the Minimal column was
> measured against the live Core source. CeTTa is **not** an independent reference for core primitives —
> it is hyperon's stdlib copied near-verbatim, so hyperon=CeTTa agreement is ONE data point. The genuinely
> independent reference is PeTTa's lib_he (a native reimplementation), useful for spotting where a hyperon
> idiom is non-essential — but for the exact reference BODY of a primitive, hyperon(=CeTTa) is authoritative.

## Architectural model (settled)
- hyperon: single canonical MeTTa-written stdlib loaded into the runner.
- CeTTa:   hyperon's stdlib copied near-VERBATIM, then CeTTa extensions (select/collect/fold/search-policy,
           ordered stack/queue spaces, MORK lane) layered IN THE SAME FILE, distinguished by @doc.
- PeTTa:   thin native (Prolog) core + SEPARATE lib_he.metta shim REIMPLEMENTING the HE surface natively
           + thematic lib_*.metta via import!.
- Core:    `CoreExtensions.metta` as a SEPARATE file == PeTTa's model. Deliberate: keeps the faithful
           stdlib physically uncontaminated so the 234/234 gate means what it says.

## Faithfulness is SPLIT (the most important non-obvious fact)
- Bool (True/False):        follow PeTTa  — bare SYMBOLS, never grounded Bool.  [[Minimal: ✓ symbols]]
- assert-result-set sema:   follow HYPERON — evaluate + result-set compare (NOT PeTTa's assert-alias).
- unify:                    HYPERON — structural builtin (Minimal adds a space-query extension, see below).
- A hyperon-extracted unit corpus assumes HYPERON assert semantics; a PeTTa-faithful Bool layer is
  orthogonal to that. Mixing them wrong = vacuous green corpus.

---

## Primitive-by-primitive (Minimal column = measured against source this pass)

### filter-atom
- hyperon: function + decons + unify(head/tail) + sealed($var) + filter-atom(tail) + atom-subst(head)
  -> $filter-expr + (chain $filter-expr $is-filtered (eval (if ...))).
- CeTTa:   IDENTICAL to hyperon. PeTTa: not in lib_he (native).
- **Minimal: ✓ VERBATIM** (stdlib.metta:80, byte-identical to hyperon — confirmed this session).
- **LIVE BUG (relocalized):** bug is NOT in filter-atom. It is `chain` failing to reduce the BARE computed
  operand `$filter-expr` from atom-subst. eval-wrapped predicate works; bare predicate ((> $x 1),
  (isLiteral $e)) errors → produces a free var `$X`. **FIX SITE = `chain` nested-operand evaluation.**
  ← root of the MOSES M6 cluster. Gated by test/standard/unit/atom.metta Core-regression cases.

### map-atom
- hyperon: function + decons + unify + sealed + map-atom(tail) + atom-subst + chain. CeTTa: identical.
  PeTTa: for-each-in-atom delegates to map-atom.
- **Minimal: ✓ VERBATIM** (stdlib.metta:70). Same chain-operand dependency as filter-atom.

### assertEqual / assertEqualToResult / assertAlphaEqualToResult (+ Msg variants)
- hyperon: ALL via (chain (context-space) ... (metta (collapse $x) %Undefined% $space) ...). ToResult
  forms evaluate ONLY the first arg, compare result SETS. CeTTa: same. PeTTa: assertEqualToResult ALIASED
  to assertEqual (NO result-set semantics — would pass vacuously).
- **Minimal: ✓ HYPERON SEMANTICS** — implemented as Julia grounded SpaceOps (Minimal.jl:966-975), NOT the
  MeTTa metta+collapse chain, but semantically equivalent: `Set(metta_run(actual,space)) == Set(expected.children)`.
  Result-set compare confirmed. NOT the PeTTa alias. atom.metta corpus relies on this and gates correctly.
- MISSING vs hyperon: `assert` (bare), `assertIncludes`, `assertAlphaEqual`, all the `*Msg` variants.
  (Only assertEqual / assertEqualToResult / assertAlphaEqualToResult exist — ⬜ to close.)

### is-function
- hyperon: get-metatype -> unify Expression -> size-atom -> decons -> (unify $h -> True False). Returns
  SYMBOL True/False, decides via metatype Expression NOT Grounded. CeTTa: identical. PeTTa: arrow-pattern + cut.
- **Minimal: ✓ HYPERON** (stdlib.metta:109 — get-metatype Expression → symbol True/False). Corroborates
  Bool-as-symbol; the `(== (get-metatype …) Grounded)` idiom is wrong even by hyperon's own stdlib here.

### unify
- hyperon: declared (-> Atom Atom Atom Atom %Undefined%); NO stdlib equation — interpreter builtin (structural).
  CeTTa: same. PeTTa: space-AWARE — can query a space via match (a PeTTa extension, not authoritative).
- **Minimal: ⚠️ HYBRID** (Minimal.jl:137-139) — structural builtin (hyperon base) PLUS a space-query path
  when the unify target is a Grounded Space (used by get-doc, like PeTTa). Faithful to hyperon for the
  structural case; carries a PeTTa-style space-query extension on top. Document, don't "fix".

### if-error / return-on-error
- hyperon: if-error = function + get-metatype + if-equal Expression + decons + (if-equal $head Error).
  CeTTa: identical. PeTTa: (if (= $X (cons Error $_)) ...) — pattern-match on (cons Error _), simpler.
- **Minimal: ✓ HYPERON** (stdlib.metta:213 — metatype + if-equal $head Error). Matches the Error *head*,
  so the error-MESSAGE representation (see below) does not affect if-error control flow.

### match-types / match-type-or / type-cast / first-from-pair
- hyperon: full if-equal %Undefined%/Atom universal guards + unify; type-cast via collapse-bind + get-type
  + map-atom + foldl-atom + match-type-or. CeTTa: identical. PeTTa: match-types = (if (== $A $B) ...) (no
  universal guards); no type-cast/first-from-pair in lib_he.
- **Minimal: [?] PARTIAL** — match-types/match-type-or/type-cast/first-from-pair: 3 refs in stdlib.metta;
  bodies NOT yet re-read this pass (grep balked). TODO: re-read and confirm %Undefined%+Atom universals
  are honored (hyperon), not PeTTa's plain `==`. One of the interpreter-audit items.

### unique / union / intersection / subtraction (set-ops)
- hyperon: each = collapse both args -> *-atom -> superpose. CeTTa: identical. PeTTa: native (not lib_he).
- **Minimal: ✓ HYPERON** (stdlib.metta:179-189 — collapse/*-atom/superpose). Grounded *-atom ops verified
  correct in composition this session (intersection (A B C)(A B)→(A B), etc.).

### quote / unquote
- hyperon: (= (quote $atom) NotReducible) ; (= (unquote (quote $atom)) $atom). CeTTa: evaluator-backed quote.
  PeTTa: unquote with (cut); quote native.
- **Minimal: ✗ DIVERGENCE (documented)** — uses the CONSTRUCTOR form `(: quote (-> Atom Atom))` with NO
  equation, NOT `(= (quote $atom) NotReducible)`, because Minimal does not treat a NotReducible rule-body
  specially (it would reduce to the bare symbol). Equivalent for the "keep unreduced" intent; flagged so a
  test asserting the NotReducible form is understood as a known representational difference.

### if / let / let*
- hyperon: (if True/False ...); let = (unify $atom $pattern $template Empty); let* = decons recursion.
  CeTTa: identical. PeTTa: if-equal/if-equal2; let/let* native.
- **Minimal: ✓ HYPERON** — let = (unify $atom $pattern $template Empty) (stdlib.metta:44); let* = decons
  recursion (49-55); if True/False equations present.

### for-each-in-atom / noreduce-eq
- hyperon: for-each = car/cdr recursion guarded by noreduce-eq; noreduce-eq = (== (quote $a) (quote $b)).
  CeTTa: identical. PeTTa: for-each = (map-atom ...); noreduce-eq = (== $A $B) (NO quote-guard).
- **Minimal: ✓ HYPERON** — noreduce-eq = (== (quote $a) (quote $b)) (stdlib.metta:195, quote-guarded);
  for-each-in-atom car/cdr + noreduce-eq guard (197).

### car-atom / cdr-atom / cons-atom / decons-atom
- hyperon: car/cdr via decons + unify, Error on empty (exact strings); cons/decons interpreter builtins.
- **Minimal: ✓ behaviour + ✓ exact error STRINGS** (stdlib.metta:58-65 — "car-atom expects a non-empty
  expression as an argument" verbatim). cons-atom/decons-atom builtins; value cases verified PASS this pass.
  ⚠️ BUT the error MESSAGE is stored as a `Sym`, not a grounded String (see ERROR REPRESENTATION below).

### min-atom / max-atom
- hyperon: grounded (Rust). min(5 4 5.5)->4 Int, max->5.5 Float. CeTTa: declared + grounded.
- **Minimal: ✗ MISSING** (confirmed — unit/atom.metta baselines 2 of its 5 here).

### index-atom
- hyperon: grounded; out-of-bounds Error MESSAGE = "Index is out of bounds" (STRING). CeTTa: grounded.
- **Minimal: ✗ DIVERGENCE** — returns the symbol `IndexOutOfBounds`, not the string. Same root as the
  error-representation issue below. Baselined in unit/atom.metta.

### math library (pow/sqrt/abs/log/trunc/ceil/floor/round/sin/asin/cos/acos/tan/atan/isnan/isinf)
- hyperon: all grounded (Rust math.rs); @doc only in stdlib.metta. CeTTa: declared + @doc with
  MathDomainError discipline. PeTTa: n/a in lib_he.
- **Minimal: ✗ ENTIRE LIBRARY MISSING** (confirmed unit/math.metta 0/48). Implement as thin marshalling
  shims to Julia Base.Math / LinearAlgebra (per CORE_NUMERIC_BACKEND_SPEC). PRESERVE Int/Float:
  hyperon (sqrt-math 4)->2 Int, (cos-math 0)->1 Int.

### doc system (@doc/@param/@return/get-doc/help!/…)
- hyperon: full system. CeTTa: full + extension docs. PeTTa: not in lib_he.
- **Minimal: ✓ PARTIAL** — get-doc family present (stdlib.metta doc section, g1_docs conformance gates it);
  help!/help-* family MISSING (⬜).

---

## ERROR REPRESENTATION — a faithfulness DECISION to make (record like Bool-as-symbol)
- **hyperon / CeTTa:** error message is a grounded STRING: `(Error <atom> "message text")`.
- **PeTTa:** error pattern is `(cons Error $_)` — control-flow matches the `Error` head, message-agnostic.
- **Minimal (Minimal.jl:41):** `error_atom(a, msg) = Expression(ERROR, a, Sym(String(msg)))` — message is a
  `Sym`, NOT a grounded String.
- **Consequence:** control flow that matches the `Error` HEAD (if-error, return-on-error, case-on-Error) is
  UNAFFECTED (all three references and Minimal agree on the head). But EXACT-MATCH tests diverge — this is
  the root of the 16 "error-format" fails in unit/interpreter.metta and the index-atom string/symbol fail.
- **DECISION (pending, low-risk):** switch `error_atom` to a grounded String message to match hyperon(=CeTTa),
  closing the 16 corpus error-format fails and aligning exact-match faithfulness. PeTTa-style head-matching
  keeps working either way. Make it deliberately, cite this row. (Analogous to the Bool-as-symbol decision.)

---

## CeTTa-ONLY extensions (NOT hyperon — never a faithfulness gap)
- select / collect / fold / fold-by-key / reduce / once / search-policy (committed-choice over nondeterm)
- ordered spaces: stack/queue/hash kinds; space-push/peek/pop/get/truncate; space-len; step!
- with-space-snapshot; MORK lane (mork:*); pragma! search-table-mode

## PeTTa-ONLY (lib_he shim affordances — NOT authoritative)
- space-aware unify (match-into-space with cut); evalc with explicit &self; if-equal2;
  get-type-space &self specialization

---

## Open obligations (this reference drives them)
1. **`chain` bare-computed-operand fix** — the M6 root, cite filter-atom row. Gate: unit/atom.metta regressions.
2. **error_atom → grounded String** — the error-representation decision above; closes 16 interpreter fails.
3. **match-types body re-read** — confirm %Undefined%+Atom universals (hyperon), TODO `[?]` above.
4. **math library shims** — 48 missing ops, Int/Float-preserving.
5. **interpreter.metta 43-split** — needs a CORRECTED classifier (chain-bug symptom = free var `$X`, NOT
   Error; the first classifier wrongly reported chain-bug=0). Re-run before the baseline is honest-real.
