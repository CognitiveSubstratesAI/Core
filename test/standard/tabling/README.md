# Tabling tests — read this before adding one

## THE RULE

**Assert `tabled != []` BEFORE asserting anything else.** `@test !isempty(tb)` is the first line of
every tabling testset, not a nicety.

**Why, measured 2026-09-02:** four green-but-vacuous results in one day. *None* was caught by an
assertion; all four were caught by an anti-vacuity check or by a control that was supposed to pass.

| vacuous result | why it was green | caught by |
|---|---|---|
| `mm2_zam_answers` gate test | bangs passed as `"!(z 1)"`; API takes them **bare** ⇒ every gate declined | a POSITIVE CONTROL failing |
| acyclic `reach` differential | `auto_table!` returned `Symbol[]` ⇒ compared untabled **to untabled** | `tabled=Symbol[]` in the dump |
| gate-5 "declined" assertions | would pass identically if nothing ran at all | pairing each decline with a must-be-SERVED control |
| ZAM "absent" ×3 (not a test, same shape) | name search over a capability named something else | opening the file |

A test asserting only "X is rejected / declined / empty" is **indistinguishable from a test where
nothing ran**. Pair every negative with a positive control.

## Idioms that cost time when guessed

* **Explicit `table!(:head)` (`Tabling.jl:334`), not `auto_table!`** — and the reason is broader than
  it looks. MEASURED 2026-09-02 by printing the refusal fields, which is the only way to know:

      tabled = Symbol[]   skipped = [:reach]   multivalued = [:reach]   higher_order = Symbol[]

  `reach` is refused as **MULTIVALUED** — it has TWO CLAUSES. Not for `match &self`, not for
  impurity. ⚠️ This file previously said "refuses `match &self` predicates"; that was TYPED, NOT
  MEASURED, and wrong. The real rule is far wider: **`auto_table!` skips ANY multi-clause
  predicate**, which is most interesting tabling programs — and it is principled rather than a
  gap, because tabling is SET semantics and MeTTa is MULTISET, so tabling a multivalued head
  would silently collapse multiplicity.
  ⇒ Any recursive predicate worth tabling is multi-clause, so `auto_table!` will skip it and a
  differential built on it compares UNTABLED TO UNTABLED. Always pass heads explicitly, and check
  `info.skipped` / `info.multivalued` when a head you expected is missing from `info.tabled`.
* **Edges are space DATA, not `(=)` rules.** `(= (edge a b) T)` + `(= (anc $x $y) (edge $x $y))`
  diverges in `narrow_bindings`. Use `(edge a b)` as an atom and query it:
  `(= (reach $x $y) (match &self (edge $x $y) True))`.
* **`(, A B)` is a TUPLE, not conjunction.** `(= (reach $x $y) (, (match …) (reach $z $y)))` returns
  `(, True True)`. Bind and recurse INSIDE the match template:
  `(match &self (edge $x $z) (reach $z $y))`.
* **`!`-queries surface VALUES, not substitutions**, so a bare `!(reach a $y)` cannot see substitution
  loss in either arm. Carry the call variable into the answer with a wrapper —
  `(= (m $u) (pair $u (reach a $u)))`, then `!(m $w)` — and the defect appears as `(pair $w True)`
  or a missing pair. See `test_answer_substitution.jl`.

## Oracles, strongest first

1. **SWI differential** — `test_tabling_swipl_differential.jl:126` already has the cyclic `conn`
   with the symmetry clause. A second ENGINE, and the strongest oracle here for that predicate.
   ⚠️ **BUT CHECK ITS QUERY SHAPE BEFORE LEANING ON IT.** Verified 2026-09-02: it queries
   `!(conn schiphol amsterdam)` — a GROUND call. It never queries with a variable, so it does NOT
   establish that match-template bindings propagate to the caller. If your test needs the answer to
   CARRY a binding, make the template return the node — `(match &self (edge $x $y) $y)`, not
   `... True)` — instead of assuming propagation this oracle never exercised.
2. **Machine-computed expectation** — e.g. a short Julia BFS over the edge list. Computed, not typed.
3. **Core's own untabled arm** — trustworthy but **ACYCLIC ONLY**: a cyclic program
   (`(= (reach $x $y) (reach $y $x))`) hits the interpret step limit untabled. Measured.

⚠️ A cyclic program having no untabled arm does NOT mean it has no oracle — it means use (1) or (2).
