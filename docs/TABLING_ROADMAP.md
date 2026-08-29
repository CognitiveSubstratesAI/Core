# Tabling / SLG — task list

**Created 2026-08-16** from a source survey of `swipl-devel`, `jetta`, `PeTTa` and `CeTTa`.
Every item cites the upstream file:line it came from and the check that decides it is done.

> **Ordering rule, recorded 2026-08-11 and re-derived 2026-08-15 after I proposed its reverse:**
> **bounds → scope → precision.** Finer invalidation before bounds and scope would *unmask* a latent
> defect rather than fix one — our coarse per-space stamp over-evicts, which is **sound by
> construction**, while precision depends on a *complete* dependency graph and a missed edge serves a
> stale answer. See `[[reference_petta_memo_library_pr165]]`.

---

## ⚠️ READ FIRST — THE ENGINE QUESTION IS OPEN (added 2026-08-16)

`Core/docs/tabling_delimited_control_spec.md` (Desouter et al., **tabling in under 600 lines
of Prolog** via delimited control) shows this whole roadmap may be scoped against the wrong base.

**OUR ENGINE IS THE "EXTENSION TABLE" DESIGN, WHICH THAT PAPER NAMES AND REJECTS:** `_leader_pass` is
RE-RUN each fixpoint round (`Tabling.jl:374-380, :467-473`), i.e. we recompute suspended goals rather
than resuming them. *"The approach cannot achieve satisfactory performance as suspended goals are
always re-evaluated."*

⚠️ **AN EARLIER VERSION OF THIS PREAMBLE CLAIMED THIS ALSO EXPLAINS 2.0. IT DOES NOT — RETRACTED
2026-08-16.** Recomputation does force `unique`, but **tabling is SET-SEMANTICS BY DESIGN in every
implementation**: the delimited-control paper dedups deliberately (§4.4 `store_answer/2` *"only
store it in case it has not"*) and SWI dedups structurally (`wkl_add_answer` takes a `trie_node*`
— a trie IS a set). ⇒ **2.0 is a LANGUAGE-LEVEL mismatch — tabling is set, MeTTa is multiset —
and moving the base would NOT fix it.** What recomputation actually costs is PERFORMANCE (*"suspended
goals are always re-evaluated"*) and the missing structures below.

⇒ **DECIDED 2026-08-16: the target is ALL of SWI §7, and the BASE MOVES FIRST** (§1.0). Building 7.7/7.8/7.11 on the recomputation base means building them twice.
>
> Original wording, kept because the reasoning still holds: **decide the engine question before building §1.** The gap to their design is TWO STRUCTURES and
ONE PRIMITIVE (`dependency(Source, Cont, Target)`, a worklist dequeue, and `shift`/`reset`) — and
`Eval.jl` is already a *"continuation-passing stack machine"*, which is the substrate delimited
control needs. Adding SWI's nine attributes to a recomputation engine may cost more than moving the
base and getting 2.0 for free.

---

## 0n. ✅ THE TABLING CHAPTER IS VERSION-STABLE 10.1.9 → 10.1.13 (checked 2026-08-27)

**Do not re-read a newer SWI manual for tabling; this diff has been run.** Chapter 7 ("Tabled
execution (SLG resolution)", §7.1–§7.13) is **content-identical** between
`docs/specs/prolog/SWI-Prolog-10.1.9.pdf` and `docs/research/papers/prolog/SWI-Prolog-10.1.13.pdf`.

    chapter 7 diff : 46 changed lines — ALL running headers with shifted page numbers
                     ("7.2. EXAMPLE 2 … 361" -> "… 365"). Zero content changes.
    whole manual   : 33 201 changed lines

So the manual DID move substantially — just not here. §7.4's early-completion wording is byte-for-byte
the same in both, which is what §0m below rests on. Our differential oracle runs **10.1.12**, between
the two, so it is covered by that stability.

⚠️ SCOPE: this says nothing about the other chapters, where those 33k lines live. If work ever leans
on a different chapter, re-run the diff for THAT chapter rather than citing this row.

---

## 0p. 🛑 TRIED AND REVERTED — "record the read pattern, unify instead of blanket-invalidating"

**ATTEMPTED 2026-08-28, UNSOUND, reverted the same hour. Do not re-attempt this shape.**

The goal was right and still is: `_DYN_ALL` invalidates EVERY full-scan table on EVERY mutation, where
upstream's `dyn_affected/2` (boot/tabling.pl:1811) is a UNIFICATION —
`trie_gen(VTable, Term, ATrie)`. Measured over-invalidation: a table reading `(fact $z $w)` is
invalidated by adding `(other x y)`.

**The attempt:** have `dyn_read!` record the PATTERN alongside the owner, and have `dyn_changed!`
invalidate a full-scan table only when some recorded pattern unifies with the mutated atom.

**The result — UNDER-invalidation, which is strictly worse:**

    after (other x y)  [unrelated, must stay valid]   invalid=false   ✓ looked like success
    after (fact c 3)   [RELEVANT, must invalidate]    invalid=false   ✗ nothing invalidates at all

**WHY, and this is the part worth keeping.** `dyn_read!` is called from `query()`
(`Eval.jl:1033`), and `query` is only ever called with `(= subj $X)` or `(: subj $T)` — five call
sites, all rule/type lookups. So the pattern in scope there is a **RULE-LOOKUP** pattern, which can
never unify with a data atom like `(fact c 3)`. And `match`/`_match_pat` (`Eval.jl:2485`) does not
call `dyn_read!` **at all** — it full-scans `all_atoms` and records nothing.

⇒ **`_DYN_ALL` MEMBERSHIP DOES NOT MEAN "THIS TABLE READ ALL THE DATA".** It means "this table did a
rule lookup whose subject was non-discriminable (a Var, a Grounded, or a compound head)". The blanket
invalidation is not imprecision on top of a known read set — there IS no recorded data-read set.

⇒ So the precision fix REQUIRES `_match_pat` to record what it scanned for, which is a change to
MeTTa's primary query primitive, not to the IDG. That is the prerequisite, and it is the same
`_match_pat`-records-nothing fact that §0m rests on.

⚠️ The first probe result looked like a clean fix because the unrelated-mutation case passed. It only
failed under the RELEVANT-mutation case. Any retry must assert BOTH directions in the same run —
over-invalidation is sound, under-invalidation is the one failure an IDG must not have.

---

## 0s. 🔴 §0r's DIAGNOSIS WAS WRONG — the binding is NOT lost; the gap is `NotReducible` vs FAILURE

**MEASURED 2026-08-29, and it replaces the cause given in §0r below.**

    (= (p a) True) (= (p b) True) (= (r a) True)     `m :- p(X), r(X)`
    !(let $c (p $x) (r $x))   ->   [(r b), True]

**BOTH alternatives were tried** — `(r a)` reduced to `True`, `(r b)` came back unreduced. So `$x`
WAS bound to `a` and to `b`. §0r's "the call succeeds with `$b` STILL UNBOUND" is false.

### The actual divergence

Prolog: an unmatched goal **FAILS** and contributes nothing.
MeTTa: an unmatched call returns **ITSELF** — `NotReducible`, `metta_language_spec.md` §2.5,
*"returns the unchanged function call"*. The corpus harness counts any answer as a derivation, so an
UNSATISFIABLE literal reads as a successful one. That is p60's over-derivation, and it is a
translation-semantics gap, not a binding bug.

### 🛑 AND THE OBVIOUS FIX IS WRONG — TRIED, MEASURED, REVERTED

Force each CALL literal to succeed by binding it to `True` instead of a throwaway `$cN`:

    (let True (p $x) (let True (r $x) True))   ->   [True]      ← correct on the toy!
    both satisfiable -> [True, True] · no `p` at all -> []      ← and no regression there

**It broke NINE assertions across the corpus** (139/148). The pattern:

    got_true  String[]                     want ["(s)"]          ← was TRUE, now nothing
    got_undef ["(p)","(q)","(r)","(s)"]    want String[]         ← now UNDEFINED

⇒ **`True` IS A TWO-VALUED PATTERN IN A THREE-VALUED LOGIC.** A literal evaluates to `True`, to
`Empty` (failure), **or to a WFS BOTTOM**. `(let True ⊥ …)` matches ⊥ against the symbol `True` and
⊥-propagation turns the whole derivation undefined — so definite answers become undefined in exactly
the programs this corpus exists to test.

⇒ **A correct fix must be THREE-WAY**: accept `True`, accept a bottom (propagating it), and reject
only an UNREDUCED term. That is not expressible as a `let` pattern and needs a guard that can tell
"did not reduce" from "reduced to undefined".

### Also settled, so nobody re-derives it

* `superpose-bind` does NOT evaluate its argument (`superpose_bind_op` only `subst`s it), so
  `(superpose-bind (collapse-bind X))` yields EMPTY. It must be sequenced —
  `(chain (collapse-bind X) $c (superpose-bind $c))` — which is exactly how `EmitIL` emits it.
* And that round trip gives the SAME answer as the bare call (`[True, (r b)]`), so **collapse-bind is
  not the missing piece for this problem at all**. §0r's closing recommendation was wrong too.

---

## 0r. 🔴 THE GENERATIVE CALL LOSES ITS BINDING AND SILENTLY OVER-DERIVES (measured 2026-08-28)

**This is a WRONG ANSWER, not a missing feature — and it is why the refusal must stay.**

Lifted the generative-call refusal, regenerated the corpus (71 translated / 1 refused), and ran the
REAL harness against the REAL gold rather than a hand translation:

| | result |
|---|---|
| **p80** | **13/13 — PASSES.** Its structure never exposes the defect. |
| **p60** | **FAILS.** got `{q2,q3,q4,s2}` · gold `{p2,p3,p4,q3,q4,s2}` |
| p29 | diverges (early completion; `findall(B,e(B,0),L)` times out in SWI too) |

### The cause — one defect, four cascading mismatches

A generative call returns its RHS **value** and does not report the binding:

    (= (p a) True)  (= (p b) True)        !(p $x)   ->   [True, True]      ← $x is LOST

So in `q(A) :- q(B), t(A,B)` the call `(q $b)` succeeds with `$b` **still unbound**, and the next
literal `(match &self (t 2 $b) True)` then matches ANY `t` fact — deriving `q(2)` from nothing.
`q(2)` wrongly TRUE makes `tnot(q(2))` fail, which loses `p(2)`, `p(3)`, `p(4)`. All four p60
mismatches are that single over-derivation.

### 🔑 TWO THINGS TO CARRY FORWARD

1. **p80 PASSING IS A FALSE POSITIVE.** I lifted the refusal on the strength of it and would have
   shipped a translator that silently over-derives. One passing program is not evidence about a
   SHAPE — grade the whole corpus before believing a lifted refusal.
2. **`collapse-bind` IS NOT BROKEN.** Wrapped as `EmitIL` emits it —
   `(collapse-bind (metta (p $x) %Undefined% &self))` — it returns `(Atom Bindings)` pairs carrying
   `Binding($x, b)` and `Binding($x, a)`, exactly its contract. An earlier probe of mine passed a
   BARE goal, captured nothing, and I mis-read that as a defect. The capture mechanism works; what is
   missing is a LOWERING that uses it so the binding reaches the continuation.

⇒ So the fix is translator work over a working engine primitive: emit the collapse-bind/superpose-bind
form for a generative call instead of a bare call. Until then the refusal stands, and its reason in
`translate_corpus.pl` now names over-derivation rather than early completion (true of p29 only).

---

## 0q. XSB `incremental_tests` — BLOCKED BY GENERATIVE CALLS, not by the declaration (2026-08-28)

⚠️ **I claimed earlier today that honouring `as incremental` would unblock this corpus. It does not.**
That was asserted from the declaration throwing, without reading the programs. `as incremental` was
**a** blocker; it was not **the** blocker.

**Read the 15 active programs** (`xsb_test_incremental.pl` enumerates them; SWI itself comments out
~6 more). Every one with a tabled rule has the shape `translate_corpus.pl` already refuses:

    incremental_rule       t(X)   :- p(X).                      <- X bound BY the call
    test_incr_depends      baz(X) :- foo(X).
    test_wfs_update        pd_caller(X) :- pd(X).
    test_incr_depends_2    cyc(X,Y) :- cyc(X,Z), …, p(Z,Y).

Same shape as wfs p29/p60/p80. And FIVE of the fifteen route everything through
`incr_writeln(Term) :- write(incr(Term)), writeln('.')` — I/O, which the translator drops as harness,
so their gold is a stdout TRANSCRIPT with no truth-value content to grade against.

⇒ Realistic oracle value is ~10 programs, not 16, and ALL of them wait on one capability.

### What completing it would actually need, in order

1. **generative calls** — thread a call's answers into the continuation. **THE prerequisite.**
2. a STAGED-MUTATION harness — (query, mutate, query, mutate, query). Neither existing corpus has
   this shape: wfs is one truth table, delay is one stdout.
3. `incr_assert` / `incr_retract` of **RULES**, not facts — `incr_assert((p(X) :- f(1,X)))`, 55+40 uses.
4. `abolish_table_call` — 11 uses; we have only `abolish_all_tables!`.
5. stdout-transcript comparison for the five I/O-driven programs.
   ✅ `get_residual` (55 uses) we already have.

### 🔑 SO DO THE GENERATIVE CALL FIRST — it is now confirmed from TWO corpora

It unblocks p29/p60/p80 in the **wfs** corpus, which already has a working harness and validated
gold, so it is verifiable the day it lands. `incremental_tests` needs it anyway. One capability,
two upstream corpora — and §0m reached the same conclusion from the early-completion direction.

✅ **WHAT DID LAND, and the corpus confirmed it was genuinely needed:** `incremental!` / `opaque!`
(`tabling/Options.jl`) declare a head incremental WITHOUT tabling it — upstream's
`:- dynamic p/1 as incremental`. The corpus needs exactly that split (`:- dynamic p/1 as incremental`
for the DATA, `:- table t/1 as incremental` for the TABLE), and `table_as!` cannot express it because
it tables unconditionally. `boot/init.pl:234` shows why they are orthogonal: `as incremental` is a
GENERIC attribute option, expanded identically for `dynamic` and `table`.

---

## 0m. EARLY COMPLETION — ALREADY SETTLED AS "UNSOUND, PINNED, NOT PORTED"; this row adds the p29 LINK (2026-08-27)

> ⚠️ **I RE-DERIVED A SETTLED RESULT. Read these two FIRST — they predate this row:**
> * `workflows/CODEMAP.md` row 166: *"PARTIAL BY MEASUREMENT: 7.4 — early completion is UNSOUND for
>   MeTTa (a ground call has many answers because an answer is a VALUE)."*
> * `Core/test/standard/tabling/test_monotonic.jl:222` —
>   `@testset "§7.4 early completion is UNSOUND for MeTTa — pinned, not ported"`, whose comment says
>   *"This test exists so nobody ports it from the manual later."* It exists because of exactly this
>   failure mode, and it did not stop me, because I went to `pl-tabling.c` and the manual instead of
>   searching our own tree first. **It is NOT unported — it is DELIBERATELY not ported, with a gate.**
>
> What is genuinely new below, and only this: (1) the link to XSB **p29/p60/p80**, which are refused
> for this reason; (2) the sharper condition — first **DEFINITE** answer, not first answer; (3) the
> implementation site is **`interpret`**, not `metta_run`; (4) the ch7 version-stability diff (§0n).



**Upstream has it; we have nothing keyed on groundness at all.** Grep across `Tabling.jl` +
`tabling/*.jl`: `is_complete`, `_wfs_complete!`, `set_table_status!` — and ZERO early-completion
concept.

### The upstream mechanism, traced end to end

```c
pl-tabling.c:1148   if ( wl->ground )            /* early completion */
                      return UDL_COMPLETE;
pl-tabling.c:3681   case UDL_COMPLETE: PL_unify_atom(A4, ATOM_cut)
```
```prolog
boot/tabling.pl:617   '$tbl_wkl_add_answer'(WorkList, Skeleton, Delays, Complete),
                      Complete == !,
                      !                          % cut the producer's remaining clauses
```

`wl->ground` is set when the answer trie has no variables (`:2577` sets the `WL_GROUND` sentinel,
`:2920` carries it into the worklist). So: **a GROUND tabled subgoal that derives an UNCONDITIONAL
answer completes immediately and CUTS its remaining clauses.**

🔑 The driver is `delim/4` — the DELIMITED-CONTROL loop (`reset/3`). Our analogue is
`_leader_pass` (`Tabling.jl:1032`), whose `for qb in query(space, (= key X))` loop IS the clause
iteration a cut would abandon. So the hook point exists.

### 🔴🔴 BUT IT IS **NOT** DIRECTLY PORTABLE — the soundness precondition is a PROLOG fact

Upstream's cut is sound because `wl->ground` bounds the answer set: **a ground Prolog subgoal has AT
MOST ONE answer** (yes/no — the answer skeleton has no variables, `:2577` `isEmptyBuffer(&vars)`).
Once you have it, no remaining clause can contribute anything new, so cutting is free.

**MeTTa violates that precondition BY DESIGN.** `(=)` is multi-result (`metta_language_spec.md`
Invariant 6), so a GROUND goal can reduce to many different VALUES. MEASURED 2026-08-27:

    (= (g) 1)  (= (g) 2)      !(g)  untabled -> [2, 1]      TWO answers
                              !(g)  TABLED   -> [1, 2]      TWO answers

⇒ **A naive port would SILENTLY DROP ANSWERS** — `[1]` instead of `[1,2]`, no error. That is the
worst failure shape available here, and it is exactly what "port the semantics, not the mechanism"
is meant to catch. `wl->ground` is not the condition we need; the condition we need is "no remaining
rule can contribute a NEW answer", which is not decidable from groundness in MeTTa.

### So it needs a DECISION, not just an implementation

Two candidate routes, neither free, and the choice is a semantics call:

* **(a) An opt-in table mode** — the caller declares the predicate is Prolog-shaped (success is one
  bit, not a value set), and early completion applies only there. Honest, and it mirrors how upstream
  scopes `as incremental`. Cost: a new declaration surface, and `Options.jl` currently REFUSES the
  modes it does not implement rather than accepting dead ones.
* **(b) A derived condition** — cut only when every remaining rule for the key provably cannot yield
  a new value. Sound in general but needs an analysis we do not have, and is the more expensive path.
* **(c) 🟢 SCOPE IT TO ONE-BIT QUESTIONS — the likeliest right answer, from the manual's own framing.**
  SWI-Prolog 10.1.9 §7.4 (`docs/specs/prolog/SWI-Prolog-10.1.9.pdf`, and the `_ch7_tabling_spec.md`
  extraction :273): *"Ground goals … are considered completed after the first solution."* Its
  illustration is `p(42)` against a 10 000-answer table — and `p(42)` is a **MEMBERSHIP** question:
  *does this hold?* One solution settles it.

  ⇒ **PROLOG ASKS "DOES IT HOLD"; METTA ASKS "WHAT DOES IT REDUCE TO".** Early completion answers a
  question `(=)`-reduction does not ask, which is precisely why the ground precondition does not
  transfer. But several of OUR questions ARE one-bit, and there the cut is sound by construction:
    * `tnot(G)` needs only whether `G` has an answer, never which ones;
    * the corpus harness classifies on `isempty(answers)` (`_xw_run` / `_xd_run`);
    * `findall`/`collapse` ground-goal short-circuit — already named as the §7.4 target in this very
      extraction's own mapping table (":1070").
  So the sound port is **an existence query that short-circuits**, NOT a cut inside general `(=)`
  reduction. The question type carries the soundness, so nothing needs to be declared or inferred.

  ✅ **NOW VERIFIED FOR p29, AND THE CONDITION IS SHARPER THAN "EXISTENCE"** (measured 2026-08-27):

      rule 1 ONLY               (w 0) -> [True]        0.0s     <- DEFINITE answer
      rule 1 + rule 2 (full)    (w 0) -> diverges (killed at 250s; never wrote its line)

  Rule 1 yields a **definite** answer instantly, so stopping at the FIRST DEFINITE (non-undefined)
  answer never reaches rule 2 and p29 terminates with `True` — the gold value.
  🔑 The condition is **first DEFINITE answer**, NOT first answer: the harness still needs full
  enumeration to separate UNDEFINED (answers, all ⊥) from FALSE (no answers). Only the TRUE case
  short-circuits — which is exactly p29/p60/p80's case.

  🔴 **BUT THE IMPLEMENTATION SITE IS `interpret`, NOT A WRAPPER — and that is the real cost.**

      metta_run(...)      for (at,bnd) in metta_results(atom, space, b)   # ALREADY fully computed
      metta_results(...)  = interpret(_metta(atom, UNDEF), space, b)      # the stack machine

  `interpret` returns a FULLY-COMPUTED `Vector`, so by the time `metta_run` loops, the divergence has
  already happened. An early exit in `metta_run` saves nothing. The stop-condition has to be threaded
  through the iterative stack machine itself — the deepest eval-core code, under the standing "no
  eval-core change without measured need" guardrail.

  ⇒ **DECISION POINT, not a task.** The measured need now exists (3 corpus programs, plus `tnot`
  doing redundant full enumeration on a question its own comment calls one-bit: *"asks whether the
  table is empty"*). But the change is invasive and touches the machine every other test depends on.
  Weigh that against the status quo — 3 of 72 refused, honestly, with the reason recorded.

⚠️ DO NOT implement `if ground(key) → cut`. It is the obvious reading of the C and it is WRONG here.
The Prolog-translated corpora (wfs/delay) happen to be one-bit-success programs, so it would look
correct on every test we currently run while being wrong for ordinary MeTTa.

### The measured consequence — XSB p29 (also p60, p80)

```prolog
e(s(A),0) :- e(A,0).          % generative + recursive
w(A) :- tnot(u(A)).           % clause 1 — yields the answer
w(A) :- e(B,A), tnot(w(B)).   % clause 2 — reaches the divergent call
```

| | swipl 10.1.12 | ours |
|---|---|---|
| `findall(B, e(B,0), L)` | **timeout** | diverges (ErrorException @ 5.9s) |
| `findall(x, w(0), L)` | **`[x]`** | diverges |

`e(B,0)` diverges in BOTH — that is not our bug. swipl still answers `w(0)` because `w(0)` is ground,
clause 1 gives an unconditional answer, and early completion cuts clause 2 before it reaches `e`.

⇒ `wfs_programs.tsv` refuses p29/p60/p80 with exactly this reason. They are **engine** gaps, not
translator gaps — the translation is correct.

### ⚠️ AND THE FIRST DIAGNOSIS WAS WRONG, which is why this entry exists

It was committed as *"a CALL binds a variable used later; our form discards call results"*, read off
`binder_of/3` and never executed. Executed, it is false — the binding propagates:
`!(let $c (e $b 1) (tnot (w $b)))` → `(tnot (w a))`, `$b` bound. Do not re-derive the binding theory;
it has been tested and refuted.

---

## 0. BLOCKERS — these gate other work, and two are live defects

| # | item | why it blocks | verify |
|---|---|---|---|
| **0.1** | **`_pure_heads` classifies compiled IL as IMPURE.** `EmitIL` emits `(function (chain (metta …) …))`; none of `function`/`chain`/`metta`/`return`/`evalc` is in `_PURE_PRIMS`, so **every compiled head is impure**. MEASURED: `:fib` pure in source = `true`, in IL form = `false`. | **Every purity-gated feature is silently inert on the compiled lane.** `auto_table!` is the one we noticed — it is not necessarily the only one. Blocks 1.x and 3.1. | add the 6 ops; assert `:fib` pure in IL form; **then re-run the proved corpus** — `_pure_heads` also feeds `purity_may_mutate` → region splitting → Invariant 1 |
| **0.2** | 🟢 **LARGELY DONE 2026-08-16 (`21bd63b`).** Cause moved twice (the `()` and `_instr` stories were both void) before landing on the real one: **BINDERS**. `_BINDER_KEEP_FROM` (derived from the declared types — `Variable` in an argument position) + PeTTa's middle clause, shipped together because the mutation check proves either alone is unsafe. **MEASURED EFFECT ON THE REAL LIBRARIES:** PLN **17 → 3 declines** — the 13 `\|-` inference rules now COMPILE, which was this item's whole target. ECAN **1 → 14**, and **all 14 are binder-related and were previously MIS-COMPILED**: with binders off, `sum-prob-weights` emitted `(unify ($Pr $w) $pt (chain (metta (+ $acc $w) …) …))` with `$acc`/`$pt` FREE, the fold template hoisted OUT and evaluated eagerly, and `foldl-atom` handed a VALUE where it expects a TEMPLATE. ⇒ the ECAN "regression" converts silent WRONG ANSWERS into safe DECLINES. | — | **REMAINING: 3 in PLN** (`StampDisjoint`, `PLN.Derive`, `PLN.Query` — none binder-related) **and 14 in ECAN**, which now need binder-aware EMISSION: `EmitIL` has no way to express a `GCall` whose template argument is an unlowered term. That is a design question about how a template crosses into minimal MeTTa, not another predicate. |
| **0.3** | **`_TABLED_HEADS` is process-global.** `untable_all!` is the only removal. | A `compile_run` needs a `finally` to avoid changing the next caller's semantics; per-head undo would make it scoped. Feeds 2.2. | two `compile_run` calls in one process; assert the second is unaffected |

---

## 0h. 7.C DONE (as a REGRESSION FIX), 7.D's PREMISE MEASURED — 2026-08-17

### 7.C — and it landed as a bug fix, not a feature

Making the bottom residuated **broke dedup**, and the suite did not catch it: 89 files / 0 failed
while `(r)` returned **two** `undefined` answers where it had returned one. While `UNDEFINED` was a
singleton, two bottoms were `==` and collapsed; carrying a DNF makes them distinct atoms. Found by a
two-paradox probe the same day, because the suite never covered a goal undefined via two derivations.

Upstream cannot have this bug, and the reason is exactly 7.C: `delay_info` hangs off the TRIE NODE,
so one answer term has ONE record holding a DISJUNCTION of `delay_set`s. Several derivations
contribute alternative conjunctions to the same answer — they do not become several answers.
`merge_bottom_into!` restores that: `⊥{A}` and `⊥{B}` are one answer conditional on `A ∨ B`.

**A second gap surfaced with it.** The `== UNDEFINED` sweep converted the *conditions* but left
`ExecOk(Atom[UNDEFINED])` returning the bare constant, so the DNF died at the first binary op. Ten
sites; the 7.D test is what exposed it. Contagion now propagates the found bottom everywhere, and the
alternating fixpoint's own bottom (`_wfs_bottom_for`) carries the disjunction of what its optimistic
answers were conditional on.

### 7.D — the premise, measured rather than argued

In Prolog an answer is a substitution and the condition is SEPARATE, so `p(a)` is stored
conditionally with its value intact — simplify the condition away and `a` is still there. Here
`(+ 1 ⊥)` cannot form a value at all: strict-op contagion returns the BOTTOM. We never hold "4,
conditional on p"; we hold ⊥. **If p is later refuted, the 4 is not waiting to be un-delayed — it was
never computed, and the producer must RE-RUN.** ⇒ 7.D is a genuine divergence, not an unported
detail, and that is now a test rather than a paragraph.

### Static analysis (JET + AllocCheck, global env)

Run with a POSITIVE CONTROL first — a JET sweep reporting zero proves nothing until a deliberately
dynamic function is shown to be reported.

| result | reading |
|---|---|
| 56 `report_opt` findings over 18 functions | root cause is abstract `Atom` (`Atoms.jl:22`) reached via `Vector{Atom}` — the correct representation for a term language, PRE-EXISTING, guarded by `[[reference_core_interpreter_perf_findings]]` |
| no `Any` in the new files | the only match is a comment saying we avoid it |
| `is_undefined` | narrowed to `a isa Grounded{WFSBottom}` — one concrete check, **JET 0, ZERO allocations** on every concrete type. Was an unparameterised `isa` plus a dynamic field read, behind ~34 call sites |
| ⚠️ an earlier "1 allocation site" reading was FALSE | `check_allocs` asserts on a non-dispatch signature; the `catch` counted the AssertionError as a finding. Concrete signatures only |

### Tooling: `CORE_SUITE_SHARD=i/n`

The suite outgrew the 10-minute window a wrapped runner can wait for, and backgrounding it is what
the hooks forbid. Sharding keeps each lane inside the window while covering every file across lanes.
**A sharded run announces itself loudly** — a partial run printing the same summary as a full one is
how "89 files, 0 failed" comes to mean nothing. Measured: cold load is **3.2 s**, so cold start was
never the cost; ~265 s is test execution and the rest is JIT.

---

## 0g. 🟢 7.A PART TWO + 7.B — DELAY LISTS: THE CONDITION RIDES ON THE VALUE (2026-08-17)

`src/standard/tabling/Delays.jl` + a residuated `WFSBottom`. 36 tests.

**We already had the third truth value** — the alternating fixpoint computes the same WFS model SWI
computes with delay lists + simplification. What we did not have is the **reason**. An answer is now
undefined *because of* named literals, readable via `answer_residual`.

### The adaptation, and why it is forced

SWI keeps conditionality in `LD->tabling.delay_list`, a trail-scoped thread-global scraped at
insertion time. Correct there because the engine runs **exactly one derivation** and the trail erases
abandoned ones. We map over a **collection** of values: at the k-th insertion there is no "current
branch", and a literal port leaks value #1's condition onto value #2 with no trail to unwind it. So
`WFSBottom` carries its own DNF, and conjunction is **explicit** (`dnf_and`, which distributes) where
upstream gets it implicitly from pushing onto one register. `dnf_and` is the operation upstream does
not need at all.

⚠️ **Empty is the UNIT, not the zero.** Unconditional ∧ conditional = conditional; and an unrecorded
reason is "no information", never "unsatisfiable". Reading empty as false inverts the lattice, and it
reads plausible — hence a test for it at both levels (`dnf_and`, and `answer_residual`).

### 7.B — settled, and honestly

`DELAY_NEGATIVE_ANSWER` exists because 7.B decides a **struct field** and the struct was being
written. Upstream has two kinds encoded by `answer == NULL`; a value language also needs
`(not (== (f a) 3))`, and upstream's struct has nowhere to put the 3. **No site produces it yet** —
our `tnot` is table-level — and the tests assert that rather than let the enum look implemented.

### The sweep that had to come first

~34 sites asked `x == UNDEFINED`. Every one was a **type test wearing a value test's clothes**: a
residuated bottom is not `==` to the bare constant, so all 34 would have silently answered false and
treated it as an ordinary value — a soundness bug in the strict-op layer. `is_undefined` landed
first, the sweep was verified behaviour-preserving on its own (88/88), and only then did the field go
in. The two WFS test harnesses needed the same fix, which is the test-layer instance of the same
defect.

| measured | result |
|---|---|
| end-to-end | `p :- tnot(q), q :- tnot(p)` yields a residual naming `q` — **not** the vacuous `True` |
| oracle safety | the bottom still PRINTS `"undefined"`, so the swipl WFS differentials compare unchanged |
| suite | 89 files / 0 failed, health 6/6 |

### What remains: 7.C and 7.D

Both are about REVISION, not representation, and both are now unblocked but unbuilt:
**7.C** — conditionality is per answer KEY upstream (`data.delayinfo` hangs off the trie node) and
unconditional re-derivation ERASES it; that is sound under set semantics and interacts with roadmap
2.0 (multiset). **7.D** — SWI's `remove_conditional_answer` drops the conjunct and the answer,
relying on ordinary resolution to re-derive next round; in a value language `(+ 1 (f a))` produced
`4` BECAUSE `(f a)` gave `3`, so if `3` is refuted we may have to **RE-RUN THE PRODUCER**, which SWI
never does.

---

## 0k. 🟢 §7.6.1 SIMPLIFICATION — MOTIVATION MEASURED AWAY, ~675 LINES NOT BUILT (2026-08-18)

A spec agent scoped simplification at **~675 lines** and produced probes showing three wrong answers
it would fix. Step 0 of that spec — the SCC-union fix, **44 lines, shipped as `0c2ff93`** — was the
prerequisite. After it landed, the SAME probes were re-run:

| case | after Step 0 | verdict |
|---|---|---|
| chain `q ← r ← p` with `(= (p) (tnot (q)))` | `q=[1] p=[] r=[]` | ✅ the WFS model |
| pure paradox | both `undefined` | ✅ correct, and must stay so |
| conditional-then-definite | `p=[] q=["1","True"]` | ✅ correct — `tnot(p)` RETURNS the value `True` here |

⇒ **every case simplification was to fix is already right.** The remaining upstream machinery
(`simplify_component`, `propagate_to_answer`, `make_answer_unconditional`) has **no demonstrable
consumer in this engine**, so building it now would be building against a premise we can no longer
reproduce. NOT BUILT, deliberately. `[[feedback_measured_need_not_checklist]]`

⚠️ **The third row is a lesson in reading our own semantics.** The expected value was written as
`q=[1]`, which is the Prolog answer; in a VALUE language `(= (q) (tnot (p)))` with `p` false yields
the atom `True`, so `["1","True"]` is right. A "wrong answer" that is actually a wrong expectation is
exactly how a port acquires unnecessary features.

**What genuinely remains** of §7.6.1 is the REPORTING surface, not the engine: `answer_residual`
works but has no MeTTa-level operation, and `get_residual/2` needs the `library(tables)` shape. That
is tens of lines, not hundreds.

---

## 0j. 🔴🔴 AUDIT ROUND TWO — 27 FINDINGS, 10 SURVIVED REFUTATION, ALL FIXED (2026-08-18)

Four adversarial slices over the delay lists, §7.11.1, the 7.A/7.C metadata work, and a cross-cutting
regression hunt. Each finding was handed to an independent agent whose job was to REFUTE it.

**27 raised · 10 survived · 17 refuted.** The refutation pass is not ceremony: it rejected nearly two
thirds, and on one finding it CONFIRMED the defect while rejecting the finding's own evidence and
severity — *"the defect is REAL and I reproduced it, but the claim's evidence is INVALID and its
attribution is wrong."* Taking that reasoning on trust would have put a wrong rationale in the file.

### The worst one, seen from two ends at once

`WFSBottom` gained a `DelayDNF` field on 2026-08-17 and **no `==` / `hash`**. Julia compares a
struct's `Vector` field by IDENTITY, so two bottoms carrying the SAME reason were different answers:

| measured before the fix | |
|---|---|
| `b1 == b2` (content-identical DNFs) | **false** |
| `Set([b1, b2])` | **2 elements** |
| `issetequal([b1], [b2])` | **false** ← `_wfs_complete!`'s convergence test |

One slice reported it as **non-termination of the alternating fixpoint**, another as **broken variant
identity**. Same bug. `_variant_unique` was *accidentally* safe because `merge_bottom_into!`
intercepts bottoms before the equality test — incidental cover, shared by nothing else, and exactly
how a defect sits under a green suite.

### 🔴 THE STANDING PATTERN: A SWEEP MATCHES A SHAPE, NOT A MEANING

Four sites survived four separate sweeps, each doing the same wrong thing in a different SHAPE:

| site | did | the sweep it evaded |
|---|---|---|
| `case` (`Eval.jl:1974`) | pushed the bare `UNDEFINED` constant | the `ExecOk(Atom[UNDEFINED])` residuation sweep |
| `fire_dependencies!` | `unique` (`==`) | the `_variant_unique` conversion |
| `_wfs_complete!` | `issetequal` (`==`) | same |
| `unify` | took its `else` branch on ⊥ | the strict-op contagion sweep |

⇒ **after a sweep, enumerate by MEANING and check each one, rather than trusting the pattern found
them all.** Three of four slices flagged `case` independently — that is what a real gap looks like
from the outside.

### Also fixed

`tnot` suspended on an in-progress table without first checking for a definite answer (upstream
checks before suspending — sound but needlessly imprecise, and the imprecision propagates), and
`untable!` cleared four registries but not §7.11.1's, so a RETRACTED declaration kept abstracting and
changed answers.

**Commits:** `58f434e` · `cbbca5b` · `94a6a42` · `d664709` · `c1b7b9e`. Verified 89/89, health 6/6.

---

## 0i. 🔴 THE §7.11.1 AUDIT — SIX FINDINGS AGAINST ONE DAY-OLD FEATURE (2026-08-18)

**Everything sections 0d and 0f claim about §7.11.1 being EXACT is RETRACTED. Read this first.**

An adversarial audit of the previous day's own work returned six findings against §7.11.1 — the
feature that had shipped hours earlier with 49 green tests. Fixed in `58f434e` + `cbbca5b`.

| # | defect | how it was settled |
|---|---|---|
| 1 | **the instance filter LOST REAL ANSWERS** | reproduced in 3 lines before touching anything |
| 3 | the abstraction model diverged on **every multi-argument goal** | live swipl oracle, 6 variants |
| 4 | an in-progress general table answered **EMPTY** | read `_PARTIAL`, as the consumer branch does |
| 5 | `subgoal_abstract(N)` did what **SWI refuses to do by default** | live swipl: default action is `error` |
| 2 | the most-general shortcut **skipped specialisation** | route every abstracted call through the arm |
| 6 | a docstring asserted three properties that are **false here** | all three checked from the code body |

### 🔴 #1 — and it is the deepest thing found so far

    (= (e (f a)) v)     (= (e (f (g $x))) (e (f $x)))
    !(e (f (g (g a))))     unrestrained -> ["v"]     subgoal_abstract(1) -> []     ← ANSWER GONE

The general table holds `v` with recorded instance `(e (f a))`; the call is `(e (f (g (g a))))`,
which does not unify with it — yet `v` IS correct, because the call **reduces into** `(e (f a))`.

⇒ **"some instance that produced this answer unifies with the call" is NOT "this answer holds for the
call".** Upstream's test only looks equivalent because a Prolog answer IS a substitution over the goal
skeleton, so unifying the SKELETON carries the CALLER's bindings — it never asks about provenance. In
a rewriting language the call reduces into other instances and no provenance test can see it.
**This is the THIRD ASSUMPTION one level subtler than 7.A found it: recording the instance was not
enough, because the instance does not answer the question.** Recovering precision needs the answer to
carry the caller's bindings — the same representation change 7.D needs.

### 🔴 #3 — the file ARGUED the wrong model, citing the C

It cited `pl-trie.c:768`'s **generic** `from_depth = 1`. Tabling uses `pl-tabling.c:2472`
`{.from_depth = 2}`, and `compounds` is a **depth that unwinds on POP**, not a running total — so the
budget re-arms at **every top-level argument**. Ground truth, live swipl 10.1.12:

| goal | N | swipl |
|---|---|---|
| `p(s(s(s(a))))` | 1 | `p(s(_))` |
| `q(f(a), g(b))` | 1 | **UNCHANGED** ← we abstracted `g(b)` |
| `r(f(a), g(b), h(c))` | 1 | **UNCHANGED** ← we abstracted two arguments |
| `a2(f(g(h(a))), k(l(m(b))))` | 2 | `a2(f(g(_)), k(l(_)))` |

All six rows are now the test. **Reading the source is not reading the CALL SITE** — an executable
oracle settled in one command what re-reading the C had got wrong twice.

### THE STANDING LESSON

Six defects, one day old, 49 green tests, written carefully with upstream citations throughout — and
the citations were part of how it went wrong. **An audit against the source is not optional after a
feature; it is part of shipping it.** `[[feedback_green_suite_hides_unwired_correct_code]]`

---

## 0f. 🟢 7.A PART ONE — PER-ANSWER METADATA ON THE TRIE NODE (2026-08-17)

`TrieNode` gained `instances::Vector{Atom}`; `_leader_pass` records `subst(key, bnd)` — the goal
instance that produced each answer — on the answer's node.

**Why the node, and nowhere else.** The trie is the only store with VARIANT identity: `p($x)` and
`p($y)` reach one node, which is exactly the grouping the metadata needs. A `Dict{Atom,…}` side table
cannot do it (`==` splits variants); an index-aligned parallel vector cannot survive
`_merge_partial`'s dedup. This is why 0e (making the trie authoritative) had to come first.

**Why the recording step exists at all.** In Prolog it does not: an answer IS a substitution over the
goal skeleton, so the node carries the instance inherently and the delay list hangs off the same
node. A MeTTa answer is a VALUE, so the relation — one answer to MANY instances — has to be made
explicit. `_leader_pass` is the ONLY place the binding still exists; one line later it is gone.

| measured | result |
|---|---|
| §7.11.1 precision | ⚠️ **CLAIM RETRACTED 2026-08-18 — the filter that made it "exact" was UNSOUND and LOST ANSWERS. See section 0i.** |
| coverage | 11 of 11 answers carry an instance on `fib 10` |
| cost | **+0.08%** allocations (fib 12: 5,836,784 vs 5,832,208) |
| suite | 88 files / 0 failed |

⚠️ **EMPTY MEANS UNRECORDED, NOT "NO INSTANCE."** Only `_leader_pass` records; answers arriving by
the completion mirror or monotonic propagation have none. A consumer reading empty as "nothing
matches" would DROP answers — turning a documented imprecision into a silent unsoundness, the
strictly worse failure. `abstract_answers` falls back to the over-approximation there, and that
fallback is gated by its own test rather than left to a comment.

### WHAT IS LEFT OF 7.A

The `delays` half. The node now has a home for it, and the two features that need it
(WFS residuation, §7.11.2 `answer_abstract`) are unblocked structurally — but the CONTENT is a
separate decision: a delay condition must ride WITH the value, because our evaluator maps over a
COLLECTION of values where SWI has one linear derivation and a trail to unwind. That is 7.B/7.C.

---

## 0e. 🟢 THE ANSWER TRIE IS THE READ PATH — flipped 2026-08-17 (roadmap 1.0b step 2)

Flipped on the same two-part standard as the resumption flip, MEASURED not argued:

| evidence | result |
|---|---|
| whole suite, trie ON | 88 files / 0 failed |
| whole suite, `CORE_TABLING_TRIE_READ=0` | 88 files / 0 failed — the reverse lane still runs |
| anti-vacuity (`fib 12`) | 13 of 13 tables carried a mirrored trie; `trie_answers(k) == _ANSWER_TABLE[k]` for EVERY key — same answers AND same order |
| cost | **+0.1%** allocations at fib 12 and fib 16 (best of 3) — noise |

⚠️ **The agreement only became real with audit finding #1.** Before it, `_PARTIAL` deduped by `==`
and the trie by VARIANT, so the two stores held different answer COUNTS wherever an answer set
contained variants — this switch was *not* answer-preserving, and the comment claiming it was had
been true only of ground answer sets. Both now use one identity. The evidence above is kept
executable in `test_answer_trie.jl` rather than left in a commit message.

### 🔑 THE REASON TO FLIP IS NOT THE COST — IT IS WHAT IT UNBLOCKS

Per-answer METADATA has no home in a `Vector{Atom}`, and **three separate features now need one**:

| feature | needs |
|---|---|
| §7.11.1 subgoal abstraction | each answer's goal INSTANCE — measured over-approximating without it (0d) |
| delay lists / WFS residuation | per-answer CONDITIONS (7.A) |
| §7.11.2 `answer_abstract` | the same conditions — `radial_restraint` makes its answers conditional |

Upstream keeps all of it on the **trie node**. Making the trie authoritative is the prerequisite
those three share, and it is now done — so 7.A is next, and it pays for three items at once rather
than one.

---

## 0d. §7.11.1 SUBGOAL ABSTRACTION — BUILT 2026-08-17, and it found a THIRD-ASSUMPTION case

`src/standard/tabling/Abstract.jl` + the `start_abstract_tabling` arm in `tabled_eval`. 42 tests.

**It was refused for a reason that was never true.** `Options.jl` had it blocked on "abstraction over
TRIE TERMS at a depth — trie walk not built", i.e. the answer trie as prerequisite. Upstream states
the design in one sentence (`boot/tabling.pl:469-472`): *"This is a merge between variant and
subsumptive tabling."* It rides on §7.5, which we already had. **A refusal reason carried forward
unexamined kept a buildable feature out of reach for weeks** —
`[[feedback_capability_claims_expire_retest_the_premise]]`.

**It is a SIZE BUDGET, not a depth limit.** `aleft` is one counter for the whole term, decremented at
every compound and never restored per branch (`pl-trie.c:893`), DFS pre-order. On `q(f(a), g(b))`
with N=1 a depth limit treats both arguments alike; the budget keeps the first and abstracts the
second. That case is the test that tells the two implementations apart.

### 🔴 …AND IT SURFACED THE THIRD ASSUMPTION AGAIN, BY BEING BUILT

Upstream specialises the general table's answers by UNIFYING the answer against the specific call —
sound because **a Prolog answer IS a substitution over the goal skeleton**. A MeTTa answer is a
**VALUE**: `(= (depth $x) ok)` answers `ok`, which carries no record of which instance produced it.
The Prolog filter has no argument to work on, and the first implementation — a faithful port —
returned EMPTY for every non-ground abstraction.

What is recoverable is the ABSTRACTION BINDING (`match_atoms(gen, red)`), so:

| the answer… | result |
|---|---|
| MENTIONS the abstracted variable | specialised EXACTLY, as upstream |
| does NOT (a constant; two rules → two constants) | **OVER-APPROXIMATES** — cannot be filtered |

Sound in both cases (the real answer is never lost), imprecise in the second. **Both sides are pinned
as tests**, including a baseline showing the unrestrained table is exact — an over-approximating
restraint that looked exact would be the worse failure. Making it exact requires answers to carry
their goal instance, which is the **same structural change delay lists need**. That is now THREE
features converging on one representation change (7.A): delay lists, `answer_abstract`, and this.

---

## 0c. THE ADVERSARIAL AUDIT vs THE C — 2026-08-17, 23 FINDINGS, 22 FIXED

An agent read all ten `src/standard/tabling/*.jl` plus `Tabling.jl` against `pl-tabling.c`,
`boot/tabling.pl`, `library/tables.pl` and `pl-prims.c`. **This is the highest-yield hour the port
has had**, and the reason is worth keeping: the tests were green throughout — every one of these
survived a suite that reported 87 files / 0 failed. A test suite gates the behaviours you thought
to assert; only the source gates the ones you did not.

**Four were CRITICAL, and two of those changed answers on the DEFAULT path:**

| # | defect | why it was invisible |
|---|---|---|
| 1 | the completion fixpoint's duplicate test was `==`, not variant | a non-ground answer with a fresh body variable is structurally new EVERY round ⇒ **the fixpoint does not terminate**. `variant_eq` already existed, and its own header argued this exact point — it was called only from `trie_insert_moded!` |
| 4 | `_complete_resume!` never set `_CURRENT_TARGET` | `record_dependency!` hit its `tgt === nothing` guard and **recorded nothing**. Any variant first reached inside a resumed continuation suspended without a suspension: incomplete table, no error |
| 2 | monotonic propagation was ONE HOP | A→B→C left C **silently stale**. Upstream's `pdelim/3` recurses via `propagate_answer/2` |
| 3 | monotonic invalidation stopped at the direct target | the retract branch — the file's own soundness argument — invalidated only the first ring |

**The pattern across all 23:** in nine cases the correct code was already present somewhere in the
file and the wired path used something else (`variant_eq`, the trie, `mode_key`). The port did not
lack knowledge; it lacked the connection. `[[feedback_verify_code_body_not_comments]]`

**Fixed:** 1–15, 17–19, 21–23, plus an aliasing bug the #19 fix introduced and the anti-vacuity
probe in `test_completion_resume.jl`, which had been reading the leak that #6 fixed.

**#16** (`lattice`/`po` restricted to a fixed builtin set) is fixed by OPENING the registries —
`register_lattice!` / `register_po!`. Upstream accepts any `Name/3` and `Name/2`, and ships **no
built-in `po` predicates at all**; ours are a convenience, not a ceiling. The `M:`-qualified and
`lattice(Head)` compound forms remain unported — module qualification has no analogue here yet.

**#20 is the one NOT fixed, deliberately.** Our work iteration is suspensions-outer/answers-inner,
forward; upstream is answers-outer and walks both **backwards** (`advance_wkl_state`). Answer ORDER
is user-visible in this engine, so changing it is a corpus-wide behavioural change that needs its own
differential — not a line edit smuggled into an audit response. **Recorded as a known divergence.**

---

## 0b. THE CONFIG PRINCIPLE — USER-STATED 2026-08-17

> **"in SLG there may be different options — we will port them, but in config we will only config
> what is suitable and working for us."**

**PORT THE FULL SURFACE; LET CONFIG DECIDE WHAT IS LIVE.** This settles a question that was being
re-litigated per feature, and it changes the bar for landing one:

* an option does NOT have to WIN to be worth porting — it has to be CORRECT and SELECTABLE. The
  trie read path (1.0b step 2) is the case that made this concrete: it is a consolidation, not
  obviously a speed-up, and under this principle it lands behind a flag whether or not it is faster.
* "ported but not enabled" is a REAL STATE, not a half-measure. An option may be declarable,
  documented, and REFUSED with a stated reason — which is what `subgoal_abstract`/`answer_abstract`
  already do (they name the answer trie as their prerequisite instead of silently no-opping).
  ⚠️ The failure mode this avoids is the one that has cost most in this port: a no-op that looks
  like it works.

### ⚠️ CONSEQUENCE — THE CONFIG SURFACE MUST CONVERGE ON `table_options/3`

Ours has drifted into FIVE shapes for one concept: env `CORE_TABLING_RECOMPUTE`, env
`CORE_TABLING_TRIE_READ`, `table_subsumptive!(head)`, `table_mode!(head, specs)`,
`restraint!(head, :max_answers, n)`.

Upstream has ONE (`boot/tabling.pl:1291-1335`):

    :- table p/2 as subsumptive, incremental, max_answers(1000).
    :- table path(_,_,min).

`table_options/3` dispatches every option — subsumptive · variant · incremental · monotonic ·
opaque · lazy · dynamic · shared · private · max_answers(N) · subgoal_abstract(N) ·
answer_abstract(N) — through one entry point into one options dict.

⇒ **consolidate onto that shape before 7.7/7.8/7.11.1-2 land.** It is cheap at five options and gets
steadily more expensive with each one added. Per-PREDICATE options go through `table_options`;
ENGINE-level choices (resumption vs recomputation, trie read path) stay env-level, because they are
global rather than per-predicate — a distinction upstream also makes (`$tbl_*` flags vs table
options).

## 1. THE TARGET IS ALL OF SWI §7 — DECIDED 2026-08-16

**Build the complete tabling solution whether or not it is used immediately, so the solution is
FIXED.** User decision, taken after the measured-need objection was raised and reaffirmed. Nothing is
scoped out: 7.9 (shared) and 7.10 (constraints) are IN, on the basis that threading arrives later.

### 1.0 BASE FIRST — continuation capture, not recomputation

**This is not an optional refactor; it is what makes the rest ONE build instead of two.** See
`Core/docs/tabling_delimited_control_spec.md`. Our engine recomputes (`_leader_pass` re-run per
fixpoint round) — the "extension table" design the literature rejects. Three later items want
structures that base simply does not have:

* **7.7 incremental** and **7.8 monotonic** need to know WHICH ANSWERS ARE NEW. A
  recompute-until-no-growth loop has no notion of a new answer, only "the table got bigger".
  7.8's eager/lazy split is precisely about WHEN to propagate one.
* **7.11 restraints** — `subgoal_abstract`/`answer_abstract` operate on TRIE TERMS; we use a `Dict`.
* **7.3 mode-directed** needs the merge point AND a value-based fixpoint test.

Build: `shift`/`reset` over the CPS frame stack · `dependency(Source, Cont, Target)` · the worklist
dequeue with the left/right invariant · an answer TRIE.

> **🟢 STEP 1 of 4 LANDED 2026-08-16 — the control-flow primitives, MEASURED, NOT YET WIRED.**
> `Eval._run_plan` extracted from `interpret` (ONE driver, so `resume` cannot drift from `interpret`
> on the step cap or the finished/root discipline) · `Continuation` · `capture_continuation` (`shift`)
> · `resume_continuation` (the resume side of `delim/3`) · `Dependency(source,cont,target)` + `_DEPS`,
> cleared by `_table_reset!`. Gate: `test/standard/test_delimited_control.jl` **19/19**, in
> `runtests.jl`. Regression: health **5/5**, `test_tnot_wfs` 39/39, the swipl §7.1/§7.2 differential
> green, full suite unchanged (still EXIT 1 at the pre-existing `test_eval_one_step` ratchet,
> **57 violations before and after** — measured, not assumed).
>
> **TWO PLANNED PIECES TURNED OUT UNNECESSARY, both measured rather than argued:**
> * **No `reset`.** `reset/3` exists to delimit where a captured chain STOPS. Ours already stops —
>   `_run_plan` collects exactly the frames finishing at `prev === nothing`, so a nested `interpret`
>   call IS the delimiter. `Continuation` is the `shift` half alone.
> * **No continuation COPY.** The spec called `Frame`'s in-place mutation "THE ONE REAL CONSTRAINT";
>   it is retracted there. The whole tree has ONE `Frame` field write (`evalc_op`'s `f.atom`,
>   `Eval.jl:912`) and it is on the DISPATCHED frame, never a captured `prev`. So the paper's
>   `copy_term/2` — and the `copy_continuation/2` it lists as future work — are both moot here.
>   The `Bindings` copy IS kept, for a stated reason: `merge_bindings` trail-undoes its in-place fold
>   on every exit path (`Atoms.jl:224-252`), which is safe only single-threaded, and **7.9 is in scope**.
>
> **REMAINING in §1.0:** (2) `dependency/3` FIRING on each new answer · (3) the worklist dequeue with
> the left/right invariant · (4) the answer trie. Then the rewire of `tabled_eval` off `_leader_pass`,
> with the proved corpus + `test_tnot_wfs` + both swipl differentials as the oracle. ⚠️ **NOT a reason to move the base: roadmap 2.0.** Retracted 2026-08-16 — tabling is set-semantics
by design everywhere, so the guard is still needed after the move. The reasons are PERFORMANCE and
the three structures above.

### 1.0b — WIRING THE TRIE IN (open, found 2026-08-17)

§7.3 and §7.11.3 are now re-seated onto `AnswerTrie`, but the trie is not yet `tabled_eval`'s
storage — `_ANSWER_TABLE`/`_PARTIAL` still are. Two things to carry over when it is, both from
reading the C rather than the Prolog:

* **`Cluster` should hold `TrieNode`, not `Atom`.** Upstream's cluster member is a TRIE NODE POINTER
  (`answer ans = {an}` where `an` is `trie_node *`; `pl-tabling.h:106-111`, `pl-tabling.c:3133`), so
  the trie OWNS answers and the worklist only references them. Taking an answer off the worklist,
  upstream can return to its node — for `TN_IDG_DELETED`, conditionality, pruning. Ours loses that
  identity and would have to re-walk the path.
* **A moded table is `TRIE_ISMAP`** and holds possibly MANY answers per skeleton key
  (`update_subsuming_answers` maps over every child, `:3871`). Our one-row-per-key is correct only
  while no answer can be conditional — i.e. only until delay lists land.

### 1.0c — DELAY LISTS: SCOPED FROM THE C, AND THE THIRD PROLOG ASSUMPTION (2026-08-17)

Delay lists block §7.6.1, three of §7.12's predicates, §7.5's efficient retrieval, and conditional
answers generally. Scoped from `pl-tabling.c` directly. **~1,850 lines of code** (C ~1,435 +
Prolog ~407), concentrated in `TABLE DELAY LISTS :741-1511`, `SIMPLIFICATION :1512-1869`,
`ANSWER COMPLETION :1870-2177`, and the reporting path `:5230-5570`.

**The structure is a DNF.** `delay_info` holds a flat `delays` buffer plus `delay_sets` windows into
it — each set is a CONJUNCT, the sets are a DISJUNCTION. One `delay` is two pointers: the callee's
answer trie, and a node in it — **`answer == NULL` IS the encoding of negation**. It hangs off the
answer trie node in three states: `NULL` = unconditional · `DL_UNDEFINED` = undefined-reason-discarded
· pointer = the condition. `unify_delay_info` (`:5342`) is literally where §7.6.1's `undefined`
surfaces: `true` / a `;`-`,` body / the bare atom `undefined`.

## 🔴🔴 7.A — THE THIRD ASSUMPTION, AND IT IS ARCHITECTURAL, NOT SEMANTIC

The first two were semantic (tabling-is-set vs multiset; ground-goal-completes-after-first). **This
one is about where the condition LIVES.**

`LD->tabling.delay_list` is a **trail-scoped THREAD-GLOBAL** (`pl-setup.c:1552`), pushed
destructively with `TrailAssignment` (`pl-tabling.c:1389-1399`) and UNWOUND BY BACKTRACKING. Every
entry point brackets it as `( reset_delays, ..., fail ; true )` (`boot/tabling.pl:587`, `:724`,
`:782`). `update_delay_list` then decides conditionality by SCRAPING that global at the moment of
insertion: `if ( isNil(*ldlp) && isNil(*gdlp) )` (`:1123-1128`).

**The invariant that makes this correct is: between generating an answer and inserting it, the engine
is executing EXACTLY ONE derivation, and any abandoned attempt is erased by the trail.** That holds
because Prolog control is depth-first backtracking over one substitution at a time.

⇒ **IT DOES NOT HOLD FOR US.** A call to `(f a)` yields a COLLECTION of values which we then map over.
At the moment the k-th result is inserted there is no "current branch" — delayed literals from
DIFFERENT result values are simultaneously live in the same dynamic extent. Port the register
literally and **value #1's `tnot(p)` condition leaks onto value #2**, with no trail to unwind it.
⚠️ Even SWI must hand-roll save/reset/restore where the linear-branch assumption breaks — `'$wfs_call'/2`
(`boot/tabling.pl:938-948`) saves `DL0`, resets, calls, re-appends, precisely because `call/1` is a
re-entrancy point.

⇒ **THE CONDITION MUST RIDE WITH THE VALUE.** Every answer becomes a pair `(value, condition)` — a
residuated value — and combination is an EXPLICIT conjunction at each join, not a push onto ambient
state. **That is a change to the ANSWER REPRESENTATION, the continuation/worklist payloads, and the
dependency record — a prerequisite, not an optimisation, and budgeted SEPARATELY from the 1,850
lines.** (SWI already threads `Delays` explicitly through SUSPENSIONS, `boot/tabling.pl:803-838`; we
would need it EVERYWHERE.)

## THREE MORE, EACH DECIDING A STRUCT FIELD — SETTLE BEFORE WRITING THE STRUCT

* **7.B — negative delays have NO answer slot.** `tnot(g)` is table-level ("the callee's table is
  empty"), decided by `wl->table->value_count == 0` (`:1779`) and `d->answer == NULL` (`:1668`). In a
  value language the natural negations are `(not (f a))` AND `(not (== (f a) 3))` — **the struct has
  nowhere to put the 3.** Needs a third delay kind, negative-with-answer.
* **7.C — conditionality is per answer KEY, and unconditional re-derivation ERASES it.**
  `data.delayinfo` hangs off the trie node, so at most ONE condition per distinct answer term, and a
  later unconditional derivation calls `destroy_delay_info` (`:1131-1138`). Sound under SET semantics
  — and it is the direct reason our one-answer-per-key holds. **Unsound if multiplicity is
  observable**, which is roadmap 2.0 again: `delay_info` would have to live per answer-OCCURRENCE,
  and `wl->delays` (a flat buffer keyed by node pointer, `:803-815`) needs a different index.
* **7.D — deleting a conditional answer is NOT ENOUGH for us.** SWI's rule is drop-the-conjunct,
  drop-the-answer (`remove_conditional_answer`, `:1592`), because in Prolog ordinary resolution
  re-derives it next round. In a value language `(+ 1 (f a))` produced `4` BECAUSE `(f a)` gave `3`;
  if `3` is later refuted and `5` is true, the answer `4` is dead and `6` **was never produced**.
  ⇒ **we may have to RE-RUN THE PRODUCER**, which SWI never does. Check against the worklist design.

## PORT ORDER (from the source, cheapest useful win last-but-one)

1. decide 7.B and 7.C — **they change the struct**
2. residuated values replacing the global delay list (7.A) — the PREREQUISITE
3. `update_delay_list` + the `tnot` trichotomy (unconditional answer ⇒ fail · conditional ⇒ delay ·
   complete-and-empty ⇒ succeed · incomplete ⇒ suspend)
4. `propagate_to_answer` + `simplify_component` (~213 lines) — unlocks §7.6.1 "why undefined"
5. `put_delay_set` + `unify_delay_info` (~145 lines) — unlocks `get_residual/2` and the two
   `get_returns_and_*`; **cheapest win once (2) exists**
6. `$tbl_answer_update_dl` — unlocks efficient §7.5 retrieval, trivial after (2)
7. **ANSWER COMPLETION — DEFER.** It removes POSITIVE LOOPS (`p :- p`) that local propagation can
   never detect, by re-running the residual program in an isolated tabling environment. 450 lines,
   `#ifdef`-guarded upstream, reachable only at `:1847`. Shippable without it: SOUND but incomplete
   on positive loops.

### 1.1–1.13 the §7 surface, in dependency order

| § | feature | status | notes |
|---|---|---|---|
| **7.1** | memoizing | ✅ **HAVE** | variant tabling |
| **7.2** | avoiding non-termination | ✅ **HAVE** | suspend-on-variant (`a13af09`) |
| **7.6** | Well-Founded Semantics | ✅ **HAVE** | Van Gelder alternating fixpoint; swipl differential 13/13 |
| **7.6.1** | WFS and the toplevel | 🔴 **NEEDS DELAY LISTS — bigger than it reads** | RESOLVED 2026-08-16 from `library(tables)`: this is NOT a formatting question. SWI's toplevel can print a RESIDUAL PROGRAM because the engine CARRIES one — conditional answers hold DELAY LISTS, resolved by SIMPLIFICATION (`pl-tabling.c:742` DELAY LISTS + `:1513` SIMPLIFICATION; 258 `delay` mentions). Ours computes WFS by the Van Gelder ALTERNATING FIXPOINT at answer-set level: also a correct WFS, but it yields a truth value (`UNDEFINED`) and NO residual, so we can say THAT an answer is undefined and never WHY. `capability_search` for delay list / residual program / conditional answer → ZERO in Core. ⇒ a STRUCTURAL addition on the scale of the answer trie, and the prerequisite for `get_residual/2`, `get_returns_and_dls/3` and `get_returns_and_tvs/3` in 7.12. |
| **7.5** | subsumptive tabling | ❌ | a second LOOKUP MODE over the same tables — first feature after the base. ⚠️ upstream: does not combine with incremental/shared |
| **7.11.3** | restraint: answer **count** (`max_answers`) | ❌ | `pl-tabling.c:3659` tripwire — the one restraint that ports to a `Dict` today |
| **7.11.1/2** | restraint: subgoal / answer **size** | ❌ | abstraction over trie terms ⇒ needs the base's answer trie |
| **7.3** | answer subsumption / mode-directed | ❌ | `lattice(F/3)`, `po(F/2)`. Consumer named by §3.6 in our vocabulary ("product quantale structure"); `Core/lib/quantale/` exists. 🔴 CATCH: the fixpoint test is CARDINALITY-based and a lattice breaks it silently |
| **7.7** | incremental | ❌ | IDG + `falsecount`, lazy like ours; buys per-table GRANULARITY. Consumes the base's dependency graph |
| **7.8** | monotonic (+ eager/lazy, tracking, external data) | 🟡 **CHEAPER THAN LISTED — IT REUSES §1.0 STEP 2** | READ FROM SOURCE 2026-08-17. Monotonic is NOT another invalidation scheme: `mon_propagate` (`boot/tabling.pl:1644`) BRANCHES — on ASSERT it calls `propagate_assert`, pushing the new answer FORWARD through a stored continuation (monotone addition); on RETRACT it falls back to `mon_invalidate_dependents`, because retraction is not monotone. The lazy variant queues via `$mono_idg_changed` instead of propagating eagerly. 🔑 **THE PROPAGATION VEHICLE IS OUR `Dependency`.** `mon_assert_dep` stores `dependency(SrcSkel, IsMono, Cont, Skel)` against the source trie — SOURCE · CONTINUATION · TARGET — which is exactly `Tabling.Dependency` from §1.0 step 2, and `resume_continuation` is the mechanism that feeds an answer through it. ⇒ 7.8 needs the ASSERT/RETRACT branch and the eager/lazy split, NOT a new propagation engine. Substantially cheaper than 7.7's re-evaluation half, which genuinely does need new machinery (old answers held for comparison). |
| **7.4** | tabling for impure programs | 🟡 **HALF DONE ALREADY — one mechanism of two** | SCOPED 2026-08-17 from our own extraction (`docs/specs/prolog/SWI-Prolog_10.1.9_ch7_tabling_spec.md:236`). §7.4 is not one feature; it is TWO mechanisms that recover correctness for impure patterns, and the hazard they recover from is: *"pruning the choice points of an INCOMPLETE tabled goal may leave an incomplete table, so subsequent queries return only the partial answer set."* ✅ **DYNAMIC SCC — WE HAVE IT.** `_COMPONENT` union-find merges scheduling components on a cross-leader cycle, and dynamic (not static) determination is what keeps them MINIMAL. The Desouter paper lists static SCC identification as its own FUTURE WORK, so this is a place we are ahead of the design we took the control flow from. ❌ **EARLY COMPLETION — WE DO NOT.** *"Ground goals are considered completed after the FIRST solution… this is what lets `p(42)` short-circuit the recursive enumeration of `p(_)`."* We treat groundness only as an answer-PROJECTION fast path (`_ordered_vars` identity); the completion loop still runs to fixpoint. 🔴 **AND IT IS UNSOUND FOR MeTTa — MEASURED 2026-08-17, DO NOT PORT AS STATED.** Upstream's rule assumes a ground goal has AT MOST ONE answer, because in Prolog the answer to a ground call is a SUBSTITUTION OVER ZERO VARIABLES. MeTTa returns a VALUE, so a ground call can have many: `(= (p 1) a)` + `(= (p 1) b)` with `p` tabled returns **`["a", "b"]`** — two answers for a goal with zero variables. Completing after the first would return `a` and SILENTLY DROP `b`. ⇒ SAME SHAPE AS ROADMAP 2.0 (tabling-is-set vs MeTTa-is-multiset): a Prolog assumption that does not survive the language change, and the second one found in this port. **IF IT IS WANTED, THE CONDITION MUST BE DIFFERENT** — not "the GOAL is ground" but something like "the goal is ground AND its head has exactly one applicable rule", which is the multivalued question roadmap 2.0 already had to answer. Until then the fixpoint runs, which is CORRECT and slower. ⚠️ The termination benefit is real and is therefore also forfeited: a ground goal over an infinitely enumerating predicate still does not terminate. That is a genuine cost of MeTTa's semantics, not a gap in the port. |
| **7.9** | shared tabling (+ abolishing) | ❌ | **IN SCOPE — threading later.** Prereq: a threading model. Julia has `Threads.@spawn`; MettaJam is the natural first consumer. Upstream's `tshared` + `abolish_shared_tables/0`. ⚠️ the paper flags NON-BACKTRACKABLE MUTATION as essential to retain answers across disjunctions — the concurrency story starts there |
| **7.10** | tabling and constraints | ❌ | **IN SCOPE.** Prereq we do not yet have: a CONSTRAINT STORE for tabling to interact with. Possible substrate — MORK's optional `z3` source (see the MM2 capability-boundary row in CODEMAP). Scope this only after a constraint story exists |
| **7.12** | predicate reference | 🟡 **PARTIAL — and `library(tables)` is the fuller surface** | HAVE: `untable!` + `abolish_table_subgoals!` at head granularity (0.3, `ceb7e40`). ⚠️ SWI ALSO SHIPS `library(tables)`, an **XSB-COMPATIBILITY** layer that is the INSPECTION API over the answer trie — read 2026-08-16: `get_call/3` · `get_calls/3` · `get_returns/2,3` · `get_returns_and_tvs/3` · `get_returns_and_dls/3` · `get_residual/2` · `get_returns_for_call/2` · `abolish_table_pred/1` · `abolish_table_call/1,2` · `abolish_table_subgoals/2`. Our answer trie (§1.0 step 4) is the substrate these need, so `get_call`/`get_returns` are now cheap. 🔴 BUT the THREE truth-value/delay ones (`get_returns_and_tvs`, `get_returns_and_dls`, `get_residual`) are BLOCKED ON DELAY LISTS — see 7.6.1. Note `set_pil_on/0`/`set_pil_off/0` are documented DUMMIES for XSB compat: do not port. 🟢 **AND IT IS SMALL AND VENDORED** — read from SOURCE 2026-08-16, not the web page: `dev-zone/swipl-devel/library/tables.pl`, **381 lines of Prolog** over **7 C primitives**. (The source also corrects the doc page: it exports `'t not'/1` with a SPACE, plus `abolish_all_tables/0`, `abolish_module_tables/1` and `op(900, fy, tnot)`.) PRIMITIVE-BY-PRIMITIVE, WE ALREADY HAVE FIVE: `$tbl_variant_table`→`_ANSWER_TRIES` · `$tbl_answer`→`trie_answers` · `$tbl_trienode`→`MODED_SLOT` · `$table_mode`→`table_modes` · `$tbl_table_status`→🟡 `_TABLE_INPROG`+`_ANSWER_TABLE` (no `fresh/active/complete` FIELD yet). MISSING EXACTLY TWO, both delay-list: **`$tbl_answer_dl`** and **`$tbl_answer_update_dl`** — which is why the split is `get_residual`/`get_returns_and_dls`/`get_returns_and_tvs` on one side and everything else on the other. ⇒ the portable half is a SMALL, well-scoped job on the trie we already built. |
| **7.13** | about the implementation / status | — | our equivalent is `Core/docs/tabling_delimited_control_spec.md` + this file |

**Mid-evaluation guard** (`permission_error` when a change hits an incomplete table —
`pl-tabling.c` `state.incomplete` → `change_incomplete_error`) has no § of its own but is a soundness
guard we lack; it belongs with 7.7.


## 2. FROM JeTTa — `jetta/backend/.../Generator.kt`, `compiler/Compiler.kt`

| # | item | upstream | notes |
|---|---|---|---|
| **2.0** | 🔴🔴 **BLOCKS 2.2 — TABLING COLLAPSES MULTIPLICITY.** `_leader_pass` merges answers with `unique(vcat(…))` — a SET — while MeTTa is MULTISET. MEASURED 2026-08-16: `(= (h) 1)` twice, `(= (k) (h))` ⇒ `!(k)` untabled `[1,1]`, tabled `[1]`. **NOT introduced by auto-tabling — explicit `table!` has always had it**; auto-tabling made it reachable on 5 corpus scripts at once (b1_equal_chain +1, b2_backchain +2, d3_deptypes +1, d4_type_prop +1, e1_kb_write +1; the PROVED corpus caught every one). ⚠️ **THE TENSION IS FUNDAMENTAL:** tabling REQUIRES set semantics to reach a fixpoint — dropping `unique` never converges. So this constrains WHICH HEADS MAY BE TABLED; it is not a merge to fix. **Upstream already guards it and we dismissed the guard:** JeTTa requires `!f.isMultivalued()` (`Generator.kt:166`), called "a downgrade" on 08-15 — wrongly, since handling multi-answer as a SET is not preserving MULTIPLICITY. PINNED by a test that asserts the DEFECT and must be UPDATED (not deleted) when a guard lands. 🔴 **NOT SUPERSEDED — that claim was RETRACTED 2026-08-16.** Tabling is SET-SEMANTICS BY DESIGN in every implementation (the delimited-control paper dedups in `store_answer/2`; SWI dedups structurally via the answer trie), so the base move does NOT fix this. **2.0 is a LANGUAGE-LEVEL mismatch — tabling is set, MeTTa is multiset — and the guard is the RIGHT answer, independent of the engine.** The three converging sources are the correct response to that mismatch, not workarounds for a weak base. | `Generator.kt:166` | **Decide the guard before 2.2.** Candidate signal: `length(rules[h]) > 1`, which is conservative-but-safe — it would also exclude ordinary disjoint-pattern definitions like `(= (fact 0) 1)` + `(= (fact $n) …)`, so it may be too blunt. Needs its own measurement. |
| **2.1** | **RECURSIVE requirement in `auto_table!`** ⚠️ *and see 2.0 — the multivalued guard is the harder sibling of this one* — table only heads that transitively call themselves | `Generator.kt:164-169`: *"Recursive ⇔ transitively calls itself — **bounds the cache and is where memoization pays**"* | We currently table EVERY pure user head. Memoizing a non-recursive function is pure overhead. **Independently corroborated by PeTTa #165** (*"avoid memoization for trivial functions called <20 times"*). Cheap; lands in `Purity.jl`. |
| **2.2** | **The lane split, ENFORCED BY TEST** — auto-table on the closed-world path, OFF on the open-world one | `MemoTablingTest.kt:39-41`: `tabling is off without autoTable (the REPL or JIT path)`, asserting `fib must NOT be tabled when autoTable is off` | Maps exactly onto `compile_run` (fixed program, bounded lifetime) vs the MettaJam server (`add-atom` any time, runs for days). Their justification, `Compiler.kt:184`: *"AOT is a closed world (rules fixed at compile), so memoizing … is sound **without cache invalidation**"*. Depends on **0.1** — an auto-table call on the compiled lane is INERT until `_pure_heads` learns the IL ops (tried 2026-08-15, did nothing). |

### 🛑 DO NOT ADOPT from JeTTa

- **Their purity gate.** `Generator.kt:153` `impureGrounded` is a **DENYLIST**, and it is **provably unsound**: it lists `"add-atom!"` and `"remove-atom!"` while MeTTa's operators are `add-atom` / `remove-atom` (no bang), so a function calling the real mutator passes `bodyPure` and **gets memoized**. `CompileLane.jl:35` already records this ("6 dead entries, both space mutators misspelled"); verified from source 2026-08-16. **Our whitelist fixpoint fails SAFE and is strictly better.**
- **`keyable` (INT/LONG/DOUBLE/BOOLEAN only)** and **`!isMultivalued()`**. They exist because JeTTa memoizes into a `ConcurrentHashMap` keyed on boxed primitives. Our SLG keys arbitrary atoms via `_variant_rename` and handles multi-answer, non-ground goals — adopting these would be a downgrade.
- **Compile-time wrapper emission** as the mechanism. It makes sense for an AOT target with *no runtime tabling engine*. We have one.

---

## 3. FROM PeTTa PR #165 — `lib/lib_memo.pl` (read at `0dc1198`; 799 LOC)

> **🛑 VERDICT ON FILE: DO NOT ADOPT YET**, and the 2026-08-16 SLG survey **retires most of the case** —
> its `answer-limit` IS `max_answers` (1.2), its `aggregate` enum IS `lattice`/`po` (1.1, and the SLG
> form is strictly more general), its dependency invalidation IS `incremental` (1.5).
> **#165 largely reimplements SLG features inside a system that already runs on SLG.**

| # | item | notes |
|---|---|---|
| **3.1** | **Eviction policy (LRU)** — **the ONE part with no SLG analogue** | SLG **BOUNDS** (abstraction, `max_answers`) and never evicts; #165 **EVICTS** under a memory cap. Bounding ≠ evicting. Our table is unbounded and our own header says so. Take LRU; **skip WTinyLFU** until a measurement wants it. |
| **3.2** | **Per-head `untable!(h)`** | Currently only `untable_all!`. See 0.3. |
| **3.3** | **Stats** — hits / misses / entries per head | Without it, "should this be tabled" is unanswerable. **Do this before 3.1** — otherwise the eviction policy is chosen blind. |
| **3.4** | **MeTTa-level `!(table! f)`** | `TABLE_DECL` exists in `Tabling.jl`; confirm the surface and document it. |

---

## 3.5 EXPLICIT MEMOIZATION — a THIRD option, available TODAY with zero engine work

Source: Markus Triska, *metalevel.at/prolog/memoization* (user-supplied 2026-08-16). O'Keefe's two
rules for efficiency: **"Don't do it. Don't do it again."** Tabling is option 2 automated; explicit
memoization is option 2 by hand.

**MEASURED IN PURE MeTTa, no engine change** — the `assertz` pattern as `add-atom`:

    (= (fib $n) (if (< $n 2) $n (fib-memo $n)))
    (= (fib-memo $n)
       (let $hit (collapse (match &self (fib-cache $n $v) $v))
         (if (== $hit ())
             (let $r (+ (fib (- $n 1)) (fib (- $n 2)))
               (let $_ (add-atom &self (fib-cache $n $r)) $r))
             (car-atom $hit))))

    untabled          dies at n=18 (step limit)
    EXPLICIT MEMO     fib(30) = 832040 in **571 ms**   ← works TODAY
    SLG tabling       fib(30) = 832040 in **36 ms**    ← 16x faster

The 16x is the lookup path: `match` is a space query, tabling hits a `Dict`.

**WHAT IT BUYS** — the cache is ATOMS: inspectable by `match`, dumpable, persistable to `.act`,
removable by `remove-atom`. No revision stamp, no IDG, no process-global state. `_ANSWER_TABLE` is a
`Dict` nothing can see.

🔴 **WHAT IT DOES NOT BUY, IN TRISKA'S OWN WORDS:** *"this rather ad hoc definition **does not help to
improve termination properties** of your programs"* and *"it requires modifications of the original
program… You have to manually wrap the goals"*. Tabling's suspend-on-variant is what makes
left-recursive `adjacent(X,Y) :- adjacent(Y,X)` terminate; a memo check cannot. **They are not
substitutes** — memo avoids recomputation, tabling ALSO fixes non-termination.

🔴🔴 **AND IT CARRIES THE SAME MULTIVALUED CONSTRAINT — A THIRD INDEPENDENT SOURCE FOR 2.0.** Triska's
`memo/1` wraps the goal in **`once(Goal)`**, with the condition stated explicitly: *"As long as Goal
is **semi-deterministic or deterministic**, `memo(Goal)` is equivalent to `Goal`."* So:

| source | the guard |
|---|---|
| JeTTa `Generator.kt:166` | `!f.isMultivalued()` |
| our measurement 2026-08-16 | tabling turns `[1,1]` into `[1]` |
| **Triska** | **`once(Goal)`, "semi-deterministic or deterministic"** |

⇒ **memoization of ANY kind requires single-valuedness.** An earlier note here suggested explicit
memo "gives you the choice to preserve multiplicity" — true in principle, but NOT of this pattern.

⭐ **AND A POINTER WORTH FOLLOWING BEFORE ANY 1.x WORK:** *"Scryer Prolog implements tabling via
**delimited continuations**. See **Tabling as a Library with Delimited Control**, Desouter et al."*
**Tabling as a LIBRARY, not a 9 472-line C engine** — and `Eval.jl` is already a CPS stack machine
("continuation-passing stack machine… a stack of frames… a `ret` continuation"), which is precisely
the substrate delimited control needs. That is a far closer architectural match than SWI's approach,
and it may make 1.1/1.4 much cheaper than the ~8 600-vs-250 line comparison suggests.
⚠️ NOT IN dev-zone — no Scryer clone, no local copy of the paper. Fetch both before scoping 1.x.

---

## 4. STRUCTURAL

| # | item | notes |
|---|---|---|
| **4.1** | ✅ **DONE `031a999`** — extract tabling from `Eval.jl` into `Tabling.jl` (475 lines; `Eval.jl` 2853→2385) | Mirrors SWI (`boot/tabling.pl` + `pl-tabling.c`) and CeTTa (`table_store.c`). |
| **4.2** | **`src/tabling/` subfolder**, split by PROVENANCE — `Tabling.jl` (hub: state, `table!`, attributes land here) · `Purity.jl` (MeTTa-TS: `_pure_heads`, `auto_table!`) · `Variant.jl` (SWI §7.1: keying, `_leader_pass`, `tabled_eval`; modes land here) · `WFS.jl` (SWI WFS: `_S_P!`, `_wfs_complete!`, `TNOT`) | ⚠️ WFS state is INTERLEAVED with general state, so this is not a pure line-range cut. Arguably over-split at 500 lines — the justification is that each file is where a NAMED item above lands. |

---

## Verification standard for every item

1. **A swipl differential where one is possible** — `test_wfs_swipl_differential.jl` is the model: consult real `.pl` oracle files, compare, and **skip loudly** if swipl is absent. Not pinned literals.
2. **The LeaTTa PROVED corpus** (`test_compile_lane_corpus.jl`) for anything touching purity, region splitting or emission — it caught both `\|-` attempts.
3. **`Core/bin/health` 5/5** — but see `[[feedback_primus_health_gate_obsolete]]`: it is a MeTTa front-end gate, NOT a substrate gate.
4. **A mutation check** — flip the assertion and confirm it fails. A test that cannot fail is not evidence.

---

## 7.B — ANSWER-LEVEL DELAY: the design constraint, measured 2026-08-19

**Status: unbuilt, with a concrete failing case.** XSB gold program `p31` is marked `@test_broken` in
`test/standard/tabling/upstream/test_xsb_wfs_corpus.jl`; it is the only one of 70 translated programs
we get wrong.

    q(A) :- p(A), eq(A,b).    p(a).    p(_A) :- r.    r :- tnot(r).

`p(b)` holds only via `p(_A) :- r`, and `r` is undefined, so `q(b)` is `true ∧ undefined` — UNDEFINED
by Kleene and by upstream. We answer TRUE.

### What is already correct — and constrains the fix

Measured directly, three cases:

| case | our result | verdict |
|---|---|---|
| `p :- para.` + `p :- True.` (disjunction) | `[undefined, True]` ⇒ TRUE | ✅ correct |
| `p :- para.` (sole derivation) | `[undefined]` ⇒ UNDEFINED | ✅ correct |
| `p :- (let $c (para) True)` (conjunction) | `[True]` ⇒ TRUE | ❌ must be UNDEFINED |

Disjunction is right for a real reason, not by accident: distinct derivations produce distinct
answers into the same set, and the classifier takes "any definite ⇒ true", which IS
`true ∨ undefined = true`. **Do not break this while fixing conjunction.**

### 🔴 WHY THE OBVIOUS FIX DOES NOT WORK

`propagated_undefined`'s docstring notes that upstream conjoins delays "implicitly from pushing onto
one ambient register". An ambient register is TOO COARSE HERE. Case 1 shows a single `_leader_pass`
producing BOTH a `⊥` and a `True` answer; a register read at `_merge_partial` would mark every answer
that pass produced, turning the correct disjunction result into UNDEFINED. The register must be
scoped **per derivation**, and our answer production is per PASS.

Nor is the site `unify_op`. It knows it bound a ⊥ to a variable, but it returns a FRAME for the
machine to continue evaluating — the answer does not exist yet, so there is nothing there to mark.
(Marking the unevaluated `then` term was tried in analysis and rejected for this reason.)

### The shape that could work

`Bindings` is already a per-derivation channel: `finished_result(subst(then, mb), mb, f.prev)` carries
`mb` along exactly the derivation that bound the ⊥. Carrying the accumulated `DelayDNF` there would
give per-derivation scope for free, and `_merge_partial` could then conjoin the binding's delay onto
the answers that derivation produced.

⚠️ That is a field on `Bindings`, i.e. an eval-core struct change:
`[[reference_core_interpreter_perf_findings]]` applies (`Bindings` is opt-target #1, risk HIGH), and
a struct change strands `const` containers under Revise
([[reference_revise_binding_bugs_and_world_partitioning]]). Design it, measure it, and expect a
daemon restart — do not start it as a quick fix.

