# Tabling as a Library with Delimited Control — spec extraction

> **READ-ONCE.** Extracted 2026-08-16 from
> `docs/research/papers/prolog/Tabling/Tabling as a library with Delimited Control.pdf`
> (Desouter, van Dooren, Schrijvers — TPLP). Pages 1–8 read in full: abstract, §1 introduction,
> §2 delimited continuations, §3 shallow transformation, §4.1–§4.4 the implementation.
> Consult this instead of re-opening the PDF.

**The headline.** Tabling in **under 600 lines of Prolog**, no engine changes, no complicated program
transformation. Compare SWI: `pl-tabling.c` 9 472 + `boot/tabling.pl` 2 321 + header = **12 133**.

> *"Existing approaches require substantial changes to the Prolog engine, which is an investment out
> of reach of most systems. To enable more widespread adoption, we present a new implementation of
> tabling in under 600 lines of Prolog code."*

---

## 1. The two primitives it needs (§2)

* **`reset(Goal, Cont, Term1)`** — executes `Goal`. If `Goal` calls `shift(Term2)`, its further
  execution is SUSPENDED and unified with continuation `Cont`. A continuation is an opaque term,
  resumable with `call/1`.
* **`shift(Term2)`** — unifies the remainder of `Goal` up to the nearest `reset/3` with `Cont`, and
  `Term2` with `Term1`; returns control to just after the `reset/3`.

🔑 **WE ALREADY HAVE THE SUBSTRATE.** `Eval.jl`'s header: *"Minimal instruction set, as a
**continuation-passing stack machine** … a stack of frames, each frame carrying an atom, its
variables, a link to the previous frame, and a `ret` continuation invoked when the frame it pushed
finishes."* `reset` ≈ pushing a delimiting frame; `shift` ≈ capturing the frame stack up to it.

## 2. Shallow program transformation (§3)

`:- table p/2` rewrites to a WRAPPER + WORKER pair — that is the whole transformation:

    p(X,Y)     :- table(p(X,Y), p_aux(X,Y)).      % wrapper
    p_aux(X,Y) :- p(X,Z), e(Z,Y).                 % worker = the original clauses, renamed
    p_aux(X,Y) :- e(X,Y).

## 3. The control flow (§4.1–§4.3)

* **`table/2`** intercepts every call. Look up the table for this call VARIANT; if `complete`,
  consume answers. Else become a **leader** (only non-tabled ancestors) or a **follower**. Leader +
  followers = a **scheduling component**.
* **`delim/3`** runs the worker inside `reset/3`. Worker succeeds ⇒ `store_answer/2`. Worker calls a
  tabled predicate ⇒ the follower `shift/1`s WITHOUT producing an answer, so the worker SUSPENDS and
  the remainder is captured in `Continuation`.
* **`dependency(SourceCall, Continuation, TargetCall)`** is stored in the SOURCE call's table, and
  fires whenever a new answer is added there. *"Given an answer for the q/m call, one may obtain
  answers for the p/n call by resuming the suspended continuation."*
* **`completion/0`** is a worklist-driven LEAST FIXPOINT: pop a table, `completion_step/1` takes an
  unprocessed Answer/Dependency pair and RESUMES the continuation with the answer via `delim/3`.
  When the worklist empties, set every table `complete` and erase dependencies.

## 4. The table data structure (§4.4)

Two parts: an **answer trie** (also gives cheap duplicate detection on `store_answer/2`) and a
**local worklist** — a DEQUEUE with the invariant *"an answer is to the left of a dependency if and
only if they have not been combined"*. New answers go LEFT, new dependencies RIGHT. `table_get_work/3`
takes a batch of answers immediately left of a batch of dependencies, SWAPS them, and yields the
Cartesian product. Batches of consecutive answers/dependencies are merged on insertion for speed.

**Implementation support required:** mutable terms, NON-BACKTRACKABLE mutation, one global variable.
*"The non-backtrackable nature is essential to retain the collected answers and dependencies across
disjunctions."*

---

## 🔴🔴 WHAT THIS SAYS ABOUT OUR IMPLEMENTATION — AND IT NAMES OUR DESIGN

> *"Extension tables (Fan and Dietrich 1992) provide a tabling mechanism that is implemented directly
> in Prolog. However, **the approach cannot achieve satisfactory performance as suspended goals are
> always re-evaluated.**"*
> *"In contrast with extension tables, our approach **does not require recomputation of suspended
> goals**."*

**OURS IS THE EXTENSION-TABLE DESIGN.** `Core/src/standard/Tabling.jl` (`:374-380`, `:467-473`):

    grew = false
    for m in comp()
        np = _leader_pass(m, typ, space); n0 = length(_PARTIAL[m])
        _PARTIAL[m] = unique(vcat(_PARTIAL[m], np))      # ← dedup REQUIRED by recomputation
        length(_PARTIAL[m]) != n0 && (grew = true)
    end
    grew || break

`_leader_pass` is **RE-RUN every round**. We reach the fixpoint by RECOMPUTING, not by resuming.

### ⚠️ A CLAIM I MADE HERE WAS WRONG — RETRACTED 2026-08-16, SAME DAY

This section first argued: *"recomputation forces `unique`, and `unique` is what collapses
multiplicity, therefore continuation capture would preserve multiplicity and roadmap 2.0 dissolves."*
**The first half is true and the conclusion is FALSE.** Checked against upstream on the user's
"I do not know the quality you adopted" prompt:

* **This paper dedups deliberately** (§4.4): *"the trie allows `store_answer/2` to quickly check
  whether a newly produced answer has already been computed before, and **to only store it in case it
  has not**."*
* **SWI dedups structurally.** `wkl_add_answer(worklist*, trie_node *an)` (`pl-tabling.c`) takes an
  answer ALREADY INSERTED INTO THE ANSWER TRIE — and a trie is a set: the same term maps to the same
  node.

⇒ **TABLING IS SET-SEMANTICS BY DESIGN IN EVERY IMPLEMENTATION.** Our `unique(vcat(…))` reaches the
same semantics by a different mechanism; it is not a defect of the recomputation base.

**SO ROADMAP 2.0 IS A LANGUAGE-LEVEL SEMANTIC MISMATCH, NOT AN ENGINE ARTIFACT:** Prolog programmers
EXPECT tabled predicates to return each answer once (it is documented behaviour); MeTTa is MULTISET.
Moving to continuation capture would NOT fix it. The multivalued guard is the RIGHT answer, and the
three converging sources are all the correct response to that mismatch, not workarounds for a weak
base:

| source | the guard |
|---|---|
| JeTTa `Generator.kt:166` | `!f.isMultivalued()` |
| Triska `memo/1` | `once(Goal)` |
| our measurement | tabling turns `[1,1]` into `[1]` |

**What recomputation DOES cost is performance, which is the paper's actual complaint** — *"suspended
goals are always re-evaluated"* — plus the absence of the structures 7.7/7.8/7.11 need. Those remain
the reasons to move the base. Multiplicity is not one of them.

### What we already have that maps onto theirs

| theirs | ours (`Tabling.jl`) |
|---|---|
| scheduling component | `_GEN_STACK` + `_COMPONENT` (union-find SCC) |
| leader / follower | `_leader_pass` / consumer branch in `tabled_eval` |
| table status `fresh/active/complete` | `_TABLE_INPROG` + `_ANSWER_TABLE` |
| answer trie | `_PARTIAL` / `_ANSWER_TABLE` (`Dict`, not a trie) |
| **`dependency(Source, Cont, Target)`** | **ABSENT** |
| **continuation capture (`shift`/`reset`)** | **ABSENT — we recompute instead** |
| local worklist dequeue + left/right invariant | **ABSENT** |

**The gap is two structures and one primitive**, not 8 600 lines.

---

## Bearing on `TABLING_ROADMAP.md`

* **Reconsider the whole of §1 before building it.** The roadmap scoped SWI's four modes and nine
  attributes against *our recomputation engine*. Adding attributes to the wrong base may cost more
  than restructuring onto continuation capture — which our CPS machine already supports and which
  fixes 2.0 for free.
* **2.0's guard may be unnecessary** rather than merely awkward. Decide the engine question first.
* **1.1 (mode-directed) still needs its own answer**: a lattice join replaces set-union in the merge,
  and the CARDINALITY-based fixpoint test breaks under it either way.
* ⚠️ **NOT YET READ:** §5 (evaluation/benchmarks), §6 (related work), and Appendices A–C — Appendix C
  has "more code details" on completion, Appendix B the mutable-term support. Read those before
  scoping an implementation; this extraction covers architecture only.
