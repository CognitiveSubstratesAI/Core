# Tabling.jl — SLG variant tabling + WFS negation, EXTRACTED FROM `Eval.jl` 2026-08-16.
#
# ─── WHY ITS OWN FILE ────────────────────────────────────────────────────────────────────────────
# Every engine we cross-check against keeps tabling separate: SWI-Prolog splits `boot/tabling.pl`
# (2 321 lines) + `src/pl-tabling.{c,h}` (9 812), CeTTa has `src/table_store.c`. Ours was ~475 lines
# WEDGED BETWEEN the interpreter's section header (`Eval.jl`, "THE METTA DRIVER AS STACK-MACHINE
# INSTRUCTIONS") and the `metta_instr` function that header introduces — so extracting it makes BOTH
# sections contiguous rather than merely relocating a problem.
#
# 🔑 THIS IS A FILE SPLIT, NOT A MODULE SPLIT. It is `include`d INSIDE `module Eval`, so every name
# resolves exactly as before and nothing is re-exported. A real module boundary is NOT possible here
# without inverting a dependency: tabling calls `metta_run`/`_reduced_goal`/`Space`, and the
# interpreter calls `tabled_eval` from `metta_instr` — mutual recursion by design, the same
# arrangement SWI has between `boot/tabling.pl` and its C engine.
#
# ─── WHAT STAYS IN Eval.jl (the integration points) ──────────────────────────────────────────────
#   * `export table!, untable_all!, auto_table!`   — the module's public surface
#   * `is_tabled(atom) && return tabled_eval(…)`   — the interpreter's dispatch into tabling
#   * `load_metta!(…; auto_table::Bool=false)`     — the loader's opt-in kwarg
#
# ─── SCOPE, MEASURED 2026-08-16 ──────────────────────────────────────────────────────────────────
# We implement ONE of SLG's four modes (variant) and ZERO of its nine attributes. SWI additionally
# has `subsumptive`, mode-directed (`lattice`/`po`) and abstract tabling, plus `incremental`,
# `monotonic`, `lazy`, `dynamic`, `tshared`, `opaque`, `max_answers`, `subgoal_abstract`,
# `answer_abstract` — ~250 lines of code here against ~8 600 there. **THIS FILE IS WHERE THOSE LAND.**
# The point of the split is that future SLG/Prolog adoption accumulates HERE instead of growing the
# interpreter. See the CODEMAP row "SLG's COMPLETE FEATURE SURFACE" for the survey, and for the trap
# already identified: the fixpoint test below is CARDINALITY-based (`length(_PARTIAL[m]) != n0`),
# which a lattice mode would silently break — a table can keep its SIZE while its VALUE improves.

# ═══════════════════════════════════════════════════════════════════════════════
# SLG VARIANT TABLING (opt-in; default OFF) — SWI-Prolog §7.1 memoisation in the top-down interpreter.
# `table!(head)` marks a predicate tabled; a tabled goal's FULLY-REDUCED answer set is computed ONCE and
# replayed on every variant re-call, turning exponential recomputation (fib) into linear. The interpreter is
# already a CPS stack machine, so this rides the existing nested-`interpret` pattern (cf. collapse_bind_op).
#   DEFAULT-OFF GUARANTEE: with no head registered the hook in metta_instr is always false ⇒ the 234
#   conformance reduction path is byte-identical by construction (the disable-to-prove pattern).
#   ⚠️ SCOPE — CORRECTED 2026-08-11. This said "memoisation only … no suspend-on-variant yet (that needs
#   the worklist/dynamic-SCC completion machinery; §7.2)". BOTH HALVES ARE NOW FALSE, and a reader who
#   trusted them would either rebuild suspension or avoid tabling that already works:
#     * SUSPEND-ON-VARIANT IS IMPLEMENTED (`tabled_eval`, the CONSUMER branch): a variant re-entry does
#       NOT fall through to normal reduction — it answers from `_PARTIAL` and stays suspended, and the
#       generator/consumer split is right there (`push!(_TABLE_INPROG, key); push!(_GEN_STACK, key)`).
#     * THE DYNAMIC-SCC COMPLETION MACHINERY LANDED TOO (`b540296`), cross-referenced in the comment
#       above `tabled_eval` to SWI's own `boot/tabling.pl` `completion` → `$tbl_table_complete_all(SCC)`.
#   PROVENANCE, since it is easy to blur — THREE sources, and this file cites each at its own site:
#     * the SLG MECHANISM (variant tabling, generator/consumer, SCC completion) — SWI-Prolog §7.1 and
#       `boot/tabling.pl` (`:989`, and the comment above `tabled_eval`).
#     * REVISION-STAMPED INVALIDATION — CeTTa `table_store.c:153` (`:1007`), landed 2026-07-01
#       (`2435f42`).
#     * WHICH heads to table (policy, not mechanism) — MeTTa-TS (`:1084`), opt-in and default OFF.
#   ⚠️ NOT PeTTa. Its memo library (PR #165, `lib/lib_memo.pl`, generation-based invalidation) merged
#   2026-07-24 — THREE WEEKS AFTER our revision stamping — is absent at PeTTa HEAD, and is referenced
#   nowhere in this tree except at `ANormal.jl:193`, where a FABRICATED claim about it was corrected.
#   It is recorded as adoptABLE, not adopted. From PeTTa we took the A-normal translator, not this.
#   On these two axes we now follow SWI. What remains genuinely open is
#   listed at `tabled_eval` (naive rather than semi-naive; no answer subsumption §7.3; ground/enumerable
#   answers) — that list is the accurate one. Handles the fib/ackermann class. Variant key = the substituted goal (ground ⇒ identity; non-ground
#   canonicalization ⚠️ IS NOT TODO — third stale claim in this header, corrected 2026-08-11:
#   `_variant_rename` (`:1192`) renames vars by first occurrence, which its own comment identifies as
#   "SWI's variant canonicalization", and `_canonical_goal` uses it. Non-ground goals ARE variant-keyed.)
#   ⚠️ THE TABLE IS UNBOUNDED — no eviction, no size limit. Removal happens only on staleness (a
#   revision mismatch) or a manual `table!`/`untable_all!`. A long session with many distinct tabled
#   goals grows the table without bound — but MEASURED 2026-08-11, that is NOT reachable on the
#   default path: the one place tabling is on by default (`DualTrack` `fallback_table=true`) calls
#   `_table_reset!()` in its `finally`, clearing this table after every fallback. Residual exposure is
#   a user calling `!(auto-table!)` in a long-lived space, which is opt-in. So PeTTa PR #165's
#   LRU/WTinyLFU + `unique-limit`/`size-limit`/`answer-limit` would close a REAL gap that currently
#   has NO measured need — recorded as available, not as owed. (That library is LIVE at PeTTa's
#   upstream HEAD `43705f5`; an earlier note here and in memory called it "removed", which was a
#   four-day-stale local clone misread as an upstream deletion.) Table is global+session-scoped and cleared by table!/untable_all!; entries are now
#   REVISION-STAMPED per space (CeTTa table_store.c:153) so a mutation to the space auto-evicts its stale answers on
#   the next lookup (closes the silent-staleness half of §7.7; fine-grained IDG dependency tracking still TODO).
# 🔴 SCOPE — PROCESS-GLOBAL, NAME-ONLY, AND THE REFERENCE IS NEITHER. Cross-checked 2026-08-11
# against SWI-Prolog, which this tabler was adopted from (`dev-zone/swipl-devel`):
#
#   * SWI has NO global tabled-set. The mark lives ON THE PREDICATE —
#     `return (props=def->tabling) && ison(props, TP_TABLED);` (`src/pl-tabling.c:5583`), set via
#     `tbl_set_predicate_attribute(Definition def, …)` (`:8795`). A `Definition` is
#     (MODULE, NAME, ARITY), so the mark is module-scoped and ARITY-AWARE.
#   * Tables are abolished at three granularities: `abolish_all_tables/0`,
#     `abolish_module_tables/1  % +Module`, `abolish_table_subgoals/2` (`library/tables.pl:37-42`).
#     We have only the first (`untable_all!`).
#   * SLG SCHEDULING state is THREAD-LOCAL in SWI (`LD->tabling.component`, `LD->tabling.delay_list`,
#     `pl-tabling.c:320,1123`). Ours — `_GEN_STACK`/`_COMPONENT`/`_NEG_*`/`_WFS_*` below — is global.
#
# So this set is wrong on TWO axes the reference gets right: it is not per-space, and it is keyed by
# NAME ALONE. The arity half is the same defect fixed in `ANormal.is_fun` the same day, where
# `b1_equal_chain.metta` defines `S` at arity 3 and uses it at arity 1.
#
# ⚠️ MEASURED, AND THE HARM IS NOT YET DEMONSTRATED — recorded honestly so the next attempt starts
# from evidence rather than from this comment's alarm. The MARK does leak: `auto_table!(sp1)` marks
# `f` because it is pure in sp1, and `f` then reads as tabled in a DIFFERENT space where it is impure.
# But the impure effect still fired on every call, because `_ANSWER_STAMP` keys answers by
# `(objectid(space), revision)` and `add-atom` bumps the revision, evicting the entry. So the
# revision stamp is currently masking the scope bug. A probe comparing effect counts across two
# spaces was too loose to attribute a difference and is NOT cited as evidence.
#
# ⇒ Per-space + arity-keyed is the RIGHT shape (the reference says so). Whether it is URGENT is
# unproven; a test that exhibits a wrong ANSWER — not merely a leaked mark — is the prerequisite.
const _TABLED_HEADS = Set{Symbol}()
const _ANSWER_TABLE = Dict{Atom,Vector{Atom}}()
const _ANSWER_STAMP = Dict{Atom,Tuple{UInt,Int}}()   # key → (objectid(space), revision) at completion; auto-evict on mismatch
const _TABLE_INPROG = Set{Atom}()
const _PARTIAL = Dict{Atom,Vector{Atom}}()   # a leader's accumulating answer set during completion
const _PARTIAL_READ = Set{Atom}()            # tabled keys whose partials a consumer read ⇒ self-recursive
const _GEN_STACK = Atom[]                     # in-progress leaders (generators), in call order
const _COMPONENT = Dict{Atom,Atom}()          # key → SCC root (union-find; merged on a cross-leader cycle)
const _NEG_BARRIER = Set{Atom}()              # in-progress keys sitting BEHIND an active tnot (negation)
const _NEG_DEPTH = Ref(0)                      # active tnot-drive depth (>0 ⇒ evaluating under a negation)
const _NEG_TAINT = Ref(false)                 # a consumer read a barrier key under negation ⇒ unsound 2-valued
# WFS Stage B increment 2 — phase-fixed interpretation for the Van Gelder alternating fixpoint. During
# `_wfs_complete!`, an IN-SCC `tnot(G)` reads this FIXED bound I (succeeds iff G has no DEFINITE answer in I)
# instead of driving G + tainting (the taint is what makes the tabler over-conservative on dynamically-
# stratified SCCs). OUT-of-SCC `tnot` (key ∉ _WFS_BOUND) and all off-WFS execution (_WFS_ACTIVE=false) are
# untouched ⇒ 234-conformance byte-identical.
const _WFS_BOUND  = Ref(Dict{Atom,Vector{Atom}}())   # SCC-member key ↦ bound answer-set I (read-only in a phase)
const _WFS_ACTIVE = Ref(false)                        # true only inside an `_S_P!` phase
const _SCC_NEG    = Set{Atom}()                       # in-progress goals re-entered ACROSS a tnot barrier (a
#   positive edge closing a cycle through negation) ⇒ their SCC needs `_wfs_complete!`. Set at the source in
#   `tabled_eval`'s consumer path; the routing checks whether any SCC member is marked. Replaces the old
#   hardcoded `tnot`-body scan (`_body_has_tnot`/`_scc_has_negation`) — same info, from the machinery that owns it.
# WFS bottom / third truth value. MUST be OUT-OF-BAND: a plain `Sym("undefined")` COLLIDES with a user datum
# literally named `undefined` — a tabled predicate whose real answer is that symbol would be mis-read as the
# truth value at the classification in TNOT (`== UNDEFINED`), a soundness bug (returns undefined when the true
# WFS value is false). A zero-field `Grounded` singleton is NOT constructible from MeTTa source (source
# `undefined` parses to a `Sym`, and cross-type `Sym == Grounded` is `false`), so it can never collide. It
# renders as "undefined" (SWI's term) via `show(::Grounded)=print(value)`; the printed form does NOT round-trip
# back to this sentinel, by design — it is a truth value, not reconstructable data.
struct WFSBottom end
Base.show(io::IO, ::WFSBottom) = print(io, "undefined")
const UNDEFINED = Grounded(WFSBottom())       # NOT aliased to Empty or False; NOT a program Sym
_table_reset!() = (empty!(_ANSWER_TABLE); empty!(_ANSWER_STAMP); empty!(_TABLE_INPROG); empty!(_PARTIAL);
                   empty!(_PARTIAL_READ); empty!(_GEN_STACK); empty!(_COMPONENT); empty!(_NEG_BARRIER);
                   _NEG_DEPTH[] = 0; _NEG_TAINT[] = false; empty!(_SCC_NEG); empty!(_DEPS);
                   _WFS_BOUND[] = Dict{Atom,Vector{Atom}}(); _WFS_ACTIVE[] = false)
_scc_root(k::Atom)::Atom = (r = get(_COMPONENT, k, k); r == k ? k : (_COMPONENT[k] = _scc_root(r)))
"Mark predicate `head` (a Symbol) for tabled (memoised) execution; clears the answer table."
table!(head::Symbol) = (push!(_TABLED_HEADS, head); _table_reset!(); nothing)
"Disable all tabling and clear the answer table."
untable_all!() = (empty!(_TABLED_HEADS); _table_reset!(); nothing)
@inline is_tabled(atom::Atom)::Bool = !isempty(_TABLED_HEADS) && head_name(atom) in _TABLED_HEADS
# MeTTa surface for the directive (the analog of SWI `:- table fib/1`): `!(table! fib)` marks the `fib`
# predicate tabled, so a program/server enables tabling without a Julia call. Registered in TOKEN_REGISTRY.
const TABLE_DECL = Grounded(Operation("table!", xs ->
    (length(xs) == 1 && xs[1] isa Sym) ?
        (table!((xs[1]::Sym).name); ExecOk(Atom[Expression(Atom[])])) : ExecNoReduce()))

# ── PURITY-ANALYSIS AUTO-TABLER (MeTTa-TS-style `automatic tabling of pure functions`) ──────────────
# `table!` is opt-in (`!(table! fib)`); MeTTa-TS instead auto-detects which functions are PURE (their
# answer set is a function of their args — no space mutation / state / I/O / mutable-state read) and tables
# them with no directive. Core already owns the hard part (the SLG table engine above); this is only the
# missing FRONT-END: an impurity-propagation fixpoint over the space's `(=)` rules. CONSERVATIVE WHITELIST
# of side-effect-free primitives ⇒ any function whose body-closure touches an unknown/impure op (add-atom,
# remove-atom, match/&self, state, superpose, I/O, or any un-whitelisted grounded op / data constructor) is
# left UNTABLED. Result-preserving: tabling memoises a pure function's answer set, so answers are identical,
# only faster (fib: exponential → linear). Not auto-wired into load_metta! — call `auto_table!(space)` explicitly.
const _PURE_PRIMS = Set{Symbol}(Symbol.([
    "+","-","*","/","%","<",">","<=",">=","==","!=",                       # arithmetic + comparison
    "and","or","not","xor","if","if-equal","unify","let","let*","case",    # boolean + control
    "quote","unquote","eval","id","noeval","noreduce-eq","=alpha",         # quote / eval (pure)
    "car-atom","cdr-atom","cons-atom","size-atom","index-atom","min-atom","max-atom",  # pure list/tuple
    "get-type","get-metatype","match-types","is-function",                 # type queries (pure)
    "sqrt-math","pow-math","abs-math","log-math","exp-math","sin-math","cos-math",
    # 🔴 THE MINIMAL-MeTTa CONTROL INSTRUCTIONS — added 2026-08-16 (roadmap item 0.1).
    # THEIR ABSENCE WAS A SILENT NO-OP, NOT A MISSING FEATURE. `EmitIL` lowers every definition to
    #     (= (fib $n) (function (chain (metta (< $n 2) %Undefined% &self) $__t1 …)))
    # so a COMPILED body's callees are `function`/`chain`/`metta`/`return`. None was whitelisted, and
    # `_pure_heads` is a WHITELIST fixpoint (unknown op ⇒ impure), so EVERY compiled head came back
    # impure. MEASURED 2026-08-15:
    #     `:fib` in `_pure_heads`, SOURCE form  ->  true
    #     `:fib` in `_pure_heads`, IL form      ->  FALSE
    # ⇒ every purity-gated consumer is inert on the compiled lane. `auto_table!` is the one we
    # noticed — tabling `compile_run`'s output did LITERALLY NOTHING — and it is not necessarily the
    # only one.
    #
    # THEY ARE PURE. `function`/`return` are a call boundary and its join point; `chain` binds an
    # intermediate and continues; `metta`/`evalc` evaluate a sub-term; `decons-atom` destructures.
    # None mutates, reads state, or does I/O. Purity of what they CONTAIN is still checked
    # independently: `_callees!` recurses into every child, so `(metta (add-atom …) …)` still
    # surfaces `add-atom` and fails the head.
    #
    # ⚠️ `collapse-bind`/`superpose-bind` DELIBERATELY OMITTED. The header above lists `superpose`
    # among the impure ops; that conservative stance is kept. Their answer SET is well-defined so
    # they are arguably tabl-able, but widening nondeterminism handling is its own decision with its
    # own evidence, not a side effect of unblocking the compiled lane.
    #
    # ⚠️ BLAST RADIUS — `_pure_heads` ALSO FEEDS `purity_may_mutate` (`CompileLane.jl:40`), which
    # drives REGION SPLITTING for Invariant 1: more pure heads ⇒ fewer forms flagged mutating ⇒ FEWER
    # SPLITS. Mostly contained, because these heads appear in COMPILED bodies while
    # `purity_may_mutate` analyses SOURCE forms — the exception is a user writing minimal MeTTa
    # directly (legal since `d3e245f`), where the new classification is the CORRECT one and the old
    # "impure" verdict was conservative-and-wrong rather than a deliberate guard.
    # ⇒ THE PROVED CORPUS IS THE GATE FOR THIS CHANGE, not the unit tests.
    "function","return","chain","metta","evalc","decons-atom",
]))

# extract `(= (h …) body)` rules from a list of atoms → head Symbol ↦ [body atoms]
function _rules_of(atoms)::Dict{Symbol,Vector{Atom}}
    d = Dict{Symbol,Vector{Atom}}(); EQ = Symbol("=")
    for a in atoms
        (a isa Expression && length(a.children) == 3 && head_name(a) == EQ) || continue
        lhs = a.children[2]
        (lhs isa Expression && !isempty(lhs.children) && lhs.children[1] isa Sym) || continue
        push!(get!(d, head_name(lhs), Atom[]), a.children[3])
    end
    d
end

# every operator-position symbol reachable in `a` (its "callees" — reducible heads AND data constructors)
function _callees!(a::Atom, acc::Set{Symbol})
    if a isa Expression && !isempty(a.children)
        a.children[1] isa Sym && push!(acc, (a.children[1]::Sym).name)
        for c in a.children; _callees!(c, acc); end
    end
    acc
end

# impurity-propagation fixpoint: a head is impure if a body calls something that is neither a pure prim
# nor a (defined) head (⇒ an unknown/impure grounded op), or calls a known-impure head. Self-recursion OK.
function _pure_heads(rules::Dict{Symbol,Vector{Atom}})::Set{Symbol}
    heads = Set(keys(rules)); impure = Set{Symbol}()
    while true
        changed = false
        for h in heads
            h in impure && continue
            done = false
            for body in rules[h]
                for op in _callees!(body, Set{Symbol}())
                    op == h && continue
                    if !(op in _PURE_PRIMS || op in heads) || op in impure
                        push!(impure, h); changed = true; done = true; break
                    end
                end
                done && break
            end
        end
        changed || break
    end
    setdiff(heads, impure)
end

"""
    auto_table!(space) -> (; tabled, skipped)

Analyze `space`'s `(=)` rules and mark every USER-defined PURE function head tabled (the MeTTa-TS
`automatic tabling of pure functions`, bolted onto Core's existing `table!` engine). Purity is decided by
an impurity-propagation fixpoint over a conservative pure-primitive whitelist, so anything touching an
unknown/impure op is left untabled — result-preserving, only faster. Returns the heads it tabled/skipped.
"""
function auto_table!(space::Space)
    pure = _pure_heads(_rules_of(all_atoms(space)))                         # analyze ALL rules (stdlib deps too)
    user = keys(_rules_of(own_atoms(space)))                               # but only TABLE the user's own heads
    up = intersect(pure, user)
    for h in up; table!(h); end
    (tabled = sort!(collect(up)), skipped = sort!(collect(setdiff(user, up))))
end

# `!(auto-table!)` — the MeTTa surface for the auto-tabler (the analog of MeTTa-TS's automatic tabling; cf.
# `!(table! fib)` for the per-predicate directive). Analyzes `&self` and tables every PURE user function head,
# returning `(auto-tabled h1 h2 …)` so a program/server enables it with no Julia call and sees what was tabled.
const AUTO_TABLE_DECL = Grounded(SpaceOp("auto-table!", function (xs, space)
    r = auto_table!(space)
    ExecOk(Atom[Expression(Atom[Sym("auto-tabled"); Atom[Sym(string(h)) for h in r.tabled]])])
end))

_replay(answers::Vector{Atom}, b::Bindings, prev) =
    isempty(answers) ? finished_result(EMPTY, b, prev) :
    reduce(vcat, (finished_result(ans, b, prev) for ans in answers))

# ═══════════════════════════════════════════════════════════════════════════════
# DELIMITED CONTROL — `shift`/`reset` over the CPS frame chain (roadmap §1.0, step 1 of 4)
#
# Desouter, van Dooren & Schrijvers, *Tabling as a Library with Delimited Control* (TPLP 2015), §2:
#   `reset(Goal, Cont, Term1)` runs Goal; if Goal `shift(Term2)`s, its REMAINDER is captured in Cont.
#   `shift(Term2)` yields control back to just after the reset, producing NO answer.
# Their §5.1: the control-flow half of the whole library is **60 of 577 lines** — the other 85% is
# tries and dequeues that exist only because Prolog lacks them. This is that 60.
#
# 🔑 WE DO NOT NEED `reset`. A `reset` delimits where a captured chain STOPS; ours already stops,
# because `_run_plan` collects exactly the frames that finish at the root (`prev === nothing`) and a
# nested `interpret` call IS the delimiter. So `Continuation` is the `shift` half alone: the pending
# frame chain `prev` plus the bindings at the suspension point. `tabled_eval` is handed precisely
# `(b, prev)` already — the consumer branch's existing `_replay(partials, b, prev)` is a resume that
# happens to fire immediately.
#
# ─── MEASURED 2026-08-16, and it corrected TWO documented constraints ────────────────────────────
# Probe: drive `interpret_stack` from outside the engine, capture `(f.prev, b)` at a marker goal, drop
# the frame, then resume that ONE continuation twice with different answers.
#     (= (g $x) (Result $x))  (= (mark) M1)  (= (mark) M2)
#     baseline ["(Result M1)","(Result M2)"]  ==  resumed ["(Result M1)","(Result M2)"]   ✓
#
# * `Core/docs/tabling_delimited_control_spec.md` called it "THE ONE REAL CONSTRAINT" that `Frame` is
#   mutable and `finished` is written in place, so a captured chain MUST be copied. **FALSE, and now
#   retracted there.** The entire tree holds ONE `Frame` field write — `evalc_op`'s `f.atom`
#   (`Eval.jl:912`) — on the frame being DISPATCHED, never on a captured `prev`. A `prev` is only ever
#   read (`f.prev.ret(f.prev,…)`, `f.prev.vars`) and is never re-entered into a plan as an `f`.
#   ⇒ NO frame copy, so not even the `copy_continuation/2` the paper lists as future work (§5.2).
#   Their future-work item #1 is not our starting point; it is already unnecessary here.
#
#   🔴 BUT THE WRITE COUNT IS THE SYMPTOM, NOT THE GUARANTEE — and the distinction is load-bearing
#   for whoever wires step 2. Verified 2026-08-16 (independently raised by a peer session, then
#   re-checked here against the bodies): what makes a captured chain safe to ALIAS is that every
#   `ret` closure is FRAME-AGNOSTIC — it takes `self::Frame` as a PARAMETER and closes over nothing
#   but immutables. All three forms:
#       `cont`       (`Eval.jl:952`, setup_chain)    closes over var/templ/depth/propagate; uses self.prev
#       `fret`       (`Eval.jl:968`, setup_function) closes over atom/depth;                 uses self/self.prev
#       `no_handler` (`Eval.jl:190`)                 ignores all three arguments
#   None holds a reference to a particular Frame, so re-running a chain cannot observe state left
#   behind by an earlier run.
#
#   ⚠️ ⇒ "there is only one Frame field write" DOES NOT PROTECT THIS. An 8th `Frame(` site whose
#   closure captured an OUTER frame (`f -> … outer_frame …` — a natural reach when wiring
#   `dependency/3` firing) would break continuation safety while adding ZERO field writes, and a
#   write-counting check would stay green. The invariant to guard is frame-agnosticism of `ret`.
#   NOT PINNED BY ANY TEST YET — `test_delimited_control.jl` gates capture/resume BEHAVIOUR, which a
#   frame-capturing closure could pass. A mechanical guard is owed; a peer session claimed it, so it
#   is deliberately not built here rather than built twice.
#
# * THE `Bindings` COPY BELOW IS NOT LOAD-BEARING TODAY — and is kept deliberately, with the reason
#   stated so nobody deletes it as cargo. Two mutation checks (drop the copy at capture AND at resume)
#   both PASSED, which means those probes were BLIND to the class, not that the class is absent
#   (`[[feedback_oracle_must_observe_the_defect_class]]`). Settled from the CODE BODY instead:
#   `merge_bindings` (`Atoms.jl:224-252`) folds into `left` in place via `_extend_*_inplace!` but
#   `resize!`s back to its checkpoint on EVERY exit path, returning `copy(left)` as the survivor — an
#   append-only trail with an O(1) undo, observationally pure. No probe COULD have discriminated.
#   ⚠️ THAT UNDO IS SAFE ONLY BECAUSE THE TRAIL WINDOW CLOSES BEFORE WE RESUME, which holds on ONE
#   THREAD. Roadmap 7.9 (shared tabling) is IN SCOPE and puts a live capture inside that window.
#   `Bindings(copy(b.entries))` is cheap insurance against an item we have already committed to build.
# ═══════════════════════════════════════════════════════════════════════════════

"""
    Continuation

A suspended computation captured at a tabled call — the `shift/1` half of delimited control.
`prev` is the pending frame chain (NOT copied; see the header — frames are read-only in practice),
`b` the bindings at the suspension point (copied), `goal` the SOURCE goal in its `_reduced_goal` form,
retained because answers are stored in the canonical key's variables and must be `_project`ed back.
"""
struct Continuation
    prev::Union{Frame,Nothing}
    b::Bindings
    goal::Atom
end

"""
    capture_continuation(b, prev, goal) -> Continuation

`shift/1`: capture the remainder of the current computation without producing an answer.
"""
capture_continuation(b::Bindings, prev::Union{Frame,Nothing}, goal::Atom) =
    Continuation(prev, copy(b), goal)

"""
    resume_continuation(c, answer, space) -> Vector{Tuple{Atom,Bindings}}

Feed one `answer` into a captured continuation and run it to completion — the paper's
`delim(Wrapper, Continuation, TargetTable)` on the resume side (§4.3 `completion_step/1`).

Runs on the SHARED driver (`Eval._run_plan`), so the step cap and diagnostics apply exactly as to a
top-level `interpret`. RE-ENTRANT BY CONSTRUCTION: `c` is never consumed, so the same continuation may
be resumed once per answer — which is the whole point, since a dependency fires on every new answer of
its source table.
"""
resume_continuation(c::Continuation, answer::Atom, space)::Vector{Tuple{Atom,Bindings}} =
    _run_plan(finished_result(answer, copy(c.b), c.prev), space)

"""
    Dependency(source, cont, target)

*"Given an answer for the q/m call, one may obtain answers for the p/n call by resuming the suspended
continuation."* (§4.2). Stored in the SOURCE call's table and fired whenever a new answer lands there;
`target` names the table the resumed continuation's answers belong to.
"""
struct Dependency
    source::Atom          # the variant key of the tabled goal that suspended us
    cont::Continuation    # the captured remainder of the TARGET's worker
    target::Atom          # the variant key whose answer set the resumption feeds
end

const _DEPS = Dict{Atom,Vector{Dependency}}()   # source key ↦ dependencies waiting on its answers

# Canonicalize a tabled goal to its VARIANT KEY. Cross-checked vs SWI-Prolog boot/tabling.pl `start_tabling`
# + the C `$tbl_variant_table`: SWI variant-matches the goal up to variable RENAMING and does NOT reduce
# args (Prolog's is/2 pre-evaluates them before the call). MeTTa nests the arithmetic IN the goal
# (`(fib (- n 1))`) with no is/2-before-call split, so we (a) REDUCE the args — the MeTTa analog of Prolog's
# pre-call arg eval — then (b) RENAME vars by first occurrence (= SWI's variant canonicalization). Result:
# `(fib (- 20 2))` and `(fib (- 19 1))` both key to `(fib 18)` (halves the table → O(n)), and `(fib $x)` /
# `(fib $y)` share one table.
function _variant_rename(a::Atom)::Atom
    seen = Dict{Var,Var}(); n = Ref(0)
    rn(x::Atom) = x isa Var ? get!(() -> (n[] += 1; Var("_v", UInt64(n[]))), seen, x) :
                  (x isa Expression ? Expression(Atom[rn(c) for c in x.children]) : x)
    rn(a)
end
# reduced goal = subst + REDUCE args (no var-rename); _canonical_goal renames on top ⇒ the variant KEY.
function _reduced_goal(atom::Atom, space, b::Bindings)::Atom
    g = subst(atom, b)
    (g isa Expression && !isempty(g.children)) || return g
    rargs = Atom[c isa Var ? c : (rs = metta_run(c, space); isempty(rs) ? c : rs[1]) for c in g.children[2:end]]
    Expression(Atom[g.children[1]; rargs])
end
_canonical_goal(atom::Atom, space, b::Bindings)::Atom = _variant_rename(_reduced_goal(atom, space, b))

# NON-GROUND ANSWER PROJECTION (the SLG answer skeleton, variant tabling). Answers are stored in the canonical
# key's vars (_v1.._vn from _variant_rename); replaying them to a caller whose goal is a VARIANT means mapping
# _vi back to the caller's i-th (first-occurrence) variable. Ground goals have no vars ⇒ identity (the fib fast
# path, zero overhead). This is what lets tabling fire on `(Deduction $A $B $C)`-style non-ground pattern calls,
# not just ground arithmetic. (Fresh existential vars a rule body introduces are NOT standardized-apart here —
# a documented follow-up; PLN's equality-based matching is dominated by goal-var answers.)
function _ordered_vars(a::Atom)::Vector{Var}
    out = Var[]; seen = Set{Var}()
    function walk(x::Atom)
        if x isa Var
            x in seen || (push!(seen, x); push!(out, x))
        elseif x isa Expression
            for c in x.children; walk(c); end
        end
    end
    walk(a); out
end
_subst_vars(a::Atom, m::Dict{Var,Atom})::Atom =
    a isa Var ? get(m, a, a) :
    (a isa Expression ? Expression(Atom[_subst_vars(c, m) for c in a.children]) : a)
function _project(answers::Vector{Atom}, red::Atom)::Vector{Atom}
    cvars = _ordered_vars(red)
    isempty(cvars) && return answers
    m = Dict{Var,Atom}(Var("_v", UInt64(i)) => cvars[i] for i in eachindex(cvars))
    Atom[_subst_vars(a, m) for a in answers]
end

# Suspend-on-variant via NAIVE FIXPOINT — the simplification of SWI completion (boot/tabling.pl
# run_leader/`completion` resumes a delimited continuation off a worklist; we re-run the leader pass instead:
# correct for a single SCC, no continuation machinery). A tabled goal is the LEADER of its variant; a re-entry
# of an IN-PROGRESS variant is a CONSUMER that reads the leader's PARTIAL answers — so left-recursion SUSPENDS
# (returns partials) instead of looping. A leader that no consumer re-read (fib) finishes in ONE pass.
#   SCOPE: single self-recursive SCC, naive (re-derives each round, not semi-naive), ground/enumerable answer
#   atoms. No mutual-SCC merging (SWI's dynamic SCC), no WFS negation (§7.6), no answer subsumption (§7.3).

# One resolution pass for the leader: apply key's `(= key body)` rules and reduce each body. A recursive
# sub-call to an in-progress variant hits the hook → consumer → reads partials. Returns this pass's answers.
function _leader_pass(key::Atom, typ::Atom, space::Space)::Vector{Atom}
    out = Atom[]; X = freshvar("X")
    for qb in query(space, Expression(Sym("="), key, X)), mb in merge_bindings(Bindings(), qb)
        is_present(mb, X) || continue
        for (at, bnd) in interpret(_metta(subst(X, mb), typ), space, mb)
            is_empty_atom(at) || push!(out, subst(at, bnd))
        end
    end
    unique(out)
end

# ── WFS Stage B (Prolog-parity precision on dynamically-stratified programs) ──────────────────────────
# Which SCCs need the alternating-fixpoint WFS completion? EXACTLY those with recursion-through-negation — a
# positive edge that closes a cycle back through a `tnot` barrier. That is DETECTED DYNAMICALLY, at the source,
# by the existing negation machinery: when a CONSUMER (positive variant re-entry) reads an in-progress goal that
# sits behind an active `tnot` (`_NEG_DEPTH>0 && key ∈ _NEG_BARRIER`), the SCC is marked in `_SCC_NEG` (below,
# in `tabled_eval`). Routing reads that mark. No static body-scan for the `tnot` symbol — that was brittle (it
# missed the resolved `Grounded(SpaceOp("tnot"))` form vs a bare `Sym(:tnot)`) and redundant (it re-derived what
# `_NEG_TAINT` already knows). A purely-positive / stratified SCC never trips the barrier ⇒ byte-identical naive
# fixpoint (fib path); only genuine recursion-through-negation routes to `_wfs_complete!`.

# "definite" = has ≥1 REAL (non-UNDEFINED) answer — mirrors the provably-true test at TNOT (`any(a != UNDEFINED)`),
# so an only-UNDEFINED set is NOT treated as membership (keeps the layered-undefined case sound).
@inline _wfs_definite(S)::Bool = any(a -> a != UNDEFINED, S)

# S_P(I): the least model of the van Gelder reduct P/I over the SCC, materialized into _PARTIAL.
#   • positive in-SCC edges (g2:-g1) read the GROWING _PARTIAL via the consumer path (tabled_eval);
#   • in-SCC tnot(G) reads the FIXED bound I (=_WFS_BOUND) — no drive, no taint, no inprog-guard (TNOT branch);
#   • out-of-SCC goals read completed _ANSWER_TABLE exactly as today.
# _PARTIAL is RESTARTED from ⊥ each call (a genuine lfp) — that dissolves positive loops without a separate
# answer-completion pass (getting this wrong re-introduces spurious `true`s). MUST-FIX (adversary): reset EACH
# member — including a mid-phase newcomer that joins comp() during this call — to ⊥ on its FIRST appearance, so
# no member ever reads a stale cross-phase _PARTIAL under the current bound (the only unsoundness path found).
function _S_P!(members::Vector{Atom}, typ::Atom, space::Space, key::Atom,
               bound::Dict{Atom,Vector{Atom}})::Dict{Atom,Vector{Atom}}
    comp() = Atom[g for g in _GEN_STACK if _scc_root(g) == key]
    savedB = _WFS_BOUND[]; savedA = _WFS_ACTIVE[]
    _WFS_BOUND[] = bound; _WFS_ACTIVE[] = true
    seen = Set{Atom}()
    try
        while true
            for m in comp()                                       # ⊥-restart, newcomer-safe (MUST-FIX):
                (m in seen) || (_PARTIAL[m] = Atom[]; push!(seen, m))
            end
            grew = false
            for m in comp()
                np = _leader_pass(m, typ, space); n0 = length(_PARTIAL[m])
                _PARTIAL[m] = unique(vcat(_PARTIAL[m], np))
                length(_PARTIAL[m]) != n0 && (grew = true)
            end
            grew || break
        end
        return Dict{Atom,Vector{Atom}}(m => copy(_PARTIAL[m]) for m in comp())
    finally
        _WFS_BOUND[] = savedB; _WFS_ACTIVE[] = savedA             # nest-safe (mirrors _NEG_BARRIER save/restore)
    end
end

# WFS completion for a negation-bearing SCC — Van Gelder ALTERNATING FIXPOINT (option A, answer-set level).
#   K = lfp(S_P∘S_P) from ∅ = well-founded TRUE atoms;   U = S_P(K) = TRUE ∪ UNDEFINED.
# Classify each member: definite in K ⇒ true (well-founded answers); in U but unfounded in K ⇒ undefined;
# not even in the optimistic U ⇒ false. Leaves the classified set in _PARTIAL[m] for tabled_eval to cache.
function _wfs_complete!(members::Vector{Atom}, typ::Atom, space::Space, key::Atom)
    comp() = Atom[g for g in _GEN_STACK if _scc_root(g) == key]
    K = Dict{Atom,Vector{Atom}}(m => Atom[] for m in members)     # ⊥
    local U::Dict{Atom,Vector{Atom}} = K
    while true
        U     = _S_P!(members, typ, space, key, K)               # Upper = S_P(K)        (optimistic step)
        Knext = _S_P!(members, typ, space, key, U)               # T(K)  = S_P(S_P(K))   (pessimistic step)
        members = comp()
        converged = length(Knext) == length(K) &&
            all(m -> haskey(K, m) && issetequal(K[m], Knext[m]), keys(Knext))
        K = Knext
        converged && break                                       # at break: U = S_P(K) (the true upper bound)
    end
    for m in comp()
        km = get(K, m, Atom[]); um = get(U, m, Atom[])
        _PARTIAL[m] = _wfs_definite(km) ? km :                   # TRUE  — well-founded definite answers
                      !isempty(um)      ? Atom[UNDEFINED] :      # UNDEFINED — in U, unfounded in K
                                          Atom[]                  # FALSE — not even in the optimistic U
    end
    return nothing
end

# Dynamic-SCC completion — the SOUNDNESS extension over single-goal suspend. SWI completes an ENTIRE SCC
# together (boot/tabling.pl `completion` → `$tbl_table_complete_all(SCC)`); finalising one goal before a
# mutually-dependent partner makes the partner's table unsound. We track the in-progress GENERATOR stack
# (_GEN_STACK) + a union-find of SCC roots (_COMPONENT): when a CONSUMER re-enters a goal that is an ANCESTOR
# on the stack (a cross-leader cycle), every generator from that ancestor up is unioned into one component.
# The component ROOT drives a joint naive fixpoint over ALL members and completes them together; a non-root
# member is a FOLLOWER that returns its partials and stays in-progress for the root to finish. A lone,
# non-self-recursive goal (fib) is a singleton root ⇒ ONE pass (no regression). SCOPE caveats unchanged:
# naive (not semi-naive), no answer subsumption (§7.3), ground/enumerable answer atoms.
# ⚠️ "no WFS tnot (§7.6)" WAS LISTED HERE AND IS FALSE — corrected 2026-08-11. Well-founded negation is
# implemented (`_wfs_complete!` below, the `TNOT` SpaceOp, `_WFS_BOUND`/`_WFS_ACTIVE`/`_SCC_NEG`, and the
# alternating-fixpoint phase machinery), registered as `tnot` in `TOKEN_REGISTRY`, and gated by
# `test/standard/test_tnot_wfs.jl` (41 assertions) plus `test_wfs_swipl_differential.jl`, which runs a
# LIVE swipl oracle and skips loudly if swipl is absent. Two stale scope claims in one header is why
# `[[feedback_capability_claims_expire_retest_the_premise]]` exists.
function tabled_eval(atom::Atom, typ::Atom, space::Space, b::Bindings, prev)
    red = _reduced_goal(atom, space, b); key = _variant_rename(red)             # red keeps the caller's vars;
    if haskey(_ANSWER_TABLE, key)                                                # complete entry — but only replay if
        if get(_ANSWER_STAMP, key, (UInt(0), -1)) == (objectid(space), space.revision)
            return _replay(_project(_ANSWER_TABLE[key], red), b, prev)          #   FRESH (space unchanged) ⇒ project+replay
        end
        delete!(_ANSWER_TABLE, key); delete!(_ANSWER_STAMP, key)                 #   STALE (space mutated) ⇒ evict + recompute
    end
    if key in _TABLE_INPROG                                                       # CONSUMER (variant re-entry):
        push!(_PARTIAL_READ, key)                                                #   flag self-recursion,
        if _NEG_DEPTH[] > 0 && key in _NEG_BARRIER                                #   positive edge crossing a tnot
            _NEG_TAINT[] = true                                                   #   ⇒ recursion-through-negation:
            push!(_SCC_NEG, key)                                                  #   mark this SCC → `_wfs_complete!`
        end
        ki = findfirst(g -> g == key, _GEN_STACK)                                #   union key..top into one SCC
        if ki !== nothing
            root = _scc_root(key)
            for j in ki+1:length(_GEN_STACK)
                _COMPONENT[_scc_root(_GEN_STACK[j])] = root
            end
        end
        return _replay(_project(get(_PARTIAL, key, Atom[]), red), b, prev)       #   answer from partials (suspend)
    end
    push!(_TABLE_INPROG, key); push!(_GEN_STACK, key)                            # become a GENERATOR
    _PARTIAL[key] = Atom[]; _COMPONENT[key] = key; delete!(_PARTIAL_READ, key)
    local ans::Vector{Atom} = Atom[]
    try
        _PARTIAL[key] = _leader_pass(key, typ, space)                           # initial pass (may merge me up)
        if _scc_root(key) != key                                                 # I became a FOLLOWER ⇒
            return _replay(_project(_PARTIAL[key], red), b, prev)              #   ancestor root finishes me
        end
        comp() = Atom[g for g in _GEN_STACK if _scc_root(g) == key]            # I am the ROOT: my SCC members
        members = comp()
        if !(length(members) == 1 && !(key in _PARTIAL_READ))                    # singleton+no self-rec ⇒ 1 pass
            if any(m -> m in _SCC_NEG, members)                                  # WFS Stage B: recursion-thru-negation
                _wfs_complete!(members, typ, space, key)                         #   ⇒ alternating-fixpoint completion
            else
                while true                                                       # positive SCC: joint naive fixpoint
                    grew = false
                    for m in members
                        np = _leader_pass(m, typ, space); n0 = length(_PARTIAL[m])
                        _PARTIAL[m] = unique(vcat(_PARTIAL[m], np))
                        length(_PARTIAL[m]) != n0 && (grew = true)
                    end
                    grew || break
                    members = comp()                                            # component may have grown
                end
            end
        end
        ans = _PARTIAL[key]
        _stamp = (objectid(space), space.revision)                              # stamp each completed answer set with
        for m in comp(); _ANSWER_TABLE[m] = _PARTIAL[m]; _ANSWER_STAMP[m] = _stamp; end  # the (space, revision) it holds for
    finally
        if _scc_root(key) == key                                                # only the ROOT cleans its SCC
            done = Atom[g for g in _GEN_STACK if _scc_root(g) == key]
            filter!(g -> _scc_root(g) != key, _GEN_STACK)
            for m in done
                delete!(_TABLE_INPROG, m); delete!(_PARTIAL, m); delete!(_COMPONENT, m); delete!(_PARTIAL_READ, m)
                delete!(_SCC_NEG, m)
            end
        end
    end
    _replay(_project(ans, red), b, prev)
end

# tnot — SLG tabled negation (SWI boot/tabling.pl:852), negation of PROVABILITY (distinct from grounded `not`,
# which is truth-functional Bool→Bool value negation — left untouched). SPECIAL FORM: like COLLAPSE it takes G
# UNEVALUATED and controls its evaluation, so it can probe G's table BEFORE reducing. Three-valued read of G's
# COMPLETE answer set = SWI's `$tbl_answer_dl` true/conditional/none probe. SCOPED (per the design synthesis):
# STRATIFIED negation exactly (⇒ perfect-model, complete) + an HONEST `undefined` for recursion-through-negation
# — never a spurious two-valued answer. Full delay-list WFS residuals (EXPLANATION, not correctness) deferred.
#   G ∈ _TABLE_INPROG (live negative loop)   ⇒ undefined      | drive crosses a negation (barrier read) ⇒ undefined
#   G complete, has a REAL answer            ⇒ Empty (¬G false)| G complete, only `undefined`  ⇒ undefined
#   G complete, NO answers                   ⇒ True  (¬G true)
# Consistent with the bottom-up lane's stratified-NAF (KBSaturation `_is_negated_premise`: succeeds iff the
# closed-world match is empty) — same meaning of negation, extended top-down with the undefined third value.
# Opt-in gate: fires only when G's head is tabled (else usage error) ⇒ default-OFF ⇒ 234-path byte-identical.
const TNOT = Grounded(SpaceOp("tnot", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    G = xs[1]
    (G isa Expression && !isempty(G.children)) || return ExecNoReduce()
    is_tabled(G) || return ExecOk(Atom[error_atom(Expression(Atom[Sym("tnot"), G]),
        "tnot: goal head must be tabled — (table! …) it first")])
    isempty(collect_vars(G)) || return ExecOk(Atom[error_atom(Expression(Atom[Sym("tnot"), G]),
        "tnot: non-ground goal (instantiation_error)")])
    key = _canonical_goal(G, space, Bindings())
    if _WFS_ACTIVE[] && haskey(_WFS_BOUND[], key)                        # WFS Stage B: IN-SCC negation during the
        S = _WFS_BOUND[][key]                                            #   alternating fixpoint — read the phase-
        return _wfs_definite(S) ? ExecOk(Atom[]) :                       #   FIXED bound I (no drive/taint/inprog):
               isempty(S)       ? ExecOk(Atom[Sym("True")]) :            #     G∈I definite ⇒ ¬G false (Empty)
                                  ExecOk(Atom[UNDEFINED])               #     G∉I empty    ⇒ ¬G true
    end                                                                 #     I[G] only-undef ⇒ ¬G undefined
    key in _TABLE_INPROG && return ExecOk(Atom[UNDEFINED])                # live negative loop ⇒ WFS bottom
    saved = copy(_NEG_BARRIER); union!(_NEG_BARRIER, _TABLE_INPROG)       # drive G under a negation barrier:
    st = _NEG_TAINT[]; _NEG_TAINT[] = false; _NEG_DEPTH[] += 1            #   a consumer reading a barrier key
    local A::Vector{Atom} = Atom[]; local tainted::Bool = false          #   ⇒ a positive edge crossed the tnot
    try
        A = metta_run(G, space)
    finally
        _NEG_DEPTH[] -= 1; tainted = _NEG_TAINT[]; _NEG_TAINT[] = st
        empty!(_NEG_BARRIER); union!(_NEG_BARRIER, saved)
    end
    tainted                     && return ExecOk(Atom[UNDEFINED])         # crossed the negation ⇒ can't decide
    any(a -> a != UNDEFINED, A) && return ExecOk(Atom[])                  # G provably true ⇒ ¬G false ⇒ Empty
    any(a -> a == UNDEFINED, A) && return ExecOk(Atom[UNDEFINED])         # G only-undefined ⇒ ¬G undefined
    ExecOk(Atom[Sym("True")])                                            # G false ⇒ ¬G true
end))
