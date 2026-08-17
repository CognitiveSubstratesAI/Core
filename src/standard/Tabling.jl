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
                   _CURRENT_TARGET[] = nothing; _DEPS_COUNT[] = 0; clear_worklists!(); clear_answer_tries!(); clear_idg!(); clear_mono!();  # §1.0 3-4 + §7.7 + §7.8
                   _WFS_BOUND[] = Dict{Atom,Vector{Atom}}(); _WFS_ACTIVE[] = false)
_scc_root(k::Atom)::Atom = (r = get(_COMPONENT, k, k); r == k ? k : (_COMPONENT[k] = _scc_root(r)))
"Mark predicate `head` (a Symbol) for tabled (memoised) execution; clears the answer table."
table!(head::Symbol) = (push!(_TABLED_HEADS, head); _table_reset!(); nothing)
"Disable all tabling and clear the answer table."
untable_all!() = (empty!(_TABLED_HEADS); _table_reset!(); nothing)

# ═══════════════════════════════════════════════════════════════════════════════
# ROADMAP 0.3 — PER-HEAD `untable!`, so tabling state is SCOPED instead of process-global.
#
# `untable/1` (`boot/tabling.pl:250-286`). Upstream does FIVE things per predicate, and doing fewer
# leaves state that outlives the declaration it belonged to:
#   1. only acts if the predicate IS tabled (`; true` otherwise — a no-op, never an error)
#   2. `abolish_table_subgoals/1` — drops the predicate's TABLES
#   3. `retractall('$tabled'/2)` — drops the declaration
#   4. `retractall('$table_mode'/3)` — drops the MODE (our `tabling/Aggregation.jl` registry)
#   5. clears the attributes: tabled / opaque / incremental / monotonic / lazy
#      (our only landed attribute-shaped state is the §7.11 restraint, in `tabling/Tripwires.jl`)
#
# ⚠️ WHY THIS IS NOT `delete!(_TABLED_HEADS, head)`. Every other container is keyed by the VARIANT
# KEY (an `Atom`), not by the head symbol, so a head's rows have to be filtered out of eight of them.
# Left behind, they are worse than stale: `_ANSWER_TABLE` would serve answers for a predicate that is
# no longer tabled, and `_DEPS` would fire resumptions into a table that no longer exists.
#
# ⚠️ AND THE MID-EVALUATION GUARD IS NOT OPTIONAL. Upstream raises `permission_error` when a change
# hits an INCOMPLETE table (`pl-tabling.c` `state.incomplete` → `change_incomplete_error`). Pulling a
# head out from under an in-progress fixpoint would leave `_GEN_STACK`/`_COMPONENT` referring to a
# table whose answers were just deleted. We refuse the same way rather than corrupting the run.
"""
    untable!(head) -> Bool

Undo `table!` for ONE head: drop the declaration, abolish its tables, and clear its mode and
restraints. Returns `false` (a no-op) if `head` was not tabled, mirroring upstream's `; true`.

Throws if `head` has an INCOMPLETE table — upstream's `change_incomplete_error`.
"""
function untable!(head::Symbol)::Bool
    head in _TABLED_HEADS || return false
    any(k -> head_name(k) === head, _TABLE_INPROG) && throw(ErrorException(
        "permission_error(modify, incomplete_table, $(head)) — untable! during an active " *
        "completion would delete answers the running fixpoint still refers to"))
    delete!(_TABLED_HEADS, head)
    abolish_table_subgoals!(head)
    untable_modes!(head)        # '$table_mode' — tabling/Aggregation.jl
    restraint!(head, :max_answers, -1)   # the attribute-shaped state — tabling/Tripwires.jl
    untable_subsumptive!(head)           # §7.5 mode — tabling/Subsumptive.jl
    clear_table_options!(head)           # the parsed `as ...` record — tabling/Options.jl
    true
end

"""
    abolish_table_subgoals!(head)

`abolish_table_subgoals/1` (`library/tables.pl`) at head granularity — the middle of upstream's three
levels (all / module / subgoal); we previously had only `abolish_all_tables` as `untable_all!`.

Drops every row keyed by a variant of `head` from ALL the per-key containers. `_DEPS` needs both
directions: a dependency is dropped when its SOURCE is this head (its table is going away) and when
its TARGET is (resuming into a deleted table is what leaves a dangling continuation).
"""
function abolish_table_subgoals!(head::Symbol)
    _ishead(k::Atom) = head_name(k) === head
    for d in (_ANSWER_TABLE, _ANSWER_STAMP, _PARTIAL, _COMPONENT, _DEPS)
        for k in collect(keys(d)); _ishead(k) && delete!(d, k); end
    end
    for s in (_TABLE_INPROG, _PARTIAL_READ, _NEG_BARRIER, _SCC_NEG)
        for k in collect(s); _ishead(k) && delete!(s, k); end
    end
    for (src, deps) in _DEPS                       # …and dependencies TARGETING this head
        filter!(dep -> !_ishead(dep.target), deps)
        isempty(deps) && delete!(_DEPS, src)
    end
    filter!(!_ishead, _GEN_STACK)
    # §1.0 step 3: a table's WORKLIST dies with the table. Resolved at call time — `drop_worklist!`
    # is defined in `tabling/Worklists.jl`, included after this file (see the note at its include).
    for key in collect(keys(_WORKLISTS)); _ishead(key) && drop_worklist!(key); end
    # §1.0 step 4: and its ANSWER TRIE. A surviving trie would serve answers for a predicate that is
    # no longer tabled — the same class as a stranded _DEPS entry.
    for key in collect(keys(_ANSWER_TRIES)); _ishead(key) && drop_answer_trie!(key); end
    # §7.7: and its IDG node, unlinking both directions — a dropped table must not leave dangling
    # edges that propagate invalidation into nothing.
    for key in collect(keys(_IDG)); _ishead(key) && drop_idg_node!(key); end
    # §7.8: and its monotonic dependencies, in both directions — a resume into a dropped table
    # would feed answers into a trie that no longer exists.
    for key in collect(keys(_MONO_DEPS)); _ishead(key) && drop_mono_deps!(key); end
    nothing
end
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
# ═══════════════════════════════════════════════════════════════════════════════
# ROADMAP 2.0 — THE MULTIVALUED GUARD.
#
# Tabling COLLAPSES MULTIPLICITY: `(= (h) 1)` twice gives untabled `[1,1]` and tabled `[1]`. That is
# not a bug in our merge — TABLING IS SET-SEMANTICS BY DESIGN in every implementation (the
# delimited-control paper dedups in `store_answer/2`; SWI structurally, via the answer trie), while
# MeTTa is MULTISET. It is a LANGUAGE-LEVEL mismatch, so the fix is not a better merge — it is
# REFUSING TO TABLE heads whose multiplicity would be observable. Three upstreams agree that this is
# the right response: JeTTa's `!f.isMultivalued()` (`Generator.kt:166`), Triska's `once/1`, and our
# own measurement.
#
# 🔴 THE SIGNAL, and why `length(rules[h]) > 1` — the roadmap's candidate — is the WRONG one.
# It is too blunt in the way the roadmap suspected: it refuses `(= (f a) 1)` + `(= (f b) 2)`, whose
# patterns are DISJOINT, so no call can ever match both and tabling is perfectly safe.
#
# The precise question is not "how many rules" but "CAN TWO RULES FIRE ON ONE CALL", i.e. are any two
# rule-head patterns UNIFIABLE. That admits the disjoint case and still refuses the real ones:
#
#     (= (h) 1)   (= (h) 2)          heads identical        → unifiable  → NOT tabled ✓
#     (= (fact 0) 1) (= (fact $n) …) `0` unifies with `$n`  → unifiable  → NOT tabled ✓
#     (= (f a) 1) (= (f b) 2)        `a` vs `b`             → disjoint   → TABLED     ✓
#
# The `fact` row is the one worth dwelling on: MeTTa really does answer `(fact 0)` from BOTH clauses,
# so it IS multivalued there and refusing it is correct, not conservative. Prolog's first-match cut
# does not apply — `[[feedback_reference_shape_vs_primitive_semantics]]`.
#
# ⚠️ FAILS SAFE. Variables are standardised apart before the test, and anything we cannot decide is
# treated as MULTIVALUED (not tabled). The unsafe direction is tabling something multivalued, which
# silently drops answers; declining to table costs only speed.

"LHS patterns per head — `_rules_of` keeps only RHS bodies, and the guard needs the heads."
function _rule_heads_of(atoms)::Dict{Symbol,Vector{Atom}}
    d = Dict{Symbol,Vector{Atom}}(); EQ = Symbol("=")
    for a in atoms
        (a isa Expression && length(a.children) == 3 && head_name(a) == EQ) || continue
        lhs = a.children[2]
        (lhs isa Expression && !isempty(lhs.children) && lhs.children[1] isa Sym) || continue
        push!(get!(d, head_name(lhs), Atom[]), lhs)
    end
    d
end

"Rename every variable in `a` to a fresh id, so two patterns share no variable (standardise apart)."
function _standardise_apart(a::Atom, tag::UInt64)::Atom
    seen = Dict{Var,Var}(); n = Ref(0)
    rn(x::Atom) = x isa Var ? get!(() -> (n[] += 1; Var("_sa$(tag)", UInt64(n[]))), seen, x) :
                  (x isa Expression ? Expression(Atom[rn(c) for c in x.children]) : x)
    rn(a)
end

"""
    is_multivalued(heads) -> Bool

Can two of these rule-head patterns fire on ONE call? True ⇒ tabling would collapse multiplicity.

Uses `match_atoms` for unifiability after standardising apart. Any pair we cannot decide counts as
multivalued: the unsafe direction is tabling something multivalued, which drops answers silently.
"""
function is_multivalued(heads::Vector{Atom})::Bool
    length(heads) <= 1 && return false
    for i in 1:length(heads)-1, j in i+1:length(heads)
        li = _standardise_apart(heads[i], UInt64(1))
        lj = _standardise_apart(heads[j], UInt64(2))
        unifiable = try
            !isempty(match_atoms(li, lj)) || !isempty(match_atoms(lj, li))
        catch
            true                      # undecidable ⇒ treat as multivalued (fail safe)
        end
        unifiable && return true
    end
    false
end

"""
    _multivalued_heads(atoms) -> Set{Symbol}

Every head whose answers can be a genuine MULTISET, as a least fixpoint over the call graph.

🔴 THE PROPAGATION IS THE POINT, and the head-local test alone does NOT fix the measured defect.
Found by running the case rather than reasoning about it: with only the overlap test,

    (= (h) 1)  (= (h) 1)  (= (k) (h))

correctly refuses to table `h` — and then TABLES `k`, whose single rule cannot overlap anything, so
`!(k)` still collapsed `[1,1]` to `[1]`. Multivaluedness is INHERITED: a head that calls a
multivalued head returns its multiplicity. Seeded by the head-local overlap test and closed under
`_callees!`, the same shape as `_pure_heads`'s purity fixpoint.

Analyses ALL rules, stdlib included, because the call chain that carries multiplicity into a user
head can run through library code.
"""
function _multivalued_heads(atoms)::Set{Symbol}
    rh    = _rule_heads_of(atoms)
    rules = _rules_of(atoms)
    multi = Set{Symbol}(h for (h, pats) in rh if is_multivalued(pats))   # seed: overlapping clauses
    changed = true
    while changed                                                        # close over calls
        changed = false
        for (h, bodies) in rules
            h in multi && continue
            for b in bodies
                cs = Set{Symbol}(); _callees!(b, cs)
                if !isdisjoint(cs, multi)
                    push!(multi, h); changed = true; break
                end
            end
        end
    end
    multi
end

function auto_table!(space::Space)
    pure = _pure_heads(_rules_of(all_atoms(space)))                         # analyze ALL rules (stdlib deps too)
    user = keys(_rules_of(own_atoms(space)))                               # but only TABLE the user's own heads
    # ROADMAP 2.0: refuse heads whose rules can BOTH fire on one call — tabling is set-semantics and
    # would silently drop the duplicate answers MeTTa's multiset semantics requires.
    multi = _multivalued_heads(all_atoms(space))
    up = setdiff(intersect(pure, user), multi)
    for h in up; table!(h); end
    (tabled = sort!(collect(up)), skipped = sort!(collect(setdiff(user, up))),
     multivalued = sort!(collect(multi)))
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

# ── THE COMPLETION MERGE POINT — one function, and the growth signal is VALUE-based ──────────────
# Every fixpoint round in this file merges a pass's answers into a table and asks "did anything
# change?". That question had TWO hand-rolled answers, both `length(_PARTIAL[m]) != n0`.
#
# 🔴 CARDINALITY IS THE WRONG SIGNAL, AND IT FAILS SILENTLY. This file's own header has warned since
# the extraction that "a table can keep its SIZE while its VALUE improves"; §7.3 mode-directed tabling
# (landed 2026-08-16 in `tabling/Aggregation.jl`) is the consumer that makes it real. Folding
# `(k,1)` and `(k,2)` into `(k,3)` under `lattice(sum)` leaves the COUNT fixed, so a length test
# reports convergence and completes a HALF-AGGREGATED table — no error, no missing answer, just a
# wrong number.
#
# ⚠️ THE SWITCH IS BEHAVIOUR-PRESERVING TODAY, AND THAT IS CHECKABLE, NOT ASSUMED. With no modes
# declared, `merge_answers` is set-union with a value-based flag; since `_PARTIAL[m]` is always
# dup-free and the merge only ever ADDS, "a new element appeared" and "the length grew" coincide
# exactly. Order also coincides (existing first, then new in arrival order). ⇒ the gate set is a
# real oracle for this change: identical answers, or the equivalence claim is wrong.
_merge_partial(existing::Vector{Atom}, incoming::Vector{Atom}, key::Atom)::Tuple{Vector{Atom},Bool} =
    merge_answers(existing, incoming, table_modes(head_name(key)))

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
    saved_target = _CURRENT_TARGET[]; _CURRENT_TARGET[] = key   # whose worker is running (dependency TARGET)
    try
        for qb in query(space, Expression(Sym("="), key, X)), mb in merge_bindings(Bindings(), qb)
            is_present(mb, X) || continue
            for (at, bnd) in interpret(_metta(subst(X, mb), typ), space, mb)
                is_empty_atom(at) && continue
                v = subst(at, bnd)
                push!(out, v)
                # ── roadmap 7.A: RECORD THE GOAL INSTANCE THAT PRODUCED THIS ANSWER ──────────────
                # 🔑 THIS IS THE ONLY PLACE THE INSTANCE STILL EXISTS. `bnd` binds `key`'s variables
                # to whatever the matching rule required, so `subst(key, bnd)` IS the instantiated
                # goal — and one line later it is gone, because `out` carries values. Every consumer
                # that has wanted it (§7.11.1's filter, and the delay list's "which derivation") has
                # wanted it from here.
                #
                # In Prolog the recording step does not exist: an answer IS a substitution over the
                # goal skeleton, so the trie node holds the instance inherently. A MeTTa answer is a
                # VALUE, so the relation has to be made explicit — and it is one answer to MANY
                # instances, which is why it lives on the node rather than beside the answer.
                trie_record_instance!(answer_trie_for(key), v, subst(key, bnd))
            end
        end
    finally
        _CURRENT_TARGET[] = saved_target                       # nest-safe (mirrors _WFS_BOUND save/restore)
    end
    # 🔴 VARIANT DEDUP, not `unique` — FIXED 2026-08-17 with `_merge_partial`'s twin site.
    # `unique` is `==`-based, so two answers differing only by variable IDENTITY both survive, and
    # the caller then sees a "new" answer every round. Upstream's answer trie keys variables by
    # first-occurrence index, making them one node. See tabling/Aggregation.jl's merge for the full
    # argument — this is the same defect in the pass that FEEDS it.
    _variant_unique(out)
end

"`unique` under `=@=` rather than `==` — the answer trie's identity, applied to a plain vector."
function _variant_unique(xs::Vector{Atom})::Vector{Atom}
    out = Atom[]
    for x in xs
        any(y -> variant_eq(y, x), out) || push!(out, x)
    end
    out
end

# ═══════════════════════════════════════════════════════════════════════════════
# `dependency(Source, Cont, Target)` — RECORDING AND FIRING (roadmap §1.0, step 2 of 4)
#
# Desouter et al. §4.2: when a worker calls a tabled predicate it SHIFTs without producing an answer,
# and the suspended remainder is stored as `dependency(SourceCall, Continuation, TargetCall)` IN THE
# SOURCE CALL'S TABLE, fired whenever a new answer lands there — *"given an answer for the q/m call,
# one may obtain answers for the p/n call by resuming the suspended continuation."*
#
# ⚠️ RECORDING IS OFF BY DEFAULT AND NOTHING CONSUMES IT YET. This step builds the mechanism and
# proves it AGREES WITH RECOMPUTATION; the engine still reaches its fixpoint by re-running
# `_leader_pass`. Switching the completion loop over is step 4, and doing it before the agreement is
# demonstrated would be a rewrite with no oracle. `_DEPS_RECORD[]` is the gate, so the default path is
# byte-identical by construction (the disable-to-prove pattern this file already uses for tabling).
#
# 🔴 WHY THE FLAG IS NOT MERELY CAUTION: `_leader_pass` RE-RUNS every fixpoint round, so a consumer
# hit re-records its dependency each round and `_DEPS` grows without bound over a long completion.
# Under the step-4 rewire that is moot — the worker runs ONCE and suspends — but until then, leaving
# recording on by default would be a memory leak in the engine's hottest loop.
const _CURRENT_TARGET = Ref{Union{Atom,Nothing}}(nothing)   # variant key whose worker is running, or nothing
const _DEPS_RECORD    = Ref(false)                          # opt-in: record dependencies at consumers
                                                            # (on together with _RESUME_COMPLETION — resumption
                                                            #  without recording silently completes nothing)

"""How many dependencies have been RECORDED since the last table reset.

⚠️ A CUMULATIVE COUNTER, NOT `length(_DEPS)`, AND THE DIFFERENCE IS THE POINT. The resumption tests'
anti-vacuity probe used to sample `_DEPS` after a run — which only worked because completion LEAKED
its worklists and suspensions (audit finding #6, fixed 2026-08-17). Now that they are freed as
upstream frees them (`complete_worklist`, `pl-tabling.c:4876`), the surviving-state sample reads
zero for a run that did plenty of work. A counter observes the EVENT rather than its residue, so it
cannot be falsified by correct cleanup."""
const _DEPS_COUNT = Ref{Int}(0)

"Record `dependency(source, cont, target)` in the SOURCE's table (§4.2). No-op unless enabled."
function record_dependency!(source::Atom, b::Bindings, prev, red::Atom)
    _DEPS_RECORD[] || return nothing
    tgt = _CURRENT_TARGET[]
    tgt === nothing && return nothing            # not inside a worker ⇒ no target to feed
    push!(get!(_DEPS, source, Dependency[]), Dependency(source, capture_continuation(b, prev, red), tgt))
    _DEPS_COUNT[] += 1          # CUMULATIVE — `_DEPS` itself is now freed at completion (#6)
    nothing
end

"""
    fire_dependencies!(source, answers, space) -> Dict{Atom,Vector{Atom}}

Feed each of `answers` into every continuation waiting on `source`, and group the results by the
TARGET table they belong to — the paper's `completion_step/1`, minus the worklist that decides WHICH
pairs are still unprocessed (step 3).

Answers are stored in the canonical key's variables, so each is `_project`ed into the continuation's
own goal before resumption — the same mapping `_replay` does on the consumer path.
"""
function fire_dependencies!(source::Atom, answers::Vector{Atom}, space)::Dict{Atom,Vector{Atom}}
    out = Dict{Atom,Vector{Atom}}()
    for d in get(_DEPS, source, Dependency[])
        for a in _project(answers, d.cont.goal)
            for (at, bnd) in resume_continuation(d.cont, a, space)
                is_empty_atom(at) && continue
                push!(get!(out, d.target, Atom[]), subst(at, bnd))
            end
        end
    end
    for (k, v) in out; out[k] = unique(v); end
    out
end

# ═══════════════════════════════════════════════════════════════════════════════
# COMPLETION BY RESUMPTION — roadmap §1.0 step 4 (the loop half).
#
# Desouter et al. §4.3 `completion/0`: a worklist-driven LEAST FIXPOINT. Pop a table with work,
# take an (answers x dependencies) batch, RESUME each suspended continuation with each answer, and
# route the results into the TARGET table — repeating until no table has uncombined work.
#
# This is the alternative to `_leader_pass` RECOMPUTATION, which the literature names and rejects:
# *"the approach cannot achieve satisfactory performance as suspended goals are always
# re-evaluated"*. Here a worker runs ONCE; its remainder is fed answers instead of being re-run.
#
# 🟢 ON BY DEFAULT SINCE 2026-08-16, on two pieces of evidence and not before:
#
#  1. AGREEMENT AT CORPUS SCALE. The whole suite runs green under resumption — 81 files, the only
#     failure being the differential test's own "default is off" assertion. That includes the
#     §7.1/§7.2 tabling differential and the WFS differential, the gates that exercise tabling.
#  2. MEASURED, 3 STABLE RUNS. Allocations are byte-identical run to run, so they are the signal:
#       symmetric conn  1305 -> 815 KiB (-38%)    time 0.56-0.71x
#       mutual left-rec  186 ->  70 KiB (-62%)    time 0.59-0.63x
#       cycle 3          354 ->  98 KiB (-72%)    time 0.31-0.37x
#       fib 15          6919 -> 6919 KiB ( 0%)    time 0.94-1.02x   <- never resumes: UNTOUCHED
#     That last row is the important one: a program with no variant re-entry allocates the SAME
#     bytes, so the non-resuming path is unaffected rather than merely "about as fast".
#
# ⚠️ The paper's own number is a caution kept deliberately: their library is 8-38x SLOWER than XSB,
# so "resumption beats recomputation" is a property of a specific implementation, not a theorem. Ours
# was measured, not assumed. `CORE_TABLING_RECOMPUTE=1` restores the old engine for differentials.
#
# ⚠️ IT NEEDS DEPENDENCY RECORDING. The continuations it resumes are captured by
# `record_dependency!` at the consumer branch, so `_DEPS_RECORD[]` must be on for the initial pass.
# `_complete_resume!` turns both on together and restores them, rather than leaving a caller to
# discover that one without the other silently completes nothing.
# ⚠️ ENV OVERRIDE so the WHOLE SUITE can be run under resumption as a differential —
# `CORE_TABLING_RESUME=1 tools/run_tests.sh`. That is the real agreement oracle: the suite carries
# the §7.1/§7.2 and WFS swipl differentials, which are the only gates that exercise tabling at
# breadth. A handful of hand-written cases is not corpus coverage, and the flip must not rest on one.
# Same shape as `CORE_TEST_CETTA` for the opt-in CeTTa scan.
# ── roadmap 1.0b step 2: the ANSWER TRIE IS THE READ PATH. 🟢 FLIPPED ON 2026-08-17. ───────────
# It was off until the corpus agreed, and the corpus agreed, on the same two-part standard the
# resumption flip used — MEASURED, not argued:
#   • whole-suite: 88 files / 0 failed with `CORE_TABLING_TRIE_READ=1`;
#   • anti-vacuity: on `fib 12`, 13 of 13 tables carried a mirrored trie and `trie_answers(k)` was
#     `==` to `_ANSWER_TABLE[k]` for EVERY key — same answers AND same order, so the agreement is
#     evidence rather than a path that never ran;
#   • cost: +0.1% allocations at fib 12 and fib 16 (best of 3 each) — noise.
#
# 🔑 AND THE REASON TO FLIP IS NOT THE COST, IT IS WHAT IT UNBLOCKS. Per-answer METADATA has no home
# in a `Vector{Atom}`, and THREE separate features now need one: subgoal abstraction needs each
# answer's goal INSTANCE to be exact (§7.11.1, measured over-approximating without it), and delay
# lists + `answer_abstract` need per-answer CONDITIONS. Upstream keeps all of it on the trie node.
# Making the trie authoritative is the prerequisite those three share.
#
# ⚠️ THE AGREEMENT ABOVE HOLDS ONLY BECAUSE OF THE AUDIT FIX. Before 2026-08-17 `_PARTIAL` deduped by
# `==` and the trie by VARIANT, so the two stores held different answer COUNTS wherever an answer set
# contained variants — the switch was not answer-preserving and the old comment claiming it was is
# corrected at the read site. Finding #1 made both use one identity.
#
# `CORE_TABLING_TRIE_READ=0` still reaches the old store: a differential you can only run one way has
# stopped being a differential. Read in `__init__`, NOT as a const initialiser — a const is evaluated
# at PRECOMPILE time and bakes in the environment of whoever compiled the package (measured
# 2026-08-16).
# ── §7.7: record IDG edges during evaluation? OFF until the graph is consumed. ──────────────────
# Recording is OBSERVATIONAL — it changes no answer — but it costs memory per table, and the graph
# is not yet USED for invalidation (the revision stamp still does that job). `CORE_TABLING_IDG=1`
# turns recording on so the graph can be inspected against real runs before anything depends on it.
const _IDG_RECORD = Ref(false)

const _TRIE_READ = Ref(true)     # 🟢 DEFAULT ON — see the block above

const _RESUME_COMPLETION = Ref(false)

"""Read `CORE_TABLING_RESUME` at LOAD time.

⚠️ MUST be `__init__`, not a `const Ref(get(ENV,…))` initialiser. A const is evaluated during
PRECOMPILATION and baked into the image, so the env var is read when the package is compiled rather
than when it is run — measured: `CORE_TABLING_RESUME=1 julia -e 'using MeTTaCore'` reported the flag
still FALSE. Both flags move together, because resumption without recording silently completes
nothing."""
function __init__()
    # DEFAULT: resumption. `CORE_TABLING_RECOMPUTE=1` forces the old recomputation engine, which is
    # what keeps the differential runnable IN BOTH DIRECTIONS after the flip — a comparison you can
    # only run one way stops being a comparison. `CORE_TABLING_RESUME=1` is still honoured so the
    # pre-flip invocation in any script or note does not silently mean something else.
    recompute = get(ENV, "CORE_TABLING_RECOMPUTE", "") == "1"
    _RESUME_COMPLETION[] = !recompute
    _DEPS_RECORD[]       = !recompute
    _TRIE_READ[]         = get(ENV, "CORE_TABLING_TRIE_READ", "") != "0"    # ON unless explicitly 0
    _IDG_RECORD[]        = get(ENV, "CORE_TABLING_IDG", "") == "1"
end

"""The SCC's members RIGHT NOW — upstream's growing `created_worklists`, not a frozen list.

A table first reached inside a resumed continuation joins the component mid-completion and must be
drained too; `members` is the entry-time snapshot and cannot see it. Union rather than replacement,
because a member whose worklist was already dropped is still owed its `_PARTIAL`."""
function _resume_members(members::Vector{Atom}, key::Atom)::Vector{Atom}
    out = copy(members)
    seen = Set{Atom}(out)
    for g in _GEN_STACK
        _scc_root(g) == key && !(g in seen) && (push!(out, g); push!(seen, g))
    end
    out
end

"""The MERGED form of `newa` in `merged` — what a mode-directed table actually holds.

Without aggregation the answer IS its own merged form. With it, the entry sharing `newa`'s mode key
is the aggregate; falls back to `newa` if the modes cannot key it, which is the pre-aggregation
behaviour and so never worse than before."""
function _aggregated_form(merged::Vector{Atom}, newa::Atom, key::Atom)::Atom
    modes = table_modes(head_name(key))
    has_aggregation(modes) || return newa
    k = try; mode_key(newa, modes); catch; return newa; end
    for a in merged
        ka = try; mode_key(a, modes); catch; continue; end
        variant_eq(ka, k) && return a
    end
    newa
end

"""
    _complete_resume!(members, typ, space, key) -> Bool

Drive `members` to a fixpoint by RESUMPTION. Returns `true` if it ran (i.e. the flag is on).

Seeds each member's worklist with the answers its initial `_leader_pass` produced and the
dependencies that pass recorded, then repeatedly takes a work batch and resumes. `wkl_get_work!`
SWAPS the pair it returns, so a batch is combined exactly once and the loop terminates when no new
answer arrives — the trie/`_merge_partial` decides "new" structurally, not by count.
"""
function _complete_resume!(members::Vector{Atom}, typ::Atom, space::Space, key::Atom)::Bool
    _RESUME_COMPLETION[] || return false
    for m in members                                   # seed from the initial pass
        wl = worklist_for(m)
        for a in get(_PARTIAL, m, Atom[]); wkl_add_answer!(wl, a); end
        for d in get(_DEPS, m, Dependency[]); wkl_add_suspension!(wl, d); end
    end
    guard = 0
    while true
        did = false
        # 🔴 #5: THE MEMBER LIST MUST BE RE-READ EACH ROUND. `for m in members` froze the component
        # at entry, so a table first reached INSIDE a resumed continuation got `_PARTIAL`/a worklist
        # written and was then never drained — its answers leaked and vanished in the `finally`.
        # Upstream's `completion_` repeats `'$tbl_pop_worklist'(SCC, WorkList)` over the SCC's
        # GROWING `created_worklists` (`pl-tabling.c:4858`), which is exactly this re-read. The naive
        # loop and `_S_P!` already recomputed their component; only this path did not.
        for m in _resume_members(members, key)
            w = wkl_get_work!(worklist_for(m))
            w === nothing && continue
            did = true
            ansbatch, deps = w
            for d in deps, a in _project(ansbatch, d.cont.goal)
                # 🔴 #4 CRITICAL: THE TARGET MUST BE CURRENT WHILE THE CONTINUATION RUNS.
                # `_CURRENT_TARGET[]` was left at whatever the caller had — `nothing` at top level,
                # since `_leader_pass` restores it before `_complete_resume!` is ever entered — so
                # `record_dependency!` hit its `tgt === nothing && return nothing` guard and SILENTLY
                # RECORDED NOTHING. Any tabled variant first reached inside a resumed continuation
                # suspended without a suspension: incomplete table, no error, on the DEFAULT path.
                # Upstream sets it before the continuation runs — `unify_dependency` does
                # `idg_set_current_wl(a0+3)` (the TargetWL, `pl-tabling.c:4199`), and
                # `delim(TargetSkeleton, Continuation, TargetWL, Delays)` (`boot/tabling.pl:836`)
                # makes the target explicit. Saved/restored because resumption nests.
                saved_tgt = _CURRENT_TARGET[]
                _CURRENT_TARGET[] = d.target
                resumed = try
                    resume_continuation(d.cont, a, space)
                finally
                    _CURRENT_TARGET[] = saved_tgt
                end
                for (at, bnd) in resumed
                    is_empty_atom(at) && continue
                    newa = subst(at, bnd)
                    tgt = d.target
                    _PARTIAL[tgt], ch = _merge_partial(get(_PARTIAL, tgt, Atom[]), Atom[newa], tgt)
                    # 🔴 #12: PROPAGATE THE AGGREGATED ANSWER, NOT THE RAW ONE. Under a `lattice`/`po`
                    # mode `ch` is true because the MERGED value changed, but `newa` is the incoming
                    # pre-aggregation answer — so consumers of a mode-directed table saw values that
                    # were never in it. Upstream passes `wkl_add_answer(wl, node)` a TRIE NODE, whose
                    # value is the aggregated one (`wkl_mode_add_answer`, `pl-tabling.c:3928`).
                    ch && wkl_add_answer!(worklist_for(tgt), _aggregated_form(_PARTIAL[tgt], newa, tgt))
                end
            end
        end
        did || break
        # ⚠️ A guard, not a bound: each `wkl_get_work!` SWAPS its pair, so work is finite unless new
        # answers keep arriving — and a program whose answer set is genuinely infinite does not
        # terminate in SWI either (verified). This catches a BROKEN INVARIANT (a swap that failed to
        # mark a pair combined would re-offer it forever) rather than an unbounded program, and says
        # so rather than looping silently.
        guard += 1
        guard > 1_000_000 && error("completion-by-resumption exceeded 1e6 work batches for " *
                                   "$(key) — the worklist invariant is broken (a pair is being " *
                                   "re-offered), not merely a large program")
    end
    true
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
                np = _leader_pass(m, typ, space)
                _PARTIAL[m], ch = _merge_partial(_PARTIAL[m], np, m)   # VALUE-based, not cardinality
                ch && (grew = true)
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
"""Solve the GENERAL goal, then answer the SPECIFIC one from its table — §7.11.1's abstracted arm.

`start_abstract_tabling`'s non-trivial branches all reduce to this: get the general table into a
COMPLETE state (`create_abstract_table` runs `run_leader` on the general skeleton; the `complete`
branch skips straight past it), then `'\$tbl_answer_update_dl'(Trie, Skeleton)` unifies its answers
into the specific call.

⚠️ THE GENERAL GOAL IS DRIVEN THROUGH `tabled_eval` ITSELF, not through a private path. That is what
makes the abstract table a real table — invalidated by the IDG, restrained by §7.11.3, readable by
§7.5 — rather than a cache that happens to look like one. It cannot recurse indefinitely: `gen` is
strictly more general than `red`, and `abstract_subgoal(gen)` is a fixpoint (abstracting an already
abstracted goal spends the same budget on strictly fewer compounds), so the second entry takes the
plain variant arm.
"""
function _abstract_tabled_eval(red::Atom, gen::Atom, typ::Atom, space::Space, b::Bindings, prev)
    genkey = _variant_rename(gen)
    # drive the general table to completion, discarding its answers — we want the TABLE, not this
    # call's projection of it. Fresh bindings so the caller's variables cannot be bound by the
    # general solve; `prev = nothing` because these results are not the ones being returned.
    tabled_eval(gen, typ, space, Bindings(), nothing)
    general = haskey(_ANSWER_TABLE, genkey) ? _ANSWER_TABLE[genkey] :
              (has_answer_trie(genkey) ? trie_answers(answer_trie_for(genkey)) : Atom[])
    # ⚠️ PROJECT ONTO `gen` FIRST, THEN SPECIALISE. A stored answer holds `Var("_v", i)` placeholders
    # keyed to ITS OWN table's ordered variables, so an answer that mentions the abstracted variable
    # mentions `_v_i`, NOT `_sa_i` — and substituting the abstraction binding would find nothing to
    # replace. `_project(general, gen)` restores gen's actual variables; `match_atoms(gen, red)` then
    # binds the `_sa` ones to the subterms they replaced AND red's own variables to themselves, so
    # the result is already in the caller's terms and needs no second projection.
    # the trie is passed so the specialisation can FILTER by recorded instance (roadmap 7.A), not
    # merely substitute — without it §7.11.1 over-approximates whenever an answer does not mention
    # the abstracted variable, which was the measured gap when this shipped.
    gtrie = has_answer_trie(genkey) ? answer_trie_for(genkey) : nothing
    _replay(abstract_answers(_project(general, gen), gen, red, gtrie), b, prev)
end

function tabled_eval(atom::Atom, typ::Atom, space::Space, b::Bindings, prev)
    red = _reduced_goal(atom, space, b)
    # ── §7.11.1 SUBGOAL ABSTRACTION — `start_abstract_tabling/3` (boot/tabling.pl:477-499) ────────
    # Upstream's dispatch, in its own words (`:469-472`): *"If the goal is not abstracted this is
    # simple variant tabling. If the goal is abstracted we must solve the more general goal and use
    # answers from the abstract table."* So the branch is on `size_abstract`'s TRIE_ABSTRACTED flag,
    # and the abstracted arm is the §7.5 subsumptive read against the general table.
    #
    # ⚠️ THE GUARD IS `is_most_general_term(Skeleton)`, NOT "was anything abstracted". Upstream tests
    # the SKELETON: an abstraction that happens to produce a maximally-general goal is indistinguish-
    # able from having asked the general goal directly, so it takes the plain variant arm and avoids
    # a pointless self-subsumption. `is_most_general_term` (§7.5) is that test — every argument a
    # DISTINCT unbound variable, distinctness included, since `p($x, $x)` is a real constraint.
    gen, abstracted = abstract_subgoal(red)
    if abstracted && !is_most_general_term(gen)
        return _abstract_tabled_eval(red, gen, typ, space, b, prev)
    end
    abstracted && (red = gen)          # abstracted TO the most general form ⇒ just table that
    key = _variant_rename(red)                                                  # red keeps the caller's vars;
    # §7.7: THE DEPENDENCY EDGE, AT THE CALL — not at the cache hit.
    # 🔴 FIRST ATTEMPT PUT THIS ON THE CACHE-HIT PATH AND IT WAS UNSOUND. Upstream adds the edge in
    # `tbl_variant_table` (`pl-tabling.c:4549-4560`), which looks up OR CREATES the table on EVERY
    # tabled call, before any answer exists. Recording only on a hit misses every dependency where
    # the caller COMPUTED the subgoal instead of reusing it — MEASURED on `fib 8`: the edge
    # fib(7)->fib(6) was absent, because fib(7) computed fib(6) first. A missed edge means a stale
    # table never gets invalidated, which is the one failure an IDG must not have.
    # `_GEN_STACK[end]` is `idg_current()`; an empty stack is a top-level query, depending on nothing.
    _IDG_RECORD[] && !isempty(_GEN_STACK) && idg_add_edge!(key, _GEN_STACK[end])
    if haskey(_ANSWER_TABLE, key)                                                # complete entry — but only replay if
        if get(_ANSWER_STAMP, key, (UInt(0), -1)) == (objectid(space), space.revision)
            # ── roadmap 1.0b, STEP 2: the READ PATH. 🟢 ON BY DEFAULT since 2026-08-17. ──────────
            # Step 1 MIRRORED completed answers into the trie; this makes the trie AUTHORITATIVE.
            # Flipped on whole-suite agreement (88/88), anti-vacuity (13/13 tables mirrored, answers
            # and ORDER identical) and a +0.1% allocation cost — see the flag block for the numbers.
            # `CORE_TABLING_TRIE_READ=0` still reaches the old store.
            #
            # 🔴 THE CLAIM THAT THE TWO STORES AGREE WAS CONDITIONAL UNTIL THE AUDIT. The trie dedups
            # by VARIANT and `_ANSWER_TABLE` came from `_PARTIAL`, which deduped by `==` — so
            # wherever an answer set contained variants the counts DIFFERED and this switch was not
            # answer-preserving. The trie was the upstream-correct one. Fixing `_merge_partial` to
            # use `variant_eq` (audit finding #1, itself a non-termination bug) is what made the
            # agreement real rather than a property of ground answer sets.
            #
            # ⚠️ ORDER IS PRESERVED, NOT INCIDENTAL. `trie_answers` returns INSERTION order via the
            # `seq` stamp, and the mirror inserts in `_PARTIAL` order — so the two paths yield the
            # same sequence, not merely the same set. Answer order is user-visible
            # (`Eval.jl` propagates store order into answer order), so a switch that quietly
            # reordered would be a behaviour change hiding inside a storage change.
            answers = _TRIE_READ[] && has_answer_trie(key) ?
                      trie_answers(answer_trie_for(key)) : _ANSWER_TABLE[key]
            return _replay(_project(answers, red), b, prev)                      #   FRESH ⇒ project+replay
        end
        delete!(_ANSWER_TABLE, key); delete!(_ANSWER_STAMP, key)                 #   STALE (space mutated) ⇒ evict + recompute
        drop_answer_trie!(key)                                                   #   …and the mirrored trie with it: a
                                                                                 #   surviving trie would let §7.5 answer
                                                                                 #   a subsumed call from evicted data.
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
        record_dependency!(key, b, prev, red)                                    #   §4.2: THIS is the shift
                                        # ↑ `(b, prev)` here IS the suspended remainder of the target's
                                        # worker — the same pair `_replay` resumes immediately below.
                                        # Recording is opt-in (`_DEPS_RECORD`), so this line is a no-op
                                        # on the default path until the step-4 rewire consumes it.
        return _replay(_project(get(_PARTIAL, key, Atom[]), red), b, prev)       #   answer from partials (suspend)
    end
    push!(_TABLE_INPROG, key); push!(_GEN_STACK, key)                            # become a GENERATOR
    _PARTIAL[key] = Atom[]; _COMPONENT[key] = key; delete!(_PARTIAL_READ, key)
    local ans::Vector{Atom} = Atom[]
    try
        _PARTIAL[key], _ = _merge_partial(Atom[], _leader_pass(key, typ, space), key)  # initial pass (may merge me up)
                                        # ↑ through the SAME merge point: a non-recursive head takes the
                                        # singleton fast path below and never enters a fixpoint round, so
                                        # a merge point wired only into the loops would silently skip it.
        if _scc_root(key) != key                                                 # I became a FOLLOWER ⇒
            return _replay(_project(_PARTIAL[key], red), b, prev)              #   ancestor root finishes me
        end
        comp() = Atom[g for g in _GEN_STACK if _scc_root(g) == key]            # I am the ROOT: my SCC members
        members = comp()
        if !(length(members) == 1 && !(key in _PARTIAL_READ))                    # singleton+no self-rec ⇒ 1 pass
            if any(m -> m in _SCC_NEG, members)                                  # WFS Stage B: recursion-thru-negation
                _wfs_complete!(members, typ, space, key)                         #   ⇒ alternating-fixpoint completion
            elseif !_complete_resume!(members, typ, space, key)                  # §1.0 step 4, if enabled
                while true                                                       # positive SCC: joint naive fixpoint
                    grew = false
                    for m in members
                        np = _leader_pass(m, typ, space)
                        _PARTIAL[m], ch = _merge_partial(_PARTIAL[m], np, m)  # VALUE-based, not cardinality
                        ch && (grew = true)
                    end
                    grew || break
                    members = comp()                                            # component may have grown
                end
            end
        end
        ans = _PARTIAL[key]
        _stamp = (objectid(space), space.revision)                              # stamp each completed answer set with
        for m in comp(); _ANSWER_TABLE[m] = _PARTIAL[m]; _ANSWER_STAMP[m] = _stamp; end  # the (space, revision) it holds for
        # ── roadmap 1.0b, STEP 1: MIRROR the completed answers into the ANSWER TRIE ──────────────
        # The trie is not yet the read path — `_ANSWER_TABLE` above still is — so this changes NO
        # behaviour. What it changes is REACHABILITY: `library(tables)` (`get_call`/`get_calls`/
        # `get_returns`), §7.5's `more_general_table`, and §7.3/§7.11.3's trie-seated inserts all
        # read `_ANSWER_TRIES`, and until now nothing populated it from a real evaluation. They were
        # correct and unreachable.
        #
        # 🔴 THE "THE TWO STORES AGREE" CLAIM ABOVE WAS CONDITIONAL UNTIL 2026-08-17, and the audit
        # caught it: the trie dedups by VARIANT, `_ANSWER_TABLE` came from `_PARTIAL` which deduped
        # by `==`, so wherever `_PARTIAL` held two variant-but-not-`==` answers the two stores held
        # DIFFERENT ANSWER COUNTS and the switch was not answer-preserving. The trie was the
        # upstream-correct one. Fixing `_merge_partial`/`_leader_pass` to dedup by `variant_eq`
        # (audit finding #1 — it was also a NON-TERMINATION bug) makes both stores use the same
        # identity, so the claim now holds unconditionally rather than only on ground answer sets.
        #
        # Mirroring before switching is deliberate: it makes the trie OBSERVABLE against the live
        # engine (the two must agree) without putting it on the answer path, which is the same
        # disable-to-prove order used for the resumption flip.
        for m in comp()
            t = answer_trie_for(m)
            for a in _PARTIAL[m]; trie_insert!(t, a); end
            set_table_status!(t, :complete)          # `$tbl_table_status` — §7.5 requires COMPLETE
        end
    finally
        if _scc_root(key) == key                                                # only the ROOT cleans its SCC
            done = Atom[g for g in _GEN_STACK if _scc_root(g) == key]
            filter!(g -> _scc_root(g) != key, _GEN_STACK)
            for m in done
                delete!(_TABLE_INPROG, m); delete!(_PARTIAL, m); delete!(_COMPONENT, m); delete!(_PARTIAL_READ, m)
                delete!(_SCC_NEG, m)
                # 🔴 #6: THE WORKLIST AND THE SUSPENSIONS MUST DIE WITH THE COMPLETION.
                # They did not, and re-completing the same key after a revision bump re-seeded into a
                # worklist still holding the PREVIOUS run's clusters — the old suspension cluster
                # landing adjacent to the new answer cluster, so `wkl_get_work!` resumed
                # continuations captured during an evaluation whose table had been EVICTED, against
                # the new space. Silently wrong answers, plus `_DEPS` growing without bound.
                # Upstream frees every worklist at `'$tbl_table_complete_all'`: `complete_worklist`
                # with `destroy = !wl->undefined && isEmptyBuffer(&wl->delays)` (`pl-tabling.c:4876`)
                # — and with no delay lists, which is our configuration, that is ALWAYS true.
                drop_worklist!(m); delete!(_DEPS, m)
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
