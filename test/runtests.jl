using Test
using MeTTaCore

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# EVERY TEST FILE RUNS, AND A FAILURE IS REPORTED AT THE END — never by aborting the suite.
#
# 🔴 THE BUG THIS FIXES, MEASURED 2026-08-16. A top-level `@testset` that fails THROWS a
# `TestSetException` at its own end, and that exception propagates out through `include`, aborting
# every remaining include. `test/compiler/test_eval_one_step.jl` has been failing (its ratchet is
# pinned at 0 and sits at 57 — deliberately, it is roadmap 0.2's unfinished half), so EVERYTHING
# REGISTERED AFTER IT NEVER RAN: ~20 files, including test_conformance.jl and BOTH the LeaTTa and
# mettaref oracles. Verified independently by a second session with a minimal repro.
# ⇒ "full suite EXIT 1 at the ratchet, everything else green" described a PREFIX of the suite.
# Every regression claim made against the suite before this commit covers only files up to that line.
#
# ⚠️ THE OBVIOUS FIX DOES NOT WORK. Wrapping this file in one outer `@testset` would make child
# failures record instead of throw — but this file declares `module StandardMeTTaTests`,
# `module GSLTTests`, … and `module` is rejected inside a testset scope ("syntax: module expression
# not at top level"). Also verified by repro, not assumed. Hence a per-include macro.
#
# 🔴 AND THE FAILURE MUST STILL BE LOUD. A helper that swallows and continues would trade
# "runs 60%, reports success" for "runs 100%, reports success" — strictly worse. So: record, continue,
# then FAIL LAST with every failed file NAMED, and re-raise so the exit code is real.
#
# `include` is `esc`aped so it resolves at the CALL SITE — inside `module StandardMeTTaTests` the file
# must load into THAT module, not into Main. Without the esc, macro hygiene resolves `include` in the
# macro's defining module and every wrapped file would silently land in the wrong namespace.
const SUITE_RAN = String[]
const SUITE_FAILED = Tuple{String, String}[]

# ── SHARDING: `CORE_SUITE_SHARD=1/2` runs every other file ────────────────────────────────────────
# Added 2026-08-17 because the suite outgrew the 10-minute window a wrapped runner can wait for, and
# the alternative — running it in the background and polling — is exactly what the hooks forbid, for
# good reasons. Sharding keeps each half inside the window while still executing EVERY file across
# the two runs.
#
# 🔴 A SHARDED RUN ANNOUNCES ITSELF LOUDLY, AND THAT IS THE WHOLE DESIGN. A partial run that prints
# the same summary as a full one is how "88 files, 0 failed" comes to mean nothing — the count is the
# thing people quote. `SUITE_SKIPPED` is reported alongside the failures and the header says SHARD,
# so a filtered run cannot be mistaken for a complete one. `[[feedback_measured_need_not_checklist]]`
const SUITE_SKIPPED = String[]
const SUITE_SHARD = let v = get(ENV, "CORE_SUITE_SHARD", "")
    if isempty(v)
        nothing
    else
        parts = split(v, '/')
        length(parts) == 2 || error("CORE_SUITE_SHARD must be i/n, got $(v)")
        (parse(Int, parts[1]), parse(Int, parts[2]))
    end
end
SUITE_SHARD === nothing || printstyled(
    "\n  ⚠️  SHARDED RUN: shard $(SUITE_SHARD[1]) of $(SUITE_SHARD[2]) — this is NOT the full suite\n";
    color=:yellow, bold=true)

macro suite(path)
    quote
        local p = $(esc(path))
        if Main.SUITE_SHARD !== nothing &&
            (length(Main.SUITE_RAN) + length(Main.SUITE_SKIPPED)) % Main.SUITE_SHARD[2] !=
           Main.SUITE_SHARD[1] - 1
            push!(Main.SUITE_SKIPPED, p)
        else
            push!(Main.SUITE_RAN, p)
            try
                $(esc(:include))(p)
            catch e
                push!(Main.SUITE_FAILED,
                    (p, first(replace(sprint(showerror, e), '\n' => ' '), 200)))
                printstyled(
                    "\n  ✗ SUITE FILE FAILED (continuing): ", p, "\n"; color=:red, bold=true
                )
            end
        end
    end
end


# CoreSpace + MORK-substrate regression tests (extracted to test_corespace.jl when the legacy
# Eval_obsolete.jl tree-walker was retired; the modern engine's builtins are validated by
# StandardMeTTaTests / test_conformance / the LeaTTa oracle).
# EVERY test file must be reachable from here, or exempted by name with a reason. "A test exists and
# does not run" cost work three times on 2026-08-16: test_tripwires.jl shipped unregistered, its
# registration then broke on a rename, and test/standard/test_unit.jl had NEVER run — six conformance
# gaps closed under a stale baseline with no attributable commit. First, so the suite says so early.
Main.@suite("test_suite_reachability.jl")
Main.@suite("test_corespace.jl")
Main.@suite("test_corespace_load.jl")   # load_metta!(::CoreSpace) — libs into the shared MORK trie
# Space constructor REGISTRY + capability ledger. Every declared capability is exercised, so the ledger
# fails when it drifts from the code — including the DECLINES (:mork evaluate=false IS compile-arrow 6).
Main.@suite("test_spaces_registry.jl")
Main.@suite("test_lib_policy.jl")        # policy constants stay MeTTa atoms; Julia asks, never copies
# UNWIRED until 2026-08-05: a conformance gate against upstream MetaMo helpers_test.metta that
# nothing ran — not runtests, not bin/health, not CI. Wired now; see NumpyOps.jl header.
Main.@suite("test_numpyops.jl")
# The Int/Float boundary vs hyperon/LeaTTa/CeTTa. @test_broken lines are MEASURED divergences the
# vendored LeaTTa corpus structurally cannot cover — see docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md
Main.@suite("test_numeric_seam.jl")
Main.@suite("test_multiset_semantics.jl")  # MeTTa surface = MULTISET, MORK trie = SET — both pinned

# PLN factor-graph suite (test/pln/) — demand-driven backward chaining on the lib/pln substrate:
# STV engine (DAG + arity-complete, all 8 rules), Layer-2 DTV (core + sweep + all rules), Layer-3
# (Fisher-weighted sensitivity + demand vectors, §5.4/§5.8), and §4.9 PLN↔ECAN coupling. Each file
# is wrapped in its own (gensym) module to isolate `using MeTTaCore.Eval` and per-file
# helpers (_derrs / const _FG / …) from each other and from Main. Auto-discovers pln/*.jl.
let _plndir = joinpath(@__DIR__, "pln")
    for _plnf in sort(readdir(_plndir))
        endswith(_plnf, ".jl") || continue
        _plnpath = joinpath(_plndir, _plnf)
        @eval module $(gensym("PLN"))
        Main.@suite($_plnpath)
        end
    end
end

# Standard MeTTa (typed atom model + matcher) — faithful port of hyperon/CeTTa
# representations, validated against docs/metta.md §Matching. Standalone subsystem
# (does not touch eval_metta/eval_nd) — the foundation for the minimal-MeTTa port.
# Wrapped in a module so the standard tests' short helpers (S/V/E/G = Sym/Var/Expression/Grounded)
# stay isolated from any global `S`/`V`/… that other top-level test files leak into Main
# ("cannot define function S; it already has a value").
module StandardMeTTaTests
using MeTTaCore, Test
Main.@suite("standard/test_atoms.jl")
Main.@suite("standard/test_minimal.jl")
# No instruction, at any arity, may crash the interpreter — the whole dispatch surface.
Main.@suite("standard/test_instr_arity.jl")
# MeTTa Invariant 1 (sequential effects) at the FORM level — the lane-neutral partition that
# stops a query being answered with a rule added after it. Lives above every lane on purpose.
Main.@suite("standard/test_program_regions.jl")
Main.@suite("standard/test_interpreter.jl")
Main.@suite("standard/test_tnot_wfs.jl")
# The LIVE swipl differential. test_tnot_wfs.jl's header claims oracle verification but its
# assertions are pinned literals and it never invokes swipl (measured 2026-08-06); this is the
# file that actually runs the oracle. Skips LOUDLY if swipl is absent — never silently passes.
Main.@suite("standard/test_wfs_swipl_differential.jl")
# SWI manual §7.1 (memoizing) + §7.2 (avoiding non-termination) — the two areas of §7 the
# roadmap records us as HAVING. That claim previously rested on "fib returns 832040", which is
# one number matching one expectation, not a comparison. This runs the manual's own examples
# under swipl and asserts Core agrees value-for-value. Same two guards as the WFS differential:
# loud skip if swipl is absent, and a positive control before any comparison.
Main.@suite("standard/test_tabling_swipl_differential.jl")
# Delimited control over the CPS frame chain — tabling roadmap §1.0 step 1. The primitives
# (`Continuation`/`capture_continuation`/`resume_continuation`/`Dependency`) that replace
# `_leader_pass` RECOMPUTATION with dependency-driven RESUMPTION. NOT yet wired into
# `tabled_eval`: this gates the primitives standalone, so a green run means capture-and-resume is
# sound on this machine, not that tabling uses it.
Main.@suite("standard/test_delimited_control.jl")
# CONTINUATION SAFETY — the invariant that makes §1.0's capture/resume sound: every `Frame.ret`
# closure is FRAME-AGNOSTIC (takes `self` as a parameter, closes over immutables only). A closure
# capturing an outer frame breaks it while adding ZERO Frame field writes, and
# test_delimited_control.jl would pass it — that gates BEHAVIOUR on one run, this gates the
# invariant. Includes a mutation battery proving the checker sees the defect class.
Main.@suite("standard/test_frame_agnostic_ret.jl")
# Mode-directed tabling / answer subsumption — SWI §7.3, ported into `src/standard/tabling/`
# (the subfolder mirrors swipl-devel's own section boundaries). Differentialled against live
# swipl on lattice(min/max/sum) and po/2. Compares AGGREGATION SEMANTICS, not an end-to-end
# tabled query — the merge point is §1.0's `tabled_eval` rewire and is not landed yet.
Main.@suite("standard/tabling/test_aggregation.jl")
# The COMPLETION MERGE POINT — `Tabling._merge_partial` and the growth signal it reports. The
# rest of the gate set CANNOT see this change: with no modes declared the value-based signal is
# behaviour-preserving by construction, so health/corpus/differentials stay green either way.
# This pins the case where cardinality and value DISAGREE, and the sum-under-recomputation hazard
# that makes non-idempotent §7.3 aggregates unsound until the §1.0 rewire lands.
Main.@suite("standard/tabling/test_completion_merge.jl")
# SWI §7.11.3 max_answers — the one restraint that ports to a Dict today (no answer trie needed:
# `bounded_rationality` does not TRUNCATE, it adds one maximally-general answer subsuming what the
# bound stopped computing). Landed in `tabling/Tripwires.jl` — named for upstream's own section
# header (boot/tabling.pl:2263), like every file in that subfolder.
Main.@suite("standard/tabling/test_tripwires.jl")
# The per-table WORKLIST — roadmap §1.0 step 3. ONE invariant: an answer is LEFT of a dependency
# iff they have not been combined, so combining is recorded by SWAPPING the pair and there is no
# "done" flag anywhere. NOT wired: the completion loop still recomputes via `_leader_pass`.
Main.@suite("standard/tabling/test_worklist.jl")
# The ANSWER TRIE — roadmap §1.0 step 4 (structure half). Structural duplicate detection and
# VARIANT identity, which a Dict{Atom,Vector{Atom}} cannot give: two answers equal up to variable
# renaming reach ONE node. Prerequisite for §7.11.1/2 abstraction and the insertion-time mode
# merge. NOT wired: tabled_eval still stores into _ANSWER_TABLE.
Main.@suite("standard/tabling/test_answer_trie.jl")
# Completion by RESUMPTION vs RECOMPUTATION — §1.0 step 4 (loop half). `_complete_resume!` is
# OFF by default and this file is why it stays off: the oracle for a rewrite of the engine core
# is agreement with the engine it replaces. Every case asserts whether it ACTUALLY exercised
# resumption before comparing — most programs do not (fib is a plain memo, no suspension).
Main.@suite("standard/tabling/test_completion_resume.jl")
# SWI `library(tables)`, the PORTABLE half — §7.12 inspection over the answer trie. The three
# predicates NOT here (get_residual/2, get_returns_and_dls/3, get_returns_and_tvs/3) need delay
# lists, which is a boundary visible in the C primitive list rather than a judgement call.
Main.@suite("standard/tabling/test_inspect.jl")
# SWI §7.5 subsumptive tabling — a second LOOKUP MODE over the same tables: the more specific
# call is answered from the more general table. NOT wired into tabled_eval; gates the lookup.
Main.@suite("standard/tabling/test_subsumptive.jl")
# ONE declaration surface — SWI's table_options/3 (roadmap 0b, the config principle). Gates the
# three states an option can be in: HONOURED, REFUSED-with-a-reason, and UNKNOWN (domain_error).
Main.@suite("standard/tabling/test_options.jl")
# SWI §7.7 — the incremental dependency graph. Replaces the revision stamp's all-or-nothing
# invalidation with per-table. Gates the GRAPH (edges, direction, transitive propagation,
# teardown); the RE-EVALUATION half of §7.7 is not built.
Main.@suite("standard/tabling/test_idg.jl")
# SWI §7.8 monotonic — PROPAGATE FORWARD on assert, INVALIDATE on retract. The propagation
# vehicle is §1.0's Dependency + resume_continuation, so 7.8 needed the assert/retract branch
# and the eager/lazy split rather than a new engine.
Main.@suite("standard/tabling/test_monotonic.jl")
# SWI §7.11.1 subgoal_abstract — the OTHER restraint: §7.11.3 bounds how big one table gets, this
# bounds how MANY tables there are. Upstream calls it "a merge between variant and subsumptive
# tabling", which is why it rides on §7.5 and NOT on the answer trie — the refusal reason that
# kept it unbuilt was simply wrong. WIRED into `tabled_eval`. Pins that the budget is a SIZE
# limit, not a depth limit (they differ on branching terms), and pins BOTH sides of the
# precision boundary: exact when an answer mentions the abstracted variable, over-approximating
# when it does not — because a MeTTa answer is a VALUE, not a substitution over the skeleton.
Main.@suite("standard/tabling/test_abstract.jl")
# SWI §7.7's RE-EVALUATION half — the IDG's second stage. The graph (edges, falsecount,
# transitive invalidation) shipped earlier; this is `prepare_reeval!` / `reeval_complete!` /
# `reset_reevaluation!` plus the DECREMENT walk that re-validates dependants.
# 🔴 The verdict is a CONTENT DIGEST, not upstream's `answer_count == value_count`. Cardinality
# is sound in Prolog because an answer IS its substitution; here every answer has a payload, and
# TWO measured mutation classes change content at constant count — `trie_insert_moded!` replaces
# a moded aggregate in place, and `merge_bottom_into!` widens a WFS bottom's condition. SWI
# documents the same insufficiency and patches it only in the monotonic path.
# ⚠️ The hook stays INERT until something calls `idg_changed!` on a space mutation, which is the
# dynamic-predicate edge and is still unbuilt — this lands the re-evaluation half, NOT
# incremental tabling end to end. The tests supply the trigger directly.
Main.@suite("standard/tabling/test_reeval.jl")
# 🔴 SCENARIOS PORTED FROM UPSTREAM'S OWN SUITE, not written by us. Every other tabling test here
# was authored from the same reading of `pl-tabling.c` that produced the code it grades — a
# closed loop in which a misreading becomes both the implementation and the assertion.
# `swipl-devel/tests/tabling/test_reeval.pl` supplies the claims; all 18 upstream tabling files
# (165 tests) pass against the live binary — `workflows/swipl_tabling_oracle.sh`.
Main.@suite("standard/tabling/upstream/test_upstream_reeval.jl")
# XSB's own WFS conformance corpus — 72 programs each shipping a machine-readable gold row
# (TRUE set / UNDEFINED set; absent ⇒ false), validated 72-agree-0-differ against live swipl by
# `test/standard/tabling/upstream/verify_corpus.sh`. 7 translated so far, spanning all three
# verdicts. This is the defect class `test_delays.jl` CANNOT see: that file tests the delay
# ALGEBRA, and a perfect algebra over a broken fixpoint passes every assertion in it.
Main.@suite("standard/tabling/upstream/test_xsb_wfs_corpus.jl")
# The GROUNDED enumeration: which `Grounded{T}` payloads the PARSER can produce (three) versus
# which the engine constructs (five more), and that `Grounded{Bindings}` never reaches an answer.
# A gate rather than prose in `docs/src/language/grammar.md`, because enumerations in prose go
# stale on the first addition.
Main.@suite("standard/test_grounded_payloads.jl")
# How a WFS bottom travels through the INTERPRETER: constructors and control forms must not
# absorb one (a rule that ignores its argument must still fire), while strict ops must, and
# `unify` must not launder ⊥ into its `else` branch. Both properties were wrong until
# 2026-08-18 and cost four XSB gold programs.
Main.@suite("standard/test_wfs_propagation.jl")
# §7.11.2 is WIRED: `answer_abstract(N)` fires at the answer-PRODUCTION site, not the completion
# mirror — the mirror cannot work, because the programs this restraint exists for never complete.
Main.@suite("standard/tabling/test_answer_restraint_wiring.jl")
# SWI §7.6 delay lists — conditional answers, roadmap 7.A-7.D. We already computed the WFS third
# truth value (the alternating fixpoint gives the same model); what was missing is the REASON.
# 🔴 The adaptation: the condition RIDES ON THE VALUE. SWI keeps it in a trail-scoped thread-global
# and scrapes it at insertion, correct there because the engine runs ONE derivation and the trail
# erases abandoned ones; we map over a COLLECTION, so a literal port leaks value #1's condition
# onto value #2 with no trail to unwind it. Pins the DNF algebra (empty is the UNIT, not the
# zero), that 7.B's third delay kind exists with NO producer yet, and end-to-end that a real
# paradox yields a residual naming the goal it is stuck on — not the vacuous `True`.
Main.@suite("standard/tabling/test_delays.jl")
# The compiler's coverage FLOOR. 27.5% of the corpus emits and every other gate is green,
# because the rest silently falls back to the interpreter. This is the only thing that makes
# that incompleteness cost something: the emitted count may not decrease.
Main.@suite("compiler/test_definition_name.jl")  # which function is a definition ABOUT — grouping identity
Main.@suite("compiler/test_call_staging.jl")
Main.@suite("compiler/test_emit_substitution.jl")
Main.@suite("compiler/test_emit_il.jl")          # MeTTa → MeTTa-IL: the Figure-2 compile arrow
Main.@suite("compiler/test_compile_lane.jl")     # compiler-PRIMARY execution, differential vs interpreter
Main.@suite("compiler/test_compile_lane_corpus.jl")  # the REAL corpora: 26 hyperon scripts + LeaTTa PROVED
Main.@suite("compiler/test_compile_lane_fuzz.jl")    # GENERATED programs — 26 scripts is a thin corpus
Main.@suite("compiler/test_il_roundtrip.jl")    # IL goes out as TEXT: which values survive parse(show(v))
Main.@suite("compiler/test_il_wire_roundtrip.jl")  # randomized parse(il_text(a))==a over the
Main.@suite("compiler/test_type_declarations.jl")  # `(: name type)` visible to the compiler —
Main.@suite("compiler/test_lib_differential.jl")   # Core/lib compiled-vs-interpreted answers —
# the gate the three corpora do not cover
# the arrow half of the call-vs-data predicate
# WIRE form, with the known-loss ledger
Main.@suite("compiler/test_eval_one_step.jl")   # metta.txt:96 — `eval` is ONE STEP; args are not reduced
Main.@suite("compiler/test_gslt_presentation.jl")  # G = (Σ,E,R): binders · freshness · premised rewrites
Main.@suite("compiler/test_gslt_parse.jl")         # the s-expr surface — presentations you can WRITE
Main.@suite("compiler/test_mettail_presentation.jl")  # MeTTa's own assembly language, presented as a GSLT
Main.@suite("compiler/test_gslt_reduce.jl")        # the ENGINE — a presentation that RUNS, so its R can be wrong out loud
Main.@suite("compiler/test_gslt_context.jl")       # closure under CONTEXT + PREMISED rules firing
Main.@suite("compiler/test_gslt_multicategory.jl")  # Def 5.1: interfaces · contexts · plugging
# Def 2.2: bisimilarity over the UNLABELLED one-step relation + the bisimilarity-preserving term
# map. A DIFFERENT, weaker morphism than 5.1 — no labels, no contexts, no multicategory — and
# buildable from `GPresentation` + `reducts`, which 5.1 is not.
Main.@suite("compiler/test_gslt_bisimulation.jl")
Main.@suite("compiler/test_coverage_ratchet.jl")
Main.@suite("standard/test_stdlib.jl")
Main.@suite("standard/test_space_arg_fail_closed.jl")   # space ops refuse a non-Space arg (no silent retarget)
Main.@suite("standard/test_conformance.jl")
# UNIT conformance — hyperon's OWN stdlib `#[test]` corpus over ten `unit/*.metta` modules, with a
# per-module expected-failure baseline. ⚠️ REGISTERED 2026-08-16 AFTER NEVER HAVING RUN: adopted at
# `0c51e87`, then touched only by mechanical renames, so `core.metta` sat at baseline 8 while only 2
# still failed. Wrapped in its own module because it defines generic names (`SM`, `BASELINE`,
# `UNIT_DIR`) that would otherwise land in StandardMeTTaTests' namespace — the same reason the
# pln/ loop wraps each of its files.
# (test_unit.jl is registered at TOP LEVEL below, not here — see the note there.)
Main.@suite("oracle/leatta/test_leatta_oracle.jl")   # differential vs the Lean-4 machine-proved MeTTa
Main.@suite("oracle/mettaref/test_mettaref_oracle.jl")  # MeTTapedia metta-ref: HOL4-specified M1
# goldens + a nondeterminism/bag corpus.
# VENDORED, no MeTTapedia/Lean/HOL4 toolchain
# at test time — .metta files + .expected only.
end

# MM2 dual-lane router (src/standard/MM2Router.jl) — module-wrapped so its top-level `MC`/`facts`/`prog`
# consts stay isolated from Main (same discipline as StandardMeTTaTests). Covers `(=)→exec` lowering in
# BOTH modes (relational forward-closure + reduction delete-redex), partition/route, and bisimulation.

# MM2 dual-lane SURFACE — the remaining front-ends over the same MM2/MORK substrate, each module-wrapped so
# their top-level `MC`/`facts` consts stay isolated (same discipline as MM2RouterTests). Together with the
# router suite these cover every caller of the mm2_expr_args / mm2_split_forms parsers: the unified `mc_run`
# dispatch, the GSLT theory algebra, the MeTTa-IL rewrite lane, and the frequent-pattern miner. (Previously
# orphaned — present in test/ but never included here, so drift went unnoticed; wired in 2026-07-02.)
# UNIT conformance — hyperon's OWN stdlib `#[test]` corpus over ten `unit/*.metta` modules, with a
# per-module expected-failure baseline. ⚠️ REGISTERED 2026-08-16 AFTER NEVER HAVING RUN: adopted at
# `0c51e87`, then touched only by mechanical renames, so `core.metta` sat at baseline 8 while only 2
# still failed. Wrapped in its own module because it defines generic names (`SM`, `BASELINE`,
# `UNIT_DIR`) that would collide inside StandardMeTTaTests.
# 🔴 AT TOP LEVEL, NOT NESTED INSIDE StandardMeTTaTests — measured: a gensym submodule created inside
# another module resolves `using MeTTaCore.Eval` RELATIVE to its parent and dies with
# "UndefVarError: `MeTTaCore` not defined in Main.StandardMeTTaTests.var\"##UnitConformance\"".
# The pln/ loop is at top level for the same reason; that is why it works.
@eval module $(gensym("UnitConformance"))
# `using MeTTaCore, Test` is REQUIRED, not decoration: test_unit.jl does `const SM = MeTTaCore.Eval`,
# and its own `using MeTTaCore.Eval` binds `Eval` WITHOUT binding `MeTTaCore`. StandardMeTTaTests
# carries the same line at its head, which is why every file in it resolves.
using MeTTaCore, Test
Main.@suite(joinpath(@__DIR__, "standard", "test_unit.jl"))
end

module GSLTTests
Main.@suite("test_gslt.jl")
end
module MeTTaILTests
Main.@suite("test_mettail.jl")
end
module PatternMinerTests
Main.@suite("test_pattern_miner.jl")
end

# Structural lint — no lib/ definition shadows a Core-provided name (closes the
# duplication class from the 2026-06-10 primitive audit; clamp/xor/is-member consolidation).
Main.@suite("test_no_stdlib_shadow.jl")

# Structural lint (dual) — no lib/ op CALLS a dangling primitive: an op undefined in the live engine
# but present only in the dead top-level stdlib/ or an upstream stdlib name. Closes the silent
# ported-dangling class found 2026-06-30 in PLN (append/list_to_set/exclude-item).
Main.@suite("test_no_dangling_ops.jl")

# Structural lint (third) — no unescaped `$` in a docstring. A `$name` in a Julia string is
# INTERPOLATION, so in a docstring it fails PRECOMPILE with UndefVarError before any test runs. It
# recurred four times on 2026-08-16/17 because this port quotes exactly the two things that trip it:
# SWI's `$tbl_*` C predicates and MeTTa's `$variables`. Registered HERE as well as in bin/health,
# matching the other two structural lints — the reachability gate caught the omission.
Main.@suite("test_no_docstring_interpolation.jl")

# Type-system conformance — Core vs the metta-lang.dev types_basics tutorials,
# grounded in hyperon-experimental's b5_types_prelim/d4_type_prop scripts: gradual
# typing, function-application return-type inference, BadArgType checking, parametric
# types, get-metatype, types-as-propositions, let-destructure, Atom-typed match.
Main.@suite("test_types.jl")

# Quantale foundation — lib/quantale/ (substrate-native port from PRIMUS_Core,
# corrected per quantale_spec: scalar=Q_prob, the real paired (n+,n-)=Q_PLN §4.4.1,
# fixed total-leaf-count program-cost). The commutative-quantale algebra PLN/MOSES/
# WILLIAM share (truth, variation, Occam weakness). Runs on Minimal — co-works with PLN.
Main.@suite("test_quantale.jl")

# SubRep (lib/subrep/{cds,pds,store}.metta) — the §4 goal-loop option-admission
# stage. CDS: uniform improvement over the whole motive cone (simplex/box/vertex).
# PDS: weaker — ε budget (PDS-ε) or componentwise Pareto over a cover (§2.3).
# store: atom-native certificate storage + zero-shot reuse under motive shift
# (whitepaper §5.9 "neurosymbolically native"; iCog Quarter Plan Phase 4). attention:
# Full SubRep stack (lib/subrep/): CDS/PDS gates + certificates + atom storage/zero-shot
# (§2.2/§2.3/§5.9) · anytime gate + conformal certs (§2.4/§2.3.7) · cross-paradigm
# generators (§4) · MDN cone consumption / end-to-end (§2.4) · conservative attention
# (§10) · categorical backbone (§8) · EASA chart gluing (§9) · Waveformer budget-weighted
# attention (§11) · §7 theorem checks (join-safety, monotone persistence). Minimal-native.
# (Neural MDN + admission-coupling + CVaR + PC-native gate live in FabricPC examples/subrep_mdn.jl.)
Main.@suite("test_subrep.jl")

# MorkSupercompiler tier-2 (`execute!`) integrated into Core's MORK path via `sc_execute!`.
Main.@suite("test_supercompiler_core.jl")

# LangDef rule-table (CeTTa-adopted). BOTH files existed since the port and NEITHER was wired in —
# runtests.jl referenced "langdef" zero times, so the test whose entire job is verifying the WELD
# between the table and the interpreter has never run in CI. Wired 2026-07-28.
Main.@suite("test_mork_native_rewrite.jl")   # native rewrite over trie-stored rules (byte paths, no MM2)
Main.@suite("test_primitives_guards.jl")   # guard-clause fail-open regressions (operator precedence)
Main.@suite("test_grounded_registry_differential.jl")  # MORK.GROUNDED_REGISTRY vs Eval.TOKEN_REGISTRY
Main.@suite("test_langdef_pack.jl")
Main.@suite("test_langdef_welding.jl")

@testset "MorkBridge (E1.0) — native unify + shared-var rule rewrite" begin
    # E1.0 foundation: rewrite via MORK's verified engine (expr_unify + expr_apply), not Core's
    # Julia-structural _unify / string-replace. The crossed-variable case is the one that breaks
    # naive separate-parse — see the CRUX note in src/eval/MorkBridge.jl.
    @test mork_rule_rewrite("(= (f \$x) (g \$x))", "(f bar)") == "(g bar)"
    @test mork_rule_rewrite("(= (p \$x \$y) (q \$y \$x))", "(p a b)") == "(q b a)"   # crossed vars
    @test mork_rule_rewrite("(= (dup \$x) (\$x \$x))", "(dup k)") == "(k k)"          # template duplication
    @test mork_rule_rewrite("(= (p \$x \$y) (q \$y \$x))", "(z a b)") === nothing     # head mismatch
    @test mork_rule_rewrite("(foo bar)", "(foo bar)") === nothing                     # not a (= ..) rule
    # 🔴 AbstractDict, NOT Dict — and this test was the LAST carrier of a defect the SOURCE
    # already fixed on 2026-08-20. `expr_unify` returns MORK's `Bindings`, a direct-indexed slab
    # that is `<: AbstractDict` but NOT `<: Dict`. MorkBridge.jl stopped testing the success
    # representation then ("the failure type is the stable half of the contract"); this assertion
    # kept testing it, and went red the moment the source became right.
    _b = mork_unify("(f \$x)", "(f bar)")                                             # match → bindings
    @test _b isa AbstractDict && !isempty(_b)
    @test mork_unify("(f \$x)", "(h bar)") === nothing                                # no match
end

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# FAIL LAST, FAIL LOUD, NAME THE FILES — and assert the suite actually RAN what it can reach.
#
# `@suite` records failures instead of throwing, so every file gets to run. That is only an
# improvement if the suite still goes RED at the end: swallowing failures would trade "runs 60% and
# reports success" for "runs 100% and reports success", which is strictly worse. The `error` below is
# what makes the exit code real.
#
# THE DYNAMIC HALF OF THE REACHABILITY GATE. `test_suite_reachability.jl` runs FIRST and checks the
# include GRAPH statically — it catches an unregistered file, but it could not have caught the abort,
# because the include existed and simply never executed. This check runs LAST and compares files
# ACTUALLY EXECUTED against files reachable, which is the check that would have caught it all day.
let testdir = @__DIR__
    reachable = Set{String}()
    function walk(path)
        occursin(r"^\s*#", path) && return nothing
        txt = join(
            (
                occursin(r"^\s*#", l) ? "" : split(l, '#')[1]
                for l in split(read(path, String), '\n')
            ), '\n')
        dir = dirname(path)
        for m in eachmatch(r"(?:include|@suite)\(\s*\"([^\"]+\.jl)\"", txt)
            p = normpath(joinpath(dir, m.captures[1]))
            (occursin('$', p) || !startswith(p, normpath(testdir)) || p in reachable) &&
                continue
            push!(reachable, p)
            isfile(p) && walk(p)
        end
    end
    walk(joinpath(testdir, "runtests.jl"))
    # ⚠️ A SHARDED-OUT FILE IS STILL REACHABLE. This gate asks "is every test file wired into
    # runtests.jl", which `CORE_SUITE_SHARD` does not change — the file is registered, this run simply
    # was not its turn. Counting only SUITE_RAN would make every sharded lane fail the gate and train
    # a reader to ignore it, which is worse than not having it. The SKIPPED count is reported
    # separately and loudly, so nothing is hidden by folding the two together here.
    ran = Set(
        normpath(isabspath(p) ? p : joinpath(testdir, p))
        for p in Iterators.flatten((SUITE_RAN, SUITE_SKIPPED))
    )
    # pln/*.jl arrive via the readdir loop, not a literal — they are in `ran`, never in `reachable`.
    missed = sort([p for p in reachable if !(p in ran) && isfile(p)])
    if !isempty(missed)
        printstyled(
            "\n  ⚠️  REACHABLE BUT NEVER EXECUTED — the suite ran less than it registered:\n";
            color=:red, bold=true)
        for p in missed
            println("      ", relpath(p, testdir))
        end
    end
    isempty(SUITE_SKIPPED) || printstyled(
        "\n  ⚠️  SHARDED: $(length(SUITE_SKIPPED)) files SKIPPED — this run does NOT cover the suite\n";
        color=:yellow, bold=true)
    printstyled(
        "\n  suite: $(length(SUITE_RAN)) files executed, $(length(SUITE_FAILED)) failed\n";
        color=isempty(SUITE_FAILED) ? :green : :red, bold=true)
    if !isempty(SUITE_FAILED) || !isempty(missed)
        for (p, m) in SUITE_FAILED
            printstyled("  ✗ "; color=:red, bold=true)
            println(p)
            println("      ", m)
        end
        error(
            "Core suite: $(length(SUITE_FAILED)) file(s) failed" *
            (isempty(missed) ? "" : ", $(length(missed)) reachable file(s) never ran") *
            " — " *
            join(first.(SUITE_FAILED), ", ")
        )
    end
end
