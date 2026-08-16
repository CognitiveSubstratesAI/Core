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
const SUITE_RAN    = String[]
const SUITE_FAILED = Tuple{String,String}[]
macro suite(path)
    quote
        local p = $(esc(path))
        push!(Main.SUITE_RAN, p)
        try
            $(esc(:include))(p)
        catch e
            push!(Main.SUITE_FAILED,
                  (p, first(replace(sprint(showerror, e), '\n' => ' '), 200)))
            printstyled("\n  ✗ SUITE FILE FAILED (continuing): ", p, "\n"; color = :red, bold = true)
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

module GSLTTests;         Main.@suite("test_gslt.jl");          end
module MeTTaILTests;      Main.@suite("test_mettail.jl");       end
module PatternMinerTests; Main.@suite("test_pattern_miner.jl"); end

# Structural lint — no lib/ definition shadows a Core-provided name (closes the
# duplication class from the 2026-06-10 primitive audit; clamp/xor/is-member consolidation).
Main.@suite("test_no_stdlib_shadow.jl")

# Structural lint (dual) — no lib/ op CALLS a dangling primitive: an op undefined in the live engine
# but present only in the dead top-level stdlib/ or an upstream stdlib name. Closes the silent
# ported-dangling class found 2026-06-30 in PLN (append/list_to_set/exclude-item).
Main.@suite("test_no_dangling_ops.jl")

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
    @test mork_unify("(f \$x)", "(f bar)") isa Dict                                   # match → bindings
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
        occursin(r"^\s*#", path) && return
        txt = join((occursin(r"^\s*#", l) ? "" : split(l, '#')[1]
                    for l in split(read(path, String), '\n')), '\n')
        dir = dirname(path)
        for m in eachmatch(r"(?:include|@suite)\(\s*\"([^\"]+\.jl)\"", txt)
            p = normpath(joinpath(dir, m.captures[1]))
            (occursin('$', p) || !startswith(p, normpath(testdir)) || p in reachable) && continue
            push!(reachable, p); isfile(p) && walk(p)
        end
    end
    walk(joinpath(testdir, "runtests.jl"))
    ran = Set(normpath(isabspath(p) ? p : joinpath(testdir, p)) for p in SUITE_RAN)
    # pln/*.jl arrive via the readdir loop, not a literal — they are in `ran`, never in `reachable`.
    missed = sort([p for p in reachable if !(p in ran) && isfile(p)])
    if !isempty(missed)
        printstyled("\n  ⚠️  REACHABLE BUT NEVER EXECUTED — the suite ran less than it registered:\n";
                    color = :red, bold = true)
        for p in missed; println("      ", relpath(p, testdir)); end
    end
    printstyled("\n  suite: $(length(SUITE_RAN)) files executed, $(length(SUITE_FAILED)) failed\n";
                color = isempty(SUITE_FAILED) ? :green : :red, bold = true)
    if !isempty(SUITE_FAILED) || !isempty(missed)
        for (p, m) in SUITE_FAILED
            printstyled("  ✗ "; color = :red, bold = true); println(p); println("      ", m)
        end
        error("Core suite: $(length(SUITE_FAILED)) file(s) failed" *
              (isempty(missed) ? "" : ", $(length(missed)) reachable file(s) never ran") * " — " *
              join(first.(SUITE_FAILED), ", "))
    end
end
