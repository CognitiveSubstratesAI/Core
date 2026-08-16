using Test
using MeTTaCore


# CoreSpace + MORK-substrate regression tests (extracted to test_corespace.jl when the legacy
# Eval_obsolete.jl tree-walker was retired; the modern engine's builtins are validated by
# StandardMeTTaTests / test_conformance / the LeaTTa oracle).
include("test_corespace.jl")
include("test_corespace_load.jl")   # load_metta!(::CoreSpace) — libs into the shared MORK trie
# Space constructor REGISTRY + capability ledger. Every declared capability is exercised, so the ledger
# fails when it drifts from the code — including the DECLINES (:mork evaluate=false IS compile-arrow 6).
include("test_spaces_registry.jl")
include("test_lib_policy.jl")        # policy constants stay MeTTa atoms; Julia asks, never copies
# UNWIRED until 2026-08-05: a conformance gate against upstream MetaMo helpers_test.metta that
# nothing ran — not runtests, not bin/health, not CI. Wired now; see NumpyOps.jl header.
include("test_numpyops.jl")
# The Int/Float boundary vs hyperon/LeaTTa/CeTTa. @test_broken lines are MEASURED divergences the
# vendored LeaTTa corpus structurally cannot cover — see docs/NUMERIC_SEAM_DIVERGENCES_2026-08-05.md
include("test_numeric_seam.jl")
include("test_multiset_semantics.jl")  # MeTTa surface = MULTISET, MORK trie = SET — both pinned

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
            include($_plnpath)
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
    include("standard/test_atoms.jl")
    include("standard/test_minimal.jl")
    # No instruction, at any arity, may crash the interpreter — the whole dispatch surface.
    include("standard/test_instr_arity.jl")
    # MeTTa Invariant 1 (sequential effects) at the FORM level — the lane-neutral partition that
    # stops a query being answered with a rule added after it. Lives above every lane on purpose.
    include("standard/test_program_regions.jl")
    include("standard/test_interpreter.jl")
    include("standard/test_tnot_wfs.jl")
    # The LIVE swipl differential. test_tnot_wfs.jl's header claims oracle verification but its
    # assertions are pinned literals and it never invokes swipl (measured 2026-08-06); this is the
    # file that actually runs the oracle. Skips LOUDLY if swipl is absent — never silently passes.
    include("standard/test_wfs_swipl_differential.jl")
    # SWI manual §7.1 (memoizing) + §7.2 (avoiding non-termination) — the two areas of §7 the
    # roadmap records us as HAVING. That claim previously rested on "fib returns 832040", which is
    # one number matching one expectation, not a comparison. This runs the manual's own examples
    # under swipl and asserts Core agrees value-for-value. Same two guards as the WFS differential:
    # loud skip if swipl is absent, and a positive control before any comparison.
    include("standard/test_tabling_swipl_differential.jl")
    # The compiler's coverage FLOOR. 27.5% of the corpus emits and every other gate is green,
    # because the rest silently falls back to the interpreter. This is the only thing that makes
    # that incompleteness cost something: the emitted count may not decrease.
    include("compiler/test_definition_name.jl")  # which function is a definition ABOUT — grouping identity
    include("compiler/test_call_staging.jl")
    include("compiler/test_emit_substitution.jl")
    include("compiler/test_emit_il.jl")          # MeTTa → MeTTa-IL: the Figure-2 compile arrow
    include("compiler/test_compile_lane.jl")     # compiler-PRIMARY execution, differential vs interpreter
    include("compiler/test_compile_lane_corpus.jl")  # the REAL corpora: 26 hyperon scripts + LeaTTa PROVED
    include("compiler/test_compile_lane_fuzz.jl")    # GENERATED programs — 26 scripts is a thin corpus
    include("compiler/test_il_roundtrip.jl")    # IL goes out as TEXT: which values survive parse(show(v))
    include("compiler/test_il_wire_roundtrip.jl")  # randomized parse(il_text(a))==a over the
    include("compiler/test_type_declarations.jl")  # `(: name type)` visible to the compiler —
    include("compiler/test_lib_differential.jl")   # Core/lib compiled-vs-interpreted answers —
                                                   # the gate the three corpora do not cover
                                                   # the arrow half of the call-vs-data predicate
                                                   # WIRE form, with the known-loss ledger
    include("compiler/test_eval_one_step.jl")   # metta.txt:96 — `eval` is ONE STEP; args are not reduced
    include("compiler/test_gslt_presentation.jl")  # G = (Σ,E,R): binders · freshness · premised rewrites
    include("compiler/test_gslt_parse.jl")         # the s-expr surface — presentations you can WRITE
    include("compiler/test_mettail_presentation.jl")  # MeTTa's own assembly language, presented as a GSLT
    include("compiler/test_gslt_reduce.jl")        # the ENGINE — a presentation that RUNS, so its R can be wrong out loud
    include("compiler/test_gslt_context.jl")       # closure under CONTEXT + PREMISED rules firing
    include("compiler/test_gslt_multicategory.jl")  # Def 5.1: interfaces · contexts · plugging
    include("compiler/test_coverage_ratchet.jl")
    include("standard/test_stdlib.jl")
    include("standard/test_space_arg_fail_closed.jl")   # space ops refuse a non-Space arg (no silent retarget)
    include("standard/test_conformance.jl")
    include("oracle/leatta/test_leatta_oracle.jl")   # differential vs the Lean-4 machine-proved MeTTa
    include("oracle/mettaref/test_mettaref_oracle.jl")  # MeTTapedia metta-ref: HOL4-specified M1
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
module GSLTTests;         include("test_gslt.jl");          end
module MeTTaILTests;      include("test_mettail.jl");       end
module PatternMinerTests; include("test_pattern_miner.jl"); end

# Structural lint — no lib/ definition shadows a Core-provided name (closes the
# duplication class from the 2026-06-10 primitive audit; clamp/xor/is-member consolidation).
include("test_no_stdlib_shadow.jl")

# Structural lint (dual) — no lib/ op CALLS a dangling primitive: an op undefined in the live engine
# but present only in the dead top-level stdlib/ or an upstream stdlib name. Closes the silent
# ported-dangling class found 2026-06-30 in PLN (append/list_to_set/exclude-item).
include("test_no_dangling_ops.jl")

# Type-system conformance — Core vs the metta-lang.dev types_basics tutorials,
# grounded in hyperon-experimental's b5_types_prelim/d4_type_prop scripts: gradual
# typing, function-application return-type inference, BadArgType checking, parametric
# types, get-metatype, types-as-propositions, let-destructure, Atom-typed match.
include("test_types.jl")

# Quantale foundation — lib/quantale/ (substrate-native port from PRIMUS_Core,
# corrected per quantale_spec: scalar=Q_prob, the real paired (n+,n-)=Q_PLN §4.4.1,
# fixed total-leaf-count program-cost). The commutative-quantale algebra PLN/MOSES/
# WILLIAM share (truth, variation, Occam weakness). Runs on Minimal — co-works with PLN.
include("test_quantale.jl")

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
include("test_subrep.jl")

# MorkSupercompiler tier-2 (`execute!`) integrated into Core's MORK path via `sc_execute!`.
include("test_supercompiler_core.jl")

# LangDef rule-table (CeTTa-adopted). BOTH files existed since the port and NEITHER was wired in —
# runtests.jl referenced "langdef" zero times, so the test whose entire job is verifying the WELD
# between the table and the interpreter has never run in CI. Wired 2026-07-28.
include("test_mork_native_rewrite.jl")   # native rewrite over trie-stored rules (byte paths, no MM2)
include("test_primitives_guards.jl")   # guard-clause fail-open regressions (operator precedence)
include("test_grounded_registry_differential.jl")  # MORK.GROUNDED_REGISTRY vs Eval.TOKEN_REGISTRY
include("test_langdef_pack.jl")
include("test_langdef_welding.jl")

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
