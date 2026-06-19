"""
MeTTaCore — Standalone MeTTa substrate built directly on MORK.

Zero dependency on PRIMUS_Core or PRIMUS_Metagraph.
Redesigned pure-Julia MeTTa engine using MORK.Space as atom store.

Architecture:
  MORK.Space  (byte-trie, PathMap substrate)
      ↓
  CoreSpace   (AbstractAtomSpace wrapper — match, add, remove, rules)
      ↓
  Parser      (S-expression parser: string → Julia values)
      ↓
  Primitives  (grounded Julia functions: arithmetic, math, I/O)
  AtomOps     (grounded atom/list ops: cons/car/cdr/foldl/map/filter)
      ↓
  Eval        (MeTTa interpreter: rule rewriting + special forms)
      ↓
  stdlib/     (pure .metta files: if, let, list ops, types — hot-reloadable)

Design principles (per MeTTa spec + CeTTa/Mettatron/hyperon cross-check):
  - Only operations that MUST control evaluation order are grounded in Julia
  - Everything expressible as (= pattern body) lives in stdlib/*.metta
  - MeTTa atoms are S-expression strings ↔ MORK byte-paths (no UUID atoms)
  - stdlib files are loaded at init — no recompile needed to change them
"""
module MeTTaCore

using MORK
using MORK: Space, new_space,
            space_add_all_sexpr!, space_dump_all_sexpr,
            space_val_count, space_metta_calculus!, space_metta_calculus_at!,
            sexpr_to_expr, expr_serialize, read_zipper,
            space_query_multi, ExecError,
            register_grounded!, is_grounded, GROUNDED_REGISTRY,
            # .act + multi-source machinery (Stage 1 CoreSpaceActIO)
            asource_new, source_factor, ACT_PATH
using MorkSupercompiler: plan!, execute!, SCOptions, SC_DEFAULTS, SCResult
using PathMap: PathMap, UnitVal, UNIT_VAL,
               read_zipper_at_path, zipper_to_next_val!, zipper_path,
               set_val_at!, remove_val_at!,
               act_from_zipper, act_save, ArenaCompactTree

# WILLIAM (Adaptive Compression and Discovery Service) — Pattern B1 Pkg dep.
# Its `__init__` registers the `WILLIAM.mine-patterns` grounded primitive into
# MORK.GROUNDED_REGISTRY at module load; the `(library william)` resolver
# entry is installed below after _PACKAGE_REGISTRY is in scope (Eval.jl).
using AdaptiveCompression

include("space/CoreSpace.jl")
include("space/CoreSpaceActIO.jl")   # Stage 1 .act lifecycle (snapshot / load / open_node! / close_node!)
include("parser/Parser.jl")
include("primitives/Primitives.jl")
include("primitives/AtomOps.jl")
include("eval/MorkBridge.jl")   # E1.0: native MORK unify+apply bridge (foundation) — NOT legacy
# ⚠️ OBSOLETE — legacy interpreters being RETIRED (docs/ARCHITECTURE_TARGET.md: the Interpreter supersedes
# eval_metta AND eval_nd). Retained ONLY because ~13 full-Eval test scripts (test_ecan/_dual, test_types,
# test_metamo, test_actpc_chem, test_william, test_moses full-Eval path, …) have not yet migrated to the
# Interpreter harness. DO NOT build new code on eval_metta / run_metta / eval_nd. Delete after migration.
include("eval/Eval_obsolete.jl")     # eval_metta / run_metta / run_file (legacy tree-walker)
include("eval/EvalND_obsolete.jl")   # eval_nd / eval_nd_results (legacy OutcomeSet experiment)

# Standard-MeTTa Interpreter (faithful hyperon interpreter.rs port of the minimal-MeTTa instruction set).
# Fully SELF-CONTAINED — it does NOT touch eval_metta/eval_nd and shares no types with the MORK-backed
# engine above; it lives here only so its ~28s one-time compile is BAKED INTO the precompile cache
# (`MeTTaCore.Interpreter`) instead of being recompiled on every fresh `include`. Accessed as `MeTTaCore.Interpreter`.
include("standard/Interpreter.jl")

# Dual-lane program routing (CeTTa-adopted, PRIMUS-native). In MAIN scope (uses CoreSpace + the
# MORK-backed engine), NOT inside the self-contained `Interpreter` submodule above.
include("standard/MM2Router.jl")
include("standard/LangDefPack.jl")   # reflectable HE small-step rule-table (CeTTa-adopted)
include("standard/MeTTaIL.jl")       # MeTTa-IL lane (F1R3FLY layered track): MeTTa-IL → MM2 → MORK
include("standard/GSLT.jl")          # GSLT theory front-end: theory algebra (extends/union/replace) → MeTTa-IL

# Point `(library william)` resolution at the AdaptiveCompression package dir.
# `_resolve_library` already has step-2 fallback to `_PACKAGE_REGISTRY[name]`;
# we just need to install the entry.  The actual `.metta` lives at
# `pkgdir(AdaptiveCompression)/william.metta` (matches AdaptiveCompression's
# repo layout: william.metta at package root, examples/ alongside).
_PACKAGE_REGISTRY["william"] = pkgdir(AdaptiveCompression)

# stdlib directory relative to this package root
const _STDLIB_DIR = joinpath(@__DIR__, "..", "stdlib")

"""
    load_stdlib!(space::CoreSpace)

Load all stdlib/*.metta files into the given space.
Pure MeTTa rules — hot-reloadable, introspectable, no recompile needed.
"""
function load_stdlib!(space::CoreSpace)
    # Load in dependency order: types first, then core (uses types), then list/math
    for fname in ["types.metta", "core.metta", "list.metta", "math.metta"]
        path = joinpath(_STDLIB_DIR, fname)
        isfile(path) || continue
        try
            src = read(path, String)
            # CRITICAL: use Core's parser (parse_metta + core_add!), NOT
            # MORK.space_add_all_sexpr!. MORK's parser encodes $x as anonymous
            # NewVar bytes (de Bruijn), losing variable names on serialisation.
            # Core's parser stores variables as __var_x (named ground symbols)
            # which survive the MORK byte-trie round-trip correctly.
            exprs = parse_metta(src)
            for expr in exprs
                # Skip execution directives (!) in stdlib files
                expr isa Vector && !isempty(expr) && expr[1] === :! && continue
                core_add!(space, expr)
            end
        catch e
            @warn "load_stdlib!: failed to load $fname" exception=e
        end
    end
    space
end

"""
    register_all_primitives!(eval_fn=nothing)

Register all grounded primitives into MORK.GROUNDED_REGISTRY.
Pass `eval_fn` (a String→String callback) to enable foldl/map/filter.
"""
function register_all_primitives!(eval_fn::Union{Function,Nothing} = nothing)
    register_core_primitives!()
    _register_atom_ops!(
        eval_fn !== nothing ? eval_fn :
            (s -> begin
                sp = default_space()
                r = eval_metta(from_sexpr(s), sp)
                to_sexpr(r)
            end)
    )
end

"""
    register_for_space!(space::CoreSpace; use_supercompiler=false)

Register all primitives with `foldl-atom`/`map-atom`/`filter-atom` wired
to evaluate sub-expressions in `space`.

When `use_supercompiler=true`, all exec atoms evaluated in this space are
routed through `MorkSupercompiler.plan!` which applies join-order reordering
and Rule-of-64 source decomposition before running MORK calculus.  Output
contract is identical to the default path (same trie mutations, no approx
pipeline engaged).

Opt-in rationale: SET semantics is safe by construction (PipelineDecompose's
flow_vars carries every final-template variable through every intermediate
_sc_tmp* hop — verified transitively for chained decompositions).  CountSink
safety is conditional: dedup only collapses identical *final* atoms, so
count-shaped reads are correct iff distinct binding paths never produce the
same final atom.  Algorithms with that property (MetaMo, MOSES) can safely
opt in.  Algorithms where two paths legitimately produce duplicate finals
(WILLIAM.count, WILLIAM.dict-size) need workload-level verification first.

Flag grain: per-space, not per-rule.  Every exec atom in this space gets
decomposed.  Acceptable for spaces holding a coherent algorithm library;
for spaces mixing safe and unsafe rules, this is too coarse and would need
per-exec-atom markers in the byte trie.

Usage:
    s = new_core_space()
    register_for_space!(s)                          # default: raw MORK calculus
    register_for_space!(s; use_supercompiler=true)  # Rule-of-64 decomposition
    load_stdlib!(s)
    run_metta("!(import! &self (library william))", s)
"""
function register_for_space!(space::CoreSpace; use_supercompiler::Bool = false)
    use_supercompiler && enable_sc!(space)
    register_core_primitives!()
    _register_atom_ops!(expr_str -> to_sexpr(eval_metta(from_sexpr(expr_str), space)))
end

"""
    sc_execute!(space::CoreSpace, program::AbstractString; opts=SC_DEFAULTS) -> SCResult

Run `program` through the **full MorkSupercompiler tier-2 pipeline** against this space's MORK
trie and return the `SCResult`. Tier-2 is a superset of the per-space `use_supercompiler` flag
(which uses tier-1 `plan!` — join-order + Rule-of-64 decomposition only): depending on `opts`
it also runs the approximate-pipeline rewrite, KB saturation, the §6 supercompilation driver,
and MM2 lowering, then loads + executes the optimized program (`SCResult.steps_executed`,
`n_facts_derived`, `drive_results`, per-stage `timings`).

Operates directly on `space.inner` (bypasses Core's prefix scoping) — pass a **root** CoreSpace
(empty prefix, the `new_core_space()` default). This is the first-class tier-2 entry; previously
only tier-1 `plan!` was reachable (and only via the legacy eval path). Stage opt-ins live on
`SCOptions` (`supercompile`, `saturate`, `use_approx_pipeline`, `use_mm2_compiler`, …).
"""
sc_execute!(space::CoreSpace, program::AbstractString; opts::SCOptions = SC_DEFAULTS)::SCResult =
    execute!(space.inner, program; opts = opts)

export sc_execute!, SCOptions, SC_DEFAULTS, SCResult
export CoreSpace, new_core_space, enable_sc!
export core_add!, core_remove!, core_match, core_rules, core_atoms
export core_calculus!, core_calculus_at!
# Dual-lane MM2 program routing (CeTTa-adopted)
export mm2_run!, mm2_partition, mm2_is_exec_rule, mm2_split_forms
export mm2_route!, mm2_match!, mm2_lower_match, mm2_expr_args
# Reflectable HE small-step rule-table (CeTTa-adopted)
export LangDefPack, LangDefRule, LangDefRuleId, HE_SMALL_STEP_RULES
export he_small_step_pack, langdef_rule_enabled, langdef_step_rules_atom, langdef_digest
# MeTTa-IL lane (F1R3FLY layered track)
export metta_il_lower, metta_il_lower_rewrite, metta_il_lower_saturation, metta_il_run!, metta_il_normalize
export metta_il_lower_def, metta_il_lower_pipeline, metta_il_run_pipeline!   # def/match/emit pipeline surface
# GSLT theory front-end (theory algebra: extends / union / replacement → flatten → MeTTa-IL)
export Theory, parse_theory, load_theories, theory_flatten, theory_rewrites, theory_run!, theory_instantiate
export theory_orient_equations
# Stage 1 multi-space + .act lifecycle
export PREFIX_REGISTRY, register_prefix!, lookup_prefix, unregister_prefix!
export get_node_shared, derive_prefix_from_name, rebind_to_shared_prefix
export with_read_permit, with_write_permit
export snapshot_space_to_act!, load_act_source, act_exists, set_act_dir!
export open_node!, close_node!
export to_sexpr, from_sexpr, to_sexpr_query, _tokenise
export parse_metta, parse_sexpr
export eval_metta, run_metta, run_file, default_space
export register_core_primitives!, register_all_primitives!, register_for_space!, load_stdlib!
export register_grounded!, is_grounded, GROUNDED_REGISTRY
export mork_unify, mork_apply, mork_rule_rewrite   # E1.0 native-engine bridge
export eval_nd, eval_nd_results                    # OutcomeSet (nondeterministic) evaluator

end # module MeTTaCore
