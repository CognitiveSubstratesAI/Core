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

# WILLIAM / AdaptiveCompression REMOVED 2026-08-05. Its `__init__` registered three grounded ops —
# `WILLIAM.mine-patterns`, `WILLIAM.prefix-of?`, `WILLIAM.continuation-of-prefix` — and ALL THREE had
# ZERO call sites across every .jl/.metta/lib/test in the tree. The package itself was a string shim:
# `mine_patterns` unpacked text to Vector{SNode}, called `MorkSupercompiler.run_trie_miner`, and
# re-serialised. WorldModel now calls that miner directly (`WorldModel/src/Mining.jl`).
#
# It had to go: its only checkout lives OUTSIDE the workspace (`~/WILLIAM.retired`) behind a remote
# that 403s, so Core/OmegaClaw/MettaJam resolved it from a DEPOT COPY that any `Pkg.gc` could delete
# with no way to restore — while WorldModel pinned `path = "../WILLIAM"`, a directory that does not
# exist, so WorldModel could not load standalone at all.
#
# ⚠️ The LGG capability is unaffected and stays MORK-native: `WILLIAM.lgg` is registered inline in
# `primitives/Primitives.jl` over MORK's own `_au_merge!` (upstream `anti_unify`, expr/src/lib.rs:669).

# ── THE GRAMMAR'S ATOM TYPE — hoisted out of `module Eval` (2026-07-29) ────────────────────
# `metta_grammar.ebnf`, our declared parser-of-record, says
#     ATOM = SYMBOL | VARIABLE | GROUNDED | EXPRESSION
# and `StandardMeTTa` implements exactly those four. It is STANDALONE — its own header says "this
# module is standalone — it does NOT touch eval_metta / eval_nd" — but it used to be `include`d INSIDE
# `module Eval` (Eval.jl:20), which made the grammar's type a private member of the
# EVALUATOR.
#
# 🔴 WHY THAT MATTERED. Everything here was originally written interpreter-first, so the shared
# foundation accreted inside the evaluator. The consequences were structural, not stylistic:
#   • `CoreSpace` loads BELOW (line 49) and so could not reach `Atom` at all. It declared its own
#     element type, `SExprConvertible`, which uses ONE Julia `Symbol` for BOTH grammar-SYMBOL and
#     grammar-VARIABLE — and `__var_` exists solely to undo that collapse on the MORK round trip.
#   • The compiler lane could not call a grounded op without depending on the FALLBACK's module,
#     which inverts the standing compiler-primary directive.
# Hoisting it here — ABOVE the store, the parser, the primitives and the MORK bridge — is what lets
# both of those be fixed. Pure move: same code, earlier position.
include("standard/NumericSeam.jl")  # §3.4 boundary decisions — ONE owner for / % and int literals
# NumericSeam is a MODULE, so `include` alone does not put its names in ours. Without this line the
# `export SeamError, seam_div, seam_mod, seam_parse_integer` below exported four names MeTTaCore did
# not have, and `using MeTTaCore; seam_div` threw `UndefVarError` — the whole point of that export
# being "one entry over both execution lanes". Found by Aqua's undefined-exports check, 2026-08-07.
using .NumericSeam: SeamError, seam_div, seam_mod, seam_parse_integer
include("standard/Atoms.jl")

# ── THE COMPILER ─────────────────────────────────────────────────────────────────────────────────
# Stage 1: the IR data type. Core had none — every "compiled" path was String→String, which is why
# the exec source functor got hand-typed at four sites and three were wrong. Node set ported from
# JeTTa (`dev-zone/jetta`), the only MeTTa-specific compiler IR among our references; names kept
# verbatim so we stay diffable against it. A frontend and passes are separate files, not yet written.
# `module CompilerIR` — its `Symbol`/`Variable`/`Expression`/`Grounded` are the COMPILER's layer and
# must not be confused with the surface ATOM grammar in standard/Atoms.jl directly above.
include("compiler/IR.jl")

include("space/CoreSpace.jl")
include("space/CoreSpaceActIO.jl")   # Stage 1 .act lifecycle (snapshot / load / open_node! / close_node!)
include("parser/Parser.jl")
include("primitives/Primitives.jl")
include("primitives/AtomOps.jl")
include("eval/MorkBridge.jl")   # E1.0: native MORK unify+apply bridge (foundation) — NOT legacy
# (Eval_obsolete.jl — the legacy Vector{Any} tree-walker eval_metta/run_metta/run_file — was RETIRED
#  2026-07-12. All tests migrated to the Eval harness or were dropped with their reworked algorithms.)

# Standard-MeTTa Eval (faithful hyperon interpreter.rs port of the minimal-MeTTa instruction set).
# Fully SELF-CONTAINED — it does NOT touch eval_metta/eval_nd and shares no types with the MORK-backed
# engine above; it lives here only so its ~28s one-time compile is BAKED INTO the precompile cache
# (`MeTTaCore.Eval`) instead of being recompiled on every fresh `include`. Accessed as `MeTTaCore.Eval`.
include("standard/Eval.jl")

# Compiler stage 2: surface Atom → CompilerIR, with resolution (per-clause variable identity),
# special forms as NODES, and structural heads. Included AFTER Eval because it consults the
# interpreter's EXISTING SLG registry (`_TABLED_HEADS`, Eval.jl:979-982) rather than declaring
# a second one — SLG/WFS was already adopted there and is reused, not rebuilt.
include("compiler/Frontend.jl")

# Compiler stage 2b: IR→IR passes. `specialize_matches` splits a clause whose body is a `case`/`if`
# on a HEAD VARIABLE into one clause per arm, substituting the arm pattern into the redex. That shape
# is the only one that FIRES — verified against the upstream MORK binary — and it is upstream's own
# (Control_04_Select_b_c.mm2). Must run BEFORE A-normalization, and cannot live in codegen, which
# sees only the body and not the head it must substitute into.
include("compiler/Passes.jl")

# Compiler stage 3: A-normalization of rule bodies to GOAL LISTS — a direct port of PeTTa's
# `translator.pl` (`translate_clause/3`, `translate_expr/3`), the Prolog lineage Core already took
# SLG from. `let` becomes ONE unification goal, `let*` is nested `let`, `if`/`case` become branch
# goals sharing an output, `superpose` a disjunction, `collapse` a findall. Pure — emits nothing.
include("compiler/ANormal.jl")

# Compiler stage 4: A-normalized clauses → MORK exec rules. The first stage whose output RUNS.
# One emitter owns every syntactic decision about the exec form — source functor, template functor,
# priority — so it cannot drift the way N hand-written call sites did.
include("compiler/Emit.jl")

# Compiler stage 4a: A-normalized clauses → MINIMAL MeTTa (the MeTTa-IL). THE arrow Figure 2 has —
# MeTTa → MeTTa-IL — which the pipeline previously skipped by going straight from A-normal form to
# MM2 exec atoms. SPECMAP C6: `Emit.jl` was "the right component in the wrong POSITION"; this stage
# is the position. Its output is executable on arrival, because `Eval.jl` already implements every
# instruction it emits (MINIMAL_OPS). Follows Emit.jl because it reuses `render`.
# Design + diagrams: docs/architecture/COMPILER_IL_STAGE.md
include("compiler/EmitIL.jl")

# GSLT presentations — G = (Σ, E, R), Definition 2.1. Its own subdirectory because this is a
# component (data model, and later parsing / the hypercube construction), not another linear stage in
# the IR→A-normal→emit pipeline the flat files above form.
#
# WHY IT MATTERS HERE: whitepaper §3.4.1 says MeTTa-IL is "derived from a GSLT description", and the
# type system / cost / history / logic are all GENERATED from the triple. `standard/GSLT.jl` has the
# theory ALGEBRA but cannot express binders, freshness or premised rewrites — so MeTTa itself cannot
# be presented, and with no presentation there is nothing to generate from. This is that gap.
include("compiler/gslt/Presentation.jl")
include("compiler/gslt/Parse.jl")        # s-expr surface → GPresentation (presentations you can WRITE)

# Dual-lane program routing (CeTTa-adopted, PRIMUS-native). In MAIN scope (uses CoreSpace + the
# MORK-backed engine), NOT inside the self-contained `Eval` submodule above.
include("space/CoreSpaceLoad.jl")    # load lib/*.metta into the SHARED MORK trie (needs Eval's
                                     # _MODULE_PATH, so it must follow standard/Eval.jl)
include("standard/AtomExprBridge.jl")  # typed Atom ⇄ MORK.Expr — lane-neutral, live in CoreSpace/Primitives
include("standard/SexprForms.jl")   # lane-neutral s-expr form parsers — MUST precede every consumer
# COMPILER-PRIMARY lane: MeTTa → MeTTa-IL → evaluate the IL. The live consumer of compiler/EmitIL.jl,
# without which that stage is measured coverage of nothing. Placed HERE — after SexprForms (it drives
# split_program_regions) and BEFORE DualTrack (which now consumes its may-mutate predicate instead of
# keeping a second copy), so the dependency points from the deprecated lane to the surviving one.
include("standard/CompileLane.jl")
include("standard/MM2Router.jl")
include("standard/LangDefPack.jl")   # reflectable HE small-step rule-table (CeTTa-adopted)
include("standard/MeTTaIL.jl")       # MeTTa-IL lane (F1R3FLY layered track): MeTTa-IL → MM2 → MORK
include("standard/GSLT.jl")          # GSLT theory front-end: theory algebra (extends/union/replace) → MeTTa-IL
include("standard/DualTrack.jl")     # dual-track capstone: mc_run unified entry (auto-dispatch by form)
include("standard/LibPolicy.jl")     # read lib/*.metta POLICY CONSTANTS via the compiler lane
include("standard/PatternMiner.jl")  # simplified frequent-pattern miner (Hyperon Pattern Miner) on def/match/emit

# (The legacy `(library william)` registry entry — `_PACKAGE_REGISTRY["william"]` — was removed with
#  Eval_obsolete.jl. The modern import! resolver uses `Eval._MODULE_PATH`; the WILLIAM rework will
#  register william there if/when it needs `(import! &self (library william))`.)

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

# register_all_primitives! / register_for_space! were REMOVED with the Eval_obsolete.jl tree-walker
# (2026-07-12): they wired the legacy foldl/map/filter atom-ops to eval_metta. The modern Eval
# path carries its own grounded ops; `register_core_primitives!` (Primitives.jl) remains for direct
# GROUNDED_REGISTRY population, and `enable_sc!(space)` remains the supercompiler opt-in.

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
# ── OBSOLETE PUBLIC SURFACE, un-exported 2026-08-07 ──────────────────────────────────────────────
# `mm2_partition`, `mm2_lane_from_atoms`, `mm2_lane_from_space`, `mm2_lane_saturate!` and
# `mm2_lane_saturate_seminaive!` are DEFINED and WORKING but no longer exported. They are entry points
# of the direct MeTTa-surface-`(=)` → MM2 lowering, the arrow Figure 2 does not have. MEASURED before
# un-exporting: each appeared in `src/` ONLY on an export line — no production caller — while remaining
# reachable internally and from `test/test_mm2_router.jl` (now qualified `MC.`).
# Removing the export is the DISCONNECT: nothing new can bind to them, nothing existing breaks.
# NOT un-exported: `mm2_zam_answers` is genuinely live via `DualTrack.jl:155`.
export mm2_run!, mm2_is_exec_rule, mm2_split_forms
# Lane-NEUTRAL, and deliberately not `mm2_`-prefixed: the sequential-effects partition is a property
# of MeTTa Invariant 1, not of any lane, and it must outlive the MM2 direct-lowering arrow.
export ProgramRegion, split_program_regions, region_program
export mm2_route!, mm2_match!, mm2_lower_match, mm2_lower_equals, mm2_expr_args, mm2_is_relational
export mm2_lower_equals_arith, mm2_is_arith_body, mm2_lower_eq, mm2_eq_bisim
export typed_atom_to_expr, expr_to_atom, mc_closure!
# Reflectable HE small-step rule-table (CeTTa-adopted)
export LangDefPack, LangDefRule, LangDefRuleId, HE_SMALL_STEP_RULES
export he_small_step_pack, langdef_rule_enabled, langdef_step_rules_atom, langdef_digest
# MeTTa-IL lane (F1R3FLY layered track)
export metta_il_lower, metta_il_lower_rewrite, metta_il_lower_saturation, metta_il_run!, metta_il_normalize
export metta_il_lower_def, metta_il_lower_pipeline, metta_il_run_pipeline!   # def/match/emit pipeline surface
# GSLT theory front-end (theory algebra: extends / union / replacement → flatten → MeTTa-IL)
export Theory, parse_theory, load_theories, theory_flatten, theory_rewrites, theory_run!, theory_instantiate
export theory_orient_equations
# Dual-track capstone — one entry over both execution lanes
export SeamError, seam_div, seam_mod, seam_parse_integer
export mc_run
# LibPolicy — policy constants stay MeTTa atoms; Julia asks, never copies (see LibPolicy.jl header)
export policy_space, reset_policy_space!, lib_policy, lib_policy_int, lib_policy_names
# Frequent-pattern miner (Hyperon Pattern Miner core) on def/match/emit
export pattern_support, pattern_support_interp, pattern_support_native, mine_frequent
# MORK-native prefix-locality miner (MORK-Miner)
export prefix_support, mine_prefix_patterns, grow_prefix
export PrefixCounter, prefix_insert!, prefix_counter, prefix_count_support   # in-place counters (§2.3)
# Stage 1 multi-space + .act lifecycle
export PREFIX_REGISTRY, register_prefix!, lookup_prefix, unregister_prefix!
export get_node_shared, derive_prefix_from_name, rebind_to_shared_prefix
export with_read_permit, with_write_permit
export snapshot_space_to_act!, load_act_source, act_exists, set_act_dir!
export open_node!, close_node!
export to_sexpr, from_sexpr, to_sexpr_query, _tokenise
export parse_metta, parse_sexpr
export register_core_primitives!, load_stdlib!
export register_grounded!, is_grounded, GROUNDED_REGISTRY
export mork_unify, mork_apply, mork_rule_rewrite   # E1.0 native-engine bridge

end # module MeTTaCore
