# MeTTaIL.jl — MeTTa-IL rewrite-reduction → MM2 → MORK (F1R3FLY layered track).
#
# RE-GROUNDED 2026-06-19 in the ACTUAL upstream MeTTa-IL (F1R3FLY/MeTTaIL `GSLT/.module` +
# mettail-rust `language!`), NOT the scalable-infra paper §9.1 `def/match/emit` sketch (that was a
# mislabel — corrected). The real MeTTa-IL: a Theory has `Terms` (BNF grammar), `Equations`,
# `Rewrites`, `Replacements`, with theory composition. Its EXECUTABLE reduction relation is the
# **Rewrites** — `Name : LHS ~> RHS` (base) and congruence `let Src ~> Tgt in (Ctx Src) ~> (Ctx Tgt)`
# (same structure as mettail-rust's `Name . | M0~>M1 |- LHS ~> RHS`).
#
# This lane lowers the BASE rewrites `(~> LHS RHS)` → MM2 `(exec 0 (, LHS) (, RHS))`, run on the native
# MORK CoreSpace via the router's machinery (no surface→IR rewrite, no FFI), bisimulation-gated ≡ the
# interpreter-spec. RECURSIVE closure → `saturate=true` (KBSaturation to fixpoint). CONGRUENCE / calculus
# reduction → `metta_il_normalize` (subterm rewriting). NOT yet covered: equations-as-rewrite orientation.
# The GSLT theory algebra (Terms/Equations/Replacements/composition/parameterization) lives in GSLT.jl.
#
# Two distinct `~>` execution modes (pick by workload): metta_il_run! = additive forward-derivation
# (relational/Datalog — transitive closure, deductive queries); metta_il_normalize = term reduction with
# congruence (calculi — rho/lambda, equational reduction). Same surface, different semantics.

"Lower one MeTTa-IL base rewrite `(~> LHS RHS)` (GSLT `Name : LHS ~> RHS`) to an MM2 `(exec …)` rule.
LHS may be a single pattern or a conjunction `(, P1 P2 …)`."
function metta_il_lower_rewrite(rw::AbstractString)::String
    a = mm2_expr_args(rw)
    (length(a) == 3 && a[1] == "~>") ||
        error("metta_il_lower_rewrite: expected (~> LHS RHS), got: $rw")
    lhs, rhs = a[2], a[3]
    src = startswith(lstrip(lhs), "(,") ? lhs : "(, $lhs)"
    "(exec 0 $src (, $rhs))"
end

"Lower a MeTTa-IL program (its `(~> LHS RHS)` rewrites) to MM2 exec rules."
metta_il_lower(program::AbstractString)::String =
    join([metta_il_lower_rewrite(strip(f)) for (bang, f) in mm2_split_forms(program)
          if !bang && mm2_head(f) == "~>"], "\n")

"Lower a MeTTa-IL program's rewrites to KBSaturation forward rules `(==> LHS RHS)` (for recursive
closure). `(~> LHS RHS)` and `(==> BODY HEAD)` are the same forward-derivation; `==>` runs to fixpoint."
metta_il_lower_saturation(program::AbstractString)::String =
    join(["(==> $(mm2_expr_args(f)[2]) $(mm2_expr_args(f)[3]))"
          for (bang, f) in mm2_split_forms(program) if !bang && mm2_head(f) == "~>"], "\n")

"""
    metta_il_run!(cs::CoreSpace, data, program; steps=1_000_000, saturate=false) -> Vector{String}

Run a MeTTa-IL program's rewrites over `data` on the native MORK `cs`, returning the rewritten atoms
(by each RHS head). Two engines:
  * `saturate=false` (default): lower `(~> LHS RHS)` → MM2 `(exec …)`, step the calculus ONE generation.
  * `saturate=true`: lower → KBSaturation rules `(==> LHS RHS)`, run `sc_execute!` to FIXPOINT — needed
    for RECURSIVE rewrites (a rewrite whose RHS head also appears in a body), e.g. transitive closure.
"""
function metta_il_run!(cs::CoreSpace, data::AbstractString, program::AbstractString;
                       steps::Int = 1_000_000, saturate::Bool = false)
    isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
    if saturate
        rules = metta_il_lower_saturation(program)
        isempty(rules) && return String[]
        sc_execute!(cs, rules; opts = SCOptions(saturate = true))   # seminaive saturation → fixpoint
    else
        exec = metta_il_lower(program)
        isempty(exec) && return String[]
        space_add_all_sexpr!(cs.inner, exec)
        space_metta_calculus!(cs.inner, steps)                      # single generation
    end
    heads = Set{String}()
    for (bang, f) in mm2_split_forms(program)
        (bang || mm2_head(f) != "~>") && continue
        push!(heads, mm2_head(mm2_expr_args(f)[3]))   # RHS head
    end
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) in heads]))
end

# --- Congruence: calculus reduction via subterm rewriting --------------------------------------------
# GSLT/mettail-rust `~>` for CALCULI is term REDUCTION WITH CONGRUENCE (a redex reduces inside any
# context), NOT the additive forward-derivation of metta_il_run!. Neither existing engine gives it free:
# the relational lane is additive; the interpreter does NOT reduce constructor/undefined-head subterms
# (verified — `(and (not T) Y)` stays unreduced). So congruence is BUILT here as a subterm-rewriting
# normalizer: rewrite any subterm matching a base-rewrite LHS, innermost, to fixpoint. The subterm
# descent IS the congruence — mettail-rust spells it out as explicit `rw_cat` rules ONLY because
# Ascent/Datalog is relational and cannot descend into subterms; on a term engine it is structural.

function _normalize_subterm(rules::Vector{String}, term::AbstractString)::String
    term = strip(term)
    if startswith(term, "(")                          # compound: normalize children first (← congruence)
        term = "(" * join([_normalize_subterm(rules, a) for a in mm2_expr_args(term)], " ") * ")"
    end
    for rule in rules                                 # then a top-level reduction; renormalize on success
        r = mork_rule_rewrite(rule, term)
        r !== nothing && r != term && return _normalize_subterm(rules, r)
    end
    term
end

"""
    metta_il_normalize(program, term) -> String

Reduce `term` to normal form under a MeTTa-IL calculus (the program's base rewrites `(~> LHS RHS)` as
reduction rules), rewriting subterms innermost to fixpoint. Congruence (reduction inside contexts) is
the subterm traversal — so GSLT/mettail-rust explicit congruence rules (`let Src ~> Tgt in …`), needed
only by relational backends, are unnecessary here.
"""
function metta_il_normalize(program::AbstractString, term::AbstractString)::String
    rules = String["(= $(mm2_expr_args(f)[2]) $(mm2_expr_args(f)[3]))"
                   for (bang, f) in mm2_split_forms(program) if !bang && mm2_head(f) == "~>"]
    _normalize_subterm(rules, term)
end
