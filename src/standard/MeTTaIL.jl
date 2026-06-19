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
# interpreter-spec. RECURSIVE closure is handled by `saturate=true` (KBSaturation to fixpoint). NOT yet
# covered: congruence rules (`let Src ~> Tgt in …`); equations-as-rewrite orientation. The GSLT theory
# algebra (Terms/Equations/Replacements/composition/parameterization) lives in GSLT.jl.

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
