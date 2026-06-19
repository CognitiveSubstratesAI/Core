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
# interpreter-spec. NOT yet covered (the larger GSLT front-end / follow-ons): the full theory algebra
# (Terms/grammar, Equations, Replacements, composition), congruence rules (`let Src ~> Tgt in …`), and
# recursive closure (needs the saturation engine, KBSaturation — the single-step exec does one generation).

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

"""
    metta_il_run!(cs::CoreSpace, data, program; steps=1_000_000) -> Vector{String}

Run a MeTTa-IL program's rewrites over `data` on the native MORK `cs`: lower `(~> LHS RHS)` → MM2 exec
rules, add data + rules to the trie, step the calculus, return the rewritten atoms (by each RHS head).
"""
function metta_il_run!(cs::CoreSpace, data::AbstractString, program::AbstractString;
                       steps::Int = 1_000_000)
    isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
    exec = metta_il_lower(program)
    isempty(exec) && return String[]
    space_add_all_sexpr!(cs.inner, exec)
    # single-step exec calculus (one generation); recursive closure needs the saturation engine.
    space_metta_calculus!(cs.inner, steps)
    heads = Set{String}()
    for (bang, f) in mm2_split_forms(program)
        (bang || mm2_head(f) != "~>") && continue
        push!(heads, mm2_head(mm2_expr_args(f)[3]))   # RHS head
    end
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) in heads]))
end
