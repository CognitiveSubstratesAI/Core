# MeTTaIL.jl — minimal MeTTa-IL lane (F1R3FLY layered track): MeTTa-IL → MM2 → native MORK.
#
# The middle compilation layer of Goertzel's pipeline (MeTTa/pyMeTTa → MeTTa-IL → MM2+ → MM2 → MORK/ZAM).
# This is the *other* track from the CeTTa-style direct lowering (MM2Router); PRIMUS supports both,
# selected by infra (project_dual_track_mettail). IL surface (Scalable-MeTTa-Infrastructure §9.1):
#
#   (def NAME (params) (match PAT… BODY))      BODY = (emit OUT) | (when GUARD (emit OUT))
#
# Lowers to MM2: (exec 0 (, PAT… [GUARD]) (, OUT)), runs on the native MORK CoreSpace via the router's
# machinery (NO surface→IR rewrite, NO FFI — PRIMUS-MORK runs MM2 directly). Bisimulation-gated ≡ the
# interpreter-spec. Minimal first increment: relational def→exec (+ when guard); MM2+ optimization
# (guard-hoist/fuse) and the selector are later increments.

"Lower one MeTTa-IL `(def NAME (params) (match PAT… BODY))` to an MM2 `(exec …)` rule string."
function metta_il_lower_def(def::AbstractString)::String
    a = mm2_expr_args(def)
    (length(a) == 4 && a[1] == "def") ||
        error("metta_il_lower_def: expected (def NAME (params) BODY), got: $def")
    m = mm2_expr_args(a[4])
    m[1] == "match" || error("metta_il_lower_def: def body must be (match …), got head '$(m[1])'")
    pats = m[2:end-1]                       # the source patterns (conjunction)
    eb = mm2_expr_args(m[end])              # the body: (emit …) or (when G (emit …))
    guard, emit = if eb[1] == "emit"
        nothing, eb[2]
    elseif eb[1] == "when"
        inner = mm2_expr_args(eb[3])
        inner[1] == "emit" || error("when body must be (emit …), got '$(inner[1])'")
        eb[2], inner[2]
    else
        error("match body must be (emit …) or (when G (emit …)), got '$(eb[1])'")
    end
    isempty(pats) && error("metta_il_lower_def: match needs ≥1 pattern")
    srcs = guard === nothing ? join(pats, " ") : join([pats; guard], " ")
    "(exec 0 (, $srcs) (, $emit))"
end

"Lower a MeTTa-IL program (one or more `def`s) to MM2 exec rules."
metta_il_lower(program::AbstractString)::String =
    join([metta_il_lower_def(strip(f)) for (bang, f) in mm2_split_forms(program)
          if !bang && mm2_head(f) == "def"], "\n")

"""
    metta_il_run!(cs::CoreSpace, data, il_program; steps=1_000_000) -> Vector{String}

Run a MeTTa-IL program over `data` on the native MORK `cs`: lower the `def`s → MM2 exec rules, add
data + rules to the trie, step the calculus, and return the emitted atoms (by each def's emit head).
"""
function metta_il_run!(cs::CoreSpace, data::AbstractString, il_program::AbstractString;
                       steps::Int = 1_000_000)
    isempty(strip(data)) || space_add_all_sexpr!(cs.inner, data)
    exec = metta_il_lower(il_program)
    isempty(exec) && return String[]
    space_add_all_sexpr!(cs.inner, exec)
    # NOTE: `space_metta_calculus!` does SINGLE-STEP derivation (each rule fires over the current atoms,
    # one generation) — NOT recursive saturation. So non-recursive defs and one-hop joins work here;
    # RECURSIVE defs (a def whose emit head is also a source, e.g. transitive closure) need the
    # saturation engine (MorkSupercompiler KBSaturation, wired earlier this session) — the next increment.
    space_metta_calculus!(cs.inner, steps)
    # collect emitted atoms: heads of each def's emit template
    heads = Set{String}()
    for (bang, f) in mm2_split_forms(il_program)
        (bang || mm2_head(f) != "def") && continue
        m = mm2_expr_args(mm2_expr_args(f)[4])
        eb = mm2_expr_args(m[end])
        push!(heads, mm2_head(eb[1] == "when" ? mm2_expr_args(eb[3])[2] : eb[2]))
    end
    sort(unique(String[strip(l) for l in split(space_dump_all_sexpr(cs.inner), '\n')
                        if mm2_head(strip(l)) in heads]))
end
