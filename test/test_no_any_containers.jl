# `Any[]` / `Vector{Any}` / `Ref{Any}` / a `::Any` field in `src/` — banned, with a named escape.
#
# ─── WHY THIS IS A GATE AND NOT A NOTE ──────────────────────────────────────────────────────────
# The user has given this rule, by their own count, around fifty times over six to twelve months.
# A PreToolUse hook for it (`.claude/hooks/discourage-vector-any.sh`) has been installed and correct
# for months. Seventeen `Any` containers still reached `src/`.
#
# The reason is worth recording, because it is not "the rule was forgotten". That hook reads
# `tool_input.file_path` and matches `Write|Edit`. Edits made through a Bash heredoc (`python3 -
# <<EOF`, `sed -i`) carry NO file_path, so the hook exits before looking at the content — and some
# sessions are explicitly instructed to prefer heredocs over the Write/Edit tools. The enforcement
# gap sat exactly where the workflow pushes. Patching the hook means parsing shell, which is
# fragile: the first attempt at it broke the hook outright and had to be reverted.
#
# A TEST SEES THE RESULT, whatever tool produced it. That is why this is the durable instrument.
#
# ─── WHY THE RULE, IN THIS CODEBASE SPECIFICALLY ────────────────────────────────────────────────
# MeTTa's grammar closes the atom at FOUR cases:
#
#     ATOM ::= SYMBOL | VARIABLE | GROUNDED | EXPRESSION
#
# and `src/standard/Atoms.jl` mirrors them exactly — `Sym`, `Var`, `Grounded{T}`, `Expression`, all
# `<: Atom`. So any container holding MeTTa values has a precise type available for free: `Atom`.
# Writing `Any[]` there throws away a guarantee the SPEC hands us. Beyond typing, `Vector{Any}`
# boxes every element and defeats union-splitting — CLAUDE.md's "avoid `Vector{Any}` in hot paths",
# and the ProductZipperG incident the hook's own header records.
#
# ─── THE ESCAPE, AND WHY IT IS NAMED ────────────────────────────────────────────────────────────
# `# allow-any: <reason>` on the line or just above it. Two legitimate kinds exist today:
#   • Julia AST under construction, feeding `Expr(...)` whose own `args` IS `Vector{Any}`;
#   • tagged plan steps of mixed arity, built once per clause at compile time.
# Both are annotated in `src/compiler/`. An escape without a reason is not an escape — the pattern
# requires text after the colon.
using Test

@testset "no Any-typed containers in src (grammar gives every MeTTa value a type)" begin
    root = normpath(joinpath(@__DIR__, "..", "src"))
    files = String[]
    for (dp, _, fs) in walkdir(root), f in fs
        endswith(f, ".jl") && push!(files, joinpath(dp, f))
    end
    @test length(files) > 20                    # ANTI-VACUITY: a walk that found nothing passes

    # `Any` mentioned in a comment or docstring is inert — `Atoms.jl` documents "NOT Vector{Any}",
    # and flagging that would make the gate noise, which is how a gate gets switched off.
    offenders = String[]
    allowed = 0
    for path in files
        lines = readlines(path)
        indoc = false
        for (i, raw) in enumerate(lines)
            n = count(_ -> true, findall("\"\"\"", raw))
            isodd(n) && (indoc=(!indoc); continue)
            indoc && continue
            code = replace(raw, r"#.*$" => "")
            startswith(strip(raw), "#") && continue
            # A SINGLE-LINE DOCSTRING is a string, not code. `Atoms.jl:42` is literally
            # `"Expression — typed children (NOT Vector{Any}). …"` — documenting the rule this gate
            # enforces, and the first version flagged it. A gate whose failures are noise gets
            # switched off, so the detector must not trip on prose ABOUT `Any`.
            startswith(strip(raw), "\"") && continue
            hit =
                occursin(r"(^|[^A-Za-z0-9_.])Any\[", code) ||
                occursin(r"\b(Vector|Array|Ref)\{Any[,}]", code) ||
                occursin(r"\bDict\{[^}]*,\s*Any\}", code) ||
                occursin(r"^\s*[A-Za-z_][A-Za-z0-9_!]*\s*::\s*Any\s*$", code)
            hit || continue
            # the escape may sit on this line or in the comment block immediately above it
            lo = max(1, i - 6)
            if any(l -> occursin(r"#\s*allow-any:\s*\S", l), lines[lo:i])
                allowed += 1
            else
                push!(
                    offenders,
                    string(relpath(path, root), ":", i, "  ", strip(raw)[1:min(end, 90)])
                )
            end
        end
    end

    # 🔴 ANTI-VACUITY, AND IT IS THE POINT. A detector that matches NOTHING passes this file
    # silently — which is exactly the failure mode the suite is full of. `src/compiler/` carries
    # annotated, legitimate `Any` sites today, so the detector MUST see them. If this drops to zero,
    # either those were cleaned up (then delete this assertion deliberately) or the regexes rotted.
    @test allowed > 0

    isempty(offenders) || printstyled("\n  unannotated Any containers:\n    ",
        join(offenders, "\n    "), "\n"; color=:red)
    @test offenders == String[]
end
