# A `$name` inside a Julia STRING is INTERPOLATION, not text — and in a docstring it breaks the
# whole package at PRECOMPILE time with `UndefVarError`, before any test can run.
#
# ─── WHY THIS IS A GATE AND NOT A NOTE ───────────────────────────────────────────────────────────
# It cost three precompile failures on 2026-08-16/17 alone, each time in a docstring quoting an
# UPSTREAM identifier that legitimately starts with `$`:
#
#     `$tbl_table_status`   `$tbl_wkl_add_answer`   `(f $x $x)`
#
# and the failure is maximally unhelpful — `UndefVarError: tbl_table_status not defined`, pointing at
# a docstring, with the package unusable until it is fixed. It recurs because SWI's C predicates and
# MeTTa's variables BOTH use `$`, so the two things this port quotes most often are exactly the two
# that trip it. `[[feedback_enforcement_works_prose_memory_does_not]]` — the recurring defect gets a
# gate, not a fourth note.
#
# ⚠️ SCOPE: `"` STRINGS ONLY. A `$` in a `#` comment is inert, and `raw"..."` does not interpolate.
# The check therefore looks only at docstring bodies — the `"""` blocks immediately preceding a
# definition, and single-line `"..."` docstrings — and ignores everything else. A gate whose failures
# are noise gets switched off.
using Test

@testset "no unescaped \$ interpolation in docstrings" begin
    root = normpath(joinpath(@__DIR__, "..", "src"))
    files = String[]
    for (dp, _, fs) in walkdir(root), f in fs
        endswith(f, ".jl") && push!(files, joinpath(dp, f))
    end
    @test length(files) > 20                       # ANTI-VACUITY: a walk that found nothing passes

    offenders = Tuple{String, Int, String}[]
    for path in files
        lines = split(read(path, String), '\n')
        indoc = false
        for (i, ln) in enumerate(lines)
            # `raw"""` / `raw"` never interpolate — skip the line entirely.
            occursin("raw\"", ln) && continue
            fences = count(_ -> true, eachmatch(r"\"\"\"", ln))
            body = ln
            if indoc || fences > 0
                # strip a leading `#` comment line: `$` there is inert
                startswith(lstrip(ln), "#") && (indoc=xor(indoc, isodd(fences)); continue)
                # an unescaped `$` FOLLOWED BY an identifier char is interpolation.
                for m in eachmatch(r"(?<!\\)\$([A-Za-z_(])", body)
                    push!(offenders, (relpath(path, root), i, strip(ln)[1:min(90, end)]))
                    break
                end
            end
            isodd(fences) && (indoc = !indoc)
        end
    end

    if !isempty(offenders)
        @info """UNESCAPED `\$` IN A DOCSTRING — this breaks PRECOMPILATION, not just this test.
                 Write `\\\$name` (or use raw\"\"\"...\"\"\") when quoting an upstream `\$predicate`
                 or a MeTTa `\$variable`.""" offenders
    end
    @test isempty(offenders)
end
