# EVERY TEST FILE MUST BE REACHABLE FROM runtests.jl — or be exempted BY NAME, with a reason.
#
# WHY THIS EXISTS. "A test exists and does not run" cost real work THREE times on 2026-08-16 alone:
#   1. `test_restraints.jl` (later `test_tripwires.jl`) shipped with its 21 assertions unregistered,
#      because runtests.jl was carrying another session's uncommitted hunk at the time.
#   2. Registering it then broke on a rename — runtests.jl still pointed at the old filename, so the
#      suite would have died on a missing include.
#   3. `test/standard/test_unit.jl` — 108 lines gating hyperon's own stdlib `#[test]` corpus over ten
#      `.metta` modules — had NEVER run. Adopted at `0c51e87`, then touched only by mechanical module
#      renames. SIX conformance gaps in `core.metta` closed while its baseline still said 8, and no
#      commit is attributable for any of them.
#
# ⇒ the recurring defect gets a GATE, not a fourth note
# (`[[feedback_enforcement_works_prose_memory_does_not]]`,
#  `[[feedback_recurring_defect_derive_the_rule]]`). A missing include is invisible: the suite goes
# green having run less. This makes it loud.
#
# ⚠️ AND IT IS THE `include` GRAPH, NOT A DIRECTORY LISTING. Files reach the suite transitively — a
# module wrapper includes a file which includes another — so this walks every `include(...)` in every
# test file, following BOTH the literal `include("x.jl")` form AND `include(joinpath(@__DIR__, …))`.
# The first version of this scan matched only the literal form and reported `assert_guard.jl` as
# orphaned when three files include it via joinpath — a FALSE POSITIVE found by running it. A gate
# whose failures are noise gets disabled, so the joinpath form is load-bearing, not thoroughness.
using Test

@testset "suite reachability — no test file is silently unrun" begin
    testdir = @__DIR__

    # Exempt BY NAME with a reason. Never a pattern: a pattern is how the next orphan hides.
    exempt = Dict(
        "health.jl"       => "the health GATE itself — run by `bin/health`, not by runtests.jl",
        "assert_guard.jl" => "shared helper, included via joinpath by its consumers (not a suite entry)",
        "runtests.jl"     => "the root",
        # 🔴 EXEMPT BECAUSE IT HANGS, AND THE HANG IS NOT ITS FAULT — remove this the moment the
        # completion loop consults `max_answers`. It is a correct test of §1.0 step 2, but its
        # program `(= (q) 1)  (= (q) (S (q)))` has an INFINITE tabled answer set (1, (S 1), …).
        # MEASURED: it hangs with dependency recording OFF and a 20k step cap, i.e. on the
        # pre-existing engine — `interpret` is capped but the `while grew` fixpoint in
        # `_leader_pass` is UNBOUNDED. That is exactly the case SWI's §7.11.3 restraint stops;
        # `tabling/Tripwires.jl` has it, ported and differentialled, and nothing consults it yet.
        # Registering it as-is would hang the whole suite, which is a worse failure than this one.
        "test_dependency_firing.jl" =>
            "hangs on an UNBOUNDED completion fixpoint (infinite answer set); re-register once " *
            "the completion loop consults max_answers — see tabling/Tripwires.jl",
    )

    # THREE FILTERS, each for a FALSE POSITIVE this scan actually produced when first run:
    #   * strip line comments — otherwise the scan matches the `include("x.jl")` EXAMPLES in this
    #     file's own header and reports them as dangling.
    #   * skip interpolated literals (`$`) — `tools/repl.jl` builds include paths dynamically, and a
    #     regex resolves `"test/standard/$f.jl"` to the nonexistent `test/standard/.jl`.
    #   * stay under `test/` — `tools/repl.jl` is not a test file and its includes are not this
    #     gate's business.
    # A gate whose failures are noise gets disabled, so these are load-bearing, not tidiness.
    _decomment(txt) = join((occursin(r"^\s*#", l) ? "" : split(l, '#')[1] for l in split(txt, '\n')), '\n')
    _under(p) = startswith(normpath(p), normpath(testdir))

    reached = Set{String}()
    function scan(path)
        txt = _decomment(read(path, String)); dir = dirname(path)
        function take(p)
            (occursin('$', p) || !_under(p)) && return
            p = normpath(p)
            p in reached && return
            push!(reached, p); isfile(p) && scan(p)
        end
        # BOTH entry forms: raw `include(...)` (used inside individual test files) and runtests.jl's
        # `Main.@suite(...)` recording wrapper. Missing the second would report the ENTIRE suite as
        # orphaned the moment runtests.jl switched to the macro.
        for m in eachmatch(r"(?:include|@suite)\(\s*\"([^\"]+\.jl)\"", txt)
            take(joinpath(dir, m.captures[1]))
        end
        # include(joinpath(@__DIR__, "..", "x.jl")) — the form the first version of this scan missed
        for m in eachmatch(r"(?:include|@suite)\(\s*joinpath\(([^)]*)\)\s*\)", txt)
            parts = [x.captures[1] for x in eachmatch(r"\"([^\"]+)\"", m.captures[1])]
            isempty(parts) && continue
            take(joinpath(dir, parts...))
        end
    end
    scan(joinpath(testdir, "runtests.jl"))

    # `test/pln/*.jl` are auto-discovered by a readdir loop in runtests.jl, so they are reached
    # WITHOUT an include() literal. Mirror that loop rather than exempting the directory.
    for f in readdir(joinpath(testdir, "pln"))
        endswith(f, ".jl") && push!(reached, normpath(joinpath(testdir, "pln", f)))
    end

    all_tests = String[]
    for (dp, _, fs) in walkdir(testdir), f in fs
        endswith(f, ".jl") && push!(all_tests, normpath(joinpath(dp, f)))
    end

    # ANTI-VACUITY FIRST — a scan that walked nothing would report zero orphans and pass.
    @test length(all_tests) > 40
    @test length(reached) > 40

    orphans = [p for p in sort(all_tests)
               if !(p in reached) && !haskey(exempt, basename(p))]
    @test isempty(orphans) ||
          (@info """A TEST FILE IS NOT RUN BY THE SUITE.
                   Either add an include() to runtests.jl, or add it to `exempt` above WITH A REASON.
                   An unregistered test is a test that does not run.""" orphans; false)

    # every exemption must still name a real file, or the list rots into fiction
    for (name, why) in exempt
        @test any(p -> basename(p) == name, all_tests) ||
              (@info "stale exemption — no such test file" name why; false)
    end

    # and every include() must resolve, so a rename cannot leave a dangling target (failure #2 above)
    for p in reached
        @test isfile(p) || (@info "runtests.jl includes a file that does not exist" path=p; false)
    end
end
