# test_wfs_swipl_differential.jl — WFS/`tnot` differentialled against a LIVE SWI-Prolog.
#
# ─── WHY THIS FILE EXISTS ────────────────────────────────────────────────────────────────────────
# `test_tnot_wfs.jl` says at its head "Verified against the SWI-Prolog 9.0.4 differential oracle in
# test/oracle/wfs/*.pl", and that sentence has been repeated as fact — including into memory as
# "gated 39/39 against a LIVE SWI oracle". MEASURED 2026-08-06, all three parts are wrong:
#
#   * the file holds 41 `@test`, not 39;
#   * it NEVER INVOKES swipl — the only three mentions of it are prose comments;
#   * `test/oracle/wfs/RUN.sh` is a MANUAL script no suite calls.
#
# So the assertions there are PINNED LITERALS transcribed from a run somebody did by hand once. They
# would keep passing if SWI changed its answer, and they cannot detect the divergence they claim to
# gate. That is the exact shape of `[[feedback_verify_the_oracle_runs]]` — a test that cannot fail
# for the stated reason is worse than a missing test, because it reads green.
#
# This file is the real thing: it RUNS `swipl` on `test/oracle/wfs/A_win_game.pl`, parses that
# program's own `classify/2` output, and asserts Core agrees goal by goal. If SWI's answer changes,
# this goes red. `test_tnot_wfs.jl` keeps its pins (they are a useful regression on Core alone);
# this supplies the guarantee its header claims.
#
# ─── THE ORACLE IS ITSELF GUARDED ────────────────────────────────────────────────────────────────
# Two failure modes that would make this file as hollow as the one it fixes, both closed below:
#
#  1. swipl absent ⇒ the testset must not silently pass. It reports a LOUD `@test_skip` naming the
#     reason. (Never a bare `return` — that is indistinguishable from success in the summary.)
#  2. swipl present but the parse yields nothing ⇒ zero assertions would run and the testset would
#     read green having checked NOTHING. So there is a POSITIVE CONTROL: the parse must produce
#     exactly the 8 expected goals, asserted BEFORE any comparison. This is
#     `[[feedback_oracle_must_observe_the_defect_class]]` — a green oracle only means "the defects it
#     can SEE are absent", so first prove it can see anything at all.
#
# ─── ENVIRONMENT ─────────────────────────────────────────────────────────────────────────────────
# SWI 10.1.12 was built from `dev-zone/swipl-devel` and installed to /usr/local on 2026-08-06,
# replacing the 9.0.4 apt packages. `library(wfs)` (`call_delays/2`, `delays_residual_program/2`),
# which `A_win_game.pl` needs, is core — no package build required for THIS test.
# See docs/specs/SWIPL_CAPABILITY_MAP_2026-08-06.md §0(a).
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _U_DIFF = Eval.UNDEFINED

"Run a MeTTa program then one query on a fresh space, tabling reset (tabling state is global)."

# 🔴 THE BOTTOM IS RESIDUATED SINCE 2026-08-17 (roadmap 7.A), SO EQUALITY TO `UNDEFINED` IS NO LONGER
# THE RIGHT TEST. `WFSBottom` now carries the DNF of literals it is waiting on, so a bottom produced
# by a real derivation is NOT `==` to the bare constant — `Atom[undefined] == Atom[U]` fails while
# both print "undefined". That was the predicted fallout of the sweep, and it is a TEST-LAYER
# instance of the same defect the sweep fixed in src: `== UNDEFINED` was always a TYPE test wearing a
# value test's clothes.
#
# This file compares TRUTH VALUES, not reasons — the residual is `test_delays.jl`'s subject — so the
# harness canonicalises every bottom to the bare constant on the way out. That keeps each assertion
# below reading as it did and confines the change to one place, rather than rewriting 17 comparisons
# into something less legible. `[[feedback_recurring_defect_derive_the_rule]]`
_wfs_diff_canonical(xs::Vector{Atom})::Vector{Atom} =
    Atom[Eval.is_undefined(x) ? Eval.UNDEFINED : x for x in xs]

function _wfs_diff(prog::AbstractString, query::AbstractString)::Vector{Atom}
    Eval.untable_all!()
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, prog)
    _wfs_diff_canonical(load_metta!(s, query))
end

"""
    _swipl_classify(pl_file) -> Dict{String,String}

Run `swipl -q <pl_file>` and parse its `classify/2` report into `goal => "true"|"false"|"undefined"`.

`A_win_game.pl` prints one line per goal via `format("~w~t~20|=> ~w~n", [Goal, R])`, e.g.

    win(a)              => true
    win(c)              => undefined

Returns an EMPTY dict on any failure (missing binary, non-zero exit, unparseable output) — the
caller's positive control turns that into a visible failure rather than a silent pass.
"""
function _swipl_classify(pl_file::AbstractString)::Dict{String,String}
    out = Dict{String,String}()
    swipl = Sys.which("swipl")
    swipl === nothing && return out
    txt = try
        # `-q` suppresses the banner; the program's own `:- initialization(main)` halts.
        read(`$swipl -q $pl_file`, String)
    catch
        return out
    end
    for line in split(txt, '\n')
        m = match(r"^\s*(\w+\([^)]*\))\s*=>\s*(true|false|undefined)\s*$", line)
        m === nothing && continue
        out[m.captures[1]] = m.captures[2]
    end
    out
end

"Core's answer for a goal, classified into SWI's vocabulary."
function _core_classify(answers::Vector{Atom})::String
    isempty(answers)             && return "false"
    answers == Atom[_U_DIFF]     && return "undefined"
    answers == Atom[Sym("True")] && return "true"
    "other:" * string(answers)   # anything else is a real divergence, reported verbatim
end

@testset "WFS `tnot` — LIVE differential vs SWI-Prolog (not pinned literals)" begin
    oracle_dir = joinpath(@__DIR__, "..", "oracle", "wfs")
    pl = normpath(joinpath(oracle_dir, "A_win_game.pl"))
    swipl = Sys.which("swipl")

    if swipl === nothing
        @test_skip "swipl NOT ON PATH — the WFS differential did not run. Build it: see " *
                   "docs/specs/SWIPL_CAPABILITY_MAP_2026-08-06.md §0(a). NOT a pass."
    elseif !isfile(pl)
        @test_skip "oracle program missing: $pl — the WFS differential did not run. NOT a pass."
    else
        expected_goals = ["win($p)" for p in ("a", "b", "c", "d", "e", "f", "g", "h")]
        classified = _swipl_classify(pl)

        # ── POSITIVE CONTROL — prove the oracle produced something BEFORE trusting agreement.
        # Without this, a parse returning `Dict()` would run zero comparisons and the testset would
        # report green having verified nothing — precisely the defect this file exists to fix.
        @test length(classified) == length(expected_goals)
        @test sort(collect(keys(classified))) == sort(expected_goals)

        # ── The differential proper. Core must agree with SWI goal by goal.
        prA = raw"""
            !(table! win)
            (move a b) (move g h) (move f g) (move c c) (move d e) (move e d)
            (= (win $x) (match &self (move $x $y) (tnot (win $y))))
        """
        for p in ("a", "b", "c", "d", "e", "f", "g", "h")
            goal = "win($p)"
            haskey(classified, goal) || continue          # the control above already failed
            @test _core_classify(_wfs_diff(prA, "!(win $p)")) == classified[goal]
        end

        # ── The oracle must also EXERCISE all three truth values. A corpus that happened to contain
        # only `true` goals would agree trivially while proving nothing about `undefined`, which is
        # the value this whole lane exists to get right.
        vals = Set(values(classified))
        @test "true" in vals
        @test "false" in vals
        @test "undefined" in vals
    end
end
