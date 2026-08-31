# test_intercept_position.jl — THE INTERCEPT BELONGS AT THE LATEST POINT THAT STILL PRECEDES DERIVATION.
#
# ─── THE INVARIANT ───────────────────────────────────────────────────────────────────────────────
# `tabled_eval` is spliced into `metta_instr`'s dispatch chain (Eval.jl:1196). Everything DOWNSTREAM
# of that splice is skipped for a tabled head. So the rule is:
#
#     everything that can CHANGE the answer must be UPSTREAM of the intercept;
#     only things that CONSUME the answer may be downstream.
#
# Type errors are answers. NotReducible is an answer. Three violations found so far, and the rule
# retro-explains all three:
#
#   1. the `metta-noreduce` backstop (Eval.jl:1198-1205) — FIXED `d1d872f` via a mode split
#   2. the TYPED-FUNCTION path (Eval.jl:1212-1226) — `type_check_errors` never runs for a tabled head
#   3. `_reduced_goal` (Tabling.jl) — re-implements argument reduction and drifts from
#      `interpret_args_instr`, in two independent ways (see below)
#
# ⚠️ THE DISEASE IS THAT `tabled_eval` IS A BYPASS THAT RE-IMPLEMENTS WHAT IT SKIPPED, rather than a
# WRAPPER around the untouched path. Each re-implementation drifts, and each drift stays invisible
# until a corpus query lands on it. Converting bypass→wrapper is the real fix; the per-instance
# repairs below are stepping stones and should say so.
#
# ─── WHY `@test_broken` ──────────────────────────────────────────────────────────────────────────
# These assert the CORRECT (post-fix) values and are expected to FAIL today. Written BEFORE the fix
# deliberately: a prediction recorded after the run is a description, which is exactly the failure
# mode that produced two reverts on 2026-08-30. When a fix lands, Julia reports "Unexpectedly Passed"
# and the suite goes red — that is the signal to drop the `_broken`, not a regression.
using MeTTaCore
using MeTTaCore.Eval
using Test

const _IP_CORPUS = joinpath(@__DIR__, "..", "..", "oracle", "leatta", "corpus", "b5_types_prelim.metta")

"Definitions only (no `!` directives) from a corpus file."
function _ip_defs(path::AbstractString)
    txt = read(path, String)
    join([f for (bang, f) in MeTTaCore.mm2_split_forms(txt) if !bang], "\n")
end

"Answer `q` against `defs`, with auto-tabling ON."
function _ip_tabled(defs::AbstractString, q::AbstractString)
    Eval.untable_all!()
    s = Eval.Space(); load_core_stdlib!(s); load_metta!(s, defs)
    Eval.auto_table!(s)
    r = load_metta!(s, q)
    Eval.untable_all!()
    string(r)
end

@testset "intercept position: TYPE ERRORS ARE ANSWERS (b5_types_prelim)" begin
    # ⚠️ ASSERTED, NOT SKIPPED. `isfile(...) || return` would make a path slip report ZERO tests and
    # PASS — the vacuity failure this file exists to avoid, since its whole value is going RED on a
    # flip. The `..`/`..` climb from a freshly-created directory is exactly where that slips.
    @test isfile(_IP_CORPUS)
    defs = _ip_defs(_IP_CORPUS)
    # `(: eq (-> $t $t Type))` and `(: of-same-type (-> $t $t Type))` are POLYMORPHIC: both arguments
    # must share a type. The untabled path rejects these with BadArgType; the tabled path never runs
    # `type_check_errors` (Eval.jl:1226 is 30 lines BELOW the intercept), so it answers `T` — a WRONG
    # ANSWER, not merely a lost one.
    #
    # PREDICTION, pinned 2026-08-30: these three are fixed by HOISTING the type check above the
    # intercept; the fourth testset's case is NOT, because its cause is `_reduced_goal`.
    # BOTH DIRECTIONS. `@test_broken` records Broken for a FALSE result AND for a THROWN error, so
    # it alone cannot distinguish "wrong answer for the reason we named" from "wrong for a third
    # mechanism" or "crashed". The plain `@test` pins TODAY'S wrong value, so a new mechanism turns
    # this file RED immediately instead of hiding inside the Broken count. Same discipline as the
    # anti-vacuity probes elsewhere: observe the event, not its residue.
    @test occursin("(eq Z S)", _ip_tabled(defs, "!(eq Z S)\n"))                       # today: the call itself
    @test_broken occursin("BadArgType", _ip_tabled(defs, "!(eq Z S)\n"))
    @test _ip_tabled(defs, "!(of-same-type Green Color)\n") == "MeTTaCore.StandardMeTTa.Atom[T]"
    @test_broken occursin("BadArgType", _ip_tabled(defs, "!(of-same-type Green Color)\n"))
    @test _ip_tabled(defs, "!(of-same-type Green Circle)\n") == "MeTTaCore.StandardMeTTa.Atom[T]"
    @test_broken occursin("BadArgType", _ip_tabled(defs, "!(of-same-type Green Circle)\n"))
end

@testset "intercept position: NotReducible survives an Atom-typed (LAZY) parameter" begin
    @test isfile(_IP_CORPUS)
    defs = _ip_defs(_IP_CORPUS)
    # `(: eqa (-> Atom Atom Type))` — Atom-typed, so arguments must stay UNEVALUATED. Untabled,
    # `(Add Z Z)` is not reduced, `Z` does not match it, and the call returns ITSELF. Tabled,
    # `_reduced_goal` reduces it to `Z`, the call becomes `(eqa Z Z)`, and `(= (eqa $x $x) T)` fires.
    #
    # PREDICTION: the type-check hoist does NOT fix this one. If it does, the `_reduced_goal` theory
    # is weaker than the isolated repros below suggest.
    @test _ip_tabled(defs, "!(eqa Z (Add Z Z))\n") == "MeTTaCore.StandardMeTTa.Atom[T]"   # today: wrongly matches
    @test_broken occursin("(eqa Z (Add Z Z))", _ip_tabled(defs, "!(eqa Z (Add Z Z))\n"))
end

@testset "_reduced_goal: two defects, minimal repros (no corpus needed)" begin
  try
    # Both need an EXPLICIT `table!` to reach `_reduced_goal`: the auto-table gate refuses these
    # heads for unrelated reasons (`got`/`held` are undefined ⇒ impure). A future reader must not
    # conclude from a green auto_table! run that these paths are unreachable.
    #
    # DEFECT A — `rs[1]` keeps only the FIRST answer, so a multivalued ARGUMENT is truncated at the
    # tabling boundary.
    Eval.untable_all!()
    s = Eval.Space(); load_core_stdlib!(s)
    load_metta!(s, "(= (bin) A)\n(= (bin) B)\n(= (wrap \$x) (got \$x))\n")
    Eval.table!(:wrap)
    @test_broken length(load_metta!(s, "!(wrap (bin))\n")) == 2      # untabled gives [(got B), (got A)]
    Eval.untable_all!()

    # DEFECT B — an `Atom`-typed parameter is LAZY, but `_reduced_goal` reduces every non-Var
    # argument unconditionally. Produces a WRONG ANSWER, not a lost one.
    s2 = Eval.Space(); load_core_stdlib!(s2)
    load_metta!(s2, "(: keep (-> Atom Atom))\n(= (keep \$x) (held \$x))\n(= (bin) A)\n(= (bin) B)\n")
    Eval.table!(:keep)
    @test occursin("(held B)", string(load_metta!(s2, "!(keep (bin))\n")))   # today: evaluated AND truncated
    @test_broken occursin("(held (bin))", string(load_metta!(s2, "!(keep (bin))\n")))
  finally
    # `_TABLED_HEADS` is PROCESS-GLOBAL. A throw above would leak :wrap/:keep into every file that
    # runs after this one in the same process — the leak `reset_execution_flags!` exists to prevent.
    Eval.untable_all!()
  end
end
