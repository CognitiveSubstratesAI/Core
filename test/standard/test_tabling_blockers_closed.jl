# test_tabling_blockers_closed.jl — the roadmap §0 BLOCKERS, each checked BY THE CHECK IT NAMES.
#
# WHY THIS FILE EXISTS (2026-09-09). `Core/docs/TABLING_ROADMAP.md` §0 read "these gate other work,
# and two are live defects" for weeks after both were fixed, and a session ranked its whole day off
# that line. The roadmap warns about this shape in its own READ-FIRST banner — *"a banner states a
# verdict at a point in time and is refreshed by hand"* — which is the argument for a test instead
# of a row: a row goes stale silently, a test goes RED.
#
# 🔴 EACH TESTSET RUNS THE ROADMAP ROW'S OWN VERBATIM CHECK, not a proxy for it. If one of these
# fails, the corresponding row is live again and the roadmap header must be re-corrected.
using MeTTaCore
using Test

const _TBC = MeTTaCore.Eval
const _TBC_FIB = "(= (fib \$n) (if (< \$n 2) \$n (+ (fib (- \$n 1)) (fib (- \$n 2)))))\n"

@testset "roadmap §0 BLOCKERS stay closed" begin

    # §0.1 — "assert `:fib` pure in IL form".
    # The row's claim: EmitIL emits `(function (chain (metta …) …))`, none of those ops was in
    # `_PURE_PRIMS`, and `_pure_heads` is a WHITELIST fixpoint ⇒ every compiled head came back impure
    # ⇒ every purity-gated consumer (`auto_table!` among them) was silently inert on the compiled lane.
    @testset "0.1 — a COMPILED head classifies PURE, not just its source form" begin
        sp = _TBC.Space()
        _TBC.load_core_stdlib!(sp)
        _TBC.load_metta!(sp, _TBC_FIB)
        pure_src = _TBC._pure_heads(_TBC._rules_of(_TBC.all_atoms(sp)))
        @test :fib in pure_src                       # source form was never the problem

        r = MeTTaCore.compile_run(_TBC_FIB * "!(fib 10)\n"; max_steps = 512_000)
        @test r.compiled > 0                         # a VACUOUS pass if nothing compiled
        @test hasproperty(r, :space)

        il = _TBC.all_atoms(r.space)
        # pin that we are actually looking at LOWERED IL, not the source rule — otherwise this
        # testset would pass for the wrong reason the day the lane stops emitting IL here.
        @test any(a -> occursin("(function (chain", string(a)), il)
        @test :fib in _TBC._pure_heads(_TBC._rules_of(il))     # ← the assertion 0.1 names
    end

    # §0.3 — "two `compile_run` calls in one process; assert the second is unaffected".
    # `_TABLED_HEADS` is process-global; the guard is the snapshot/restore at CompileLane.jl:910-913
    # and :971-972. Without it, one `compile_run` changes the NEXT caller's semantics.
    @testset "0.3 — a compile_run does not leak _TABLED_HEADS into the next caller" begin
        _TBC.untable_all!()
        before = copy(_TBC._TABLED_HEADS)
        @test isempty(before)

        MeTTaCore.compile_run(_TBC_FIB * "!(fib 10)\n"; max_steps = 512_000, auto_table = true)
        @test copy(_TBC._TABLED_HEADS) == before     # restored, not leaked

        r2 = MeTTaCore.compile_run(_TBC_FIB * "!(fib 10)\n"; max_steps = 512_000, auto_table = true)
        @test _TBC._TABLED_HEADS == before
        @test [string(a) for (_, ans) in r2.answers for a in ans] == ["55"]   # …and still CORRECT
    end
end
