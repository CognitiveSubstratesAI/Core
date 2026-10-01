# test_jit_head_op.jl — `(compile-head <name>)`: the link from the compiler to the RUNNING interpreter.
#
# 🔴 WHY THIS FILE EXISTS. Until 2026-09-18 NOTHING in `src/` ever called `Eval.compile_head!`.
# Every compiler stage worked in isolation and the last two links did not exist:
#
#   Frontend.lower_program → ANormal.translate_program → EmitJulia.emit_julia_program
#     → [MISSING] → compile_head! → compiled_head
#
# `emit_julia_program`'s only caller was a TEST; `compile_head!`'s only callers were TESTS. So
# `_COMPILED_HEADS` was ALWAYS EMPTY in production and `compiled_head` returned `nothing` on its
# first line, every time. PROVED BY SENTINEL rather than by reading call sites: the emitter's head
# counter was set to -1, `compile_run` was run, and -1 survived.
#
# ⇒ the compiler's coverage ratchet (FLOOR_TOTAL 396/1000) measured what the emitter WOULD ACCEPT in
# a harness, never what EXECUTES. This file pins the executing path instead.

using Test
using MeTTaCore
using MeTTaCore.Eval
const EV = MeTTaCore.Eval
const AT = MeTTaCore.StandardMeTTa   # `Atom`/`Sym`/`Grounded` are NOT in Main at this path

@testset "(compile-head …) — the compiler reaches the interpreter" begin

    @testset "the hook is installed — without it the op is a no-op that always says False" begin
        # `Eval` loads BEFORE every compiler module, so the op cannot call the emitter directly; the
        # compiler installs itself into `_JIT_HEAD_HOOK` at load. If that inversion ever breaks, the
        # op still ANSWERS — `False` — which would look like "nothing is compilable" rather than like
        # a wiring failure. Hence an explicit assertion on the hook itself.
        @test EV._JIT_HEAD_HOOK[] !== nothing
    end

    @testset "🔴 A HEAD ACTUALLY DISPATCHES COMPILED — answers preserved, seam FIRED" begin
        EV.uncompile_all!()
        EV.reset_jit_declined!()
        s = Space()
        EV.load_core_stdlib!(s)
        EV.load_metta!(s, "(= (inc \$x) (+ \$x 1))\n")
        @test !EV.is_compiled(:inc)
        before = EV.load_metta!(s, "!(inc 41)\n")

        @test occursin("True", string(EV.load_metta!(s, "!(compile-head inc)\n")))
        @test EV.is_compiled(:inc)

        after = EV.load_metta!(s, "!(inc 41)\n")
        @test string(before) == string(after)      # ANSWERS UNCHANGED — the only thing that matters
        @test EV.fired(:inc) >= 1                  # and the seam really was the one that answered
        EV.uncompile_all!()
    end

    @testset "a DECLINE is a normal outcome, counted, not an error" begin
        # Out-of-scope heads keep the interpreter. The COUNT is the honest denominator: a speedup on
        # the heads that compiled says nothing about what fraction of hot heads were in scope.
        EV.uncompile_all!()
        EV.reset_jit_declined!()
        s = Space()
        EV.load_core_stdlib!(s)
        EV.load_metta!(s, "(edge a b)\n(= (q \$x) (match &self (edge \$x \$y) \$y))\n")
        @test occursin("False", string(EV.load_metta!(s, "!(compile-head q)\n")))
        @test !EV.is_compiled(:q)
        @test EV.jit_declined() == 1
        @test !isempty(EV.load_metta!(s, "!(q a)\n"))     # still answers, interpreted
        EV.uncompile_all!()
    end

    @testset "an unknown head declines cleanly rather than throwing" begin
        EV.uncompile_all!()
        s = Space()
        EV.load_core_stdlib!(s)
        @test occursin("False", string(EV.load_metta!(s, "!(compile-head nosuchhead)\n")))
        EV.uncompile_all!()
    end

    @testset "🔴 TABLING STILL WINS over a compiled head" begin
        # `metta_instr` checks `is_tabled(atom)` and returns `tabled_eval` BEFORE any path that
        # reaches `rule_results` (and therefore before `compiled_head`). If that order ever inverted,
        # a head that is both tabled and compiled would LOSE ANSWER REUSE the moment it compiled —
        # turning a memoised evaluation back into an exponential one while a benchmark still happily
        # reported "compiled". Asserted here rather than left to the reading of two call sites.
        EV.uncompile_all!()
        s = Space()
        EV.load_core_stdlib!(s)
        EV.load_metta!(s, "(= (inc \$x) (+ \$x 1))\n")
        EV.load_metta!(s, "!(compile-head inc)\n")
        @test EV.is_compiled(:inc)

        EV.table!(:inc)   # ⚠️ Eval.table!, not MeTTaCore.table! — Tabling.jl is included INTO Eval
        try
            # 🔴 THE PROPERTY IS ANSWER REUSE, NOT BYPASS — and a first draft of this test asserted
            # the wrong one. `tabled_eval` does not skip evaluation; it MEMOISES it. So the compiled
            # seam being consulted ONCE, on the first call, is correct. What must hold is that the
            # SECOND call is served from the table and does not re-enter evaluation at all. Asserting
            # "never consulted" failed 1 == 0 and looked like a dispatch-order defect; it was a
            # misstated property. The dispatch order is fine — `metta_instr` checks `is_tabled` and
            # returns `tabled_eval` before any path that reaches `rule_results`.
            r1 = EV.load_metta!(s, "!(inc 41)\n")
            @test !isempty(r1)                              # tabling answers correctly
            @test occursin("42", string(r1))
            after_first = EV.fired(:inc)

            r2 = EV.load_metta!(s, "!(inc 41)\n")           # the SAME goal again
            @test string(r1) == string(r2)                  # same answer
            @test EV.fired(:inc) == after_first             # 🔴 served from the TABLE, not recomputed

            # 🔴 NEGATIVE CONTROL — without tabling, a repeat DOES re-enter the compiled seam. If
            # this did not hold, the assertion above would pass for the trivial reason that nothing
            # ever increments `fired`.
            EV.untable_all!()
            before_untabled = EV.fired(:inc)
            EV.load_metta!(s, "!(inc 41)\n")
            @test EV.fired(:inc) > before_untabled
        finally
            EV.untable_all!()
            EV.uncompile_all!()
        end
    end
end


# ── THE WEAK-KEY CLAIM, TESTED RATHER THAN ASSERTED IN A COMMENT ─────────────────────────────────
# `_SPACE_DEFS` is a `WeakKeyDict{Space, …}` whose comment claims a collected space "drops its WHOLE
# table". 🔴 A `WeakKeyDict` IS NOT AN EPHEMERON TABLE: anything reachable from an entry's VALUE that
# holds a STRONG reference to the key pins the space forever. So that claim is a property of the
# whole system, not of the data structure, and has to be measured.
#
# 🔴 MEASURE COLLECTION WITH A `WeakRef`, NOT WITH `length(_SPACE_DEFS)`. Dead entries are removed
# LAZILY — a finalizer on each key marks the dict for cleanup and finalizers run asynchronously — so
# a length can still count an entry whose space is already dead. A first version of this test used
# the length and was FLAKY: the same assertion passed as a probe and failed as a testset, and the
# explanation reached for (generational promotion) was wrong, since `GC.gc()` is a full collection.
# It was measuring "has the dict cleaned up yet", not "was the space collected".
@testset "a collected space drops its definition table — measured with a WeakRef" begin
    # The space is a LOCAL of this function and only its WeakRef escapes, so anything keeping it
    # alive afterwards is the system's doing, not the test's.
    function _mk(prog, call)
        s = Space(); EV.load_core_stdlib!(s)
        EV.load_metta!(s, prog)
        ok = occursin("True", string(EV.load_metta!(s, "!(compile-head pl)\n")))
        EV.load_metta!(s, call)                     # RUN it, so any lane state is actually set
        (ok, get(EV._HEAD_LANE, :pl, :none), WeakRef(s))
    end

    @testset "NATIVE head" begin
        EV.uncompile_all!(); GC.gc(); GC.gc()
        ok, lane, wr = _mk("(= (pl \$x) (+ \$x 1))\n", "!(pl 1)\n")
        @test ok                                    # ANTI-VACUITY: it really compiled
        @test lane === :native                      # ANTI-VACUITY: via the lane this case is about
        # 🔴 DO NOT DEREFERENCE THE WeakRef BEFORE COLLECTING. `@test wr.value !== nothing` was
        # here and made BOTH cases fail: reading `.value` materialises a STRONG reference into the
        # enclosing frame's slot, which can outlive the statement and root the very object the test
        # is about. The anti-vacuity it provided is already covered by `ok` and `lane` above — the
        # head compiled and ran, so the space certainly existed.
        GC.gc(); GC.gc()
        @test wr.value === nothing                  # ⇒ COLLECTED
    end

    @testset "PLAN-LANE head — no longer pinned by a global" begin
        # 🔴 THIS CASE FAILED BEFORE `_CUR_SPACE` WAS DELETED. `_head_closure` set that global
        # `Ref{Union{Nothing,Space}}` on entry and never restored it, so the most recent plan-lane
        # space was strongly reachable and never collected — its whole definition table with it.
        # Bounded (one space at a time), but unbounded in lifetime. The space is now an ARGUMENT
        # threaded through `_run_plan`/`_bind_step!`, so there is no global to pin it.
        EV.uncompile_all!(); GC.gc(); GC.gc()
        ok, lane, wr = _mk("(= (pl (stv \$a \$b)) (* \$a \$b))\n", "!(pl (stv 2.0 3.0))\n")
        @test ok
        @test lane === :plan                        # ANTI-VACUITY: head patterns decline codegen
        # 🔴 DO NOT DEREFERENCE THE WeakRef BEFORE COLLECTING. `@test wr.value !== nothing` was
        # here and made BOTH cases fail: reading `.value` materialises a STRONG reference into the
        # enclosing frame's slot, which can outlive the statement and root the very object the test
        # is about. The anti-vacuity it provided is already covered by `ok` and `lane` above — the
        # head compiled and ran, so the space certainly existed.
        GC.gc(); GC.gc()
        @test wr.value === nothing                  # ⇒ COLLECTED, the pin is gone
    end
end
