# test_ab_space_collision.jl — THE CHUNK-017 GATE. Program A's `outer` must keep answering 2 after
# an unrelated program B, in its OWN space, compiles its own `inner`.
#
# 🔴 WRITTEN TO FAIL, AND CONFIRMED FAILING AT 101 BEFORE THE REGISTRY WAS TOUCHED. A test first
# seen passing cannot show it would have caught the bug; this one was run red first, deliberately.
#
# ─── WHY THE OBVIOUS VERSION OF THIS TEST PASSES, AND PROVES NOTHING ────────────────────────────
# MEASURED 2026-10-01. Compiling A's heads ONE AT A TIME — the production `(compile-head …)` path —
# does NOT collide: A still answers 2, with `COMPILED_FALLBACK_STALE == 1`. The CHUNK-002 gate works
# exactly as designed there: `compiled_head` sees B's `CompiledHead` carries a different `space`
# WeakRef, re-hashes A's clause set for `:inner`, finds it differs, and hands the call back to the
# interpreter.
# ⇒ A test written that way is GREEN TODAY and would stay green through a broken rewrite. It must
# use the WHOLE-PROGRAM emit, where `outer` and `inner` are compiled TOGETHER.
#
# ─── WHY THAT ONE COLLIDES: THE SEAM IS NOT ON THE PATH ─────────────────────────────────────────
# `EmitJuliaCode._genname(sym) = Symbol("_gen_", sym, "_", hash(sym)…)` hashes THE NAME ONLY, so
# every space's `inner` generates the SAME Julia function, `_gen_inner_664621`. When heads compile
# together, `outer`'s generated body NAMES THAT ENTRY DIRECTLY (EmitJulia.jl:281) instead of
# re-entering `rule_results`. B's compilation then redefines that function, and A's `outer` silently
# calls B's body. MEASURED: A answers 101, and `COMPILED_FALLBACK_STALE == 0` — THE GATE NEVER FIRED,
# because a direct call never reaches the seam it lives on.
#
# ⇒ THE BUG IS LATENT, NOT FIXED, and it is not reachable from `jit_head!` today only because that
# compiles ONE head at a time. 🔴 THE PLANNED HOTNESS TRIGGER MAKES IT LIVE: C2 says a hot head must
# be compiled TOGETHER WITH THE HEADS IT CALLS, which is precisely this path. That is the mechanism
# behind "CHUNK-017 first" — every later step widens the exposure.
#
# ─── WHAT A FIX MUST COVER — BOTH HALVES ────────────────────────────────────────────────────────
#   1. the REGISTRY: a per-space definition record keyed by (head, arity), replacing the global
#      name-keyed `_COMPILED_HEADS`;
#   2. the CODEGEN NAMESPACE: `_genname` must carry space identity too, or two spaces keep colliding
#      in the Julia module namespace no matter how the registry is keyed.
# A fix that does only (1) will still fail this test.
using Test
using MeTTaCore
const EV = MeTTaCore.Eval
const V = MeTTaCore.StandardMeTTa
const F = MeTTaCore.CompilerFrontend
const AN = MeTTaCore.CompilerANormal
const EJ = MeTTaCore.CompilerEmitJulia

"Every `(= …)` atom in `sp` — what `jit_head!` collects, but for the whole program at once."
function _abc_rules(sp)
    rs = V.Atom[]
    for a in EV.all_atoms(sp)
        a isa V.Expression && length(a.children) == 3 || continue
        h = a.children[1]
        (h isa V.Sym && String(h.name) == "=") || continue
        push!(rs, a)
    end
    rs
end

"Compile every head of `sp` TOGETHER and register them against `sp`."
function _abc_compile_together!(sp)
    rs = _abc_rules(sp)
    fns = EJ.emit_julia_program(AN.translate_program(F.lower_program(rs)))
    key = hash(rs)
    for (h, fn) in fns
        EV.compile_head!(h, fn, key, sp)
    end
    fns
end

_abc_answer(sp, q) = [string(x) for x in EV.load_metta!(sp, q)]

@testset "A/B cross-space collision — B's `inner` must not answer A's `outer`" begin
    EV.uncompile_all!()
    EV.COMPILED_FALLBACK_STALE[] = 0

    a = EV.Space()
    EV.load_core_stdlib!(a)
    EV.load_metta!(a, "(= (inner \$x) (+ \$x 1))\n(= (outer \$x) (inner \$x))\n")

    # ANTI-VACUITY: the scenario must be live before the collision can mean anything.
    @test _abc_answer(a, "!(outer 1)\n") == ["2"]

    fnsA = _abc_compile_together!(a)
    @test haskey(fnsA, :outer) && haskey(fnsA, :inner)      # both really compiled, together
    @test _abc_answer(a, "!(outer 1)\n") == ["2"]           # and A is still right on its own

    # An UNRELATED program, its own space, same head NAME, different body.
    b = EV.Space()
    EV.load_core_stdlib!(b)
    EV.load_metta!(b, "(= (inner \$x) (+ \$x 100))\n")
    fnsB = _abc_compile_together!(b)
    @test haskey(fnsB, :inner)                              # B really did compile its own `inner`

    # 🔴 THE GATE. Fails at ["101"] until the definition record AND `_genname` carry space identity.
    @test _abc_answer(a, "!(outer 1)\n") == ["2"]

    # B must also be right — a fix that isolates by breaking B is not a fix.
    @test _abc_answer(b, "!(inner 1)\n") == ["101"]
end
