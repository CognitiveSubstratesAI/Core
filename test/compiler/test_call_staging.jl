# test_call_staging.jl — the staged call convention must FIRE, not merely emit.
#
# ─── WHY THIS FILE EXISTS, AND WHY ITS ASSERTIONS LOOK ODD ───────────────────────────────────────
# The first version of this test passed 4/4 against a BROKEN implementation. It ran
#
#     (= (f) (g))   (= (g) 42)
#
# and asserted the dump contained `42`. It does — but `42` is what `(g)` produces on its OWN, by
# ordinary reduction, whether or not `(f)` ever consumed it. At that moment the leaf clause published
# no `(=val …)` at all, so the consume rule could never match, and the test could not see it.
#
# So every assertion here is DISCRIMINATING: the expected value is one that ONLY the consumer can
# produce. `(= (f) (let $v (g) done))` yields `done`, which `(g)` cannot emit under any circumstance.
# If staging is broken, `done` is absent. Pair that with a NEGATIVE assertion — the redex `(f)` must
# be GONE — because a rule that emits and never fires leaves its redex behind.
#
# A value the callee produces anyway is not evidence about the caller.
#
# ─── THE CONVENTION UNDER TEST ───────────────────────────────────────────────────────────────────
# An MM2 reduction consumes its redex and adds a BARE value, so `(= (g) 42)` turns `(g)` into `42`
# and never creates anything a caller could match. Staging adds a KEYED result:
#
#   DEMAND   (exec d (, (f)) (O (+ (g))))
#   PRODUCE  (exec p (, (g)) (O (+ 42) (+ (=val (g) 42))))
#   CONSUME  (exec q (, (f) (=val (g) $t)) (O (+ $t) (+ (=val (f) $t))))
#   CLEANUP  (exec c (, (=val $k $v)) (O (- (=val $k $v))))
#
# Stage numbers come from call DEPTH — demands descend, produce/consume ascend — and the scheme
# degenerates to the previous two-stage form when nothing is staged, which `REGRESSION` below pins.
using MeTTaCore
using Test

const _SF = MeTTaCore.CompilerFrontend
const _SA = MeTTaCore.CompilerANormal
const _SE = MeTTaCore.CompilerEmit
const _SI = MeTTaCore.Eval

function _stage_parse(sp, text::AbstractString)
    toks = _SI.tokenize(text); i = Ref(1); out = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _SI.parse_from(toks, i, sp.tokens))
    end
    out
end

"Compile `src`, load it plus `seed` into a REAL MORK space, run the calculus, return the dump."
function _stage_run(src::AbstractString, seed::AbstractString)
    sp = _SI.Space(); _SI.load_core_stdlib!(sp)
    cls = _SA.translate_program(_SF.lower_program(_stage_parse(sp, src)))
    r = _SE.emit_program(cls)
    cs = MeTTaCore.new_core_space()
    MeTTaCore.space_add_all_sexpr!(cs.inner, seed)
    for rule in r.rules
        MeTTaCore.space_add_all_sexpr!(cs.inner, rule)
    end
    MeTTaCore.space_metta_calculus!(cs.inner, 1_000_000)
    (dump = MeTTaCore.space_dump_all_sexpr(cs.inner), result = r)
end

@testset "staged call convention — emitted rules must FIRE" begin

    @testset "depth-1: caller consumes callee's keyed result" begin
        # `done` is unreachable for (g); its presence proves (f) consumed (=val (g) 42).
        d, r = _stage_run("(= (f) (let \$v (g) done))\n(= (g) 42)\n", "(f)")
        @test r.emitted == 2
        @test r.staged == 1
        @test occursin("done", d)          # the consumer fired
        @test !occursin("(f)", d)          # and its redex was cleaned up
    end

    @testset "depth-2: the chain composes" begin
        d, r = _stage_run("(= (f) (let \$v (g) done))\n(= (g) (let \$w (h) mid))\n(= (h) 42)\n", "(f)")
        @test r.staged == 2
        @test occursin("mid", d)           # g consumed h
        @test occursin("done", d)          # f consumed g — the whole chain, not just one hop
        @test !occursin("(f)", d)
    end

    @testset "arguments flow through the call" begin
        d, _ = _stage_run("(= (twice \$x) (id \$x))\n(= (id \$y) \$y)\n", "(twice 7)")
        @test occursin("7", d)
        @test !occursin("(twice 7)", d)
    end

    @testset "an ARITHMETIC callee publishes too" begin
        # The pure-sink path needed its own publish: the keyed result is a SECOND `pure` sink over the
        # same expression, because `pure`'s first argument is the template (grounding.mm2:36-40).
        d, _ = _stage_run("(= (f) (let \$v (a) done))\n(= (a) (+ 1 2))\n", "(f)")
        @test occursin("3", d)             # the arithmetic still evaluates
        @test occursin("done", d)          # AND its caller could consume it
    end

    @testset "RECURSION is declined, never mis-staged" begin
        # A stage number comes from call DEPTH and a cycle has none. Emitting one with a made-up depth
        # would fire once and then silently stop — worse than declining, because coverage would count
        # it as compiled.
        sp = _SI.Space(); _SI.load_core_stdlib!(sp)
        cls = _SA.translate_program(_SF.lower_program(_stage_parse(sp, "(= (loop \$n) (loop \$n))\n")))
        r = _SE.emit_program(cls)
        @test r.emitted == 0
        @test length(r.declined) == 1
    end

    @testset "REGRESSION: call-free nondeterminism survives" begin
        # Two clauses matching one redex must BOTH contribute. This is what the add-then-cleanup split
        # protects, and the staged numbering must not disturb it.
        d, r = _stage_run("(= (f 0) zero)\n(= (f \$x) other)\n", "(f 0)")
        @test r.staged == 0
        @test occursin("zero", d)
        @test occursin("other", d)
    end

    @testset "REGRESSION: numbering degenerates when nothing is staged" begin
        # With no calls anywhere, lmax == 0, so PRODUCE lands on `priority` and CLEANUP on
        # `priority + 1` — byte-identical to the pre-staging two-stage scheme.
        sp = _SI.Space(); _SI.load_core_stdlib!(sp)
        cls = _SA.translate_program(_SF.lower_program(_stage_parse(sp, "(= (c) 1)\n")))
        r = _SE.emit_program(cls)
        @test r.staged == 0
        @test any(x -> startswith(x, "(exec 0 "), r.rules)
        @test any(x -> startswith(x, "(exec 1 "), r.rules)
        @test !any(x -> occursin("=val", x), r.rules)   # nothing calls (c), so nothing is published
    end
end

# ── PRIORITY IS THE CALL ORDER, AND GETTING IT BACKWARDS IS SILENT ───────────────────────────────
# Characterisation of the MM2 semantics any staging scheme must respect. Not a test of the emitter —
# the emitter does not produce these yet — but of the CONSTRAINT it will be generating against, and
# of the failure mode that constraint exists to prevent.
#
# MEASURED BY HAND 2026-08-15. Same two rules, same redex, only the priorities swapped:
#
#   callee LAST  (correct)   (green a) -> (frog a) -> True          ✅
#   callee FIRST (inverted)  (green a) -> (frog a) -> STUCK          🔴 wrong answer, NO error
#
# The inverted case fails because an exec is CONSUMED when selected whether or not it matched
# (MORK.wiki Minimal-MeTTa-2; upstream space.rs `btm.remove` precedes `interpret`). frog's rule is
# selected first, matches nothing — no `(frog …)` atom exists yet — and is destroyed. green then
# rewrites its redex to `(frog a)`, and the rule that would reduce it is gone.
#
# There is no error, no exhaustion, no diagnostic: the trie simply holds an unreduced atom. That is
# why the staged numbering is not cosmetic, and it is the regression this pins.
@testset "STAGING INVARIANT — a callee's exec must be selected AFTER its caller's" begin
    _mk() = MeTTaCore.new_core_space()
    _run(execs, redex) = begin
        cs = _mk()
        for e in execs; MeTTaCore.space_add_all_sexpr!(cs.inner, e); end
        MeTTaCore.space_add_all_sexpr!(cs.inner, redex)
        MeTTaCore.core_calculus!(cs, 1_000)
        [strip(l) for l in split(MeTTaCore.space_dump_all_sexpr(cs.inner), '\n')
         if !isempty(strip(l)) && !startswith(strip(l), "(exec")]
    end
    green_first = "(exec 0 (, (green \$x)) (O (+ (frog \$x)) (- (green \$x))))"
    frog_second = "(exec 1 (, (frog \$y)) (O (+ True) (- (frog \$y))))"
    green_last  = "(exec 1 (, (green \$x)) (O (+ (frog \$x)) (- (green \$x))))"
    frog_first  = "(exec 0 (, (frog \$y)) (O (+ True) (- (frog \$y))))"

    # CORRECT: caller at the lower priority, so it is selected first and the callee's rule survives.
    @test _run([green_first, frog_second], "(green a)") == ["True"]

    # INVERTED: the callee is selected first, matches nothing, and is consumed. POSITIVE CONTROL for
    # the failure — without this the test above would pass for a scheme that happened to work once.
    stuck = _run([frog_first, green_last], "(green a)")
    @test stuck == ["(frog a)"]      # the redex was rewritten and then stranded
    @test stuck != ["True"]          # stated separately: this is a WRONG ANSWER, not a slow one
end
