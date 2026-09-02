# test_mm2_zam_gates.jl — the ZAM safe-subset gates, and gate (5) in particular.
#
# ─── WHY THIS FILE EXISTS ────────────────────────────────────────────────────────────────────────
# `mm2_zam_answers` was live in 5 source files with ZERO tests (verified 2026-09-02). Its gate (5)
# discriminator was found BY A REGRESSION, not by reasoning — CODEMAP's own row records that a first
# cut of the gate rejected every multi-clause chaining head and broke a case the suite already
# locked: *"the suite knew something the repro did not."* Nothing locked the discriminator itself.
#
# ─── THE DISCRIMINATOR ───────────────────────────────────────────────────────────────────────────
# A multi-clause head is safe on the ZAM iff its clauses AGREE about chaining:
#   ALL clauses chain  -> safe      NONE chains -> safe      MIXED -> UNSAFE, LOSES ANSWERS
#
# The witness, from the original regression:
#     (= (z $x) (a $x))   (= (z $x) (t $x))   (= (a $x) (m $x))
# `z` has two clauses; one chains through `a`, one does not. ZAM serves ["(t 1)"]; the interpreter
# oracle says ["(m 1)", "(t 1)"]. The (m 1) is silently LOST — a wrong answer, not an error.
#
# ⚠️ THE TRAP THIS FILE IS SHAPED AROUND: asserting only "MIXED is declined" passes VACUOUSLY if the
# gate declines everything — which is exactly the over-rejection bug that already happened once. So
# every decline assertion is paired with a POSITIVE CONTROL that must be SERVED, and the served
# answers are differentialled against the interpreter.
using MeTTaCore
using Test

const _ZG_V = MeTTaCore.Eval

"""
Interpreter oracle for one bang over one program — the answers the ZAM must not disagree with.

⚠️ FORM CONVENTIONS, both of which cost this file a failing first run:
  * `mm2_split_forms` yields `(is_bang, form)` where `form` has NO leading `!`, and
    `mm2_zam_answers` takes its bangs in that SAME bare form (`mm2_route!` calls `mm2_head(b)`
    straight on them). Passing `"!(z 1)"` makes every gate decline and the whole file pass
    vacuously — which is exactly what happened.
  * evaluation is `load_metta!(sp, "!" * form)`; there is no `eval_metta`.
"""
function _zg_oracle(program::AbstractString, bang::AbstractString)::Vector{String}
    sp = _ZG_V.Space()
    _ZG_V.load_core_stdlib!(sp)
    for (isbang, f) in MeTTaCore.mm2_split_forms(program)
        isbang || _ZG_V.load_metta!(sp, f)
    end
    res = _ZG_V.load_metta!(sp, "!" * String(strip(bang)))
    sort(String[string(x) for y in res for x in (y isa AbstractVector ? y : [y])])
end

_served_answers(r, bang) = begin
    hit = filter(p -> strip(first(p)) == strip(bang), r.served)
    isempty(hit) ? nothing : sort(String.(last(first(hit))))
end

@testset "ZAM safe-subset gates" begin

    @testset "gate 5 — MIXED chaining is DECLINED (it would lose answers)" begin
        prog = """
        (= (z \$x) (a \$x))
        (= (z \$x) (t \$x))
        (= (a \$x) (m \$x))
        """
        bang = "(z 1)"
        r = MeTTaCore.mm2_zam_answers(prog, [bang])

        @test _served_answers(r, bang) === nothing      # not served
        @test any(b -> strip(b) == strip(bang), r.remaining)   # handed to the fallback

        # WHY it must decline: the oracle has an answer the ZAM lowering drops.
        oracle = _zg_oracle(prog, bang)
        @test "(m 1)" in oracle
        @test length(oracle) > 1
    end

    @testset "POSITIVE CONTROL — ALL clauses chain (forward-lex): served, agrees with oracle" begin
        # Head names ASCEND along the chain (a -> p,q -> m,n). See the order-dependence testset
        # below for why that is load-bearing and not cosmetic.
        prog = """
        (= (a \$x) (p \$x))
        (= (a \$x) (q \$x))
        (= (p \$x) (m \$x))
        (= (q \$x) (n \$x))
        """
        bang = "(a 1)"
        r = MeTTaCore.mm2_zam_answers(prog, [bang])
        got = _served_answers(r, bang)
        @test got !== nothing            # NOT vacuous: the gate DOES serve multi-clause chaining
        @test got == _zg_oracle(prog, bang)
    end

    @testset "ALL-chain admission is TRIE-ORDER DEPENDENT — and fails SAFE" begin
        # 🔴 FOUND 2026-09-02 while writing this file, and NOT documented at the gate.
        #
        # Execs are selected in TRIE (lexicographic) order, and an exec is CONSUMED when selected
        # whether or not it matched. So a downstream rule whose head sorts BEFORE its upstream head
        # is selected and destroyed before the atom it needs exists. The gate's own worked example
        # (h -> p) happens to ascend, which is why "ALL chain is safe" reads as unconditional.
        #
        # MEASURED, same program shape, only the head NAMES differ:
        #   a -> p,q -> m,n   (ascending)   SERVED   ["(m 1)", "(n 1)"]   <- previous testset
        #   z -> a,b -> m,n   (descending)  DECLINED, falls back to the interpreter
        #
        # ⇒ This is a COMPLETENESS limit, not a soundness bug: the descending case is DECLINED, not
        # served truncated. This test pins the SAFE half. If a future change ever makes the
        # descending case SERVE, that is a wrong answer of exactly the class gate 5 exists to stop,
        # and this test turns red.
        prog = """
        (= (z \$x) (a \$x))
        (= (z \$x) (b \$x))
        (= (a \$x) (m \$x))
        (= (b \$x) (n \$x))
        """
        bang = "(z 1)"
        r = MeTTaCore.mm2_zam_answers(prog, [bang])
        got = _served_answers(r, bang)
        @test got === nothing                                   # declined, not served
        @test any(b -> strip(b) == strip(bang), r.remaining)     # handed to the fallback
        # and if it ever IS served, it must be the oracle's answer, never a truncation
        @test got === nothing || got == _zg_oracle(prog, bang)
    end

    @testset "POSITIVE CONTROL — NO clause chains: served, and agrees with the oracle" begin
        prog = """
        (= (z \$x) (t \$x))
        (= (z \$x) (u \$x))
        """
        bang = "(z 1)"
        r = MeTTaCore.mm2_zam_answers(prog, [bang])
        got = _served_answers(r, bang)
        @test got !== nothing
        @test got == _zg_oracle(prog, bang)
    end

    @testset "single-clause chaining head is served (the simplest chain)" begin
        prog = "(= (a \$x) (m \$x))\n"
        bang = "(a 1)"
        r = MeTTaCore.mm2_zam_answers(prog, [bang])
        got = _served_answers(r, bang)
        @test got !== nothing
        @test got == _zg_oracle(prog, bang)
    end
end
