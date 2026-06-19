# MeTTa-IL lane (src/standard/MeTTaIL.jl) — the F1R3FLY layered track: MeTTa-IL → MM2 → MORK,
# bisimulation-gated against the interpreter-spec.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "MeTTa-IL lane (MeTTa-IL → MM2 → MORK)" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"

    @testset "def lowering: (def … (match PAT… (emit OUT))) → (exec …)" begin
        d = raw"(def trans () (match (edge $x $y) (edge $y $z) (emit (trans $x $z))))"
        @test metta_il_lower_def(d) ==
              raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
        # when-guard → guard joins the source conjunction
        dw = raw"(def f () (match (n $x $y) (when (== $x 1) (emit (kept $y)))))"
        @test metta_il_lower_def(dw) == raw"(exec 0 (, (n $x $y) (== $x 1)) (, (kept $y)))"
    end

    @testset "run + bisimulation: MeTTa-IL ≡ interpreter (match)" begin
        cs = MC.new_core_space()
        il = raw"(def trans () (match (edge $x $y) (edge $y $z) (emit (trans $x $z))))"
        R_il = metta_il_run!(cs, facts, il)
        @test R_il == ["(trans 0 2)", "(trans 1 3)"]
        # the IL program is equivalent to this MeTTa match — bisimulate against the interpreter-spec
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_il == R_interp                                   # MeTTa-IL lane ≡ interpreter-spec
    end

    @testset "multi-def IL composition (non-recursive)" begin
        cs = MC.new_core_space()
        il = raw"""
        (def reaches () (match (edge $x $y) (emit (reach $x $y))))
        (def twohop  () (match (edge $x $y) (edge $y $z) (emit (hop2 $x $z))))
        """
        R = metta_il_run!(cs, facts, il)
        @test "(reach 0 1)" in R && "(reach 1 2)" in R && "(reach 2 3)" in R   # reaches = edges
        @test "(hop2 0 2)" in R && "(hop2 1 3)" in R                           # twohop = 2-hop pairs
    end
    # NOTE: recursive closure (a def whose emit head is also a source) needs the saturation engine
    # (KBSaturation), not the single-step exec calculus — the next MeTTa-IL increment.
end
