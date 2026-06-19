# MeTTa-IL lane (src/standard/MeTTaIL.jl) — re-grounded in the ACTUAL upstream MeTTa-IL: lower a
# theory's REWRITES `(~> LHS RHS)` (GSLT `Name : LHS ~> RHS`) → MM2 → MORK, bisimulation-gated.
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "MeTTa-IL lane (rewrites → MM2 → MORK)" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"

    @testset "rewrite lowering: (~> LHS RHS) → (exec …)" begin
        # base rewrite, single-pattern LHS
        @test metta_il_lower_rewrite(raw"(~> (a $x) (b $x))") == raw"(exec 0 (, (a $x)) (, (b $x)))"
        # conjunctive LHS passes through as the source list
        @test metta_il_lower_rewrite(raw"(~> (, (edge $x $y) (edge $y $z)) (trans $x $z))") ==
              raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
    end

    @testset "run + bisimulation: MeTTa-IL rewrite ≡ interpreter (match)" begin
        cs = MC.new_core_space()
        il = raw"(~> (, (edge $x $y) (edge $y $z)) (trans $x $z))"
        R_il = metta_il_run!(cs, facts, il)
        @test R_il == ["(trans 0 2)", "(trans 1 3)"]
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_il == R_interp                                   # MeTTa-IL rewrite lane ≡ interpreter-spec
    end

    @testset "multi-rewrite program (non-recursive)" begin
        cs = MC.new_core_space()
        il = raw"""
        (~> (edge $x $y) (reach $x $y))
        (~> (, (edge $x $y) (edge $y $z)) (hop2 $x $z))
        """
        R = metta_il_run!(cs, facts, il)
        @test "(reach 0 1)" in R && "(reach 1 2)" in R && "(reach 2 3)" in R
        @test "(hop2 0 2)" in R && "(hop2 1 3)" in R
    end

    @testset "recursive closure via saturation (saturate=true)" begin
        # RECURSIVE rewrite (path is both a body premise and a head): single-step does one generation;
        # saturate=true runs KBSaturation to FIXPOINT → full transitive closure.
        il = raw"""
        (~> (edge $x $y) (path $x $y))
        (~> (, (path $x $y) (edge $y $z)) (path $x $z))
        """
        cs = MC.new_core_space()
        R_sat = metta_il_run!(cs, facts, il; saturate = true)
        @test R_sat == ["(path 0 1)", "(path 0 2)", "(path 0 3)", "(path 1 2)", "(path 1 3)", "(path 2 3)"]
        # the SAME program single-step (default) does NOT reach the 3-hop closure — proves saturation is needed
        cs2 = MC.new_core_space()
        @test "(path 0 3)" ∉ metta_il_run!(cs2, facts, il)
        # cyclic input TERMINATES with the correct closure (value-dedup gate, not an infinite loop)
        cs3 = MC.new_core_space()
        @test metta_il_run!(cs3, "(edge 0 1)\n(edge 1 0)", il; saturate = true) ==
              ["(path 0 0)", "(path 0 1)", "(path 1 0)", "(path 1 1)"]
    end
    @testset "congruence via subterm reduction (metta_il_normalize)" begin
        # CALCULUS `~>` = term reduction with congruence (reduce inside contexts), NOT additive derivation.
        bool = raw"""
        (~> (not T) F)
        (~> (not F) T)
        (~> (and T $x) $x)
        (~> (and F $x) F)
        """
        # pure congruence: a redex reduces inside a context whose head has NO rule (wrap)
        @test metta_il_normalize(bool, raw"(wrap (not T))") == "(wrap F)"
        # congruence in multiple positions + top-level reductions → full normal form
        @test metta_il_normalize(bool, raw"(and (not F) (not T))") == "F"   # children → (and T F) → F
        @test metta_il_normalize(bool, raw"(not (not T))") == "T"           # nested redex
        @test metta_il_normalize(bool, raw"(pair (not T) (not F))") == "(pair F T)"  # both args
    end
    @testset "def/match/emit pipeline surface (§9.1 → §9.2)" begin
        @testset "lowering: def → (exec PRIORITY (, PATS) (, EMITS)) per §9.2" begin
            @test metta_il_lower_def(raw"(def s () (match (a $x) (emit (b $x))))", 1) ==
                  raw"(exec 1 (, (a $x)) (, (b $x)))"
            # multiple patterns + multiple emits (extract-skeleton shape)
            @test metta_il_lower_def(raw"(def x () (match (p $x) (emit (q $x)) (emit (r $x))))", 2) ==
                  raw"(exec 2 (, (p $x)) (, (q $x) (r $x)))"
            # when guard folds into the source conjunction
            @test metta_il_lower_def(raw"(def m () (match (c $x $n) (when (== $n hi) (emit (k $x)))))", 4) ==
                  raw"(exec 4 (, (c $x $n) (== $n hi)) (, (k $x)))"
        end

        @testset "run a staged pipeline (stage 2 consumes stage 1's output)" begin
            cs = MC.new_core_space()
            pipe = raw"""
            (def s1 () (match (edge $x $y) (emit (reach $x $y))))
            (def s2 () (match (reach $x $y) (edge $y $z) (emit (far $x $z))))
            """
            R = metta_il_run_pipeline!(cs, facts, pipe)
            @test "(reach 0 1)" in R                        # stage 1
            @test "(far 0 2)" in R && "(far 1 3)" in R      # stage 2 consumes stage 1's output
        end
    end
    # NOTE: the GSLT theory algebra (composition/parameterization) lives in GSLT.jl / test_gslt.jl;
    # equations-as-rewrite orientation (Knuth-Bendix) is the remaining (a)-tail item.
end
