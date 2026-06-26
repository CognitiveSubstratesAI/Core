# MM2 dual-lane router (src/standard/MM2Router.jl) — CeTTa-adopted, PRIMUS-native.
# Partition a program into !/exec/data lanes; route exec+data to the native MORK CoreSpace;
# reject top-level ! in the pure-program lane (CeTTa's MM2-file-loader discipline).
using MeTTaCore
const MC = MeTTaCore
using Test

@testset "MM2 dual-lane router" begin
    facts = "(edge 0 1)\n(edge 1 2)\n(edge 2 3)"
    rule  = raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
    prog  = facts * "\n" * rule

    @testset "partition into exec / data / bang lanes" begin
        p = mm2_partition(prog)
        @test isempty(p.bangs)
        @test length(p.exec) == 1 && mm2_is_exec_rule(p.exec[1])
        @test length(p.data) == 3 && all(!mm2_is_exec_rule, p.data)
        @test mm2_is_exec_rule(rule) && !mm2_is_exec_rule("(edge 0 1)")
    end

    @testset "MM2 lane runs exec on the native MORK CoreSpace" begin
        cs = MC.new_core_space()
        @test mm2_run!(cs, prog) == (n_exec = 1, n_data = 3, n_bang = 0)
        dump = MC.space_dump_all_sexpr(cs.inner)
        @test occursin("trans 0 2", dump) && occursin("trans 1 3", dump)
    end

    @testset "bisimulation: router MM2 lane ≡ interpreter (match)" begin
        cs = MC.new_core_space(); mm2_run!(cs, prog)
        R_mm2 = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                             if occursin("trans", l)]))
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_interp == ["(trans 0 2)", "(trans 1 3)"]
        @test R_mm2 == R_interp
    end

    @testset "pure-program lane rejects top-level ! (CeTTa discipline)" begin
        @test_throws ErrorException mm2_run!(MC.new_core_space(), raw"!(match &self (foo $x) $x)")
        r = mm2_run!(MC.new_core_space(), facts * "\n" * raw"!(foo)"; allow_bang = true)
        @test r.n_bang == 1
    end

    # ── piece 2: the match→exec bridge ──
    @testset "match→exec lowering (§10.3)" begin
        @test mm2_lower_match(raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))") ==
              raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
        @test mm2_lower_match(raw"(match &self (p $x) (found $x))") ==
              raw"(exec 0 (, (p $x)) (, (found $x)))"
    end

    @testset "mm2_match! ≡ interpreter (bisimulation)" begin
        cs = MC.new_core_space(); MC.space_add_all_sexpr!(cs.inner, facts)
        R_mm2 = mm2_match!(cs, raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        @test R_mm2 == ["(trans 0 2)", "(trans 1 3)"]
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, raw"!(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))")
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_mm2 == R_interp
    end

    # ── piece 3: the (=)→exec rule bridge (general rewrite rules, relational subset) ──
    @testset "(= LHS RHS) → exec lowering + bisimulation" begin
        @test mm2_lower_equals(raw"(= (ancestor $x $y) (parent $x $y))") ==
              raw"(exec 0 (, (ancestor $x $y)) (, (parent $x $y)))"
        @test mm2_lower_equals(raw"(= (, (p $x) (q $x)) (r $x))") ==
              raw"(exec 0 (, (p $x) (q $x)) (, (r $x)))"          # conjunctive LHS passes through
        @test_throws ErrorException mm2_lower_equals(raw"(match &self (p $x) $x)")  # not a (= …) form

        # a (= …) rewrite rule fires through space_metta_calculus! and bisimulates the interpreter
        afacts = "(ancestor a b)\n(ancestor b c)"
        arule  = raw"(= (ancestor $x $y) (parent $x $y))"
        cs = MC.new_core_space()
        MC.space_add_all_sexpr!(cs.inner, afacts)
        MC.space_add_all_sexpr!(cs.inner, mm2_lower_equals(arule))
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R_mork = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                              if occursin("parent", l)]))
        @test R_mork == ["(parent a b)", "(parent b c)"]

        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, afacts)
        res = SM.load_metta!(isp, raw"!(match &self (ancestor $x $y) (parent $x $y))")
        R_interp = sort(unique(filter(s -> occursin("parent", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R_mork == R_interp                              # MORK (=) lane ≡ interpreter oracle
    end

    @testset "mm2_route! full dispatch (data + exec + !match + deferred)" begin
        cs = MC.new_core_space()
        prog2 = facts * "\n" * rule * "\n" *
                raw"!(match &self (trans $a $b) (reached $a $b))" * "\n" * raw"!(+ 1 2)"
        r = mm2_route!(cs, prog2)
        @test r.n_data == 3 && r.n_exec == 1
        @test length(r.matched) == 1                       # the !(match …) routed to the MM2 lane
        @test r.matched[1][2] == ["(reached 0 2)", "(reached 1 3)"]
        @test r.deferred == [raw"(+ 1 2)"]                 # non-match ! → interpreter lane (deferred)
    end
end
