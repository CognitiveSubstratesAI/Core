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

    # ── piece 4: grounded-op guard + auto-routing of (= …) rules in mm2_partition ──
    @testset "grounded-op guard classifies relational vs grounded rules" begin
        @test mm2_is_relational(raw"(= (ancestor $x $y) (parent $x $y))")        # plain relations
        @test mm2_is_relational(raw"(= (, (p $x) (q $x)) (r $x))")               # conjunctive, relational
        @test !mm2_is_relational(raw"(= (fib $n) (+ (fib (- $n 1)) (fib (- $n 2))))")  # + ⇒ grounded
        @test !mm2_is_relational(raw"(= (dbl $x) (* $x 2))")                     # * ⇒ grounded
        @test !mm2_is_relational(raw"(= (q $x) (match &self (p $x) $x))")        # match ⇒ special
        @test !mm2_is_relational(raw"(= (c $x) (chain $x))")                     # chain ⇒ MINIMAL_OPS
        @test !mm2_is_relational(raw"(foo $x)")                                  # not a (= …) form
    end

    @testset "mm2_partition auto-routes relational (= …), leaves grounded in data" begin
        # relational rule auto-lowered into exec; fact stays data
        p = mm2_partition("(ancestor a b)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        @test length(p.exec) == 1 && occursin("exec 0", p.exec[1])
        @test p.data == ["(ancestor a b)"]
        # grounded rule untouched — stays in the data lane exactly as before
        pg = mm2_partition(raw"(= (fib $n) (+ $n 1))")
        @test isempty(pg.exec) && pg.data == [raw"(= (fib $n) (+ $n 1))"]
        # end-to-end: a program with a relational (= …) rule now fires through the MORK lane unaided
        cs = MC.new_core_space()
        mm2_run!(cs, "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    # ── piece 5: typed Atom → MM2 sexpr (the live-eval handoff converter) ──
    @testset "typed_atom_to_expr round-trips to mm2_lower_equals" begin
        SM = MeTTaCore.Interpreter
        for s in [raw"(= (ancestor $x $y) (parent $x $y))",
                  raw"(= (, (p $x) (q $x)) (r $x))",
                  raw"(= (sym a) (sym b))",
                  raw"(= (dbl $x) (twice $x $x))"]
            atom = SM.parse_program(s)[1][2]                  # the parsed (= …) Atom
            e = typed_atom_to_expr(atom)
            @test mm2_lower_equals(e) == mm2_lower_equals(s)  # serialize→lower == lower(source)
        end
        # end-to-end: a parsed Atom rule, serialized, fires through the MORK lane and bisimulates
        atom = SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2]
        cs = MC.new_core_space()
        MC.space_add_all_sexpr!(cs.inner, "(ancestor a b)\n(ancestor b c)")
        MC.space_add_all_sexpr!(cs.inner, mm2_lower_equals(typed_atom_to_expr(atom)))
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    # ── piece 6: live-eval handoff — typed-Atom guard + MORK mirror lane (mirror, bisim-safe) ──
    @testset "mm2_is_relational(Atom) + mm2_lane_from_atoms bisimulates interpreter" begin
        SM = MeTTaCore.Interpreter
        @test mm2_is_relational(SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2])
        @test !mm2_is_relational(SM.parse_program(raw"(= (fib $n) (+ $n 1))")[1][2])   # grounded
        @test !mm2_is_relational(SM.parse_program("(ancestor a b)")[1][2])             # a fact, not a rule

        prog  = "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))"
        atoms = [p[2] for p in SM.parse_program(prog)]
        cs = mm2_lane_from_atoms(atoms)                       # build the MORK mirror from typed atoms
        MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]

        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, "(ancestor a b)\n(ancestor b c)")
        res = SM.load_metta!(isp, raw"!(match &self (ancestor $x $y) (parent $x $y))")
        R_interp = sort(unique(filter(s -> occursin("parent", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test R == R_interp                                  # MORK mirror lane ≡ interpreter oracle
    end

    # ── piece 7: P2 route gate — broad single-step bisimulation + the chain boundary + lane_from_space ──
    @testset "P2 route gate: broad bisimulation + forward-closure boundary" begin
        SM = MeTTaCore.Interpreter
        mork_derive(facts, rule, head) = begin
            atoms = [p[2] for p in SM.parse_program(facts * "\n" * rule)]
            cs = mm2_lane_from_atoms(atoms); MC.space_metta_calculus!(cs.inner, 1_000_000)
            sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n') if occursin(head, l)]))
        end
        interp_match(facts, lhs, rhs, head) = begin
            isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
            res = SM.load_metta!(isp, "!(match &self $lhs $rhs)")
            sort(unique(filter(s -> occursin(head, s),
                [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        end
        # SINGLE-STEP shapes — MORK mirror saturate ≡ interpreter !(match)
        for (facts, lhs, rhs, head) in [
                ("(ancestor a b)\n(ancestor b c)", raw"(ancestor $x $y)", raw"(parent $x $y)", "parent"),
                ("(rel p q)\n(rel q r)",           raw"(rel $x $y)",      raw"(link $x $y)",   "link"),
                ("(parent a b)\n(parent b c)",     raw"(, (parent $x $y) (parent $y $z))",
                                                   raw"(grandparent $x $z)", "grandparent")]
            @test mork_derive(facts, "(= $lhs $rhs)", head) == interp_match(facts, lhs, rhs, head)
        end
        # BOUNDARY (documented): a multi-rule chain → MORK forward CLOSURE {b,c}, by design (Datalog),
        # NOT the interpreter's (=) reduction normal-form (c). This bounds what ROUTE may soundly do.
        chain = mork_derive("(a 1)", raw"(= (a $x) (b $x))" * "\n" * raw"(= (b $x) (c $x))", "")
        @test ("(b 1)" in chain) && ("(c 1)" in chain)

        # mm2_lane_from_space — mirror a LIVE Space's own atoms (excludes stdlib)
        isp = SM.Space(); SM.load_core_stdlib!(isp)
        SM.load_metta!(isp, "(ancestor a b)\n(ancestor b c)\n" * raw"(= (ancestor $x $y) (parent $x $y))")
        cs = mm2_lane_from_space(isp); MC.space_metta_calculus!(cs.inner, 1_000_000)
        R = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                         if occursin("parent", l)]))
        @test R == ["(parent a b)", "(parent b c)"]
    end

    # ── piece 8: mm2_lane_saturate! — recursive Datalog fixpoint (transitive closure) ──
    @testset "mm2_lane_saturate! computes the full transitive closure (recursion driver)" begin
        SM = MeTTaCore.Interpreter
        prog = "(edge a b)\n(edge b c)\n(edge c d)\n" *
               raw"(= (edge $x $y) (reach $x $y))" * "\n" *
               raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))"
        atoms = [p[2] for p in SM.parse_program(prog)]
        reach(cs) = sort(unique([strip(l) for l in split(MC.space_dump_all_sexpr(cs.inner), '\n')
                                 if occursin("reach", l)]))
        # single-pass MISSES the 3-hop (exec consumed after one fire — MM2 spec)
        cs1 = mm2_lane_from_atoms(atoms); MC.space_metta_calculus!(cs1.inner, 1_000_000)
        @test !("(reach a d)" in reach(cs1))
        # the fixpoint driver reaches the full closure (re-fire until stable)
        R = sort(string.(reach(mm2_lane_saturate!(atoms))))
        @test R == sort(["(reach a b)", "(reach b c)", "(reach c d)",
                         "(reach a c)", "(reach b d)", "(reach a d)"])
    end

    # ── piece 9: MORK byte-Expr limit guard (arity 63 / 64 vars — wiki Data-in-MORK) ──
    @testset "mm2_is_relational rejects rules exceeding MORK byte-Expr limits" begin
        SM = MeTTaCore.Interpreter
        @test mm2_is_relational(SM.parse_program(raw"(= (ancestor $x $y) (parent $x $y))")[1][2])  # within limits
        over_arity = "(= (big " * join(["a$i" for i in 1:70], " ") * ") (ok))"      # 71-child LHS > 63
        @test !mm2_is_relational(SM.parse_program(over_arity)[1][2])
        over_vars = "(= (f " * join(["\$v$i" for i in 1:70], " ") * ") (g))"        # 70 distinct vars > 64
        @test !mm2_is_relational(SM.parse_program(over_vars)[1][2])
    end

    # ── piece 10: mc_closure! — opt-in substrate route, Datalog closure materialized into a live Space ──
    @testset "mc_closure! materializes the transitive closure for the interpreter to query" begin
        SM = MeTTaCore.Interpreter
        isp = SM.Space(); SM.load_core_stdlib!(isp)
        SM.load_metta!(isp, "(edge a b)\n(edge b c)\n(edge c d)\n" *
            raw"(= (edge $x $y) (reach $x $y))" * "\n" *
            raw"(= (, (edge $x $y) (reach $y $z)) (reach $x $z))")
        @test mc_closure!(isp) == 6                              # 6 derived reach atoms materialized
        res = SM.load_metta!(isp, raw"!(match &self (reach $x $y) (reach $x $y))")
        reach = sort(unique(filter(s -> startswith(s, "(reach"),
            [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        @test length(reach) == 6                                # interpreter now queries the full closure
        @test "(reach a d)" in reach                            # incl. the 3-hop only the fixpoint finds
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
