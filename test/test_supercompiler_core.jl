# Integration: MorkSupercompiler tier-2 (`execute!`) → Core via `sc_execute!`.
# Un-orphans tier-2 (previously only tier-1 `plan!` was reachable, and only on the legacy eval
# path). Runs a transitive-edge join (the canonical multi-source / Rule-of-64 workload) through
# the full pipeline on a CoreSpace's MORK trie, asserting correctness + that tier-2-only stages
# (the §6 driver, KB saturation) engage — stages tier-1 `plan!` cannot reach.
using Test, MeTTaCore
const MC = MeTTaCore

@testset "MorkSupercompiler tier-2 → Core (sc_execute!)" begin
    facts = raw"(edge 0 1) (edge 1 2) (edge 2 3)"
    prog  = raw"(exec 0 (, (edge $x $y) (edge $y $z)) (, (trans $x $z)))"
    # join: (0,1)+(1,2)→(trans 0 2); (1,2)+(2,3)→(trans 1 3)

    @testset "tier-2 default: plans, decomposes, executes on the MORK trie" begin
        s = new_core_space()
        MC.space_add_all_sexpr!(s.inner, facts)
        before = MC.space_val_count(s.inner)
        r = sc_execute!(s, prog)
        @test r isa SCResult
        @test haskey(r.timings, :execute)
        @test MC.space_val_count(s.inner) > before        # new trans atoms written
        dump = MC.space_dump_all_sexpr(s.inner)
        @test occursin("trans", dump)                     # the join fired
    end

    @testset "correctness parity vs direct MORK calculus" begin
        ssc = new_core_space(); MC.space_add_all_sexpr!(ssc.inner, facts)
        sc_execute!(ssc, prog)
        sc_dump = MC.space_dump_all_sexpr(ssc.inner)

        sd = new_core_space()
        MC.space_add_all_sexpr!(sd.inner, facts)
        MC.space_add_all_sexpr!(sd.inner, prog)
        MC.space_metta_calculus!(sd.inner, 10_000)
        direct_dump = MC.space_dump_all_sexpr(sd.inner)

        # both engines must produce the same transitive closure
        for t in ("trans 0 2", "trans 1 3")
            @test occursin(t, sc_dump) == occursin(t, direct_dump)
        end
    end

    @testset "tier-2-only stage: §6 supercompilation driver engages" begin
        s = new_core_space(); MC.space_add_all_sexpr!(s.inner, facts)
        r = sc_execute!(s, prog; opts = SCOptions(supercompile = true, drive_steps = 100))
        @test !isempty(r.drive_results)                   # tier-1 plan! never produces these
        @test haskey(r.timings, :supercompile)
        for dr in r.drive_results
            @test dr.terminated in (:value, :fold, :blocked, :max_steps)
        end
    end

    @testset "tier-2-only stage: KB saturation reports counts" begin
        s = new_core_space(); MC.space_add_all_sexpr!(s.inner, facts)
        r = sc_execute!(s, prog; opts = SCOptions(saturate = true))
        @test haskey(r.timings, :saturate)
        @test r.n_kb_facts >= 0
    end

    @testset "§10.3 MeTTa→MM2 lowering: (match …) ≡ hand-written (exec …)" begin
        # The missing bridge (MeTTa-MM2-Supercompiler_v1_spec.md:502): a `match` join query lowers to
        # exec form at execute! entry, feeds the supercompiler (join-reorder + decomposition), and
        # produces the SAME trie output as the equivalent hand-written exec program. Before this,
        # `match` atoms were inert (added verbatim, never fired) so nothing in lib/ could be optimized.
        match_prog = raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))"
        trans(p) = begin
            sp = new_core_space(); MC.space_add_all_sexpr!(sp.inner, facts); sc_execute!(sp, p)
            sort([strip(l) for l in split(MC.space_dump_all_sexpr(sp.inner), '\n') if occursin("trans", l)])
        end
        @test trans(match_prog) == trans(prog)             # match-form ≡ exec-form
        @test trans(match_prog) == ["(trans 0 2)", "(trans 1 3)"]
    end

    @testset "§9.2 bisimulation: supercompiler (match) ≡ live Interpreter (match)" begin
        # The REAL correctness gate (MeTTa-MM2-Supercompiler_v2 §9.2): the lowered+supercompiled match
        # result must equal what the live tree-walking Interpreter returns for the SAME (match …) — not
        # just self-consistency with hand-written exec, but faithfulness to the actual evaluator.
        SM = MeTTaCore.Interpreter
        match_q = raw"(match &self (, (edge $x $y) (edge $y $z)) (trans $x $z))"
        # interpreter oracle: run (match …) on a tree-walker space with the same facts
        isp = SM.Space(); SM.load_core_stdlib!(isp); SM.load_metta!(isp, facts)
        res = SM.load_metta!(isp, "!" * match_q)
        R_interp = sort(unique(filter(s -> occursin("trans", s),
                       [string(x) for r in res for x in (r isa AbstractVector ? r : [r])])))
        # supercompiler: the lowered match → exec → MORK
        sp = new_core_space(); MC.space_add_all_sexpr!(sp.inner, facts); sc_execute!(sp, match_q)
        R_sc = sort(unique(filter(s -> occursin("trans", s),
                  [strip(l) for l in split(MC.space_dump_all_sexpr(sp.inner), '\n')])))
        @test R_interp == ["(trans 0 2)", "(trans 1 3)"]   # the Interpreter actually produces this
        @test R_sc == R_interp                              # supercompiler is faithful to the Interpreter
    end
end
