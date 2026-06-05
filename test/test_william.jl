# WILLIAM on Core — all tests use one shared space (avoid repeated JIT cost)
using MeTTaCore, Test

println("Initialising space...")
S = new_core_space()
ef = e -> to_sexpr(eval_metta(from_sexpr(e), S))
register_core_primitives!();
_register_atom_ops!(ef);
load_stdlib!(S)
run_metta("!(import! &self (library william))", S)
println("Space ready ($(length(core_atoms(S))) atoms)\n")

q(e) = run_metta(e, S)   # query against shared space

# Helpers to add/clear data atoms between tests
function with_data(atoms::Vector{String}, f)
    for a in atoms
        ;
        q("!(add-atom &self $a)");
    end
    result = f()
    for a in atoms
        ;
        q("!(remove-atom &self $a)");
    end
    result
end

@testset "WILLIAM on Core" begin
    @testset "W2 size + gain + mdl-cost" begin
        @test q("!(WILLIAM.size foo)") == [1]
        @test q("!(WILLIAM.size ())") == [0]
        @test q("!(WILLIAM.size (a b c))") == [3]
        @test q("!(WILLIAM.size (f (g x) y))") == [4]
        @test q("!(WILLIAM.mdl-cost 5 3)") == [8]
        @test q("!(WILLIAM.gain (edge \$x bird) 3)") == [6]
        @test q("!(WILLIAM.gain foo 5)") == [0]
        @test q("!(WILLIAM.gain (f \$x \$y) 3)")[1] > q("!(WILLIAM.gain (f \$x \$y) 1)")[1]
    end

    @testset "W1/W6 count + support" begin
        with_data(
            ["(edge robin bird)", "(edge sparrow bird)", "(edge eagle bird)", "(edge dog mammal)"],
            () -> begin
                @test q("!(WILLIAM.count &self (edge \$x bird))") == [3]
                @test q("!(WILLIAM.count &self (edge \$x mammal))") == [1]
                @test q("!(WILLIAM.count &self (edge \$x fish))") == [0]
                sup = q("!(WILLIAM.support &self (edge \$x bird))")[1]
                @test sup isa Number && 0 < sup <= 1
            end,
        )
    end

    @testset "W5 ncd / similarity (pure math)" begin
        @test q("!(WILLIAM.ncd foo foo)") == [0]
        @test q("!(WILLIAM.similarity foo foo)") == [1]
    end

    @testset "Dictionary CRUD" begin
        q("!(WILLIAM.dict-add! &self (edge \$x bird) 3 6.0)")
        q("!(WILLIAM.dict-add! &self (move knight \$x) 4 8.0)")
        @test q("!(WILLIAM.dict-size &self)") == [2]
        lookup = q("!(WILLIAM.dict-lookup &self (edge \$x bird))")
        @test !isempty(lookup) && lookup[1] != :NotFound
        topq = q("!(WILLIAM.Query &self 2)")
        @test !isempty(topq)
        # cleanup
        q("!(remove-atom &self (WILLIAM.Entry (edge \$x bird) 3 6.0))")
        q("!(remove-atom &self (WILLIAM.Entry (move knight \$x) 4 8.0))")
    end

    @testset "W3 Learn" begin
        q("!(WILLIAM.Learn &self (move knight e4))")
        q("!(WILLIAM.Learn &self (move knight d6))")
        @test q("!(WILLIAM.count &self (move knight \$x))")[1] >= 2
        q("!(remove-atom &self (move knight e4))")
        q("!(remove-atom &self (move knight d6))")
    end

    @testset "W4 Predict" begin
        q("!(WILLIAM.dict-add! &self (move knight e4) 3 4.0)")
        q("!(WILLIAM.dict-add! &self (move bishop c4) 2 2.0)")
        pred = q("!(WILLIAM.Predict &self move)")
        @test !isempty(pred)
        q("!(remove-atom &self (WILLIAM.Entry (move knight e4) 3 4.0))")
        q("!(remove-atom &self (WILLIAM.Entry (move bishop c4) 2 2.0))")
    end

    @testset "W8 Validate" begin
        with_data(
            ["(event click a)", "(event click b)", "(event click c)"],
            () -> begin
                r = q("!(WILLIAM.Validate &self (event click \$x))")[1]
                @test r isa Vector && r[1] == Symbol("WILLIAM.ValidationResult")
                @test r[2] == r[3]
            end,
        )
    end

    @testset "WP§5.1 weakness" begin
        w  = q("!(WILLIAM.weakness (f \$x \$y) 5)")[1]
        wl = q("!(WILLIAM.weakness (f \$x \$y) 1)")[1]
        wh = q("!(WILLIAM.weakness (f \$x \$y) 10)")[1]
        @test w isa Number && 0 < w < 1
        @test wl > wh
    end

    @testset "WP§7.2 i-surprisingness" begin
        with_data(
            ["(sig high c1)", "(sig high c2)", "(sig high c3)"],
            () -> begin
                surp = q("!(WILLIAM.i-surprisingness &self (sig high \$x))")[1]
                @test surp isa Number && surp > 0
            end,
        )
    end

    @testset "Config + Stats" begin
        @test q("!(WILLIAM.Config.Threshold)") == [0.7]
        @test q("!(WILLIAM.Config.MaxDict)") == [200]
        q("!(WILLIAM.dict-add! &self (bar \$x) 2 3.0)")
        stats = q("!(WILLIAM.Stats &self)")[1]
        @test stats isa Vector && stats[1] == Symbol("WILLIAM.Summary")
        q("!(remove-atom &self (WILLIAM.Entry (bar \$x) 2 3.0))")
    end
end
println("\n✓ WILLIAM Core tests complete")
