# Validates the typed atom model + matcher (src/standard/Atoms.jl) against the
# matching semantics in docs/metta.md §Matching. Standalone (no Core dependency).
using MeTTaCore.StandardMeTTa   # precompiled submodule (was: include fresh → recompiled per file)
using Test

@testset "StandardMeTTa: typed atoms + matcher (metta.md §Matching)" begin
    a, b = Sym("a"), Sym("b")
    A, B = Sym("A"), Sym("B")
    x, y = Var("x"), Var("y")

    # symbol equality
    @test length(match_atoms(a, a)) == 1
    @test isempty(match_atoms(a, b))

    # variable assignment: $x <- A
    bs = match_atoms(x, A)
    @test length(bs) == 1
    @test resolve(bs[1], x) == A

    # two variables: $x = $y (equality, no value yet)
    @test length(match_atoms(x, y)) == 1

    # expression: (a $x) ~ ($y b)  →  $x<-b, $y<-a
    bs = match_atoms(Expression(a, x), Expression(y, b))
    @test length(bs) == 1
    @test resolve(bs[1], x) == b
    @test resolve(bs[1], y) == a

    # variable-equality PROPAGATION: ($x $x) ~ (A $y)  →  $x<-A and $y<-A
    # (this is the case Dict{Symbol,Any} bindings cannot represent)
    bs = match_atoms(Expression(x, x), Expression(A, y))
    @test length(bs) == 1
    @test resolve(bs[1], x) == A
    @test resolve(bs[1], y) == A

    # conflict: ($x $x) ~ (A B)  →  no match
    @test isempty(match_atoms(Expression(x, x), Expression(A, B)))

    # grounded: value equality
    @test length(match_atoms(Grounded(1), Grounded(1))) == 1
    @test isempty(match_atoms(Grounded(1), Grounded(2)))

    # nested expression + shared var: (f $x (g $x)) ~ (f A (g A)) ok; (f A (g B)) fails
    f, g = Sym("f"), Sym("g")
    @test length(
        match_atoms(Expression(f, x, Expression(g, x)), Expression(f, A, Expression(g, A)))
    ) == 1
    @test isempty(
        match_atoms(Expression(f, x, Expression(g, x)), Expression(f, A, Expression(g, B)))
    )
end
