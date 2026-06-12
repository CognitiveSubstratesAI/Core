# Loads the real stdlib.metta subset (verbatim from hyperon-experimental) into the
# StandardMeTTa evaluator and runs MeTTa programs that exercise if / let / let* / and.
include("../../src/standard/Minimal.jl")
using .Minimal
using .Minimal.StandardMeTTa
using Test

S(x) = Sym(x); E(xs...) = Expression(collect(Atom, xs)...)

@testset "real stdlib.metta subset — loaded + run" begin
    sp = Space()
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String))
    ev(src) = load_metta!(sp, src)

    # if (lazy else): the dead branch never runs
    @test ev("!(if True a b)")  == Atom[S("a")]
    @test ev("!(if False a b)") == Atom[S("b")]

    # grounded Bool logic + if
    @test ev("!(if (and True True)  yes no)") == Atom[S("yes")]
    @test ev("!(if (and True False) yes no)") == Atom[S("no")]
    @test ev("!(if (or False True)  yes no)") == Atom[S("yes")]
    @test ev("!(if (not False)      yes no)") == Atom[S("yes")]

    # let (the right arg is evaluated, the body is lazy then substituted)
    @test ev("!(let \$z (* 6 7) (pair \$z \$z))") == Atom[E(S("pair"), Grounded(42), Grounded(42))]

    # let* — sequential bindings via chain/decons-atom/unify, all from stdlib text
    @test ev("!(let* ((\$x 5) (\$y 7)) (+ \$x \$y))") == Atom[Grounded(12)]
    @test ev("!(let* ((\$a 2) (\$b (* \$a 10))) (+ \$a \$b))") == Atom[Grounded(22)]

    # a user function defined on top, calling stdlib if
    ev("(= (clamp0 \$x) (if (< \$x 0) 0 \$x))")
    @test ev("!(clamp0 5)")  == Atom[Grounded(5)]
    @test ev("!(clamp0 -3)") == Atom[Grounded(0)]
end
