# Loads the real stdlib.metta subset (verbatim from hyperon-experimental) into the
# StandardMeTTa evaluator and runs MeTTa programs that exercise if / let / let* / and.
using MeTTaCore.Minimal                  # precompiled submodule (was: include fresh → recompiled per file)
using MeTTaCore.Minimal.StandardMeTTa
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

@testset "stdlib list ops — car/cdr/size/index/map/filter/get-metatype" begin
    sp = Space()
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String))
    ev(src) = load_metta!(sp, src)
    G(n) = Grounded(n)

    # grounded list primitives
    @test ev("!(size-atom (a b c))")    == Atom[G(3)]
    @test ev("!(index-atom (a b c) 1)") == Atom[S("b")]
    @test ev("!(get-metatype foo)")     == Atom[S("Symbol")]
    @test ev("!(get-metatype 5)")       == Atom[S("Grounded")]
    @test ev("!(get-metatype (a b))")   == Atom[S("Expression")]

    # car-atom / cdr-atom (MeTTa = rules via decons-atom/unify)
    @test ev("!(car-atom (a b c))") == Atom[S("a")]
    @test ev("!(cdr-atom (a b c))") == Atom[E(S("b"), S("c"))]

    # map-atom / filter-atom (real upstream defs, via sealed/atom-subst/cons-atom + recursion)
    @test ev("!(map-atom (1 2 3 4) \$v (eval (+ \$v 1)))") == Atom[E(G(2), G(3), G(4), G(5))]
    @test ev("!(filter-atom (1 2 3 4) \$v (eval (> \$v 2)))") == Atom[E(G(3), G(4))]
end

@testset "stdlib switch (real upstream def)" begin
    sp = Space()
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String))
    ev(src) = load_metta!(sp, src)
    # literal match
    @test ev("!(switch A ((A 1) (B 2)))") == Atom[Grounded(1)]
    @test ev("!(switch B ((A 1) (B 2)))") == Atom[Grounded(2)]
    # pattern match with variable capture
    @test ev("!(switch (P a) (((P \$x) \$x) (\$_ none)))") == Atom[S("a")]
    @test ev("!(switch (Q a) (((P \$x) \$x) (\$_ none)))") == Atom[S("none")]
end

@testset "stdlib foldl-atom / case / get-type" begin
    sp = Space()
    load_metta!(sp, read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String))
    ev(src) = load_metta!(sp, src)
    # foldl-atom: sum and product
    @test ev("!(foldl-atom (1 2 3 4) 0 \$a \$b (+ \$a \$b))") == Atom[Grounded(10)]
    @test ev("!(foldl-atom (1 2 3 4) 1 \$a \$b (* \$a \$b))") == Atom[Grounded(24)]
    # case: literal, evaluated atom, variable capture
    @test ev("!(case 2 ((1 one) (2 two) (3 three)))") == Atom[S("two")]
    @test ev("!(case (+ 1 1) ((1 one) (2 two)))") == Atom[S("two")]
    @test ev("!(case foo ((bar no) (\$x (got \$x))))") == Atom[E(S("got"), S("foo"))]
    # get-type
    @test ev("!(get-type 5)") == Atom[S("Number")]
    ev("(: Plato Human)")
    @test ev("!(get-type Plato)") == Atom[S("Human")]
end
