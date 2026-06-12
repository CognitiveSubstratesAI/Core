# Validates the `metta` interpreter driver (metta.md §Interpretation, untyped Phase 1a) — full
# reduction, applicative order, nondeterminism — distinct from one-step `eval`.
include("../../src/standard/Minimal.jl")
using .Minimal
using .Minimal.StandardMeTTa
using Test

S(x) = Sym(x); V(x) = Var(x); E(xs...) = Expression(collect(Atom, xs)...)
rule(lhs, rhs) = E(S("="), lhs, rhs)

@testset "metta driver (metta.md §Interpretation, untyped)" begin
    # FULL reduction (vs eval's one step): (foo)→(bar)→a ⇒ metta((foo)) = a
    sp = Space(Atom[rule(E(S("foo")), E(S("bar"))), rule(E(S("bar")), S("a"))])
    @test metta_run(E(S("foo")), sp) == Atom[S("a")]

    # APPLICATIVE order (vs eval NotReducible): (+ 1 (+ 2 3)) → 6
    @test metta_run(E(PLUS, Grounded(1), E(PLUS, Grounded(2), Grounded(3))), Space()) == Atom[Grounded(6)]

    # plain arithmetic + a defined function reducing through grounded
    sp2 = Space(Atom[rule(E(S("inc"), V("n")), E(PLUS, V("n"), Grounded(1)))])
    @test metta_run(E(S("inc"), Grounded(41)), sp2) == Atom[Grounded(42)]

    # NONDETERMINISM: three equalities for (color) ⇒ fan-out to {red, green, blue}
    spc = Space(Atom[rule(E(S("color")), S("red")), rule(E(S("color")), S("green")),
                     rule(E(S("color")), S("blue"))])
    @test Set(metta_run(E(S("color")), spc)) == Set(Atom[S("red"), S("green"), S("blue")])

    # nondeterminism fans through an enclosing expression: (pair (color)) → 3 results
    spp = Space(Atom[rule(E(S("color")), S("red")), rule(E(S("color")), S("green"))])
    res = metta_run(E(S("pair"), E(S("color"))), spp)   # (pair red), (pair green) — pair undefined → as-is
    @test Set(res) == Set(Atom[E(S("pair"), S("red")), E(S("pair"), S("green"))])

    # non-reducible stays as-is: unknown symbol / unknown function
    @test metta_run(S("hello"), Space()) == Atom[S("hello")]
    @test metta_run(E(S("nope"), Grounded(1)), Space()) == Atom[E(S("nope"), Grounded(1))]
end

@testset "metta driver: gradual types — if / let (lazy args, Phase 1b)" begin
    decl(n, ty) = E(S(":"), S(n), ty)
    arrow(xs...) = E(S("->"), xs...)

    # if: (: if (-> Bool Atom Atom $t)) + the two = rules ; (boom) loops forever
    spif = Space(Atom[
        decl("if", arrow(S("Bool"), S("Atom"), S("Atom"), V("t"))),
        rule(E(S("if"), S("True"),  V("then"), V("else")), V("then")),
        rule(E(S("if"), S("False"), V("then"), V("else")), V("else")),
        rule(E(S("boom")), E(S("boom")))])
    # the DEAD branch (boom) must NOT be evaluated (else: infinite loop → step-limit error)
    @test metta_run(E(S("if"), S("True"),  S("a"), E(S("boom"))), spif) == Atom[S("a")]
    @test metta_run(E(S("if"), S("False"), E(S("boom")), S("b")), spif) == Atom[S("b")]

    # let: (: let (-> Atom %Undefined% Atom %Undefined%)); body via `unify` (a minimal op)
    splet = Space(Atom[
        decl("let", arrow(S("Atom"), S("%Undefined%"), S("Atom"), S("%Undefined%"))),
        rule(E(S("let"), V("p"), V("a"), V("tpl")),
             E(S("unify"), V("a"), V("p"), V("tpl"), S("Empty")))])
    # (let $x (+ 1 2) (g $x)) → (g 3): $a evaluated (%Undefined%), $p/$tpl lazy (Atom), unify binds $x
    @test metta_run(E(S("let"), V("x"), E(PLUS, Grounded(1), Grounded(2)), E(S("g"), V("x"))), splet) ==
          Atom[E(S("g"), Grounded(3))]
end
