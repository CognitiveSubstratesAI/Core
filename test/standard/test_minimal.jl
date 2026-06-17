# Validates the minimal-MeTTa stack machine (src/standard/Interpreter.jl) against the
# worked examples in hyperon docs/minimal-metta.md (cons-atom/decons-atom/unify).
# eval/chain/function/collapse are Phase 0c/0d — not yet ported.
using MeTTaCore.Interpreter                  # precompiled submodule (was: include fresh → recompiled per file)
using MeTTaCore.Interpreter.StandardMeTTa
using Test

# build helpers
S(x) = Sym(x); V(x) = Var(x); E(xs...) = Expression(collect(Atom, xs)...)
only_result(atom) = (rs = bare_eval(atom); @assert length(rs) == 1 "got $(length(rs)) results: $rs"; rs[1])

@testset "Minimal MeTTa: cons/decons/unify (minimal-metta.md)" begin
    a, b, c = S("a"), S("b"), S("c")

    # cons-atom (minimal-metta.md): (cons-atom a (b c)) → (a b c)
    @test only_result(E(S("cons-atom"), a, E(b, c))) == E(a, b, c)

    # decons-atom: (decons-atom (a b c)) → (a (b c));  (a) → (a ());  () → Error
    @test only_result(E(S("decons-atom"), E(a, b, c))) == E(a, E(b, c))
    @test only_result(E(S("decons-atom"), E(a)))       == E(a, E())
    r = only_result(E(S("decons-atom"), E()))
    @test r isa Expression && r.children[1] == S("Error")

    # unify (minimal-metta.md): (unify (a $b) ($a b) ($a $b) fail) → (a b)
    @test only_result(E(S("unify"), E(a, V("b")), E(V("a"), b), E(V("a"), V("b")), S("fail"))) == E(a, b)
    #                  (unify (a $b) (b a) ok fail) → fail
    @test only_result(E(S("unify"), E(a, V("b")), E(b, a), S("ok"), S("fail"))) == S("fail")

    # a non-instruction atom evaluates to itself (data)
    @test only_result(E(S("foo"), a)) == E(S("foo"), a)
    @test only_result(a) == a
end

@testset "Minimal MeTTa: eval (minimal-metta.md §eval)" begin
    # (= (foo) (bar)) (= (bar) a)
    sp = Space(Atom[E(S("="), E(S("foo")), E(S("bar"))),
                    E(S("="), E(S("bar")), S("a"))])
    ev(x) = (rs = bare_eval(x, sp); @assert length(rs) == 1 "got $(length(rs)): $rs"; rs[1])

    @test ev(E(S("eval"), E(S("foo")))) == E(S("bar"))     # ONE step: (foo)→(bar), not a
    @test ev(E(S("eval"), E(S("bar")))) == S("a")
    @test ev(E(S("eval"), E(S("baz")))) == S("NotReducible")
    # grounded: (eval (+ 1 2)) → 3 ; (eval (+ 1 a)) → NotReducible (a not a number)
    @test ev(E(S("eval"), E(PLUS, Grounded(1), Grounded(2)))) == Grounded(3)
    @test ev(E(S("eval"), E(PLUS, Grounded(1), S("a"))))      == S("NotReducible")
    # eval does NOT recurse into subexpressions: (eval (+ (+ 1 2) 3)) → NotReducible
    @test ev(E(S("eval"), E(PLUS, E(PLUS, Grounded(1), Grounded(2)), Grounded(3)))) == S("NotReducible")
end

@testset "Minimal MeTTa: chain / function / return (minimal-metta.md)" begin
    # chain (minimal-metta.md): (chain (eval (+ 2 3)) $x (eval (+ 1 $x))) → 6
    @test only_result(E(S("chain"), E(S("eval"), E(PLUS, Grounded(2), Grounded(3))), V("x"),
                        E(S("eval"), E(PLUS, Grounded(1), V("x"))))) == Grounded(6)

    sp = Space(Atom[E(S("="), E(S("foo")), E(S("bar"))), E(S("="), E(S("bar")), S("a"))])
    ev(x) = (rs = bare_eval(x, sp); @assert length(rs) == 1 "got $(length(rs)): $rs"; rs[1])
    # (chain (eval (foo)) $x (eval $x)) → a ;  (chain (eval (foo)) $x (R $x)) → (R (bar))
    @test ev(E(S("chain"), E(S("eval"), E(S("foo"))), V("x"), E(S("eval"), V("x")))) == S("a")
    @test ev(E(S("chain"), E(S("eval"), E(S("foo"))), V("x"), E(S("R"), V("x")))) == E(S("R"), E(S("bar")))

    # function/return: (= (foo)(eval (bar)))(= (bar)(eval (baz)))(= (baz)(return a)); (function (eval (foo)))→a
    sp2 = Space(Atom[E(S("="), E(S("foo")), E(S("eval"), E(S("bar")))),
                     E(S("="), E(S("bar")), E(S("eval"), E(S("baz")))),
                     E(S("="), E(S("baz")), E(S("return"), S("a")))])
    let r = bare_eval(E(S("function"), E(S("eval"), E(S("foo")))), sp2)
        @test length(r) == 1 && r[1] == S("a")
    end

    # div integration (minimal-metta.md): (function (eval (div 35 5 0))) → 7
    divrule = E(S("="),
        E(S("div"), V("x"), V("y"), V("accum")),
        E(S("chain"), E(S("eval"), E(MINUS, V("x"), V("y"))), V("r1"),
          E(S("chain"), E(S("eval"), E(LT, V("r1"), Grounded(0))), V("r2"),
            E(S("unify"), V("r2"), S("True"),
              E(S("return"), V("accum")),
              E(S("chain"), E(S("eval"), E(PLUS, Grounded(1), V("accum"))), V("inc"),
                E(S("eval"), E(S("div"), V("r1"), V("y"), V("inc"))))))))
    spd = Space(Atom[divrule])
    rs = bare_eval(E(S("function"), E(S("eval"), E(S("div"), Grounded(35), Grounded(5), Grounded(0)))), spd)
    @test length(rs) == 1 && rs[1] == Grounded(7)
end

@testset "Minimal MeTTa: collapse-bind / superpose-bind (minimal-metta.md)" begin
    # (= (xoo a) xa) (= (xoo b) xb)
    sp = Space(Atom[E(S("="), E(S("xoo"), S("a")), S("xa")),
                    E(S("="), E(S("xoo"), S("b")), S("xb"))])
    # collapse the nondeterministic (eval (xoo $a)), then superpose it back, keeping $a per branch:
    # (chain (collapse-bind (eval (xoo $a))) $c (chain (superpose-bind $c) $x ($x $a))) → [(xa a),(xb b)]
    prog = E(S("chain"), E(S("collapse-bind"), E(S("eval"), E(S("xoo"), V("a")))), V("c"),
              E(S("chain"), E(S("superpose-bind"), V("c")), V("x"), E(V("x"), V("a"))))
    rs = bare_eval(prog, sp)
    @test Set(rs) == Set(Atom[E(S("xa"), S("a")), E(S("xb"), S("b"))])
    @test length(rs) == 2
end
