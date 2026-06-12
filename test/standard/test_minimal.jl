# Validates the minimal-MeTTa stack machine (src/standard/Minimal.jl) against the
# worked examples in hyperon docs/minimal-metta.md (cons-atom/decons-atom/unify).
# eval/chain/function/collapse are Phase 0c/0d — not yet ported.
include("../../src/standard/Minimal.jl")
using .Minimal
using .Minimal.StandardMeTTa
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
