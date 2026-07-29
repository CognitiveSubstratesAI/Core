# Guard-clause regressions in grounded primitives.
#
# `a || b && return X` parses as `a || (b && return X)` because `&&` binds tighter than `||`.
# So when `a` is TRUE the expression short-circuits, the return NEVER RUNS, and execution FALLS
# THROUGH past a guard that was written to stop it. The guard reads as protective and is inert —
# the fail-open shape.
#
# Found by sweeping the whole workspace for the pattern: 12 armed sites across Core and
# MorkSupercompiler, of which one already carried a comment recording that this exact bug had been
# fixed AT THAT SITE while the others were left armed. These are the two that were reachable and
# actually crashed, proven by A/B on a warm process (revert file → probe → restore):
#
#   MetaMo.blend-vec, empty current vector "()"  → BoundsError (0-element Vector{String})
#                                                  from `tag = cur_toks[1]` at Primitives.jl:408
#   MetaMo.blend-vec, non-numeric token          → MethodError *(::Float64, ::Nothing)
#                                                  from `(1-alpha) * c` at Primitives.jl:413
#
# Both guards were meant to bail with `args[2]` (the current vector, unchanged).
using MeTTaCore, Test
const MC = MeTTaCore

@testset "grounded-primitive guards FAIL CLOSED (operator-precedence regression)" begin
    MC._register_metamo_primitives!()
    blend = MC.MORK.GROUNDED_REGISTRY["MetaMo.blend-vec"]

    # Each of these hit a fall-through crash before the fix; each must now return args[2] verbatim.
    @test blend(["0.5", "()",          "(G 1.0 2.0)"]) == "()"          # empty current  → BoundsError
    @test blend(["0.5", "(G 1.0)",     "()"])          == "(G 1.0)"     # empty target
    @test blend(["0.5", "(G x 2.0)",   "(G 1.0 2.0)"]) == "(G x 2.0)"   # non-numeric cur → MethodError
    @test blend(["0.5", "(G 1.0)",     "(G y)"])       == "(G 1.0)"     # non-numeric tgt
    @test blend(["0.5", "(G 1.0 2.0)", "(G 1.0)"])     == "(G 1.0 2.0)" # length mismatch

    # …and the well-formed path is untouched: 0.0 + 0.5·(1.0-0.0) = 0.5, 0.0 + 0.5·(2.0-0.0) = 1.0
    @test blend(["0.5", "(G 0.0 0.0)", "(G 1.0 2.0)"]) == "(G 0.5 1.0)"
    @test blend(["0.0", "(G 3.0)",     "(G 9.0)"])     == "(G 3.0)"     # alpha 0 ⇒ current
    @test blend(["1.0", "(G 3.0)",     "(G 9.0)"])     == "(G 9.0)"     # alpha 1 ⇒ target
    # a non-numeric alpha bails to args[2] via its own (correctly written) guard at :399
    @test blend(["abc", "(G 3.0)",     "(G 9.0)"])     == "(G 3.0)"
    @test blend(["0.5"])                               == "0.5"         # arity guard at :397

    # The third swept site, `_alpha_eq_val` (Primitives.jl:208). This one was fail-open in FORM but
    # not in EFFECT — the fall-through landed on `a == b`, which is already false for a `$var` vs a
    # non-var — so it is pinned for shape, not because it ever returned a wrong answer.
    ab = Dict{Symbol,Symbol}(); ba = Dict{Symbol,Symbol}()
    @test !MC._alpha_eq_val(Symbol("\$x"), :foo, ab, ba)   # var vs non-var
    @test !MC._alpha_eq_val(:foo, Symbol("\$x"), ab, ba)   # non-var vs var
    @test  MC._alpha_eq_val(Symbol("\$x"), Symbol("\$y"), Dict{Symbol,Symbol}(), Dict{Symbol,Symbol}())
    @test  MC._alpha_eq_val(:foo, :foo, ab, ba)
    @test !MC._alpha_eq_val(:foo, :bar, ab, ba)
end
