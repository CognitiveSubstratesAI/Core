# ============================================================================================
# `(: name type)` declarations are VISIBLE TO THE COMPILER.
#
# Until 2026-08-12 they were not: `lower_program` recognised `(= …)` definitions and turned everything
# else into an `IRRun`, so a type declaration was an opaque top-level form. The compiler therefore had
# NO type information at all.
#
# WHY THAT MATTERED. Every upstream that resolves "is this expression a CALL or a DATA TUPLE" consults
# types to do it (`docs/specs/expression_head_call_vs_data_four_upstreams.md`):
#   * hyperon `interpret_expression` forks on whether the head has a function type, with %Undefined%
#     qualifying for the tuple reading;
#   * MeTTaScript's predicate is *defined-head symbol OR arrow-typed head* → function, else tuple;
#   * CeTTa infers a total product type and rejects only what provably fails.
# We had the defined-head half (PeTTa's `fun/1`, in `ANormal`) and no way to compute the other half. That
# is why expression-headed clauses are declined — 41 of 66 declines, the largest open item.
#
# ⚠️ CAPTURE ONLY. Nothing consults `has_arrow_type` yet. Capturing and USING are deliberately separate
# changes: the previous attempt to widen expression-head lowering committed to one static reading and
# broke `test_stdlib.metta` on `(() () $l2)`. This lands the information with its own tests first.
# ============================================================================================

using Test
using MeTTaCore
const _TD_V = MeTTaCore.Eval
const _TD_SM = MeTTaCore.StandardMeTTa
const _TD_FR = MeTTaCore.CompilerFrontend
const _TD_IR = MeTTaCore.CompilerIR

"Parse every top-level form of `src`."
function _td_parse(src::AbstractString)::Vector{_TD_SM.Atom}
    sp = _TD_V.Space(); toks = _TD_V.tokenize(String(src)); i = Ref(1)
    out = _TD_SM.Atom[]
    while i[] <= length(toks)
        push!(out, _TD_V.parse_from(toks, i, sp.tokens))
    end
    out
end

@testset "type declarations reach the IR, and do not change what the program does" begin
    prog = _TD_FR.lower_program(_td_parse("""
        (: foo (-> Number Number))
        (: bar Number)
        (: foo (-> String String))
        (= (foo \$x) \$x)
    """))

    # SEVERAL types per name accumulate. hyperon permits an atom to carry more than one type and
    # `get_atom_types` returns them all — collapsing to one would silently pick a winner.
    @test length(_TD_IR.declared_types(prog, :foo)) == 2
    @test length(_TD_IR.declared_types(prog, :bar)) == 1
    @test isempty(_TD_IR.declared_types(prog, :never_declared))

    # The arrow predicate — the half of MeTTaScript's call-vs-data test we could not compute before.
    @test _TD_IR.has_arrow_type(prog, :foo)
    @test !_TD_IR.has_arrow_type(prog, :bar)          # declared, but not a function type
    @test !_TD_IR.has_arrow_type(prog, :never_declared)

    # 🔴 THE SAFETY PROPERTY. Recording a declaration must not REMOVE it from the program: `get-type`
    # and the evaluator's own checks read declarations out of the space, so the atom still has to be
    # loaded. All three non-definition forms remain runs, and the one definition is still a definition.
    @test length(prog.runs) == 3
    @test length(prog.definitions) == 1
end

@testset "only a SYMBOL subject is recorded" begin
    # `(: (f $x) T)` declares the type of an APPLICATION, not of a name — there is nothing to key it by,
    # and inventing a key (say `f`) would attribute a type to the function that its application has.
    prog = _TD_FR.lower_program(_td_parse("(: (f \$x) Number)\n(: g Number)"))
    @test isempty(_TD_IR.declared_types(prog, :f))
    @test length(_TD_IR.declared_types(prog, :g)) == 1
    @test length(prog.runs) == 2                       # both still reach the space
end

@testset "a `:` arriving as a grounded token is still recognised" begin
    # `parse_from` substitutes bound tokens at parse time (Eval.jl:2648), so a registered name can
    # arrive as `Grounded{Operation}` rather than `Sym`. Checking only `Sym` is the exact bug that made
    # `Frontend.lower` miss special forms — see its own comment. Same trap, same guard.
    sp = _TD_V.Space(); _TD_V.load_core_stdlib!(sp)
    toks = _TD_V.tokenize("(: h (-> Number Bool))"); i = Ref(1)
    a = _TD_V.parse_from(toks, i, sp.tokens)           # `:` resolved through the stdlib token table
    prog = _TD_FR.lower_program(_TD_SM.Atom[a])
    @test _TD_IR.has_arrow_type(prog, :h)
end
