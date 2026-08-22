# test_definition_name.jl — WHICH FUNCTION IS THIS DEFINITION ABOUT? Get it wrong and unrelated
# functions MERGE.
#
# ─── WHY A WHOLE FILE FOR ONE FUNCTION ───────────────────────────────────────────────────────────
# `lower_program` groups clauses BY NAME, because MeTTa functions are multi-clause and every matching
# clause contributes a result. So `definition_name` is not a label — it is the identity relation on
# definitions, and a name that is wrong in the SAME WAY for two definitions silently declares them
# one function.
#
# That is exactly what happened. The head of a definition's LHS can be a `Sym`, a `Grounded` (parse
# time substitutes registered ops, so `id`/`match`/`+` never arrive as `Sym`), or an EXPRESSION —
# and only the first two were handled. A curried definition has the third:
#
#     (= (((curry $f) $x) $y) ($f $x $y))        head is ((curry $f) $x)
#     (= ((curry-a $f $a) $b) ($f $a $b))        head is (curry-a $f $a)
#     (= ((lambda $v $b) $arg) (let $v $arg $b)) head is (lambda $v $b)
#
# All three fell through to `Symbol("")`, so all three became ONE `IRFunctionDefinition` with three
# clauses — measured 2026-08-11 — which then partially emitted (1 of 3). Every shape in
# `d2_higherfunc.metta` is this.
#
# ⚠️ THIS IS THE THIRD INSTANCE OF ONE RULE: Sym, then Grounded (`Frontend.jl:199` records that
# sweep and says a recurring defect gets the rule applied to every candidate site, not a fix where it
# was noticed), now Expression. The rule is "a definition's head is not always a symbol." This file
# enumerates all four head kinds so a fourth cannot arrive unnoticed.
using MeTTaCore
using Test

const _DN_F = MeTTaCore.CompilerFrontend
const _DN_V = MeTTaCore.Eval
const _DN_S = MeTTaCore.StandardMeTTa

"Parse every top-level form of `src` in a stdlib-loaded space (so registered ops arrive Grounded)."
function _dn_parse(src::AbstractString)
    sp = _DN_V.Space()
    _DN_V.load_core_stdlib!(sp)
    toks = _DN_V.tokenize(src)
    i = Ref(1)
    out = _DN_S.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _DN_V.parse_from(toks, i, sp.tokens))
    end
    out
end

_dn_names(src) = [String(d.name) for d in _DN_F.lower_program(_dn_parse(src)).definitions]

@testset "definition_name — the head of a definition is not always a symbol" begin

    @testset "all four head kinds, each in isolation" begin
        @test _dn_names("(= (twice \$x) (+ \$x \$x))") == ["twice"]   # Sym
        @test _dn_names("(= (id \$x) \$x)") == ["id"]      # Grounded op
        @test _dn_names("(= ((curry-a \$f \$a) \$b) (\$f \$a \$b))") == ["curry-a"] # Expression, 1 deep
        @test _dn_names("(= (((curry \$f) \$x) \$y) (\$f \$x \$y))") == ["curry"]   # Expression, 2 deep
        # A VARIABLE head names nothing, and descending cannot help. The sentinel is correct here —
        # what must not happen is two of them being treated as the same function (next testset).
        @test _dn_names("(= ((\$f \$x) \$y) \$y)") == [""]
    end

    @testset "THE DEFECT: distinct compound-head functions must not MERGE" begin
        src =
            "(= (((curry \$f) \$x) \$y) (\$f \$x \$y))\n" *
            "(= ((curry-a \$f \$a) \$b) (\$f \$a \$b))\n" *
            "(= ((lambda \$v \$b) \$arg) (let \$v \$arg \$b))\n"
        prog = _DN_F.lower_program(_dn_parse(src))
        # Measured BEFORE the fix: 1 definition named "" holding 3 clauses.
        @test length(prog.definitions) == 3
        @test sort([String(d.name) for d in prog.definitions]) ==
            ["curry", "curry-a", "lambda"]
        @test all(length(d.clauses) == 1 for d in prog.definitions)
    end

    @testset "un-nameable heads are not grouped with each other either" begin
        # Two variable-headed definitions are not KNOWN to be one function, so the sentinel must not
        # act as a name. Before the fix these merged for the same reason the curried ones did.
        src = "(= ((\$f \$x) \$y) \$y)\n(= ((\$g \$a) \$b) \$a)\n"
        prog = _DN_F.lower_program(_dn_parse(src))
        @test length(prog.definitions) == 2
        @test all(length(d.clauses) == 1 for d in prog.definitions)
    end

    @testset "genuine multi-clause grouping still WORKS — the fix must not over-separate" begin
        # The whole point of grouping. Two clauses of one function stay one definition, whether the
        # head is a symbol or compound. Over-separating would break dispatch as surely as merging
        # broke identity, and it would look like success in the testsets above.
        @test _dn_names("(= (f 0) zero)\n(= (f \$n) other)\n") == ["f"]
        prog = _DN_F.lower_program(_dn_parse("(= (f 0) zero)\n(= (f \$n) other)\n"))
        @test length(prog.definitions) == 1 && length(prog.definitions[1].clauses) == 2

        src = "(= ((curry-a \$f \$a) \$b) (\$f \$a \$b))\n(= ((curry-a \$f \$a) 0) zero)\n"
        prog2 = _DN_F.lower_program(_dn_parse(src))
        @test length(prog2.definitions) == 1
        @test String(prog2.definitions[1].name) == "curry-a"
        @test length(prog2.definitions[1].clauses) == 2
    end

    @testset "a bare fact is still not a definition" begin
        # `(edge a b)` yields no definition at all — it is data, and counting it as a compiler
        # decline would misreport coverage. Asserted because the loop above touches the same path.
        @test isempty(_DN_F.lower_program(_dn_parse("(edge a b)")).definitions)
    end
end
