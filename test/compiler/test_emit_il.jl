# test_emit_il.jl — the MeTTa → MeTTa-IL stage must produce IL that COMPUTES THE SAME ANSWERS.
#
# ─── WHY THE ASSERTIONS ARE ANSWERS, NOT TEXT ────────────────────────────────────────────────────
# The obvious test for an emitter is `occursin("chain", out)`. That test passes for an emitter that
# produces well-formed nonsense. This session already produced two of those: a staging test that
# asserted `42` when the callee emitted `42` on its own, and a `case` benchmark that measured trie
# deduplication. So the oracle here is EXECUTION: emit the IL, load it into a fresh Space, evaluate
# the query, and compare against the SAME source program run through the interpreter directly.
#
# That works only because minimal MeTTa is executable on arrival — `Eval.jl:40` MINIMAL_OPS already
# implements every instruction this stage emits. If the IL and the source disagree, the emission is
# wrong; there is no third possibility and no text pattern to argue about.
#
# The oracle's OWN values are pinned too (`@test oracle == [...]`), so a broken oracle cannot make the
# comparison vacuously true.
using MeTTaCore
using Test

const _IF = MeTTaCore.CompilerFrontend
const _IA = MeTTaCore.CompilerANormal
const _IE = MeTTaCore.CompilerEmit
const _IL = MeTTaCore.CompilerEmitIL
const _IV = MeTTaCore.Eval

function _il_parse(sp, text::AbstractString)
    toks = _IV.tokenize(text); i = Ref(1); out = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _IV.parse_from(toks, i, sp.tokens))
    end
    out
end

"Compile `src` to minimal MeTTa."
function _to_il(src::AbstractString)
    sp = _IV.Space(); _IV.load_core_stdlib!(sp)
    cls = _IA.translate_program(_IF.lower_program(_il_parse(sp, src)))
    (_IL.emit_il_program(cls), cls)
end

"Evaluate `query` against a Space loaded with `defs`; return sorted answer strings."
function _answers(defs::Vector{String}, query::AbstractString)::Vector{String}
    sp = _IV.Space(); _IV.load_core_stdlib!(sp)
    for d in defs; _IV.load_metta!(sp, d); end
    res = _IV.load_metta!(sp, "!" * query)
    sort(String[string(x) for r in res for x in (r isa AbstractVector ? r : [r])])
end

"THE DIFFERENTIAL: source-through-interpreter vs compiled-IL-through-interpreter."
function _agree(src::AbstractString, query::AbstractString)
    r, _ = _to_il(src)
    src_forms = String[strip(l) for l in split(src, '\n') if !isempty(strip(l))]
    (interp = _answers(src_forms, query), il = _answers(r.clauses, query), result = r)
end

@testset "MeTTa → MeTTa-IL (minimal MeTTa) emitter" begin

    @testset "ORACLE: a call chain computes the same answer through the IL" begin
        a = _agree("(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n", "(f 7)")
        @test a.interp == ["7"]            # the oracle is what we think it is
        @test a.il == a.interp             # and the IL agrees
        @test a.result.emitted == 2
        @test isempty(a.result.declined)
    end

    @testset "ORACLE: arithmetic through the IL" begin
        a = _agree("(= (inc \$x) (+ \$x 1))\n", "(inc 41)")
        @test a.interp == ["42"]
        @test a.il == a.interp
    end

    @testset "ORACLE: a `let` (GUnify) survives lowering" begin
        a = _agree("(= (h \$x) (let \$y \$x (pair \$y \$y)))\n", "(h 3)")
        @test a.interp == ["(pair 3 3)"]
        @test a.il == a.interp
    end

    @testset "the emitted form is minimal MeTTa, not MM2" begin
        r, _ = _to_il("(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n")
        joined = join(r.clauses, "\n")
        @test occursin("(function ", joined)        # clause body is a function/return
        @test occursin("(return ", joined)
        @test occursin("(chain (eval ", joined)     # calls are chain+eval
        @test !occursin("(exec ", joined)           # and emphatically NOT MM2 exec atoms
        @test !occursin("(O ", joined)
    end

    @testset "ORACLE: BOTH arms of a branch — the else path must be reachable" begin
        # REGRESSION, 2026-08-09. The first version emitted `(unify condval True then else)` — but
        # `GBranch.condval` is the LITERAL `True`, not a variable to test (the real test lives in
        # `cond` as `GUnify($__t1, True)`, and `els` holds a NESTED GBranch for the next arm). So the
        # emitted form was `(unify True True A B)`, a constant that can never select B: the else arm
        # was emitted into unreachable position and a failing condition fell to `(return Empty)`.
        #
        # `(k 1)` was RIGHT and `(k 2)` returned nothing. The earlier branch test only asserted
        # `il.emitted >= mm2.emitted` — it counted the clause without ever evaluating it, which is
        # precisely the "well-formed nonsense" this file's header warns about. Both arms now execute.
        src = "(= (k \$x) (if (== \$x 1) one other))\n"
        hit  = _agree(src, "(k 1)")
        @test hit.interp == ["one"]
        @test hit.il == hit.interp
        miss = _agree(src, "(k 2)")
        @test miss.interp == ["other"]        # the oracle takes the else arm
        @test miss.il == miss.interp          # ← failed before the fix: the IL returned nothing
    end

    @testset "ORACLE: a nested if-chain reaches its last arm" begin
        src = "(= (k \$x) (if (== \$x 1) one (if (== \$x 2) two three)))\n"
        for (q, want) in (("(k 1)", ["one"]), ("(k 2)", ["two"]), ("(k 9)", ["three"]))
            a = _agree(src, q)
            @test a.interp == want
            @test a.il == a.interp
        end
    end

    @testset "COVERAGE: shapes Emit.jl declines, the IL emits" begin
        # Emit.jl:30-31 emits only all-GCall/GUnify clauses. Each program below contains a goal type
        # it declines. Both emitters are run on the SAME clauses so the comparison is exact.
        for (label, src) in (("branch",  "(= (k \$x) (if (== \$x 1) one other))\n"),
                             ("collapse", "(= (c) (collapse (superpose (1 2))))\n"))
            sp = _IV.Space(); _IV.load_core_stdlib!(sp)
            cls = _IA.translate_program(_IF.lower_program(_il_parse(sp, src)))
            il  = _IL.emit_il_program(cls)
            mm2 = _IE.emit_program(cls)
            @test length(cls) >= 1
            # The IL must do at least as well as MM2 on every shape — never worse.
            @test il.emitted >= mm2.emitted
        end
    end

    @testset "GResidual DECLINES, with a reason, and is never dropped" begin
        # A clause that A-normalization could not flatten must be counted, not silently omitted.
        sp = _IV.Space(); _IV.load_core_stdlib!(sp)
        cls = _IA.translate_program(_IF.lower_program(_il_parse(sp, "(= (f \$x) (g \$x))\n")))
        # synthesize a residual clause so the decline path is exercised deterministically
        resid = _IA.ANClause(Base.Symbol("r"), MeTTaCore.CompilerIR.IRAtom[],
                             _IA.Goal[_IA.GResidual(cls[1].out, cls[1].out)], cls[1].out)
        r = _IL.emit_il_program(_IA.ANClause[resid])
        @test r.emitted == 0
        @test length(r.declined) == 1
        @test r.declined[1][1] == Base.Symbol("r")
        @test occursin("GResidual", r.declined[1][2])    # a REASON, not a bare tally
    end

    @testset "empty program is empty, not an error" begin
        r = _IL.emit_il_program(_IA.ANClause[])
        @test r.emitted == 0 && isempty(r.clauses) && isempty(r.declined)
    end

    @testset "types are concrete — no Any containers" begin
        r, _ = _to_il("(= (f \$x) (g \$x))\n")
        @test r isa _IL.ILResult
        @test r.clauses isa Vector{String}
        @test r.declined isa Vector{Tuple{Base.Symbol, String}}
        @test isconcretetype(fieldtype(_IL.ILResult, :clauses))
        @test isconcretetype(fieldtype(_IL.ILResult, :emitted))
    end
end
