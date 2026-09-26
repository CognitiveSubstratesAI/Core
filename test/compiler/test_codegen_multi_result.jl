# test_codegen_multi_result.jl — the NATIVE codegen lane's CALLING CONVENTION.
#
# ─── 🔴 WHY THIS FILE EXISTS ─────────────────────────────────────────────────────────────────────
# MEASURED 2026-09-25, by grepping the whole of `test/`: **NOTHING referenced `CODEGEN_ENABLED`,
# `codegen_head` or `CODEGEN_NATIVE_HEADS`.** The native lane — the one that emits Julia and hands it
# to LLVM, as opposed to `EmitJulia`'s plan-walking closures — had no test of any kind, and the plan
# on file was to switch it on by default. `EmitJulia.jl`'s seam docstring additionally cited
# `test_codegen_head_seam.jl` as its proof; that file does not exist.
#
# ─── WHAT THE CONVENTION IS, AND THE DEFECT IT REPLACES ─────────────────────────────────────────
# `codegen_head` used to emit `Atom[body₁, …, body_N]` — one element per clause, length fixed at
# codegen time. A clause could not answer zero times and could not answer twice, so `match`,
# `superpose`, `collapse` and EVERY MULTI-EQUATION FUNCTION declined, and the interpreter stayed the
# only lane that runs. It is now `f(sink, args)::Bool`, calling `sink` once per answer.
#
# 🔴 THE REGRESSION CASE IS `(g foo)` BELOW, and it is not hypothetical. Under the old shape a
# clause declining AT RUNTIME executed `return nothing` — from a function the seam immediately
# annotated `::Vector{Atom}`. Two answers were wrong at once: the surviving clause's answer was
# discarded, and the seam raised a `TypeError` rather than answering.
#
# ─── ANTI-VACUITY, TWO INDEPENDENT CHECKS ────────────────────────────────────────────────────────
#  1. `CODEGEN_NATIVE_HEADS[]` must be > 0. Without it a green run proves the PLAN-WALKING lane
#     works — that lane is always available and would answer identically.
#  2. The query space holds ONLY the stdlib; the rules are never loaded into it. An answer therefore
#     cannot come from an equation lookup, so it came from compiled code. This is the structural
#     form of "interpreter re-entry is zero" — there is no equation for the interpreter to find.
using MeTTaCore
using MeTTaCore.Eval
using Test

const _CGV = MeTTaCore.StandardMeTTa
const _CGF = MeTTaCore.CompilerFrontend
const _CGA = MeTTaCore.CompilerANormal
const _CGE = MeTTaCore.CompilerEmitJulia
const _CGC = MeTTaCore.CompilerEmitJuliaCode

"Parse → lower → A-normalise."
function _cg_clauses(sp, text::AbstractString)
    toks = Eval.tokenize(text); i = Ref(1); atoms = _CGV.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(atoms, Eval.parse_from(toks, i, sp.tokens))
    end
    _CGA.translate_program(_CGF.lower_program(atoms))
end

"A-normal clauses for ONE head, in source order."
function _cg_head(text::AbstractString, name::Base.Symbol)
    sp = Eval.Space(); load_core_stdlib!(sp)
    [c for c in _cg_clauses(sp, text) if c.name === name]
end

"Answers for `q` from COMPILED code only — rules are never loaded into the query space."
function _cg_ask(prog::AbstractString, q::AbstractString)
    sp = Eval.Space(); load_core_stdlib!(sp)
    was = _CGE.CODEGEN_ENABLED[]
    _CGE.CODEGEN_ENABLED[] = true
    local heads, native
    try
        heads  = _CGE.emit_julia_program(_cg_clauses(sp, prog))
        native = _CGE.CODEGEN_NATIVE_HEADS[]
    finally
        _CGE.CODEGEN_ENABLED[] = was
    end
    Eval.uncompile_all!()
    s2 = Eval.Space(); load_core_stdlib!(s2)          # ← rules deliberately NOT loaded
    for (h, fn) in heads
        Eval.compile_head!(h, fn, UInt64(1))
    end
    res = load_metta!(s2, q)
    Eval.uncompile_all!()
    (sort!([string(x) for y in res for x in (y isa AbstractVector ? y : [y])]), native)
end

"The same query through the INTERPRETER, rules loaded normally."
function _cg_interp(prog::AbstractString, q::AbstractString)
    Eval.uncompile_all!()
    s = Eval.Space(); load_core_stdlib!(s)
    load_metta!(s, prog)
    res = load_metta!(s, q)
    sort!([string(x) for y in res for x in (y isa AbstractVector ? y : [y])])
end

# Clause 1 DECLINES AT RUNTIME on a non-numeric argument (`+` answers NotReducible); clause 2 always
# answers. On a numeric argument BOTH answer, which is the multiplicity case.
const _CG_TWO = "(= (g \$x) (+ \$x 1))\n(= (g \$x) tagged)\n"

@testset "native codegen — the multi-result calling convention" begin

    @testset "🔴 a two-equation head COMPILES (it declined entirely before)" begin
        cls = _cg_head(_CG_TWO, :g)
        @test length(cls) == 2                       # ANTI-VACUITY: both equations reached A-normal
        @test _CGC.codegen_head(:g, cls) !== nothing
    end

    @testset "🔴 sink is called ONCE PER ANSWER — multiplicity, not a fixed-length vector" begin
        fn = _CGC.codegen_head(:g, _cg_head(_CG_TWO, :g))
        @test fn !== nothing

        got = _CGV.Atom[]
        @test Base.invokelatest(fn, (r, _b) -> (push!(got, r); true), _CGV.Atom[_CGV.Grounded(1)]) == true
        @test sort!(string.(got)) == ["2", "tagged"]

        # 🔴 `NotReducible` IS AN ANSWER. `+` cannot reduce `(+ foo 1)`, and MeTTa's answer for that
        # equation is the RESIDUAL TERM itself — the interpreter returns `(+ foo 1)`. The
        # expectation here originally read `["tagged"]`, encoding the belief that a declining
        # grounded call means "this clause has no answer"; the differential below disagreed with the
        # interpreter on its first run and that is what corrected it. The old shape was worse than
        # either: `return nothing` from a function the seam annotated `::Vector{Atom}`, a TypeError.
        got2 = _CGV.Atom[]
        @test Base.invokelatest(fn, (r, _b) -> (push!(got2, r); true), _CGV.Atom[_CGV.Sym("foo")]) == true
        @test sort!(string.(got2)) == ["(+ foo 1)", "tagged"]
    end

    @testset "sink returning false STOPS the producer — this is what `once` needs" begin
        fn = _CGC.codegen_head(:g, _cg_head(_CG_TWO, :g))
        got = _CGV.Atom[]
        # `false` on the FIRST answer: the producer must not run the second clause.
        @test Base.invokelatest(fn, (r, _b) -> (push!(got, r); false), _CGV.Atom[_CGV.Grounded(1)]) == false
        @test length(got) == 1
    end

    @testset "🔴 a multi-clause head MAY now recurse — the old decline was lifted, not forgotten" begin
        # It used to decline, and the reason was sound AT THE TIME: only `f_det` could be
        # self-called, a multi-clause head has none, so a callee answering twice would have had one
        # answer kept and the other dropped. What lifted it is the user-call case: in the loop path
        # a self-call is an ordinary call to the head's own ENTRY, which delivers every answer
        # through the sink. The differential is what makes that claim checkable rather than asserted.
        prog = "(= (down \$n) (if (== \$n 0) done (down (- \$n 1))))\n(= (down \$n) tag)\n"
        cls = _cg_head(prog, :down)
        @test length(cls) == 2
        @test _CGC.codegen_head(:down, cls) !== nothing
        compiled, native = _cg_ask(prog, "!(down 2)\n")
        interp = _cg_interp(prog, "!(down 2)\n")
        @test native > 0                          # ANTI-VACUITY: the NATIVE lane took it
        @test length(interp) > 1                  # ANTI-VACUITY: more than one answer to lose
        @test compiled == interp                  # sorted ⇒ multiset
    end

    @testset "🔴 A CALL TO ANOTHER HEAD — the capability the sink convention was built for" begin
        # Before this, a compiled head could call grounded ops and itself, nothing else. That single
        # restriction blocked 162 heads in `Core/lib` outright. The callee is named directly in the
        # generated code, so which heads compile is a FIXPOINT — `emit_julia_program` shrinks the
        # candidate set until stable, and a callee that drops takes its callers with it.
        prog = "(= (inner \$x) (+ \$x 1))\n(= (outer \$y) (inner (* \$y 2)))\n"
        # In ISOLATION `outer` must decline: nothing promises `inner` will be registered.
        @test _CGC.codegen_head(:outer, _cg_head(prog, :outer)) === nothing
        # Told that `inner` compiles, it must take it.
        @test _CGC.codegen_head(:outer, _cg_head(prog, :outer),
                                Set([:inner])) !== nothing
        compiled, native = _cg_ask(prog, "!(outer 20)\n")
        interp = _cg_interp(prog, "!(outer 20)\n")
        @test native >= 2                         # BOTH heads native, not just the leaf
        @test interp == ["41"]                    # ANTI-VACUITY: the query is not vacuous
        @test compiled == interp
    end

    @testset "a callee that CANNOT compile disqualifies its caller — the fixpoint shrinks" begin
        # `mid` calls `leaf`, and `leaf` has a pattern head arg, so `leaf` declines. `mid` must then
        # decline too rather than name an entry that was never registered — a MethodError at runtime.
        prog = "(= (leaf 0) zero)\n(= (mid \$x) (leaf \$x))\n"
        @test _CGC.codegen_head(:leaf, _cg_head(prog, :leaf)) === nothing
        @test _CGC.codegen_head(:mid, _cg_head(prog, :mid), Set{Symbol}()) === nothing
    end

    @testset "the deterministic path is preserved — one clause still emits `_det`" begin
        cls = _cg_head("(= (inc \$x) (+ \$x 1))\n", :inc)
        @test length(cls) == 1
        fn = _CGC.codegen_head(:inc, cls)
        @test fn !== nothing
        got = _CGV.Atom[]
        @test Base.invokelatest(fn, (r, _b) -> (push!(got, r); true), _CGV.Atom[_CGV.Grounded(41)]) == true
        @test string.(got) == ["42"]
        # The det path must residualise too, not answer zero times — same rule as above.
        res = _CGV.Atom[]
        @test Base.invokelatest(fn, (r, _b) -> (push!(res, r); true), _CGV.Atom[_CGV.Sym("foo")]) == true
        @test string.(res) == ["(+ foo 1)"]
    end

    @testset "🔴 DIFFERENTIAL vs the interpreter — MULTISET parity, end to end through the seam" begin
        for q in ("!(g 1)\n", "!(g foo)\n")
            compiled, native = _cg_ask(_CG_TWO, q)
            interp = _cg_interp(_CG_TWO, q)
            @test native > 0                          # ANTI-VACUITY 1: the NATIVE lane took the head
            @test !isempty(interp)                    # ANTI-VACUITY 2: the query is not vacuous
            @test compiled == interp                  # sorted ⇒ multiset, order unspecified
        end
    end

    @testset "🔴 DET SELF-RECURSION — one Julia call, no sink, no seam re-entry" begin
        # The deterministic entry is the ONLY thing a self-call may target, and this rewrite changed
        # that call site: it used to allocate a `Vector{Atom}` per return and check its length, and
        # now returns the `Atom`. `fib` itself declines — its equations dispatch on CONSTANT head
        # args — so the recursive shape is exercised through a single-clause head with a `GBranch`.
        prog = "(= (countdown \$n) (if (== \$n 0) done (countdown (- \$n 1))))\n"
        cls = _cg_head(prog, :countdown)
        @test length(cls) == 1
        fn = _CGC.codegen_head(:countdown, cls)
        @test fn !== nothing
        got = _CGV.Atom[]
        @test Base.invokelatest(fn, (r, _b) -> (push!(got, r); true), _CGV.Atom[_CGV.Grounded(200)]) == true
        @test string.(got) == ["done"]               # 200 recursive calls, one answer
        # and the same answer through the interpreter, which is the only authority on what it is
        @test _cg_interp(prog, "!(countdown 200)\n") == ["done"]
    end

    @testset "🔴 `superpose` — a goal that answers N times, as nested loops" begin
        # The ONLY in-scope `Operation` measured able to answer with != 1 result. A head calling it
        # has no deterministic entry, so it takes the loop path even with a single clause.
        prog = "(= (pick \$x) (superpose (\$x 7 9)))\n"
        cls = _cg_head(prog, :pick)
        fn = _CGC.codegen_head(:pick, cls)
        if fn === nothing
            @test_broken false   # records that the form is not yet reaching codegen, with the reason visible
        else
            got = _CGV.Atom[]
            @test Base.invokelatest(fn, (r, _b) -> (push!(got, r); true), _CGV.Atom[_CGV.Grounded(5)]) == true
            @test sort!(string.(got)) == ["5", "7", "9"]
        end
    end

    @testset "🔴 SINK TAKES BINDINGS — the parameter exists before anything produces them" begin
        # ORACLE, 2026-09-25: `(= (p (S $x)) (got $x))` then `!(let $r (p $y) ($y $r))` gives
        #   hyperon [((S $x#38) (got $x#38))] · CeTTa [((S $x#1) (got $x#1))] · Core same shape.
        # `$y` TOOK THE VALUE `(S $x)`: a binding made inside the callee reaches the caller, and the
        # same variable appears in both positions. A sink that receives only the answer atom cannot
        # carry that. Nothing produces bindings YET — head args are bound positionally — so the
        # generators pass `nothing`; the signature is widened now because head-argument PATTERNS is
        # what starts producing them, and widening afterwards means rewriting every call site.
        fn = _CGC.codegen_head(:g, _cg_head(_CG_TWO, :g))
        seen = Any[]
        @test Base.invokelatest(fn, (r, b) -> (push!(seen, (r, b)); true),
                                _CGV.Atom[_CGV.Grounded(1)]) == true
        @test length(seen) == 2
        @test all(x -> x[2] === nothing, seen)      # today: positional binding, so no bindings

        # and the SEAM turns that `nothing` into a real empty `Bindings`, one per answer, because
        # `CompiledOk` is what `rule_results` substitutes through.
        was = _CGE.CODEGEN_ENABLED[]; _CGE.CODEGEN_ENABLED[] = true
        try
            heads = _CGE.emit_julia_program(_cg_clauses(Eval.Space(), _CG_TWO))
            @test haskey(heads, :g)
        finally
            _CGE.CODEGEN_ENABLED[] = was
        end
    end

    @testset "🔴 CENSUS GATE — no op outside `_NONDET_OPS` may answer with != 1 result" begin
        # `_NONDET_OPS` is a MEASUREMENT (2026-09-25: `superpose`, alone among 80 in-scope
        # `Operation`s), and the deterministic fast path is generated on the strength of it. A new
        # multi-valued op registered later would make `_det` drop answers SILENTLY. So the census is
        # re-run here rather than recorded in a comment that rots:
        # `[[feedback_enforcement_works_prose_memory_does_not]]`.
        G(x) = _CGV.Grounded(x); Sy(x) = _CGV.Sym(x)
        E(xs...) = _CGV.Expression(_CGV.Atom[xs...])
        probes = [_CGV.Atom[], _CGV.Atom[G(1)], _CGV.Atom[G(1), G(2)], _CGV.Atom[G(1), G(2), G(3)],
                  _CGV.Atom[E(G(1), G(2), G(3))], _CGV.Atom[E(G(1), G(2)), E(G(2), G(3))],
                  _CGV.Atom[Sy("a")], _CGV.Atom[Sy("a"), Sy("b")],
                  _CGV.Atom[E(Sy("a"), Sy("b")), Sy("a")], _CGV.Atom[G(1), E(G(1), G(2))]]
        skip = Set(["println!", "trace!", "table!", "change-state!", "new-space", "fork-space",
                    "new-mork-space"])
        checked = 0; offenders = String[]
        for (k, v) in Eval.TOKEN_REGISTRY
            (v isa _CGV.Grounded && v.value isa Eval.Operation) || continue
            k in skip && continue
            checked += 1
            for a in probes
                try
                    r = v.value.fn(a)
                    if r isa Eval.ExecOk && length(r.results) != 1 && !(k in _CGC._NONDET_OPS)
                        push!(offenders, string(k, " -> ", length(r.results)))
                    end
                catch; end
            end
        end
        @test checked > 50                      # ANTI-VACUITY: a census that found nothing passes
        @test unique!(offenders) == String[]
    end
end
