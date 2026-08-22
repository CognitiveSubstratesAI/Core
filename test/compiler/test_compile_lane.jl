# test_compile_lane.jl — COMPILER-PRIMARY execution must give the interpreter's answers.
#
# ─── THE ONLY ASSERTION THAT MATTERS ─────────────────────────────────────────────────────────────
# `compile_run` lowers each definition to minimal MeTTa and evaluates the IL. It is correct exactly
# when it answers what the interpreter answers on the same source. So every test here is a
# DIFFERENTIAL, and the interpreter is the oracle.
#
# ⚠️ THE TRAP THIS FILE IS SHAPED AROUND: `compile_run` falls back to source for declined definitions.
# A differential that passes because everything FELL BACK proves nothing about the compiler — it
# proves the interpreter equals itself. So the compiled cases assert `fell_back == 0`, and the
# strongest ones pass `fallback=false`, which turns a decline into an error instead of a rescue.
using MeTTaCore
using Test

const _CL_V = MeTTaCore.Eval

"Interpreter oracle: the same forms, in order, through one Space."
function _cl_interp(program::AbstractString)::Vector{Tuple{String, Vector{String}}}
    sp = _CL_V.Space()
    _CL_V.load_core_stdlib!(sp)
    out = Tuple{String, Vector{String}}[]
    for (bang, f) in MeTTaCore.mm2_split_forms(program)
        res = _CL_V.load_metta!(sp, bang ? "!" * f : f)
        bang && push!(
            out,
            (String(f),
                sort(
                    String[
                        string(x) for y in res for x in (y isa AbstractVector ? y : [y])
                    ]
                ))
        )
    end
    out
end

"Parse program text to surface atoms without evaluating — for emitter-level assertions."
function _cl_parse(text::AbstractString)
    sp = _CL_V.Space()
    _CL_V.load_core_stdlib!(sp)
    toks = _CL_V.tokenize(text)
    i = Ref(1)
    out = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _CL_V.parse_from(toks, i, sp.tokens))
    end
    out
end

_cl_sorted(a) = Tuple{String, Vector{String}}[(q, sort(v)) for (q, v) in a]

@testset "compile lane — compiler primary, interpreter as the IL's evaluator" begin

    @testset "DIFFERENTIAL: compiled answers == interpreter answers, with NOTHING falling back" begin
        for src in ("(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n!(f 7)\n",
            "(= (inc \$x) (+ \$x 1))\n!(inc 41)\n",
            "(= (h \$x) (let \$y \$x (pair \$y \$y)))\n!(h 3)\n")
            r = MeTTaCore.compile_run(src)
            @test r.fell_back == 0                        # the COMPILER produced this, not the fallback
            @test r.compiled > 0
            @test _cl_sorted(r.answers) == _cl_interp(src)
        end
    end

    @testset "fallback=false proves the compiled path alone answered" begin
        # If any definition were declined this errors instead of quietly producing the right answer.
        r = MeTTaCore.compile_run(
            "(= (f \$x) (g \$x))\n(= (g \$x) \$x)\n!(f 7)\n"; fallback=false
        )
        @test r.answers == [("(f 7)", ["7"])]
        @test r.fell_back == 0
    end

    @testset "INVARIANT 1 holds on the compiled lane too" begin
        # The defect fixed on 2026-08-08 for mc_run must not reappear here: a query may not see a
        # rule added after it. compile_run drives the same partition, so this is a regression lock.
        src = "(= (f) a)\n!(f)\n(= (f) b)\n!(f)\n"
        r = MeTTaCore.compile_run(src)
        got = Vector{String}[sort(v) for (_, v) in r.answers]
        @test got == [["a"], ["a", "b"]]
        @test got == Vector{String}[v for (_, v) in _cl_interp(src)]
    end

    @testset "a DECLINED definition falls back to source and still answers" begin
        # Ground facts are not definitions and must not be counted as declines; a genuinely
        # uncompilable body must fall back rather than lose answers.
        src = "(edge a b)\n(= (q \$x \$y) (match &self (edge \$x \$y) (edge \$x \$y)))\n!(q a b)\n"
        r = MeTTaCore.compile_run(src)
        @test _cl_sorted(r.answers) == _cl_interp(src)     # answers preserved whatever the route
    end

    @testset "NO DOUBLE-LOADING: a compiled definition contributes once, not twice" begin
        # Loading both the IL form and the source form would not "prefer" the compiled one — MeTTa
        # dispatch yields EVERY match (Invariant 6), so answers would duplicate. This is the single
        # correctness constraint of the lane.
        src = "(= (f) one)\n!(f)\n"
        r = MeTTaCore.compile_run(src)
        @test r.answers == [("(f)", ["one"])]              # exactly one result, not ["one","one"]
    end

    @testset "multi-clause dispatch keeps ALL results" begin
        src = "(= (f 0) zero)\n(= (f \$x) other)\n!(f 0)\n"
        r = MeTTaCore.compile_run(src)
        @test _cl_sorted(r.answers) == _cl_interp(src)
        @test length(r.answers[1][2]) == 2                 # both clauses fired
    end

    @testset "empty program, and a program with no queries" begin
        @test isempty(MeTTaCore.compile_run("").answers)
        r = MeTTaCore.compile_run("(= (f) a)\n")
        @test isempty(r.answers) && r.compiled == 1
    end

    @testset "types are concrete — no Any containers" begin
        r = MeTTaCore.compile_run("(= (f) a)\n!(f)\n")
        @test r.answers isa Vector{Tuple{String, Vector{String}}}
        @test r.compiled isa Int && r.fell_back isa Int
    end

    @testset "MATCH over the atomspace — compiled, and the GUARD that keeps it sound" begin
        # `match` is the largest fragment the IL unlocked (109 declined clauses -> 3, emitted
        # 726 -> 832), and it is also the one with a real wrong-answer hazard, so it is tested HERE —
        # through `compile_run`, the whole-program lane — rather than through the emitter harness.
        # THE REASON IS THE HAZARD ITSELF: a compiled program's `&self` holds the EMITTED IL clauses
        # in place of the source rules. The emitter harness loads only `r.clauses`, so a `match` test
        # there would query a space with no facts in it and pass for the wrong reason.

        # DATA-SHAPED PATTERN ⇒ lowered, and it must answer what the interpreter answers.
        src =
            "(likes alice bob)\n(likes carol dave)\n" *
            "(= (who \$y) (match &self (likes \$x \$y) \$x))\n!(who bob)\n!(who dave)\n"
        r = MeTTaCore.compile_run(src)
        # ⚠️ `fell_back` IS NOT ZERO HERE, and expecting it to be was a wrong assertion about the
        # LANE, not a compiler defect. `compile_run` counts every non-compilable DEF FORM as a
        # fallback, and a bare fact `(likes alice bob)` is a def form with no `(=)` to compile — it is
        # data, loaded as-is. So the meaningful claim is that the RULE compiled:
        @test r.compiled == 1                           # `who` went through the compiler
        @test r.fell_back == 2                          # …and exactly the two FACTS did not
        @test _cl_sorted(r.answers) == _cl_interp(src)

        # …and with a multi-answer query, where a duplicated goal would show up as a duplicated answer.
        # That is the failure mode of hoisting `match`'s arguments before lowering the node verbatim,
        # which is why `ANormal` leaves them untouched.
        src2 =
            "(edge a b)\n(edge a c)\n(edge b d)\n" *
            "(= (succ \$x) (match &self (edge \$x \$y) \$y))\n!(succ a)\n!(succ b)\n!(succ z)\n"
        r2 = MeTTaCore.compile_run(src2)
        @test r2.compiled == 1                          # `succ` compiled; the 3 edges are facts
        @test r2.fell_back == 3
        @test _cl_sorted(r2.answers) == _cl_interp(src2)
        @test ("(succ a)", ["b", "c"]) in _cl_sorted(r2.answers)   # the oracle is not vacuous
        @test ("(succ z)", String[]) in _cl_sorted(r2.answers)     # no match ⇒ no answer, not an error

        # RULE-SHAPED PATTERN ⇒ DECLINED, and this is what keeps the guard honest. A compiled `&self`
        # does not hold `(= (f …) …)` in the source's shape — it holds the emitted IL clauses — so
        # matching a rule would read a space the source never had.
        #
        # ⚠️ ASSERTED AT THE EMITTER, NOT BY EXECUTING IT, and the reason is measured: running
        # `(match &self (= $h $b) $h)` or `(match &self $a $a)` against a Space with the stdlib loaded
        # returns every rule / every atom in it. The first version of this test did exactly that and
        # the suite was OOM-KILLED (exit 137) after ~10 minutes. The claim here is "the guard declines
        # this clause"; executing a space-wide match tests the interpreter's appetite, not the guard.
        for src_guarded in ("(= (rules) (match &self (= \$h \$b) \$h))\n",       # rule-shaped
            "(= (types) (match &self (: \$s \$ty) \$s))\n",      # type-shaped
            "(= (all) (match &self \$a \$a))\n",                 # bare variable
            "(= (dyn \$p) (match &self (\$p x) \$p))\n")         # variable head
            cls = MeTTaCore.CompilerANormal.translate_program(
                MeTTaCore.CompilerFrontend.lower_program(_cl_parse(src_guarded)))
            r = MeTTaCore.CompilerEmitIL.emit_il_program(cls)
            @test r.emitted == 0
            @test !isempty(r.declined)
        end

        # …and the positive control for the same harness: a data-shaped pattern DOES emit, so the
        # four declines above are the guard firing and not the harness failing to compile anything.
        cls_ok = MeTTaCore.CompilerANormal.translate_program(
            MeTTaCore.CompilerFrontend.lower_program(
                _cl_parse("(= (who \$y) (match &self (likes \$x \$y) \$x))\n")))
        @test MeTTaCore.CompilerEmitIL.emit_il_program(cls_ok).emitted == 1
    end

    @testset "MINIMAL-MeTTa INSTRUCTIONS in the source compile to THEMSELVES" begin
        # `Core/lib` and `stdlib.metta` contain hand-written minimal MeTTa — `car-atom` is literally
        # `(chain (decons-atom $atom) $ht (unify ($head $_) $ht $head (Error …)))`. A-normalization
        # makes those residuals because it has no RELATIONAL reading of them, which is right for MM2
        # and wrong here: `chain`/`eval`/`function`/`return` ARE this target's language. The lowering
        # is the identity, with no `eval` wrapper — `chain` interprets its first argument by
        # definition.

        # The `car-atom` shape, through the compiler, answering what the interpreter answers.
        src =
            "(= (hd \$p) (chain (decons-atom \$p) \$ht (unify (\$h \$t) \$ht \$h nope)))\n" *
            "!(hd (a b c))\n!(hd (x))\n"
        r = MeTTaCore.compile_run(src)
        @test r.compiled == 1
        @test r.fell_back == 0
        @test _cl_sorted(r.answers) == _cl_interp(src)
        @test ("(hd (a b c))", ["a"]) in _cl_sorted(r.answers)     # the oracle is not vacuous

        # `function`/`return` — the join point, which has no Prolog goal and so was always a residual.
        src2 = "(= (idf \$x) (function (return \$x)))\n!(idf 7)\n!(idf (p q))\n"
        r2 = MeTTaCore.compile_run(src2)
        @test r2.compiled == 1 && r2.fell_back == 0
        @test _cl_sorted(r2.answers) == _cl_interp(src2)

        # NESTED, and mixed with an ordinary call — the instruction must compose with the chain the
        # emitter builds around it rather than only working as a whole body.
        src3 =
            "(= (dbl \$x) (+ \$x \$x))\n" *
            "(= (both \$p) (chain (decons-atom \$p) \$ht (unify (\$h \$t) \$ht (dbl \$h) nope)))\n" *
            "!(both (4 z))\n"
        r3 = MeTTaCore.compile_run(src3)
        @test r3.compiled == 2 && r3.fell_back == 0
        @test _cl_sorted(r3.answers) == _cl_interp(src3)
        @test ("(both (4 z))", ["8"]) in _cl_sorted(r3.answers)

        # …and `fallback=false`, which turns a decline into an error rather than a silent rescue. This
        # is the assertion that proves the COMPILED path produced these answers.
        @test MeTTaCore.compile_run(src; fallback=false).fell_back == 0
        @test MeTTaCore.compile_run(src2; fallback=false).fell_back == 0

        # ⚠️ NONDETERMINISM IS THE CASE THAT WOULD EXPOSE DOUBLE-EVALUATION. Only `chain` is kept
        # whole by `ANormal`; the other three have their argument BOTH hoisted into a goal AND
        # re-rendered inside the verbatim node, so it is evaluated more than once — measured, e.g.
        # `(= (w) (function (return (nd))))` emits three evaluations of `(nd)`. With a
        # nondeterministic `(nd)` that would surface as DUPLICATED ANSWERS if it were a real branch
        # duplication rather than repeated work. It does not, and this is what says so.
        for (defs, q) in
            (("(= (nd) a)\n(= (nd) b)\n(= (w) (function (return (nd))))\n", "(w)"),
            ("(= (nd) a)\n(= (nd) b)\n(= (w2) (eval (nd)))\n", "(w2)"),
            ("(= (nd) a)\n(= (nd) b)\n(= (w3) (chain (nd) \$v \$v))\n", "(w3)"))
            whole = defs * "!" * q * "\n"
            rn = MeTTaCore.compile_run(whole)
            @test rn.fell_back == 0
            @test _cl_sorted(rn.answers) == _cl_interp(whole)
            # `answers` is UNSORTED (only `_cl_sorted` sorts); the pinned claim is the COUNT — two,
            # not four, which is what a duplicated branch would have produced.
            @test sort(rn.answers[1][2]) == ["a", "b"]
        end
    end

    @testset "A PROGRAM THAT READS ITS OWN RULES compiles nothing" begin
        # 🔴 THE WRONG ANSWER THIS PREVENTS, from the real corpus (`b3_direct.metta`):
        #
        #     source    (= (croaks Fritz) T)
        #     compiled  (= (croaks Fritz) (function (return T)))
        #     directive !(assertEqualToResult (match &self (= ($p Fritz) T) $p) (croaks eat_flies))
        #
        # The directive asks the space for rules whose right-hand side is `T`. Against source rules it
        # finds two; against emitted IL it finds none, because the right-hand side is now
        # `(function (return T))`. The compiled lane answered AssertionFailed where the interpreter
        # answered `()` — with all six definitions compiled and nothing fallen back.
        #
        # ⚠️ `EmitIL._lowerable_match` DOES NOT COVER THIS. That guard refuses to LOWER a `match` whose
        # pattern could bind a rule — it protects matches inside a DEFINITION. A `!` directive is never
        # compiled, so no per-clause guard can see it. The question is not "may this match be
        # compiled" but "may this program's definitions be compiled at all".
        introspecting = ("(= (f) T)\n!(match &self (= (\$p) T) \$p)\n",          # rule-shaped
            "(= (g) T)\n!(match &self (: \$s \$ty) \$s)\n",         # type-shaped
            "(= (h) T)\n!(match &self \$a \$a)\n",                  # bare variable
            "(= (i) T)\n!(match &self (\$p x) \$p)\n")              # variable head
        for src in introspecting
            r = MeTTaCore.compile_run(src)
            @test r.introspects
            @test r.compiled == 0                       # NOTHING compiled, not just the named rule
        end

        # ANSWER AGREEMENT on ALL FOUR shapes — including the bare-variable and variable-headed ones.
        # ⚠️ THOSE TWO USED TO CRASH THE INTERPRETER, and the crash was a real defect this test flushed
        # out: `!(match &self $a $a)` returns every atom in the space, stdlib's own type declaration
        # `(: return-on-error (-> Atom Atom %Undefined%))` among them, and evaluating it dispatched
        # `return-on-error` on a 2-child atom → BoundsError. Fixed by the arity guard in
        # `Eval._INSTR_MIN_CHILDREN`; asserted here rather than worked around.
        # ⚠️ COMPARED MODULO ALPHA-RENAMING. A bare-variable `match` returns atoms containing FRESH
        # variables, and the gensym counter is process-global — so the interpreter run and the
        # compiled run number them differently (`$t#22944480` vs `$t#22979031`) while computing the
        # same 133 answers. That is not a difference between the lanes; comparing the raw strings
        # would fail on renaming alone, which is the oracle being wrong rather than the code.
        _alpha(v) = [replace(s, r"#\d+" => "") for s in v]
        for src in introspecting
            r = MeTTaCore.compile_run(src)
            got = [(q, _alpha(a)) for (q, a) in _cl_sorted(r.answers)]
            want = [(q, _alpha(a)) for (q, a) in _cl_interp(src)]
            @test got == want
        end

        # …AND THE NEGATIVE CONTROL, without which the four above pass for a lane that never compiles.
        # A data-shaped match does not read rules, so compilation proceeds exactly as before.
        plain = "(likes a b)\n(= (who \$y) (match &self (likes \$x \$y) \$x))\n!(who b)\n"
        rp = MeTTaCore.compile_run(plain)
        @test !rp.introspects
        @test rp.compiled == 1
        @test _cl_sorted(rp.answers) == _cl_interp(plain)

        # THE NESTED CASE, which the first version of the guard missed: `match` is almost never the
        # top-level form. Reading the outer form's arguments finds `(match …)` and never its pattern.
        nested = "(= (f) T)\n!(assertEqualToResult (match &self (= (\$p) T) \$p) (f))\n"
        @test MeTTaCore.compile_run(nested).introspects
    end
end
