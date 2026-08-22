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
    toks = _IV.tokenize(text)
    i = Ref(1)
    out = MeTTaCore.StandardMeTTa.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1)
        i[] > length(toks) && break
        push!(out, _IV.parse_from(toks, i, sp.tokens))
    end
    out
end

"Compile `src` to minimal MeTTa."
function _to_il(src::AbstractString)
    sp = _IV.Space()
    _IV.load_core_stdlib!(sp)
    cls = _IA.translate_program(_IF.lower_program(_il_parse(sp, src)))
    (_IL.emit_il_program(cls), cls)
end

"Evaluate `query` against a Space loaded with `defs`; return sorted answer strings."
function _answers(defs::Vector{String}, query::AbstractString)::Vector{String}
    sp = _IV.Space()
    _IV.load_core_stdlib!(sp)
    for d in defs
        _IV.load_metta!(sp, d)
    end
    res = _IV.load_metta!(sp, "!" * query)
    sort(String[string(x) for r in res for x in (r isa AbstractVector ? r : [r])])
end

"THE DIFFERENTIAL: source-through-interpreter vs compiled-IL-through-interpreter."
function _agree(src::AbstractString, query::AbstractString)
    r, _ = _to_il(src)
    src_forms = String[strip(l) for l in split(src, '\n') if !isempty(strip(l))]
    (interp=_answers(src_forms, query), il=_answers(r.clauses, query), result=r)
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
        # CALLS ARE `chain` + `metta`, NOT `chain` + `eval`. This asserted `eval` until 2026-08-11 and
        # was pinning a defect: `eval` makes ONE STEP (`metta.txt:96`), so the chain variable bound the
        # callee's BODY rather than its value, and every downstream goal computed on an unreduced term.
        # Switching the emitter to `metta` removed every extra error in both corpora (e1_kb_write 2→0,
        # c3_pln_stv 1→0). Asserted positively AND negatively so the old shape cannot come back.
        @test occursin("(chain (metta ", joined)
        @test !occursin("(chain (eval ", joined)
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
        hit = _agree(src, "(k 1)")
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
        for (label, src) in (("branch", "(= (k \$x) (if (== \$x 1) one other))\n"),
            ("collapse", "(= (c) (collapse (superpose (1 2))))\n"))
            sp = _IV.Space()
            _IV.load_core_stdlib!(sp)
            cls = _IA.translate_program(_IF.lower_program(_il_parse(sp, src)))
            il = _IL.emit_il_program(cls)
            mm2 = _IE.emit_program(cls)
            @test length(cls) >= 1
            # The IL must do at least as well as MM2 on every shape — never worse.
            @test il.emitted >= mm2.emitted
        end
    end

    @testset "GResidual DECLINES, with a reason, and is never dropped" begin
        # A clause that A-normalization could not flatten must be counted, not silently omitted.
        sp = _IV.Space()
        _IV.load_core_stdlib!(sp)
        cls = _IA.translate_program(
            _IF.lower_program(_il_parse(sp, "(= (f \$x) (g \$x))\n"))
        )
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

@testset "PATTERNS ARE DATA — and values are still values" begin
    # THE DISTINCTION IS POSITION, NOT NODE TYPE, and getting it backwards is a wrong answer in one
    # direction and 39 declined clauses in the other. Both directions are asserted here.
    #
    # `translate_pattern` was added because both pattern sites ran the EXPRESSION translator, which
    # turns an all-variable tuple `($h $t)` into a `GResidual` — no symbol head, no predefined head,
    # so it falls to the catch-all — and one residual declines the whole clause. That shape is
    # `stdlib.metta`'s own `car-atom` / `is-function` / `get-doc-params`.

    # (1) PATTERN POSITION ⇒ DATA. A `let`-destructuring pattern must lower to ONE unification with
    #     no residual, and the clause must emit.
    r, cls = _to_il("(= (fst \$p) (let (\$h \$t) \$p \$h))")
    @test isempty(r.declined)
    @test r.emitted == 1
    @test !any(g -> g isa _IA.GResidual, _IA.all_goals(only(cls).goals))

    # …and it must COMPUTE, not merely emit. The oracle is execution, as everywhere in this file.
    @test _answers(["(= (fst \$p) (let (\$h \$t) \$p \$h))"], "(fst (a b))") == ["a"]

    # (2) A `case`/`if` ARM PATTERN is the other site, same rule.
    r2, cls2 = _to_il("(= (tag \$x) (case \$x (((p \$a) (got \$a)) (\$other none))))")
    @test isempty(r2.declined)

    # (3) VALUE POSITION IS A DYNAMIC CALL — and it is now LOWERED, not declined.
    #
    # 🔴 THIS ASSERTED `!isempty(r3.declined)` UNTIL 2026-08-11 — the third test this day found to be
    # pinning a LIMITATION rather than a REQUIREMENT. Its stated reason was "lowering it as DATA would
    # silently return the unevaluated pair", which is right about DATA and does not apply to what the
    # emitter now does: `($f $x)` lowers to `(chain (metta ($f $x) %Undefined% &self) …)`, i.e.
    # RUNTIME DISPATCH — PeTTa's `reduce/2` expressed in one of the thirteen instructions.
    #
    # Asserted by EXECUTION, this file's own standard, in both directions:
    r3, cls3 = _to_il("(= (app \$f \$x) (let \$r (\$f \$x) \$r))")
    @test isempty(r3.declined)
    @test r3.emitted == 1
    #   …it COMPUTES when the callee resolves,
    @test _answers(
        ["(= (double \$x) (+ \$x \$x))", "(= (app \$f \$x) (let \$r (\$f \$x) \$r))"],
        "(app double 4)") == ["8"]
    #   …and — THE CONTROL THE OLD ASSERTION EXISTED TO PROTECT — an UNRESOLVED callee is NOT faked:
    #   the term comes back unevaluated, exactly as the interpreter returns it. That is the property
    #   that made `metta` the right instruction and `eval` the wrong one (`eval` yields NotReducible).
    @test _answers(["(= (app \$f \$x) (let \$r (\$f \$x) \$r))"], "(app nosuch 4)") ==
        ["(nosuch 4)"]
end

@testset "STRUCTURAL emission agrees with the TEXT path — the prerequisite for switching" begin
    # The compile lane currently launders IL through text: `emit_il_clause` builds a String and
    # `CompileLane` re-parses it with `load_metta!`. That round-trip is what corrupted
    # `Grounded{Space}` and `Grounded{StateCell}` (see `test_il_roundtrip.jl`), and two guards exist
    # only to survive it. `_il_atom` is the structural counterpart of `_render_il`, so the lane can
    # eventually pass ATOMS and keep `render` for the wire — struct in memory, bytes on the wire.
    #
    # 🔴 THIS TEST IS THE SAFETY PROPERTY FOR THAT SWITCH, and it is why the converter is deliberately
    # text-EQUIVALENT rather than text-IMPROVED: `string(_il_atom(a))` must equal `_render_il(a)` on
    # every node the corpus produces. Any divergence introduced later is then a DELIBERATE, visible
    # change rather than something hidden inside a refactor.
    _IL = MeTTaCore.CompilerEmitIL
    _CE = MeTTaCore.CompilerEmit
    _IR = MeTTaCore.CompilerIR

    # walk every IR node the real corpus lowers, not a handful I thought of
    function _walk(a, f)
        f(a)
        if a isa _IR.IRExpression
            _walk(a.head, f)
            for x in a.args
                _walk(x, f)
            end
        elseif a isa _IR.IRSpecial
            for x in a.args
                _walk(x, f)
            end
        end
    end

    checked = 0
    mismatches = Tuple{String, String}[]
    for src in ("(= (f \$x) (g \$x))",
        "(= (h \$x) (if (== \$x 1) \"one\" other))",
        "(= (k \$x) (let (\$a \$b) \$x (pair \$b \$a)))",
        "(= (m \$x) (match &self (p \$x \$y) \$y))",
        "(= (n) (superpose (1 2 3)))",
        "(= (q \$f \$x) (\$f \$x))")
        _, cls = _to_il(src)
        for cl in cls
            # EVERY IRAtom reachable from EVERY goal — not just residuals. The first version walked
            # only `GResidual.node` + head args and visited 16 nodes; the anti-vacuity floor below
            # caught it. A converter proven on 16 nodes is not proven.
            goal_atoms(g) =
                if g isa _IA.GUnify
                    _IR.IRAtom[g.lhs, g.rhs]
                elseif g isa _IA.GCall
                    _IR.IRAtom[g.args...; g.out]
                elseif g isa _IA.GBranch
                    _IR.IRAtom[g.condval, g.out]
                elseif g isa _IA.GDisj
                    _IR.IRAtom[g.out]
                elseif g isa _IA.GFindall
                    _IR.IRAtom[g.template, g.out]
                elseif g isa _IA.GResidual
                    _IR.IRAtom[g.node, g.out]
                else
                    _IR.IRAtom[]
                end
            for g in _IA.all_goals(cl.goals), nd in goal_atoms(g)
                _walk(
                    nd,
                    a -> begin
                        checked += 1
                        # BOTH builders against THEIR OWN renderer. Checking only `_il_atom` vs
                        # `_render_il` would pass while the `render`-sites diverged — the exact gap
                        # recorded in `6a9e2dd`, since `render` has no `IRSpecial` method and `_il_atom`
                        # does. A property that holds while behaviour changes is worse than none.
                        #
                        # ⚠️ COMPARED VIA `il_text`, NOT `string`. The builders are now PARSE-EQUIVALENT:
                        # a grounded string becomes a real `Grounded{String}`, and `show` prints it
                        # WITHOUT quotes (`string(Grounded("one")) == "one"`), which re-parses as a
                        # SYMBOL. `il_text` is the emitter's wire serializer and quotes it correctly.
                        # This test caught exactly that when the builders changed under it — comparing
                        # against `show` asserted a property the wire format does not have.
                        for (txt, at, which) in
                            ((_IL._render_il(a), _IL._il_atom(a), "_il_atom"),
                            (_CE.render(a), _IL._render_atom(a), "_render_atom"))
                            if at === nothing
                                occursin("<unrenderable", txt) ||
                                    push!(mismatches, (which * " " * txt, "nothing"))
                            elseif _IL.il_text(at) != txt
                                push!(mismatches, (which * " " * txt, _IL.il_text(at)))
                            end
                        end
                    end
                )
            end
            for a in cl.head_args
                checked += 1
                for (txt, at, which) in ((_IL._render_il(a), _IL._il_atom(a), "_il_atom"),
                    (_CE.render(a), _IL._render_atom(a), "_render_atom"))
                    if at === nothing
                        (
                            occursin("<unrenderable", txt) ||
                            push!(mismatches, (which * " " * txt, "nothing"))
                        )
                    else
                        (
                            _IL.il_text(at) == txt ||
                            push!(mismatches, (which * " " * txt, _IL.il_text(at)))
                        )
                    end
                end
            end
        end
    end
    for (txt, got) in first(mismatches, 5)
        @info "STRUCTURAL/TEXT MISMATCH" text=txt structural=got
    end
    @test isempty(mismatches)
    @test checked > 20        # anti-vacuity: the walk actually visited nodes
end
