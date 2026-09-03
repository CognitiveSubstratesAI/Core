# test_compiled_head_seam.jl — the compiled-head seam. Design: docs/architecture/COMPILED_HEAD_SEAM.md
#
# ─── WHY EVERY LOCATION HERE IS A SYMBOL, NEVER A LINE ───────────────────────────────────────────
# The design doc cites `Eval.jl:968` etc. Those are verdicts at a point in time. MEASURED 2026-09-02:
# TABLING_ROADMAP's READ-FIRST banner cited `Tabling.jl:374-380` for `_leader_pass`; the line numbers
# had drifted OFF the symbol entirely and the banner misled a session for two weeks. This file is the
# thing that fails if the design stops being true, so it locates by SYMBOL and asserts the ORDERING
# structurally — position is the whole design, and a line number stops describing it the moment
# someone edits above it.
using MeTTaCore
using MeTTaCore.Eval
using Test

const _CHS_EVAL_SRC = read(joinpath(dirname(pathof(MeTTaCore)), "standard", "Eval.jl"), String)

"Body of a top-level `function <name>(` … matching `end`, located BY SYMBOL."
function _chs_fn_body(src::AbstractString, name::AbstractString)
    lines = split(src, '\n')
    i = findfirst(l -> startswith(l, "function $name("), lines)
    i === nothing && return nothing
    j = findnext(l -> l == "end", lines, i + 1)
    j === nothing && return nothing
    join(lines[i:j], '\n')
end

# ── 1.2's THREE ACCEPTANCE TESTS, on ONE HAND-WRITTEN closure. No emitter. ───────────────────
# Proving the DELIVERY MECHANISM end to end before EmitJulia exists — the opposite of the
# MorkSupercompiler order, where the machinery landed before anything drove it.
const _V = MeTTaCore.StandardMeTTa

"Compiled `hc`: `(hc \$u)` reduces to `schiphol` AND binds `\$u` to it. Returns NO-MATCH otherwise."
function _chs_hc(args::Vector{_V.Atom}, space)
    length(args) == 1 || return Eval.ExecNoReduce()
    u = args[1]
    u isa _V.Var || return Eval.ExecNoReduce()      # ground/mismatched call ⇒ no clause matched
    bs = _V.add_var_binding(_V.Bindings(), u, _V.Sym("schiphol"))
    isempty(bs) && return Eval.ExecNoReduce()
    Eval.CompiledOk(_V.Atom[_V.Sym("schiphol")], [bs[1]])
end

function _chs_ask(q::AbstractString; defs::AbstractString="", compile::Bool=true)
    Eval.uncompile_all!()
    sp = Eval.Space(); load_core_stdlib!(sp)
    isempty(defs) || load_metta!(sp, defs)
    compile && Eval.compile_head!(:hc, _chs_hc, UInt64(1))
    r = load_metta!(sp, q)
    nfired = Eval.fired(:hc)
    Eval.uncompile_all!()
    (sort!([string(x) for y in r for x in (y isa AbstractVector ? y : [y])]), nfired)
end

@testset "compiled-head seam" begin

    @testset "🔑 SINGLE SITE — one lookup, one seam, and no lane re-implements it" begin
        # ⚠️ THIS TESTSET REPLACED AN EARLIER ONE THAT ASSERTED THE WRONG DESIGN AND PASSED 5/5.
        # It checked `compiled_head(` precedes `query(` inside `eval_op` — true, verified, and
        # describing a function the live `metta` path never enters. The closure fired ZERO times.
        # A structural assertion is only as good as the claim it encodes; this one encodes the
        # invariant that actually matters: the equation lookup exists in EXACTLY ONE PLACE.
        body = _chs_fn_body(_CHS_EVAL_SRC, "rule_results")
        @test body !== nothing                                    # located BY SYMBOL, never by line

        ci = findfirst("compiled_head(", body)
        qi = findfirst("query(", body)
        @test ci !== nothing && qi !== nothing
        @test first(ci) < first(qi)                               # seam precedes the space query

        # THE ANTI-DRIFT ASSERTION: exactly ONE inlined `(= call X)` query in the whole source tree,
        # and it is the one inside `rule_results`. Five copies is five ways to drift — the shape
        # CODEMAP row 232 names as the disease, and today it produced a seam on a dead lane.
        srcdir = joinpath(dirname(pathof(MeTTaCore)), "standard")
        hits = String[]
        for f in readdir(srcdir; join=true)
            endswith(f, ".jl") || continue
            for (n, l) in enumerate(eachline(f))
                occursin("Expression(Sym(\"=\")", l) && occursin(", X)", l) &&
                    push!(hits, "$(basename(f)):$n")
            end
        end
        @test length(hits) == 1                                   # if this fails, a lane re-inlined it

        # …and no lane calls the seam directly; they all go through `rule_results`.
        for fn in ("eval_op", "metta_call_instr", "metta_call_step")
            fb = _chs_fn_body(_CHS_EVAL_SRC, fn)
            @test fb === nothing || findfirst("compiled_head(", fb) === nothing
            @test fb === nothing || findfirst("rule_results(", fb) !== nothing
        end
    end

    @testset "CompiledOk makes the (\$w …) defect UNCONSTRUCTIBLE" begin
        # `ExecOk(results)` (one-arg) yields EMPTY binds, so the merge loop falls through to the
        # caller's UNMERGED bindings — that is exactly `(pair \$w schiphol)`. A lint would not catch a
        # hand-written closure; an inner constructor makes the shape impossible for ANY caller.
        @test isdefined(Eval, :CompiledOk)
        ok = Eval.CompiledOk(_V.Atom[_V.Sym("a")], [_V.Bindings()])
        @test length(ok.results) == length(ok.binds)
        @test_throws Exception Eval.CompiledOk(_V.Atom[_V.Sym("a")], _V.Bindings[])   # no binds ⇒ error
    end

    @testset "🔑 SEAM TEST 1 — the answer CARRIES the binding (the defect's 3rd appearance)" begin
        d = raw"(= (m $u) (pair $u (hc $u)))" * "\n"
        (got, nf) = _chs_ask("!(m \$w)\n"; defs=d)
        @test nf > 0                                          # ANTI-VACUITY, FIRST, ALWAYS
        @test got == ["(pair schiphol schiphol)"]
        @test !any(a -> occursin("\$", a), got)
    end

    @testset "SEAM TEST 2 — fired AND declined AND the call came back as itself" begin
        # ⚠️ ALL THREE, because any one alone is vacuous: an UNREGISTERED head also returns itself.
        # This test passed for 3 runs while the closure never ran (seam was on the wrong lane).
        (got, nf) = _chs_ask("!(hc a b)\n")                   # arity 2 ⇒ the closure declines
        @test nf > 0                                          # it FIRED …
        @test got == ["(hc a b)"]                             # … and the call returned ITSELF
        @test got != ["()"] && !isempty(got)                  # NOT Empty
        (got0, nf0) = _chs_ask("!(hc a b)\n"; compile=false)  # and the CONTROL: uncompiled agrees
        @test nf0 == 0
        @test got0 == got
    end

    @testset "🔑 SEAM TEST 3 — typed head, BAD argument: compiled must AGREE with uncompiled" begin
        # DIFFERENTIAL, not an absolute expectation. My first version asserted "an Error appears",
        # which is a claim about the TYPE SYSTEM, not about the seam — and it failed for a reason
        # about my closure rather than the seam. What the seam must guarantee is that compiling a
        # head does not CHANGE the answer.
        d = "(: hc (-> Number Number))\n"
        (tc, nfc) = _chs_ask("!(hc foo)\n"; defs=d)
        (tu, nfu) = _chs_ask("!(hc foo)\n"; defs=d, compile=false)
        @test nfu == 0
        @test tc == tu                                        # compiling changed nothing
    end

    @testset "🔑 SEAM TEST 4 — typed head, GOOD argument: the closure is NOT bypassed" begin
        # The hazard: argument/head reduction reaches equations through `metta_call_step`, a THIRD
        # lookup site which is currently UNWIRED. If a typed head with an acceptable argument routes
        # through that path, it silently skips the closure. `fired` is the only thing that detects it.
        d = "(: hc (-> Atom Atom))\n"
        (got, nf) = _chs_ask("!(hc \$z)\n"; defs=d)
        @test nf > 0                                          # NOT bypassed
        @test got == ["schiphol"]
    end

    @testset "🔑 SEAM TEST 5 — a TABLED compiled head reaches its closure (tabling composes)" begin
        # The doc CLAIMED this before it was true. `_leader_pass` used to run its own
        # `query(space, (= key X))`, so a tabled compiled head never saw the closure; and
        # `_probe_no_rule` — which feeds `_NO_RULE`, which `tnot` reads — would report "no rule"
        # for a head that HAS a compiled implementation. That was a negation hazard, not a missed
        # optimisation. Now both route through `rule_results`, so this holds BY CONSTRUCTION —
        # and this test is what keeps it honest.
        Eval.untable_all!()
        Eval.uncompile_all!()
        sp = Eval.Space(); load_core_stdlib!(sp)
        Eval.compile_head!(:hc, _chs_hc, UInt64(1))
        Eval.table!(:hc)
        r = load_metta!(sp, "!(hc \$z)\n")
        got = sort!([string(x) for y in r for x in (y isa AbstractVector ? y : [y])])
        nf = Eval.fired(:hc)
        Eval.untable_all!(); Eval.uncompile_all!()

        @test nf > 0                                    # ANTI-VACUITY: the closure ran UNDER tabling
        @test got == ["schiphol"]                       # …and gave the compiled answer
    end
end
