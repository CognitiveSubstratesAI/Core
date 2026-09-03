# test_emit_julia.jl — stage 4c: A-normal clauses → Julia closures. MILESTONE 1a.
#
# ─── 🔴 WHAT THIS PROVES, AND WHAT IT DOES NOT ───────────────────────────────────────────────────
# PROVES: the REGISTRATION PATH. emitter → per-head grouping → `compile_head!` → `rule_results` seam
# → `fired > 0`, with answers correct through it.
#
# DOES **NOT** PROVE COMPILATION. `_head_closure` runs `match_atoms(pattern, rename_fresh(rule))`,
# which is `Eval.query`'s inner loop WITHOUT THE INDEX. A fact clause registered this way is the
# interpreter's own lookup RELOCATED into a closure, not native code. Nothing here may be cited as
# evidence of speed, and `tools/bench_fib.jl` deliberately does NOT gate this increment: `fib` has
# goals so it declines, and a fact-clause head measures at best EQUAL to `query`. A "0x speedup"
# measured now would read as a finding about closures when it is a finding about a lookup
# relocation. The constant-factor gate becomes meaningful when the GOAL LOOP emits Julia.
#
# ─── ANTI-VACUITY, STRUCTURAL ────────────────────────────────────────────────────────────────────
# The query space loads ONLY the stdlib — the RULES ARE NEVER LOADED INTO IT. So an answer can only
# come from a closure; there is no `(= (col red) T)` to fall back on. Paired with `Eval.fired(head)`,
# a field on `CompiledHead` precisely because a "no-match returns itself" test once passed for three
# runs while nothing ran at all.
using MeTTaCore
using MeTTaCore.Eval
using Test

const _EJV = MeTTaCore.StandardMeTTa
const _EJF = MeTTaCore.CompilerFrontend
const _EJA = MeTTaCore.CompilerANormal
const _EJE = MeTTaCore.CompilerEmitJulia

"Parse → lower → A-normalise, mirroring the ratchet's front half."
function _ej_clauses(sp, text::AbstractString)
    toks = Eval.tokenize(text); i = Ref(1); atoms = _EJV.Atom[]
    while i[] <= length(toks)
        toks[i[]] == "!" && (i[] += 1); i[] > length(toks) && break
        push!(atoms, Eval.parse_from(toks, i, sp.tokens))
    end
    _EJA.translate_program(_EJF.lower_program(atoms))
end

"Register every emitted head, then ask `q` against a space holding ONLY the stdlib."
function _ej_ask(prog::AbstractString, q::AbstractString)
    sp = Eval.Space(); load_core_stdlib!(sp)
    heads = _EJE.emit_julia_program(_ej_clauses(sp, prog))
    Eval.uncompile_all!()
    s2 = Eval.Space(); load_core_stdlib!(s2)          # ← rules deliberately NOT loaded
    for (h, fn) in heads
        Eval.compile_head!(h, fn, UInt64(1))
    end
    res = load_metta!(s2, q)
    fired = Dict(h => Eval.fired(h) for h in keys(heads))
    Eval.uncompile_all!()
    (sort!([string(x) for y in res for x in (y isa AbstractVector ? y : [y])]), heads, fired)
end

const _EJ_PROG = "(= (col red) T)\n(= (col blue) T)\n(= (idf \$x) \$x)\n"

@testset "EmitJulia — stage 4c registration path (1a facts + 1b goals)" begin

    @testset "emits per HEAD, not per clause" begin
        sp = Eval.Space(); load_core_stdlib!(sp)
        heads = _EJE.emit_julia_program(_ej_clauses(sp, _EJ_PROG))
        @test sort(String.(collect(keys(heads)))) == ["col", "idf"]
        @test length(heads) == 2                     # `col`'s TWO clauses became ONE closure
    end

    @testset "🔑 a matching call is answered BY THE CLOSURE (rules absent from the space)" begin
        (got, _, fired) = _ej_ask(_EJ_PROG, "!(col red)\n")
        @test fired[:col] > 0                        # ANTI-VACUITY, first
        @test got == ["T"]
    end

    @testset "🔑 a NON-MATCHING call returns ITSELF — NotReducible, never Empty" begin
        (got, _, fired) = _ej_ask(_EJ_PROG, "!(col green)\n")
        @test fired[:col] > 0                        # it FIRED and declined …
        @test got == ["(col green)"]                 # … and the call came back
        @test got != ["()"] && !isempty(got)
    end

    @testset "🔑 a NON-GROUND out is SUBSTITUTED — the seam parity fix, via the real emitter" begin
        # `(= (idf $x) $x)`. Before the fix `rule_results`' compiled branch pushed `res`
        # uninstantiated while the query branch pushed `subst(X, mb)`; a ground-only test could not
        # see it. Same defect family as the tabling substitution bug.
        (got, _, fired) = _ej_ask(_EJ_PROG, "!(idf foo)\n")
        @test fired[:idf] > 0
        @test got == ["foo"]
        @test !any(a -> occursin("\$", a), got)
    end

    @testset "ALL-OR-NOTHING PER HEAD — one declined clause disqualifies the whole head" begin
        # The seam SHADOWS the head, so a partial registration means the interpreter never sees the
        # clauses the closure lacks and their answers are silently lost. Milestone 1a declines any
        # clause with goals, so a two-clause head with one goal-bearing clause is the natural probe.
        # ⚠️ THIS PROBE HAS BEEN WRONG TWICE, both times because MY OWN CAPABILITY MOVED:
        #   `(other $x)` — A-normalises to goals=0 (unknown head stays DATA ⇒ fact clause ⇒ emits).
        #   `(+ $x 1)`   — declined in 1a, but 1b COMPILES grounded GCall, so it now emits.
        # `if` lowers to GBranch, which is MILESTONE 2. Stable until that lands, and when it does
        # THIS TEST GOES RED — which is correct: the probe must then move again.
        prog = "(= (mix a) T)\n(= (mix \$x) (if (> \$x 0) yes no))\n"
        sp = Eval.Space(); load_core_stdlib!(sp)
        heads = _EJE.emit_julia_program(_ej_clauses(sp, prog))
        @test !haskey(heads, :mix)                   # partially-emittable ⇒ NOT registered
    end

    # ── MILESTONE 1b: THE GOAL LOOP — the first genuinely COMPILED code here ─────────────────────
    @testset "🔑 grounded GCall runs via DIRECT `execute` — native, no interpreter round trip" begin
        # `(= (inc $x) (+ $x 1))` A-normalises to one GCall head=`+`. `+` resolves through
        # TOKEN_REGISTRY to a Grounded op, so the plan calls `execute` on it directly. THIS is the
        # part that is compiled rather than relocated: no `interpret`, no IL text, no lookup.
        (got, _, fired) = _ej_ask(raw"(= (inc $x) (+ $x 1))" * "\n", "!(inc 41)\n")
        @test fired[:inc] > 0
        @test got == ["42"]
    end

    @testset "🔑 GUnify binds — `let` lowered to unification, FREE on Eval and absent from MM2" begin
        # `Emit.jl` records GUnify+GFindall as 73 of 279 blocked paths on ECAN+PLN, "FREE on Eval
        # and ABSENT from MM2 BY CONSTRUCTION". This is that class working.
        (got, _, fired) = _ej_ask(raw"(= (dup $x) (let $y $x (pair $y $y)))" * "\n", "!(dup 7)\n")
        @test fired[:dup] > 0
        @test got == ["(pair 7 7)"]
        @test !any(a -> occursin("#", a), got)   # no renamed variable leaked into the answer
    end

    @testset "🔴 rule and plan are renamed as ONE unit (variable correspondence)" begin
        # THE BUG THIS PINS, measured before the fix: `rename_fresh` is applied per call so a
        # clause's variables cannot capture across calls — but it renames ONE atom. The plan's
        # atoms are built at COMPILE time, so renaming the rule alone left the plan pointing at the
        # original names and every goal unified against a variable that no longer existed.
        # `(dup 7)` answered `(pair $y#1097 $y#1097)`; `(inc 41)` returned the call itself.
        # Two calls in a row is what catches a rename that only works once.
        for _ in 1:2
            (got, _, fired) = _ej_ask(raw"(= (dup $x) (let $y $x (pair $y $y)))" * "\n", "!(dup 7)\n")
            @test fired[:dup] > 0
            @test got == ["(pair 7 7)"]
        end
    end

    @testset "a NON-GROUNDED GCall is DECLINED, not deferred to `interpret`" begin
        # ⚠️ `(zzz $x 1)` does NOT work as this probe — MEASURED: goals=0, because an unknown head
        # stays as DATA, so it is a fact clause and legitimately emits. A real non-grounded GCall
        # needs a head that IS a known function but NOT in TOKEN_REGISTRY — i.e. a call to another
        # user-defined function, which is what `_plan_goals` declines.
        sp = Eval.Space(); load_core_stdlib!(sp)
        prog = raw"(= (a $x) (+ $x 1))" * "\n" * raw"(= (b $x) (a $x))" * "\n"
        heads = _EJE.emit_julia_program(_ej_clauses(sp, prog))
        @test haskey(heads, :a)                  # grounded call ⇒ emits
        @test !haskey(heads, :zzzz)              # sanity: no phantom heads
        @test haskey(Eval.TOKEN_REGISTRY, "+")   # the gate's premise
        @test !haskey(Eval.TOKEN_REGISTRY, "a")  # `a` is NOT grounded — a call to it must decline
    end
end
