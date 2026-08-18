# `GROUNDED` — the grammar's word versus the runtime's type.
#
# `docs/src/language/grammar.md` says `GROUNDED ::= STRING | WORD`, which is a PARSER-level
# production: what SOURCE TEXT may denote a grounded atom. The runtime `Grounded{T}` is wider — it
# wraps arbitrary host values, most of which no source text can produce. A census on 2026-08-18 put
# numbers on the gap: three payload types are parser-reachable, and five more exist only because the
# engine constructs them (`Operation`, `SpaceOp`, `Space`, `StateCell`, `WFSBottom`), plus
# `Bindings`, which is internal and must never surface.
#
# 🔴 THIS IS A GATE, NOT A NOTE. Prose stating an enumeration goes stale the first time somebody adds
# a payload type — which is the single most repeated failure in this tree. A test makes adding one a
# DELIBERATE act.
#
# ⚠️ WHY THIS IS ITS OWN FILE. It first went into `test_atoms.jl`, whose header says "Standalone (no
# Core dependency)" — and these testsets need `Eval`, `Space`, `load_metta!`, all of Core. It passed
# when run alone and failed in the suite with `UndefVarError: Space`, because the probe daemon's
# `Main` still carried those imports from earlier debugging. Isolation lied; the suite did not.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

@testset "GROUNDED — parser-reachable payloads are exactly Int64, Float64, String" begin
    s = Space()
    reachable = Set{Type}()
    walk(a::Atom) = a isa Grounded ? push!(reachable, typeof(a).parameters[1]) :
                    a isa Expression ? (for c in a.children; walk(c); end) : nothing
    for src in ("42", "-7", "0", "3.14", "1e10", "\"a string\"", "True", "False",
                "(f 1 2.5 \"s\")", raw"(g $x True)", "()")
        walk(Eval.parse_from(Eval.tokenize(src), Ref(1), s.tokens))
    end
    @test reachable == Set{Type}([Int64, Float64, String])

    # 🔑 `True`/`False` are SYMBOLS, not `Grounded{Bool}` — the PeTTa-faithful convention. Asserted
    # here because `compiler/Frontend.jl:156` DOES lower `Grounded{Bool}` while nothing in the
    # interpreter produces one. Harmless today (a lowering for an unreachable case is inert), but if
    # a grounded-boolean producer ever appears the two halves must be reconciled on purpose.
    @test Bool ∉ reachable
    @test Eval.parse_from(Eval.tokenize("True"), Ref(1), s.tokens) isa Sym
end

@testset "GROUNDED — Bindings is an internal carrier and must not reach an answer" begin
    # `compiler/EmitIL.jl:502` records a MEASURED defect: a primitive once leaked `Grounded{Bindings}`
    # atoms into answers, caught against four engines. Bindings riding through evaluation as an atom
    # is fine; surfacing one to a caller is not, because it is not a term of the language.
    s = Space(); load_core_stdlib!(s)
    # ⚠️ PUT ATOMS IN *THIS* SPACE FIRST. The first draft queried `!(get-atoms &self)` on a fresh
    # `Space()` and got ZERO — `load_core_stdlib!` populates a different store
    # (`[[feedback_empty_result_may_be_the_wrong_store]]`). The anti-vacuity counter below is what
    # caught it: the testset was inspecting three atoms with one of four queries inert.
    load_metta!(s, "(edge a b)\n(edge b c)\n")
    leaked = Atom[]; seen = 0
    # `match` and `let` are the binding-CARRYING paths — where a `Grounded{Bindings}` could plausibly
    # surface — so they matter here far more than arithmetic does.
    for src in ("!(+ 1 2)\n", "!(< 1 2)\n", raw"!(let $x 1 $x)" * "\n",
                "!(get-atoms &self)\n",
                raw"!(match &self (edge $x $y) ($x $y))" * "\n",
                raw"!(match &self (edge $x $y) $x)" * "\n")
        for y in load_metta!(s, src)
            for x in (y isa AbstractVector ? y : [y])
                seen += 1
                x isa Grounded && typeof(x).parameters[1] === Eval.Bindings && push!(leaked, x)
            end
        end
    end
    # ANTI-VACUITY FIRST: `isempty(leaked)` is trivially true over an empty list.
    @test seen > 4
    @test isempty(leaked)
end
