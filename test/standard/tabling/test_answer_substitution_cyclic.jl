# test_answer_substitution_cyclic.jl — the substitution defect on a CYCLIC, left-recursive predicate.
#
# Companion to test_answer_substitution.jl, which pins the same ONE defect on `eq`/`g`. This file
# adds what those cannot have: a program where TABLING IS LOAD-BEARING rather than an optimisation.
#
# ─── READ test/standard/tabling/README.md FIRST ──────────────────────────────────────────────────
# Every idiom below was got wrong once before it was got right. In particular:
#   * `auto_table!` would return `Symbol[]` here (`reach` is MULTIVALUED — two clauses), so a
#     differential built on it compares UNTABLED TO UNTABLED. `table!` is passed EXPLICITLY, and the
#     first assertion of every testset is the anti-vacuity check.
#   * the match template returns the NODE (`$y`), not `True`. The SWI oracle for this program only
#     queries GROUND calls, so binding propagation is NOT established by it and is not assumed.
#
# ─── WHY THERE IS NO UNTABLED ARM ────────────────────────────────────────────────────────────────
# `(= (reach $x $y) (reach $y $x))` is directly left-recursive: untabled it CANNOT terminate, and it
# raises the interpreter step limit (asserted below, so the claim is checked rather than repeated).
# The oracles are therefore EXTERNAL, per the README's ordering:
#   1. the SWI differential already covers this program shape (test_tabling_swipl_differential.jl:126)
#   2. a machine-computed BFS over the edge list — below, computed, never typed
using MeTTaCore
using MeTTaCore.Eval
using Test

# Program from test_tabling_swipl_differential.jl:123-128, with the template returning the NODE.
const _CY_PROG = "(edge amsterdam schiphol)\n(edge schiphol leiden)\n" *
    raw"(= (reach $x $y) (match &self (edge $x $y) $y))" * "\n" *
    raw"(= (reach $x $y) (reach $y $x))" * "\n"
# Carries the CALL VARIABLE into the answer — without this the loss is invisible, because `!`-queries
# surface VALUES, not substitutions, so both arms would look identical.
const _CY_WRAP = raw"(= (m $u) (pair $u (reach amsterdam $u)))" * "\n"

"BFS oracle: these two rules are the SYMMETRIC closure of `edge` (NOT transitive). Computed."
function _cy_bfs(from::String)
    edges = [("amsterdam", "schiphol"), ("schiphol", "leiden")]
    sym = Set{Tuple{String, String}}()
    for (a, b) in edges
        push!(sym, (a, b)); push!(sym, (b, a))
    end
    sort([b for (a, b) in sym if a == from])
end

function _cy_ask(q::AbstractString, heads::Vector{Symbol}; defs::AbstractString)
    Eval.untable_all!()
    s = Eval.Space(); load_core_stdlib!(s); load_metta!(s, defs)
    for h in heads
        Eval.table!(h)
    end
    tb = collect(Eval._TABLED_HEADS)
    a = load_metta!(s, q)
    Eval.untable_all!()
    (sort!([string(x) for y in a for x in (y isa AbstractVector ? y : [y])]), tb)
end

@testset "answer substitution — CYCLIC, left-recursive (tabling is load-bearing)" begin

    @testset "🔑 ATTRIBUTION CONTROL — acyclic, BOTH arms: the loss is TABLING, not the interpreter" begin
        # 🔴 WITHOUT THIS TESTSET THE FILE PROVES NOTHING ABOUT TABLING. The cyclic testsets below
        # can only ever observe the TABLED arm (the untabled one does not terminate), so on their own
        # the attribution is INHERITED from test_answer_substitution.jl rather than shown here. A
        # competing explanation survives that: Core might not propagate a body-match binding back to
        # a caller's variable AT ALL, tabled or not — in which case `(pair $w schiphol)` is
        # interpreter semantics and "symptom A" is misattributed in BOTH files.
        #
        # Same program, same idiom, symmetry clause dropped so the untabled arm terminates. Only
        # tabling differs. MEASURED 2026-09-02:
        #     UNTABLED  ->  (pair schiphol schiphol)     binding PROPAGATES
        #     TABLED    ->  (pair $w schiphol)           binding LOST
        # => the interpreter propagates it; TABLING drops it. Attribution SHOWN, not inherited.
        ac = "(edge amsterdam schiphol)\n(edge schiphol leiden)\n" *
             raw"(= (reach $x $y) (match &self (edge $x $y) $y))" * "\n" *
             raw"(= (m $u) (pair $u (reach amsterdam $u)))" * "\n"

        (u, tbu) = _cy_ask("!(m \$w)\n", Symbol[]; defs=ac)
        @test isempty(tbu)                                  # the untabled arm really is untabled
        @test u == ["(pair schiphol schiphol)"]             # ORACLE: the binding propagates

        (t, tbt) = _cy_ask("!(m \$w)\n", [:reach]; defs=ac)
        @test tbt == [:reach]                               # ANTI-VACUITY
        @test t != u                                        # the arms DIVERGE - that is the defect
        @test t == ["(pair \$w schiphol)"]                  # pinned: the call variable is unbound
        @test_broken t == u                                 # the fix: tabled must equal untabled

        # And why a BARE call cannot find this: identical in both arms, because `!`-queries surface
        # VALUES, not substitutions.
        (bu, _) = _cy_ask("!(reach amsterdam \$y)\n", Symbol[]; defs=ac)
        (bt, _) = _cy_ask("!(reach amsterdam \$y)\n", [:reach]; defs=ac)
        @test bu == bt == ["schiphol"]
    end

    @testset "the untabled arm CANNOT be the oracle (it does not terminate)" begin
        # Asserted, not asserted-in-prose: this is why the oracles below are external.
        Eval.untable_all!()
        s = Eval.Space(); load_core_stdlib!(s); load_metta!(s, _CY_PROG)
        @test_throws Exception load_metta!(s, "!(reach amsterdam \$y)\n")
        Eval.untable_all!()
    end

    @testset "tabled agrees with the BFS oracle — ground AND variable calls" begin
        (g, tb)  = _cy_ask("!(reach amsterdam schiphol)\n", [:reach]; defs=_CY_PROG)
        @test tb == [:reach]                       # ANTI-VACUITY, first, always
        @test g == ["schiphol"]                    # the SWI-oracled ground shape

        (v, tb2) = _cy_ask("!(reach amsterdam \$y)\n", [:reach]; defs=_CY_PROG)
        @test tb2 == [:reach]                      # ANTI-VACUITY
        @test v == _cy_bfs("amsterdam")            # machine-computed, not typed
    end

    @testset "🔑 THE DEFECT — the answer does not carry the binding" begin
        (a, tb) = _cy_ask("!(m \$w)\n", [:reach]; defs=_CY_PROG * _CY_WRAP)
        @test tb == [:reach]                                  # ANTI-VACUITY
        @test length(a) == 1                                  # the answer SET is not truncated…
        # …but the call variable comes back UNBOUND. `(reach amsterdam $u)` yields `schiphol` as a
        # VALUE and never binds `$u` to it — symptom A of test_answer_substitution.jl ("fails to
        # BIND"), here on a cyclic predicate. Pinned as the CURRENT behaviour:
        @test occursin("\$", only(a))                         # a variable survives into the answer
        @test only(a) == "(pair \$w schiphol)"
        # The fix — substitution-valued answers — must make this pass:
        @test_broken only(a) == "(pair schiphol schiphol)"
    end
end
