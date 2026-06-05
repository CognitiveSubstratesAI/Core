# test/test_recursive_lists.jl
#
# Standalone probe — NOT included in runtests.jl yet.
# Proves the list-library rewrite (single guarded clauses + `if`) terminates
# and fires, where main's ($h . $t) cons-pattern stdlib does not.
#
# Run:  julia --project=packages/Core packages/Core/test/test_recursive_lists.jl
#
# Expected against MAIN:   RED — list ops return unreduced; `is-function`
#                          over-produces.
# Expected against REWRITE: GREEN — all terminate and reduce.
#
# Each @test is annotated with its audit bin so a failure is self-describing.

using Test
using MeTTaCore

# Fresh space, primitives + stdlib loaded explicitly so this file is
# self-contained and order-independent from the main suite.
const S = new_core_space()
register_all_primitives!()
load_stdlib!(S)

# factorial is a demo program, not stdlib — define it here as the guarded
# single clause so the probe is closed over everything it asserts.
run_metta(
    """
(= (factorial \$n)
   (if (> \$n 0)
       (* \$n (factorial (- \$n 1)))
       1))
""",
    S,
)

# Helper: evaluate one expression, return the bare result.
ev(src) = run_metta(src, S)[1]

@testset "recursive lists — rewrite closes divergent + dead-on-arrival bins" begin

    # ── DEAD-ON-ARRIVAL on main: ($h . $t) never unifies against a real list,
    #    so these returned the expression unreduced. Rewrite makes them fire. ──
    @testset "length (was unreduced on main)" begin
        @test ev("!(length ())") == 0
        @test ev("!(length (1 2 3 4))") == 4
    end

    @testset "reverse (was unreduced on main)" begin
        @test ev("!(reverse ())") == []
        @test ev("!(reverse (a b c))") == [:c, :b, :a]
    end

    @testset "member (was unreduced on main)" begin
        # NB: PRIMUS's parser converts True/False to Julia Bool; H-E keeps them
        # as Symbols of type Bool. The probe asserts against PRIMUS's actual
        # shape — that divergence is a separate finding (Parser.jl L109-113).
        @test ev("!(member 3 (1 2 3))") === true
        @test ev("!(member 9 (1 2 3))") === false
    end

    @testset "sort — exercises the insert/sort clause pair" begin
        @test ev("!(sort (3 1 4 1 5))") == [1, 1, 3, 4, 5]
    end

    @testset "zip — doubly-recursive, two is-empty guards" begin
        @test ev("!(zip (1 2 3) (a b c))") == [[1, :a], [2, :b], [3, :c]]
    end

    # ── DIVERGENT bin: under streaming these fired BOTH the base (literal-head)
    #    and recursive (var-head) clause; the recursive branch descended forever.
    #    Single guarded clause + `if` must make them TERMINATE. ──
    @testset "nth — DIVERGENT bin (was infinite under streaming)" begin
        @test ev("!(nth (a b c d) 0)") === :a   # base arm: must not recurse to -1
        @test ev("!(nth (a b c d) 2)") === :c
    end

    @testset "factorial — headline DIVERGENT case (was stack-overflow)" begin
        @test ev("!(factorial 0)") == 1         # base arm: must not recurse to -1
        @test ev("!(factorial 5)") == 120
    end

    # ── OVER-PRODUCE bin: (is-function (-> $a $b)) and (is-function $x) both
    #    fired on an arrow → stream [True, False]. Single structural clause
    #    must return exactly ONE result. ──
    @testset "is-function — OVER-PRODUCE bin (was [True, False])" begin
        # Cardinality is the load-bearing assertion: was [True, False] under
        # streaming, must be single result under any rewriter post-fix.
        rf = run_metta("!(is-function (-> Int Int))", S)
        @test length(rf) == 1                    # the cardinality assertion that matters
        @test rf[1] === true                     # PRIMUS Bool shape (see member testset note)
        @test ev("!(is-function foo)") === false
    end
end
