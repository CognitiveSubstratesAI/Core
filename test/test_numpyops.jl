# Conformance gate for the MeTTa↔Julia numeric adapter (src/standard/NumpyOps.jl).
# ✓ values are upstream MetaMo's core/tests/helpers_test.metta (the numpy spec); ⊘ values are derived
# from the numpy CONVENTION (read from helpers.py), NEVER from this Julia layer's output (would be circular).
# Tolerance: ops replicate upstream's rounding (std→2, vectorAdd→8) IN the op, so a tight atol suffices.
using MeTTaCore, Test
const SM = MeTTaCore.Eval
const _ST = read(joinpath(@__DIR__, "..", "src", "standard", "stdlib.metta"), String)
const _SP = (s=SM.Space(); SM.load_core_stdlib!(s); s)
_mval(a) =
    if a isa SM.Grounded
        a.value
    elseif a isa SM.Sym
        Symbol(a.name)
    elseif a isa SM.Expression
        Any[_mval(c) for c in a.children]
    else
        a
    end
qn(src) = (r=SM.load_metta!(_SP, src); isempty(r) ? nothing : _mval(r[1]))
function _ae(g, e; atol=1e-9)
    e isa Number && g isa Number && return isapprox(g, e; atol=atol)
    e isa AbstractVector && g isa AbstractVector &&
        return length(g)==length(e) && all(_ae(gi, ei; atol=atol) for (gi, ei) in zip(g, e))
    g == e
end

@testset "NumpyOps — numpy-equivalence gate (helpers_test.metta + derived)" begin
    @testset "vec→scalar (✓ helpers_test)" begin
        @test _ae(qn("!(norm (3 4))"), 5.0)
        @test _ae(qn("!(norm ())"), 0.0)
        @test _ae(qn("!(sum (1 2 3 4))"), 10.0)
        @test _ae(qn("!(sum ())"), 0.0)
        @test _ae(qn("!(sum (1))"), 1.0)
        @test _ae(qn("!(product (1 2 3 4))"), 24.0)
        @test _ae(qn("!(product ())"), 1.0)
        @test _ae(qn("!(mean (1 2 3 4))"), 2.5)
        @test _ae(qn("!(variance (1 2 3 4))"), 1.25)
        @test _ae(qn("!(variance (10))"), 0.0)
        @test _ae(qn("!(variance (2 2 2))"), 0.0)
        @test _ae(qn("!(variance (1.0 2.0))"), 0.25)   # ddof=0
        @test _ae(qn("!(std (1 2 3 4))"), 1.12)                                                            # round-2
        @test _ae(qn("!(calculateNormDifference (1 2 3) (4 5 6))"), 27.0)
        @test _ae(qn("!(calculateNormDifference () ())"), 0.0)
        @test _ae(qn("!(dotProduct (1 2 3) (4 5 6))"), 32.0)
        @test _ae(qn("!(dotProduct (1 0) (0 1))"), 0.0)
        @test _ae(qn("!(dotProduct () ())"), 0.0)
    end
    @testset "vec→vec (✓ helpers_test)" begin
        @test _ae(qn("!(listDifference (7 6 13) (4 5 6))"), Any[3.0, 1.0, 7.0])
        @test _ae(qn("!(listDifference () ())"), Any[])
        @test _ae(qn("!(normalizeVector (3 4))"), Any[0.6, 0.8])
        @test _ae(qn("!(normalizeVector ())"), Any[])
        @test _ae(
            qn("!(softmax (1 2 3))"),
            Any[0.09003057317038046, 0.24472847105479764, 0.6652409557748218];
            atol=1e-10
        )
    end
    @testset "✓ scalar + split-free helpers_test" begin
        @test _ae(qn("!(roundNum 2.67777 2)"), 2.68)
        @test _ae(qn("!(roundNum 0.0 2)"), 0.0)
    end
    @testset "⊘ derived from numpy convention (NOT from Julia output)" begin
        @test _ae(qn("!(vectorAdd (1 2) (0.5 0.5))"), Any[1.5, 2.5])              # round-8
        @test _ae(qn("!(averageArrays (0 0) (1 1))"), Any[0.5, 0.5])
        @test _ae(qn("!(clipVector (0.2 1.5 -0.3) 0.0 1.0)"), Any[0.2, 1.0, 0.0])
        @test _ae(qn("!(scaleArray (0.5 1 2) 10.0)"), Any[5.0, 10.0, 20.0])
        @test _ae(qn("!(roundList (1.234 5.678) 1)"), Any[1.2, 5.7])
        @test _ae(qn("!(positivePart -0.4)"), 0.0)
        @test _ae(qn("!(positivePart 0.7)"), 0.7)
        @test _ae(qn("!(sigmoidNumber 0.0)"), 0.5)
        @test _ae(qn("!(absNumber -3.0)"), 3.0)
        @test _ae(qn("!(expNumber 0.0)"), 1.0)
        @test _ae(qn("!(meanAtIndices (0.2 0.4 0.6 0.8) (1 3))"), 0.6)          # 0-based idx → 0.4,0.8
    end
end
