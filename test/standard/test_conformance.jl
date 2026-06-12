# Conformance: run hyperon-experimental's OWN interpreter test scripts (vendored verbatim from
# python/tests/scripts/) through the StandardMeTTa evaluator and assert no `(Error … AssertionFailed)`.
# These are the upstream b-series — the same scripts the earlier eval_metta/eval_nd audit used.
# Vendored: b0/b1/b3 fully pass. (b2 runs but partial; b4 nondeterminism / b5 types are follow-ons.)
include("../../src/standard/Minimal.jl")
using .Minimal
using .Minimal.StandardMeTTa
using Test

const CONF_DIR = joinpath(@__DIR__, "conformance")
const STDLIB   = read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String)

function run_script(name)
    sp = Space()
    load_metta!(sp, STDLIB)
    results = load_metta!(sp, read(joinpath(CONF_DIR, name), String))
    filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), results)
end

@testset "conformance — hyperon b-series scripts (verbatim upstream)" begin
    for f in ["b0_chaining_prelim.metta", "b1_equal_chain.metta", "b3_direct.metta"]
        @testset "$f" begin
            errs = run_script(f)
            for e in errs; @info "conformance failure" script=f expr=to_sexpr_via(e); end
            @test isempty(errs)
        end
    end
end

to_sexpr_via(e) = string(e)
