# Dual-evaluator ECAN tracker — runs every examples/ecan/*.metta acceptance file
# under BOTH evaluators and records the divergence landscape between the legacy
# tree-walker (eval_metta) and the OutcomeSet evaluator (eval_nd).
#
# WHY THIS EXISTS (2026-06-12): converging Core on a single MeTTa-correct
# evaluator (eval_nd) is gated on eval_nd becoming a drop-in on the stateful
# library workloads. But the two evaluators are NOT at parity and CANNOT be
# bridged by a mechanical library rewrite — three different setter forms each
# work in exactly one evaluator (see docs/CONFORMANCE_AUDIT.md "Migration
# ATTEMPTED" + "Evaluators incompatible"). The libraries are hand-tuned to
# eval_metta's bare-match `()` convention; eval_nd is the MORE-correct engine
# (it handles idiomatic remove-in-template / collapse+car-atom that eval_metta
# gets wrong). So the long-term flip is a per-subsystem PORT to eval_nd idioms,
# not an incremental parity migration.
#
# This file is therefore a LIVING TRACKER, not a parity gate:
#   * eval_metta side  → hard @test (the standing green guarantee).
#   * eval_nd side     → @test for files already at parity; @test_broken for
#     files that still diverge. When a port makes a divergent file pass under
#     eval_nd, its @test_broken flips to "Unexpectedly passing" — that's the
#     signal to promote it to @test and advance the flip one subsystem at a time.

using MeTTaCore, Test

const ECAN_DUAL_DIR = joinpath(@__DIR__, "..", "examples", "ecan")
const ECAN_DUAL_FILES = ["CoreAV","Funds","Wages","Rent","Stimulate","AFState",
                         "BulkOps","Spreading","Governance","Fluid","Adaptive","Forgetting"]
# Files where eval_nd currently matches eval_metta (0 divergences) — surveyed 2026-06-12.
# The rest still diverge (eval_nd no-ops bare-match setters on the empty path).
const ECAN_ND_PARITY = Set(["CoreAV","Rent","BulkOps","Spreading","Forgetting"])

function _ecan_dual_setup()
    S = new_core_space(); register_core_primitives!()
    _register_atom_ops!(e -> to_sexpr(eval_metta(from_sexpr(e), S)))
    load_stdlib!(S); S
end
_ecan_dual_iserr(r) = (s = strip(to_sexpr(r)); occursin("AssertionFailed", s) || startswith(s, "(Error"))

# eval_nd analogue of run_metta: ! directives → eval_nd_results, defs → core_add!
function _run_metta_nd(source::AbstractString, space)
    out = Any[]
    for expr in parse_metta(source)
        if expr isa Vector && !isempty(expr) && expr[1] === :!
            append!(out, eval_nd_results(expr[2], space))
        else
            core_add!(space, expr)
        end
    end
    out
end

function _ecan_metta_fails(fname)
    filter(_ecan_dual_iserr, run_file(joinpath(ECAN_DUAL_DIR, fname * ".metta"), _ecan_dual_setup()))
end
function _ecan_nd_fails(fname)
    path = joinpath(ECAN_DUAL_DIR, fname * ".metta"); S = _ecan_dual_setup()
    prev = pwd()
    try
        cd(ECAN_DUAL_DIR)
        filter(_ecan_dual_iserr, _run_metta_nd(read(path, String), S))
    finally
        cd(prev)
    end
end

println("ECAN-dual: running examples/ecan under eval_metta AND eval_nd...")
# SILENT-TEST GUARD (negative control): the standing `@test isempty(mfails)` green guarantee is
# only meaningful if _ecan_dual_iserr actually CATCHES a failure. Prove it discriminates on BOTH
# the eval_metta and eval_nd paths — else a detector/output-shape mismatch would make every file
# report empty fails and pass vacuously. (MOSES audit 2026-06-16.)
@testset "dual error-detection negative control" begin
    S1 = _ecan_dual_setup()
    @test  any(_ecan_dual_iserr, run_metta("!(assertEqual 1 2)", S1))   # eval_metta catches mismatch
    @test !any(_ecan_dual_iserr, run_metta("!(assertEqual 1 1)", S1))   # eval_metta clean on match
    S2 = _ecan_dual_setup()
    @test  any(_ecan_dual_iserr, _run_metta_nd("!(assertEqual 1 2)", S2))  # eval_nd catches mismatch
end
@testset "ECAN dual-evaluator tracker" begin
    for f in ECAN_DUAL_FILES
        @testset "$f" begin
            mfails = _ecan_metta_fails(f)
            @test isempty(mfails)                       # standing green guarantee
            nfails = _ecan_nd_fails(f)
            if f in ECAN_ND_PARITY
                @test isempty(nfails)                   # eval_nd at parity — keep it green
            else
                @info "eval_nd divergences (expected — pre-flip)" file=f n=length(nfails)
                @test_broken isempty(nfails)            # flips to "Unexpectedly passing" when ported
            end
        end
    end
end
