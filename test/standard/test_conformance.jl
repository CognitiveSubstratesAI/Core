# FULL conformance matrix — runs EVERY hyperon-experimental interpreter test script (all 26, vendored
# verbatim from python/tests/scripts/) through the StandardMeTTa evaluator and asserts the EXACT number
# of (Error … AssertionFailed)/(Error …) directives per script against an explicit baseline.
#
# WHY EXACT (not "0 errors on the ones I picked"): cherry-picking the passing scripts hides the real
# state, and a green subset can't be trusted to mean the evaluator works. This baseline records the
# COMPLETE truth — every script, with its real pass/fail count. A regression (errors go up) fails the
# test; an unrecorded improvement (errors go down) ALSO fails, forcing the baseline to be updated and
# kept honest. The matrix is printed every run so the incomplete state is always visible, never hidden.
#
# Current: 234/234 directives pass — FULL conformance against the vendored hyperon corpus. The baseline is
# all-zero; any future regression (errors go up) OR unrecorded change fails this test and must be
# explained. Keep it honest: when adding a new vendored script, add its real count here, don't cherry-pick.
using MeTTaCore.Interpreter                  # precompiled submodule (was: include fresh → recompiled per file)
using MeTTaCore.Interpreter.StandardMeTTa
using Test

const CONF_DIR = joinpath(@__DIR__, "conformance")
Interpreter._MODULE_PATH[] = [CONF_DIR]              # so `import! &kb c2_spaces_kb` resolves the module file
const STDLIB   = read(joinpath(@__DIR__, "..", "..", "src", "standard", "stdlib.metta"), String)

# baseline = expected number of error directives per script (0 = fully passing).
const BASELINE = Dict(
    "a1_symbols.metta"=>0, "a2_opencoggy.metta"=>0, "a3_twoside.metta"=>0,
    "b0_chaining_prelim.metta"=>0, "b1_equal_chain.metta"=>0, "b2_backchain.metta"=>0,
    "b3_direct.metta"=>0, "b4_nondeterm.metta"=>0, "b5_types_prelim.metta"=>0,
    "c1_grounded_basic.metta"=>0, "c2_spaces.metta"=>0, "c2_spaces_kb.metta"=>0, "c3_pln_stv.metta"=>0,
    "d1_gadt.metta"=>0, "d2_higherfunc.metta"=>0, "d3_deptypes.metta"=>0, "d4_type_prop.metta"=>0,
    "d5_auto_types.metta"=>0,
    "e1_kb_write.metta"=>0, "e2_states.metta"=>0, "e3_match_states.metta"=>0,
    "f1_imports.metta"=>0, "f1_moduleA.metta"=>0, "f1_moduleB.metta"=>0, "f1_moduleC.metta"=>0,
    "g1_docs.metta"=>0)

function script_errors(name)
    sp = Space(); load_core_stdlib!(sp)   # stdlib.metta + CoreExtensions.metta (lib, hidden from get-atoms)
    rs = try load_metta!(sp, read(joinpath(CONF_DIR, name), String)) catch e; return (-1, "CRASH $(typeof(e))"); end
    errs = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)
    (length(errs), "$(length(rs)-length(errs))/$(length(rs)) pass")
end

@testset "conformance — FULL hyperon corpus matrix (26 scripts, exact baseline)" begin
    println("\n  ── conformance matrix (StandardMeTTa vs upstream b/a/c/d/e/f/g) ──")
    totpass = 0; tot = 0
    for name in sort(collect(keys(BASELINE)))
        n, summary = script_errors(name)
        m = match(r"(\d+)/(\d+)", summary)
        if m !== nothing; totpass += parse(Int, m[1]); tot += parse(Int, m[2]); end
        flag = n == BASELINE[name] ? (n == 0 ? "✓" : "· ($n known)") : "‼ CHANGED $(BASELINE[name])→$n"
        println("    ", rpad(name, 26), rpad(summary, 12), flag)
        @testset "$name" begin
            @test n == BASELINE[name]      # exact: regression OR unrecorded improvement both fail
        end
    end
    println("    TOTAL: $totpass/$tot directives pass\n")
end
