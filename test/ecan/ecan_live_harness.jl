# ecan_live_harness.jl — run the ECAN library + acceptance examples on the LIVE engine
# (MeTTaCore.Interpreter), mirroring test_pln_ecan.jl's load_metta! approach. This is the
# migration scaffold for moving test_ecan.jl off the obsolete eval_metta/run_file path.
#
# Each examples/ecan/*.metta is run in a FRESH Interpreter Space with the ECAN modules
# pre-loaded (the files seed conflicting global state — funds/AF/tick — so isolation matters).
# Strips the `!(import! &self (library ecan))` line (we load modules explicitly instead).
#
# Usage (warm, via MettaJam /julia or REPL):
#   include(".../Core/test/ecan/ecan_live_harness.jl"); println(ECANLiveHarness.run_all())
#   ECANLiveHarness.run_example("CoreAV")
module ECANLiveHarness
using MeTTaCore.Interpreter, MeTTaCore.Interpreter.StandardMeTTa

const BASE = normpath(joinpath(@__DIR__, "..", ".."))
# Load order per lib/ecan/ecan.metta (hyperseed/adaptive_attention deferred — Phase 1c).
const MODS = ["ECAN_Policies", "core_logic", "state_logic",
              "SpreadingActivation", "AttentionPolicies", "FluidECAN", "Forgetting"]
const EXAMPLES = ["CoreAV", "Funds", "Wages", "Stimulate", "Rent", "AFState", "Spreading",
                  "Fluid", "Forgetting", "Governance", "Adaptive", "Stability", "BulkOps", "Convergence"]

eerrs(rs) = filter(r -> r isa Expression && !isempty(r.children) && r.children[1] == Sym("Error"), rs)

# Build a fresh space with stdlib + the ECAN modules. Returns (space, load_report).
function fresh()
    sp = Space(); load_core_stdlib!(sp)
    rep = String[]
    for m in MODS
        try
            load_metta!(sp, read(joinpath(BASE, "lib", "ecan", "$m.metta"), String))
        catch e
            push!(rep, "$m:LOAD_ERR(" * first(split(sprint(showerror, e), '\n')) * ")")
        end
    end
    # Phase 1c: entropy classifier + self-evolution (Governance/Adaptive/Stability depend on it).
    try
        load_metta!(sp, read(joinpath(BASE, "lib", "hyperseed", "adaptive_attention.metta"), String))
    catch e
        push!(rep, "adaptive_attention:LOAD_ERR(" * first(split(sprint(showerror, e), '\n')) * ")")
    end
    sp, rep
end

function run_example(name)
    interpret_max_steps!(3_000_000)   # finite headroom over the 512K default (Stability's 100 ticks); NOT 0/unlimited (a blowup would hang the server)
    sp, rep = fresh()
    src = replace(read(joinpath(BASE, "examples", "ecan", "$name.metta"), String),
                  "!(import! &self (library ecan))" => "")
    rs = load_metta!(sp, src)
    errs = eerrs(rs)
    (name = name, n_results = length(rs), n_errors = length(errs),
     load_errs = rep, errors = string.(errs))
end

function run_all()
    lines = String[]
    for e in EXAMPLES
        try
            r = run_example(e)
            tag = r.n_errors == 0 && isempty(r.load_errs) ? "✓" : "✗"
            msg = "$tag $(rpad(e, 11)) results=$(r.n_results) errors=$(r.n_errors)"
            !isempty(r.load_errs) && (msg *= " LOAD:" * join(r.load_errs, ";"))
            r.n_errors > 0 && (msg *= " :: " * join(first(r.errors, min(2, length(r.errors))), " | "))
            push!(lines, msg)
        catch err
            push!(lines, "✗ $(rpad(e, 11)) EXCEPTION: " * first(split(sprint(showerror, err), '\n')))
        end
    end
    join(lines, "\n")
end
end # module
