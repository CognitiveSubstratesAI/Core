# ecan_verify.jl — ECAN migration verification + Stability step-scaling diagnosis.
# Run via the warm REPL (live output):
#   cd ~/code/CognitiveSubstratesAI/Core && \
#     printf 'include("benchmark/ecan_verify.jl"); exit()\n' | julia --project=. -i tools/repl.jl
include(joinpath(@__DIR__, "..", "test", "ecan", "ecan_live_harness.jl"))
const I = MeTTaCore.Eval

# Is heartbeat!'s cost LINEAR in ticks (heavy-but-feasible → just needs a higher finite cap) or
# QUADRATIC (a per-tick re-scan of growing state → a real perf bug the cap-raise only masks)?
I.interpret_max_steps!(0)   # no cap; small depths terminate
println("=== heartbeat! step scaling (each depth = one governance tick) ===")
let prev = 0
    for d in (1, 2, 4, 8, 16)
        sp, _ = ECANLiveHarness.fresh()
        I.load_metta!(sp, "!(add-atom &self (AV g 0.5 0.3 0.0))")
        I.load_metta!(sp, "!(update-af! g 0.5)")
        I._DIAG_STEPS[] = 0
        I.load_metta!(sp, "!(heartbeat! g $d)")
        steps = I._DIAG_STEPS[]
        ratio = prev == 0 ? 0.0 : round(steps / prev; digits=2)
        println("  depth=$(lpad(d,2))  steps=$(lpad(steps,10))  x_vs_prev=$(ratio)")
        prev = steps
    end
end
println(
    "  (x≈2 per doubling = LINEAR; x≈4 = QUADRATIC)  extrapolate to depth=50 from the trend"
)
println("PROBE_DONE")
