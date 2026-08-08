#!/usr/bin/env julia
# A2′ Increment-1 wiring test: dispatch a native-compiled `concatT` from eval_op.
# Proves (a) correctness — A2-on result == A2-off (interpreted) result; (b) the spike's
# speedup is delivered THROUGH the evaluator (not just a standalone Julia call).
# Run: julia --project=. tools/test_a2_wiring.jl
using MeTTaCore
const SM = MeTTaCore.Eval

sp = SM.Space(); SM.load_core_stdlib!(sp)
# concatT lives in lib/MOSES/utilities.metta (self-contained: car/cdr/cons/if/==).
SM.load_metta!(sp, read(joinpath(@__DIR__, "..", "lib", "MOSES", "utilities.metta"), String))

lst(n) = "(" * join(("e$i" for i in 1:n), " ") * ")"
bench(expr, reps) = (SM.load_metta!(sp, expr); @elapsed for _ in 1:reps; SM.load_metta!(sp, expr); end) / reps

for n in (10, 20)
    expr = "!(concatT $(lst(n)) $(lst(n)))"
    SM.A2_ENABLED[] = false; roff = SM.load_metta!(sp, expr)
    SM.A2_ENABLED[] = true;  ron  = SM.load_metta!(sp, expr)
    ok = string(roff) == string(ron)
    SM.A2_ENABLED[] = false; toff = bench(expr, 3) * 1e3   # ms
    SM.A2_ENABLED[] = true;  ton  = bench(expr, 200) * 1e3 # ms (native is fast → more reps)
    println("n=$n  match=$(ok ? "✓" : "✗")  interp=$(round(toff;digits=1))ms  native=$(round(ton;digits=4))ms  speedup=$(round(toff/ton))×")
    ok || println("   off=", roff, "\n   on =", ron)
end
SM.A2_ENABLED[] = false  # leave off
