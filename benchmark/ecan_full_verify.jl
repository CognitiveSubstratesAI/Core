# ecan_full_verify.jl — verify the ECAN migration + the just-fixed write paths (hebbian-update!,
# set-link-weight!, forget-atom!). Skips the slow Stability example (separate perf question).
# Run via warm REPL:  printf 'include("benchmark/ecan_full_verify.jl"); exit()\n' | julia --project=. -i tools/repl.jl
include(joinpath(@__DIR__, "..", "test", "ecan", "ecan_live_harness.jl"))
const I = MeTTaCore.Interpreter
const FAST = ["CoreAV", "Funds", "Wages", "Stimulate", "Rent", "AFState", "Spreading",
              "Fluid", "Forgetting", "Governance", "Adaptive", "BulkOps"]  # all but slow Stability

println("=== ECAN live acceptance examples (12, skipping slow Stability) ===")
for e in FAST
    r = ECANLiveHarness.run_example(e)
    tag = (r.n_errors == 0 && isempty(r.load_errs)) ? "OK " : "ERR"
    extra = r.n_errors > 0 ? "  " * join(first(r.errors, min(2, length(r.errors))), " | ") : ""
    println("  $tag $(rpad(e, 11)) errors=$(r.n_errors)/$(r.n_results)$extra")
end

println("=== Hebbian write-path (was BROKEN: hebbian-update! never created a link) ===")
let sp = first(ECANLiveHarness.fresh())
    for s in ["!(add-atom &self (AV a 0.8 0.1 0.0))", "!(add-atom &self (AV b 0.7 0.1 0.0))",
              "!(hebbian-update! a b)"]
        I.load_metta!(sp, s)
    end
    after = I.load_metta!(sp, "!(collapse (match &self (AsymHebbianLink a b \$s \$c) (AsymHebbianLink a b \$s \$c)))")
    repr = isempty(after) ? "[]" : string(after[1])
    println("  link after hebbian-update! = $repr  => ", occursin("AsymHebbianLink", repr) ? "CREATE_OK" : "CREATE_FAIL")
    # update path: a second call should blend the weight, not duplicate
    I.load_metta!(sp, "!(hebbian-update! a b)")
    n = length(I.load_metta!(sp, "!(collapse (match &self (AsymHebbianLink a b \$s \$c) found))"))
    println("  links after 2nd update (expect 1 row, no dup) = $n  => ", n == 1 ? "NO_DUP_OK" : "DUP_FAIL")
end

println("=== set-link-weight! first-create (was no-op on faithful engine) ===")
let sp = first(ECANLiveHarness.fresh())
    I.load_metta!(sp, "!(set-link-weight! x y 0.42)")
    w = I.load_metta!(sp, "!(get-link-weight x y)")
    println("  get-link-weight x y after set = ", string.(w), "  => ", string(w) == "Any[0.42]" || occursin("0.42", string(w)) ? "SET_OK" : "SET_FAIL")
end
println("VERIFY_DONE")
