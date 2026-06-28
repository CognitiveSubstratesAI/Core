# ecan_perf_diag.jl — root-cause the heartbeat!/Stability compute blowup.
# Per governance tick, measure interpreter steps PER sub-call + atom-count growth → find the dominant
# and GROWING (quadratic) operation + any silent atom accumulation.
# Run via warm REPL:  printf 'include("benchmark/ecan_perf_diag.jl"); exit()\n' | julia --project=. -i tools/repl.jl
include(joinpath(@__DIR__, "..", "test", "ecan_live_harness.jl"))
const I = MeTTaCore.Interpreter
const SM = I.StandardMeTTa
I.interpret_max_steps!(0)

sp = first(ECANLiveHarness.fresh())
I.load_metta!(sp, "!(add-atom &self (AV g 0.5 0.3 0.0))")
I.load_metta!(sp, "!(update-af! g 0.5)")

# governance-step!'s sub-calls, in order (running all 8 = one tick, with mutations)
const SUBS = [("wa", "(collect-all-wa-rent!)"), ("af", "(collect-all-af-rent!)"),
              ("decay", "(apply-decay!)"), ("norm", "(apply-normalization!)"),
              ("inc", "(increment-ecan-tick!)"), ("updaf", "(update-af! g (get-sti g))"),
              ("evo", "(attention-evolution-step!)"), ("spread", "(ecan-spread-step! g 10.0)")]

nsteps(expr) = (I._DIAG_STEPS[] = 0; I.load_metta!(sp, "!" * expr); I._DIAG_STEPS[])
natoms(s) = try; length(s.atoms); catch; length(collect(s.atoms)); end

println("tick atoms | ", join([rpad(s[1], 7) for s in SUBS], " "), "| TOTAL")
for tick in 1:8
    a0 = natoms(sp)
    st = [nsteps(e) for (_, e) in SUBS]
    println(lpad(tick, 3), " ", lpad(a0, 5), " | ", join([lpad(x, 7) for x in st], " "), "| ", lpad(sum(st), 8))
end

# What's accumulating? bucket sp.atoms by head symbol.
println("--- atom-type histogram after 8 ticks (head => count) ---")
heads = Dict{String,Int}()
for a in (sp.atoms isa AbstractDict ? keys(sp.atoms) : sp.atoms)
    h = (a isa SM.Expression && !isempty(a.children)) ? string(a.children[1]) : string(a)
    heads[h] = get(heads, h, 0) + 1
end
for (h, c) in first(sort(collect(heads), by = x -> -x[2]), 14)
    println("  ", rpad(h, 30), c)
end
println("PERF_DIAG_DONE")
