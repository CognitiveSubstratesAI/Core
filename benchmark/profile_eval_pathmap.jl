# Profile the MORK-backed eval lane (the ONLY path that uses PathMap) to answer:
# "is PathMap the bottleneck for MeTTa eval?". Run via the WARM REPL (preloads MeTTaCore), NOT cold:
#   printf 'include("benchmark/profile_eval_pathmap.jl"); exit()\n' | julia --project=. -i tools/repl.jl
# saturate=true routes mc_run → sc_execute! (MorkSupercompiler) → space_metta_calculus! (MORK) → PathMap.
using MeTTaCore, Profile
const MC = MeTTaCore
try; MC.register_all_primitives!(); catch; end

const N = 120
const EDGES = join(["(edge $i $(i+1))" for i in 0:N-1], "\n")
# recursive transitive closure → saturation (KBSaturation/MorkSupercompiler) → MORK calculus → trie I/O
const PROG = "(~> (edge \$x \$y) (trans \$x \$y))\n(~> (, (edge \$x \$y) (trans \$y \$z)) (trans \$x \$z))"

function run1()
    cs = MC.new_core_space(); MC.load_stdlib!(cs)
    MC.mc_run(cs, EDGES, PROG; saturate = true, steps = 1_000_000)
end
@info "warming (one saturate run)…"; run1()

Profile.clear(); Profile.init(n = 10^7, delay = 0.0002)
@profile for _ in 1:8; run1(); end

io = IOBuffer()
Profile.print(IOContext(io, :displaysize => (100000, 320)); format = :flat, sortedby = :count, mincount = 10)
prof = String(take!(io))
B = Dict("PathMap"=>0, "MorkSupercompiler"=>0, "MORK kernel (calculus/space)"=>0,
         "MORK expr (unify/apply)"=>0, "MORK frontend (parse/ser)"=>0, "MORK other"=>0,
         "Core"=>0, "other/Base/runtime"=>0)
top = String[]
for ln in split(prof, '\n')
    m = match(r"^\s*(\d+)\s", ln); m === nothing && continue
    c = parse(Int, m.captures[1])
    k = occursin("PathMap/src", ln)            ? "PathMap" :
        occursin("MorkSupercompiler/src", ln)  ? "MorkSupercompiler" :
        occursin("MORK/src/kernel", ln)        ? "MORK kernel (calculus/space)" :
        occursin("MORK/src/expr", ln)          ? "MORK expr (unify/apply)" :
        occursin("MORK/src/frontend", ln)      ? "MORK frontend (parse/ser)" :
        occursin("MORK/src", ln)               ? "MORK other" :
        occursin("Core/src", ln)               ? "Core" : "other/Base/runtime"
    B[k] += c
    length(top) < 20 && occursin(r"PathMap/src|MORK/src|MorkSupercompiler/src|Core/src", ln) && push!(top, strip(ln))
end
tot = sum(values(B))
println("\n=== MORK-lane eval self-time by area (saturate→MorkSupercompiler→MORK; total ", tot, ") ===")
for (k, c) in sort(collect(B), by = x -> -x[2]); println("  ", rpad(k, 30), lpad(c, 8), "  (", round(100c/max(tot,1);digits=1), "%)"); end
println("\n=== top project frames ===")
for t in top[1:min(end, 16)]; println("  ", t); end
println("PROFILE_DONE")
