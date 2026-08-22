#!/usr/bin/env julia
# Issue B: Core interp of concatT allocates ~2.9 GiB at n=20 (84% GC) → super-linear.
# ALLOCATION profiling (not CPU) to find WHAT allocates. Run: julia --project=. tools/profile_concatT.jl
using MeTTaCore, Profile
const SM = MeTTaCore.Eval
const SA = MeTTaCore.StandardMeTTa

sp = SM.Space();
SM.load_core_stdlib!(sp)
SM.load_metta!(
    sp,
    "(= (concatT \$a \$b) (if (== \$a ()) \$b (let \$rest (concatT (cdr-atom \$a) \$b) (cons-atom (car-atom \$a) \$rest))))"
)
SM.A2_ENABLED[] = false
lst(n) = SM.parse_program("(" * join(("e$i" for i in 1:n), " ") * ")")[1][2]
mkcall(n) = SA.Expression(SA.Atom[SA.Sym("concatT"), lst(n), lst(n)])

c = mkcall(20);
SM.metta_run(c, sp)              # warmup
Profile.Allocs.clear()
Profile.Allocs.@profile sample_rate=0.02 SM.metta_run(c, sp)
res = Profile.Allocs.fetch()

byloc = Dict{String, Vector{Int}}()   # "func file:line" => [count, bytes]
bytype = Dict{String, Int}()
for a in res.allocs
    loc = "?"
    for fr in a.stacktrace
        s = string(fr.file)
        if occursin("Eval.jl", s) || occursin("Atoms.jl", s)
            loc = "$(fr.func)  $(basename(s)):$(fr.line)"
            break
        end
    end
    v = get!(byloc, loc, [0, 0])
    v[1] += 1
    v[2] += a.size
    t = string(a.type)
    bytype[t] = get(bytype, t, 0) + a.size
end
println("=== top allocating SITES (sampled 2%; bytes scaled ×50) ===")
for (loc, v) in sort(collect(byloc); by=x -> -x[2][2])[1:min(18, end)]
    println(rpad(string(v[2]*50 ÷ 1024, " KiB"), 12), rpad("$(v[1]*50) allocs", 14), loc)
end
println("=== top allocating TYPES ===")
for (t, by) in sort(collect(bytype); by=x -> -x[2])[1:min(10, end)]
    println(rpad(string(by*50 ÷ 1024, " KiB"), 12), t)
end
