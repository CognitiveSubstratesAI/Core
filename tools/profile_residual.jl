# Attribute reduce-to's RESIDUAL cost after the apply_and_retain narrowing fix (16.3s for (AND A B)).
# Identify the root cause — do NOT assume "abstract dispatch / residual copies". Two lenses:
#   (1) allocations by TYPE and by SITE (what is allocated, and where)
#   (2) CPU flat profile (where wall time goes)
#   julia --project=. tools/profile_residual.jl
using MeTTaCore, Profile
using Profile.Allocs
const SM = MeTTaCore.Interpreter

sp = SM.Space(); SM.load_core_stdlib!(sp)
SM.load_metta!(sp, "!(import! &self (library MOSES))")
warm = SM.parse_program("(reduce-to (AND A))")[1][2]; SM.metta_run(warm, sp)
call = SM.parse_program("(reduce-to (AND A B))")[1][2]

# ── (1) allocation profile ──────────────────────────────────────────────────
Allocs.clear(); GC.gc()
Allocs.@profile sample_rate=0.02 SM.metta_run(call, sp)
allocs = Allocs.fetch()
println("\n######## ALLOCATIONS (sampled ×0.02) ########")
println("sampled alloc events: ", length(allocs.allocs))

bytes_by_type = Dict{String,Int}(); cnt_by_type = Dict{String,Int}()
bytes_by_site = Dict{String,Int}()
for a in allocs.allocs
    ty = string(a.type)
    bytes_by_type[ty] = get(bytes_by_type, ty, 0) + a.size
    cnt_by_type[ty]   = get(cnt_by_type, ty, 0) + 1
    # first non-Profile stack frame = allocation site
    site = "?"
    for fr in a.stacktrace
        s = string(fr.func)
        if !occursin("Profile", s) && !occursin("Allocs", s); site = "$(fr.func) @ $(fr.file):$(fr.line)"; break; end
    end
    bytes_by_site[site] = get(bytes_by_site, site, 0) + a.size
end
tot = sum(values(bytes_by_type); init=1)
println("\n-- by TYPE (top 12) --   sampled bytes / share / count")
for (ty,b) in first(sort(collect(bytes_by_type); by=kv->-kv[2]), 12)
    println(lpad(round(100b/tot;digits=1),5), "%  ", lpad(b,12), "  ", lpad(get(cnt_by_type,ty,0),7), "  ", ty)
end
println("\n-- by SITE (top 15) --   share / sampled bytes")
for (site,b) in first(sort(collect(bytes_by_site); by=kv->-kv[2]), 15)
    println(lpad(round(100b/tot;digits=1),5), "%  ", lpad(b,12), "  ", site)
end

# ── (2) CPU flat profile ──────────────────────────────────────────────────────
Profile.clear(); GC.gc()
@profile SM.metta_run(call, sp)
println("\n######## CPU FLAT PROFILE (top frames) ########")
io = IOBuffer(); Profile.print(IOContext(io,:displaysize=>(120,200)); format=:flat, sortedby=:count, mincount=50)
for ln in last(split(String(take!(io)),'\n'), 40); println(ln); end
