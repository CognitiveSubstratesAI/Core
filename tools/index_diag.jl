#!/usr/bin/env julia
# tools/index_diag.jl — measure the Minimal Space first-arg index selectivity after loading a lib.
# Every query scans `wildcard` + the one matching bucket; small wildcard + small buckets ⇒ selective
# index. Used to compare indexing strategies (ours vs hyperon-trie vs CeTTa-hash): the discriminating
# metric is candidates-scanned-per-query.  Run: julia --project=. tools/index_diag.jl
using MeTTaCore
const SM = MeTTaCore.Eval

sp = SM.Space()
SM.load_core_stdlib!(sp)
SM.load_metta!(sp, "!(import! &self (library MOSES))")

total = length(sp.atoms)
wc    = length(sp.wildcard)
nbk   = length(sp.index)
sizes = sort(collect(length(v) for v in values(sp.index)); rev=true)

println("total atoms              : ", total)
println("wildcard (scanned ALWAYS): ", wc, "   (", round(100wc/total; digits=1), "% of all atoms)")
println("index buckets            : ", nbk)
println("bucket sizes (top 10)    : ", first(sizes, 10))
println("max / mean bucket        : ", maximum(sizes), " / ", round(sum(sizes)/length(sizes); digits=2))
# candidates a typical reduct query scans = its bucket + wildcard
for fn in ("reduceToElegance", "applyReduce", "gatherJunctors", "concatT", "filtP", "isLiteral")
    k = ("=", fn)
    b = haskey(sp.index, k) ? length(sp.index[k]) : 0
    println("query (= ($fn …) \$x) scans : ", b, " bucket + ", wc, " wildcard = ", b + wc,
            "   (vs ", total, " naive)")
end
