# THE decisive measurement (2026-06-17): attribute reduce-to's time by MeTTa head.
# RESULT (recorded in docs/architecture/METTA_COMPILATION_INTEGRATION §6d): the cost is NOT
# in leaf helpers — concatT=0.2%, gatherJunctors=0.2%; it's ~83 ms/reduction × 2646 reductions
# of mostly trivial structure (if 18%, data-constructors AND/A/B/NOT 35%, let/let* 23%).
#
# REQUIRES temporary instrumentation in src/standard/Interpreter.jl (removed after measuring — it
# adds a Dict op to the hot reduction path). To re-run, re-add these 4 lines:
#   after `is_minimal_op(...)`:
#     const _RHEAD = Dict{String,Int}()
#     @inline _rcount!(a::Atom) = (h = head_name(a); h != "" && (_RHEAD[h] = get(_RHEAD,h,0)+1); nothing)
#   and `_rcount!(<subject>)` immediately before each of the 3 `query(space, Expression(Sym("="), …, X))` sites.
#   julia --project=. tools/profile_reduceto.jl
using MeTTaCore
const SM = MeTTaCore.Interpreter

sp = SM.Space(); SM.load_core_stdlib!(sp)
SM.load_metta!(sp, "!(import! &self (library MOSES))")   # proven loader (index_diag.jl)

# sanity: is reduce-to actually defined now?
println("reduce-to rule present: ",
        haskey(sp.index, ("=", "reduce-to")) ? length(sp.index[("=","reduce-to")]) : 0, " rule(s)")

call = SM.parse_program("(reduce-to (AND A B))")[1][2]

# warm up the orchestrator on a tiny input so JIT cost is excluded
warm = SM.parse_program("(reduce-to (AND A))")[1][2]
SM.metta_run(warm, sp)

empty!(SM._RHEAD)
GC.gc()
t = @elapsed res = SM.metta_run(call, sp)
println("reduce-to (AND A B) => ", res, "   in ", round(t; digits=2), " s")

total = sum(values(SM._RHEAD); init=0)
println("\ntotal reductions: ", total, "   distinct heads: ", length(SM._RHEAD))

# classify each head: is it a compilable user function (A2′ target) or interpreter/builtin?
# user MOSES/stdlib functions are compilable; minimal-ops & grounded ops are NOT reduced here.
sorted = sort(collect(SM._RHEAD); by = kv -> -kv[2])
println("\n  reductions   share   head")
for (h, n) in first(sorted, 30)
    println(lpad(n, 12), "   ", lpad(string(round(100n/max(total,1); digits=1)), 5), "%   ", h)
end
