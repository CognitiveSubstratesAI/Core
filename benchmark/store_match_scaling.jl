# store_match_scaling.jl — Phase 2 store benchmark
# ─────────────────────────────────────────────────────────────────────────────
# Q: is MORK-trie matching (CoreSpace) competitive with the interpreter's in-memory
#    Julia Dict index (Interpreter.Space) on the hot path — rule lookup by ground goal?
#
# This is the "measure first" gate on making the MORK store (and the ZAM/reduction fast
# lane over it) the PRIMARY evaluation path with the tree-walking interpreter as fallback.
# The signal is SCALING across N, not one datapoint (MORK-author verdict: asymptotic
# dominates a fixed factor < 2×).
#
# FINDING (2026-07-16, warm session): the trie is competitive ONLY with a flat head-first
# (ground-prefix) atom layout. Our nested `(= (f a) body)` shape defeats prefix-narrowing
# and is O(N); Ben Goertzel's OmegaClaw "most selective stable field first" layout
# `(rule f a $b)` narrows to O(1) and matches the interpreter's order (≈8µs vs ≈4µs).
#   (A) INTERP query (=,head Dict)        O(1)   ~4–8 µs      ← the live path
#   (B) core_rules cold (trie walk)       O(N)   →166 ms @20k
#   (D) core_match nested (= (f a) $b)    O(N)   →185 ms @20k  (nested head not pinnable)
#   (E) core_match FLAT (rule f a $b)     O(1)   ~8–10 µs      ← the trie done Ben's way
# The ~2× constant on (E) is a byte→string→parse readback tax in _walk_atoms_narrowed,
# optimizable with a direct bytes→Atom decoder.
#
# Run (warm):  printf 'include("benchmark/store_match_scaling.jl"); exit()\n' | julia --project=. -i tools/repl.jl
# Run (cold):  julia --project=. benchmark/store_match_scaling.jl   # allow-cold-start: benchmark

using MeTTaCore
const _M = MeTTaCore
const _I = MeTTaCore.Interpreter

_pint(s) = _I.parse_from(_I.tokenize(s), Ref(1))       # string → interpreter Atom

"min-of-K per-op wall time (s); adaptive repeats so O(N) cases don't run forever"
function _best(f; N = 1, K = 7)
    reps = clamp(div(80_000, max(N, 1)), 1, 400)
    f()                                                # warm JIT
    t = Inf
    for _ in 1:K
        e = @elapsed (for _ in 1:reps; f(); end)
        t = min(t, e / reps)
    end
    t
end
_us(t) = round(t * 1e6; digits = 3)

function run_store_match_scaling(; Ns = [200, 2000, 20000])
    rows = Dict{String, Vector{Float64}}()
    push_r(k, v) = (haskey(rows, k) || (rows[k] = Float64[]); push!(rows[k], v))

    for N in Ns
        k = div(N, 2); khs = Symbol("f$k")
        println("\n===== N = $N  (lookup head f$k) =====")

        sp = _I.Space()
        for i in 1:N; _I.add_atom!(sp, _pint("(= (f$i a) b$i)")); end
        patA = _pint("(= (f$k \$x) \$body)")
        tA = _best(N = N) do; _I.query(sp, patA); end
        println("  (A) INTERP query           $(_us(tA)) µs"); push_r("A", tA)

        cs = _M.new_core_space()
        for i in 1:N; _M.core_add!(cs, "(= (f$i a) b$i)"); end
        tB = _best(N = N) do; empty!(cs.rule_cache); _M.core_rules(cs, khs); end
        println("  (B) core_rules COLD (walk) $(_us(tB)) µs"); push_r("B", tB)
        patD = [:(=), [khs, :a], Symbol("\$b")]
        tD = _best(N = N) do; _M.core_match(cs, patD); end
        println("  (D) core_match nested      $(_us(tD)) µs"); push_r("D", tD)

        cs2 = _M.new_core_space()
        for i in 1:N; _M.core_add!(cs2, "(rule f$i a b$i)"); end
        patE = [:rule, khs, Symbol("\$a"), Symbol("\$b")]
        tE = _best(N = N) do; _M.core_match(cs2, patE); end
        println("  (E) core_match FLAT-prefix $(_us(tE)) µs"); push_r("E", tE)
    end

    println("\n===== SCALING (t[N=$(Ns[end])]/t[N=$(Ns[1])]; ~1 = O(1), ~$(div(Ns[end],Ns[1])) = O(N)) =====")
    for (k, label) in [("A", "(A) INTERP query"), ("B", "(B) core_rules COLD walk"),
                       ("D", "(D) core_match nested"), ("E", "(E) core_match FLAT-prefix")]
        v = rows[k]
        println("  $label:  $(round(v[end]/v[1]; digits=1))×   ($(_us(v[1]))→$(_us(v[end])) µs)")
    end
    rows
end

run_store_match_scaling()
