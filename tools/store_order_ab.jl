# store_order_ab.jl — does the conformance corpus depend on STORE ORDER?
#
# `Eval.Space.store` is a Vector, so `all_atoms` returns SOURCE order; a trie returns BYTE-LEX order.
# This runs all 26 conformance scripts twice — definitions loaded in source order both times, then
# the store reordered byte-lexicographically before the queries run (permuting SOURCE would not be
# the same experiment: `!` directives execute inline, so it would change WHEN things run).
#
# MEASURED 2026-08-15:  SAME 26 / DIFFERS 0, over 254 queries.
# Permutation verified REAL, not a no-op: 141/145, 158/158, 148/148, 130/131 positions moved.
#
# 🔴 SCOPE — WHAT THIS DOES *NOT* SHOW. The corpus asserts via `assertEqual` (127 uses) and
# `assertEqualToResult` (92), and `assertEqualToResult` compares with
# `(== (union-atom (subtraction-atom $a $expected) (subtraction-atom $expected $a)) ())` — SYMMETRIC
# DIFFERENCE, i.e. a SET comparison. So this measures that the answer SET is stable under reordering.
# It CANNOT detect an answer-ORDER change, by construction. "The corpus does not depend on store
# order" is the correct claim; "answer ordering does not matter" is NOT, and this corpus can never
# establish it — that needs a consumer that consumes answers positionally.
#
# allow-new-artifact: preserves a measured A/B; corpora consulted (stdlib.metta, conformance corpus)

using MeTTaCore
const MC = MeTTaCore
const IV = MeTTaCore.Eval
CC = joinpath(dirname(pathof(MeTTaCore)), "..", "test", "standard", "conformance")

# Run one script with the store left in SOURCE order (:src) or reordered BYTE-LEXICOGRAPHICALLY
# (:sorted) — the order a trie would hand back — after definitions load but before queries run.
function run_script(src::String, mode::Symbol)
    sp = IV.Space(); IV.load_core_stdlib!(sp)
    forms = MC._cs_split_top_level(src)
    defs  = [f for f in forms if !startswith(strip(f), "!")]
    bangs = [f for f in forms if  startswith(strip(f), "!")]
    for d in defs
        try IV.load_metta!(sp, d * "\n") catch; end
    end
    if mode === :sorted
        sort!(sp.store.atoms, by = a -> string(a))    # trie order, applied to the SAME contents
    end
    out = String[]
    for b in bangs
        r = try IV.load_metta!(sp, b * "\n") catch e; ["<raise:" * string(typeof(e)) * ">"] end
        push!(out, string(r))
    end
    out
end

function main()
scripts = sort([f for f in readdir(CC) if endswith(f, ".metta")])
println("corpus: ", length(scripts), " scripts at ", CC)
println()
same = 0; diff = 0; difflist = String[]
for name in scripts
    src = read(joinpath(CC, name), String)
    a = try run_script(src, :src)    catch e; ["<ERR " * string(typeof(e)) * ">"] end
    b = try run_script(src, :sorted) catch e; ["<ERR " * string(typeof(e)) * ">"] end
    agree = (a == b)
    agree ? (same += 1) : (diff += 1; push!(difflist, name))
    n = length(a)
    println(rpad(name, 34), rpad(string(n) * " queries", 14), agree ? "SAME" : "*** DIFFERS ***")
    if !agree
        for i in 1:max(length(a), length(b))
            x = i <= length(a) ? a[i] : "<missing>"
            y = i <= length(b) ? b[i] : "<missing>"
            x == y || println("      q", i, "  src   = ", first(x, 150), "\n            sorted= ", first(y, 150))
        end
    end
end
println()
println("="^78)
println("SAME: ", same, "    DIFFERS: ", diff, "    of ", length(scripts))
isempty(difflist) || println("differing: ", join(difflist, ", "))
println("="^78)
println(diff == 0 ?
  "=> the corpus does NOT depend on store order. Answer ordering is NOT a seam blocker." :
  "=> store order IS load-bearing for the listed scripts; a trie-backed store changes their answers.")
end
main()
