# varstore_ab.jl — the A/B that shows the CoreSpace STORAGE FORM, not MORK, makes stored rules inert.
#
# MEASURED 2026-08-15 (`julia --project=. tools/varstore_ab.jl`):
#   A  core_add!            -> (= (f __var_x) __var_x)   ground query (= (f 5) $r) -> n=0   INERT
#   B  space_add_all_sexpr! -> (= (f $a) $a)             ground query (= (f 5) $r) -> n=1   FIRES
#
# Same rule, same trie, same matcher — only the write path differs. `to_sexpr` maps $x to the GROUND
# symbol __var_x, so MORK cannot unify it with a ground argument. The wildcard control fires in BOTH,
# which is why this stayed invisible: any query whose variable positions are wildcards matches fine.
#
# ⚠️ ALSO SHOWN, AND IT SEQUENCES THE FIX: two serializers disagree on the SAME trie.
#     space_dump_all_sexpr -> (= (f $a) $a)   faithful (name regenerated, co-reference kept)
#     expr_serialize(loc)  -> (= (f $) _1)    LOSSY  (bare $ = name-discarded NewVar; _1 = VarRef)
# `core_match_bind` reads via from_sexpr(expr_serialize(loc)) — the lossy one — so it is correct
# TODAY ONLY BECAUSE storage is __var_x. Switch storage to real vars first and it returns `_1` as a
# ground symbol. Read paths must move to `expr_to_atom` (6627a45, byte-level, de-Bruijn co-reference)
# BEFORE the storage form changes. History: a350007 (introduced __var_x), 103fe4e (BLOCKER 1+2,
# mork_native_vars added on the READ path, storage deliberately unchanged), 2f7e0f1 (core_match_bind).
#
# allow-new-artifact: preserves a measured A/B probe; corpora consulted (MORK.wiki, PeTTa, git history)

using MeTTaCore
const MC = MeTTaCore
sep(t) = (println(); println("="^78); println(t); println("="^78))

# ask MORK's OWN matcher, via the real signature: (btm, Expr, effect) -> Int
function ask(cs, q::String)
    pat = MC.sexpr_to_expr(q)
    hits = String[]
    n = MC.space_query_multi(cs.inner.btm, pat, function (_b, loc)
        push!(hits, strip(MC.expr_serialize(loc))); true
    end)
    (n, hits)
end

sep("A — stored via to_sexpr (CoreSpace write path): (= (f __var_x) __var_x)")
csA = MC.new_core_space()
MC.core_add!(csA, [:(=), [:f, Symbol("\$x")], Symbol("\$x")])
println("  trie: ", strip(MC.space_dump_all_sexpr(csA.inner)))
for q in ["(, (= (f 5) \$r))", "(, (= (f \$y) \$r))"]
    try
        n, hits = ask(csA, q)
        println("  ", rpad(q, 24), " -> n=", n, "  ", hits)
    catch e
        println("  ", rpad(q, 24), " raised ", typeof(e), ": ", sprint(showerror, e)[1:min(end,120)])
    end
end

sep("B — stored via space_add_all_sexpr! (REAL MORK vars): (= (f \$x) \$x)")
csB = MC.new_core_space()
MC.space_add_all_sexpr!(csB.inner, "(= (f \$x) \$x)")
println("  trie: ", strip(MC.space_dump_all_sexpr(csB.inner)), "   <- name regenerated, co-reference kept")
for q in ["(, (= (f 5) \$r))", "(, (= (f \$y) \$r))"]
    try
        n, hits = ask(csB, q)
        println("  ", rpad(q, 24), " -> n=", n, "  ", hits)
    catch e
        println("  ", rpad(q, 24), " raised ", typeof(e), ": ", sprint(showerror, e)[1:min(end,120)])
    end
end

sep("VERDICT")
println("  If A's ground query is 0 and B's ground query is >0, the STORAGE FORM is the whole cause:")
println("  the rule is inert in the trie only because to_sexpr wrote a ground symbol where a")
println("  variable belonged. Nothing about MORK, De Bruijn, or name loss is implicated.")
println()
println("done.")
