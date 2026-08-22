# PAYOFF: tier-2 sc_execute! vs direct MORK calculus on a scaling multi-source path join.
# Run WARM (hook-enforced):  printf 'include("tools/bench_supercompiler.jl"); exit()\n' | julia --project=. -i tools/repl.jl
#
# Verified result (2026-06-17, 3-source join, parity ✓ at every K):
#   K=30: direct 1.48s  tier2 2.55s  0.58×   (overhead dominates on trivial input)
#   K=60: direct 8.55s  tier2 0.32s  26.8×
#   K=90: direct 47.7s  tier2 1.11s  43.1×
# ⇒ tier-2 is a SCALE tool: 27–43× once the join cardinality grows (Rule-of-64 territory),
#   identical results; slower on tiny inputs, so don't make it the default.
using MeTTaCore;
const MC = MeTTaCore

function rand_dag(nn, ne)
    st = UInt64(0x12345678ABCDEF01)
    es = Set{String}()
    while length(es) < ne
        st = st*6364136223846793005 + 1442695040888963407
        i = Int(st>>33)%nn
        st = st*6364136223846793005 + 1442695040888963407
        j = Int(st>>33)%nn
        i==j && continue
        i, j = minmax(i, j)
        push!(es, "(edge $i $j)")
    end
    join(es, "\n")
end
const PROG = raw"(exec 0 (, (edge $a $b) (edge $b $c) (edge $c $d)) (, (p3 $a $d)))"
np3(s) = count(l->occursin("p3", l), split(MC.space_dump_all_sexpr(s.inner), '\n'))
bench(f) = (GC.gc(); @elapsed f())

println("K | direct(s) tier2(s) speedup | d# t# parity")
for ne in (30, 60, 90)
    f = rand_dag(ne÷2, ne)
    sd = new_core_space()
    MC.space_add_all_sexpr!(sd.inner, f)
    MC.space_add_all_sexpr!(sd.inner, PROG)
    td = bench(()->MC.space_metta_calculus!(sd.inner, 50_000))
    nd = np3(sd)
    st = new_core_space()
    MC.space_add_all_sexpr!(st.inner, f)
    tt = bench(()->sc_execute!(st, PROG; opts=SCOptions(; max_steps=50_000)))
    nt = np3(st)
    sp = tt>0 ? round(td/tt; digits=2) : NaN
    println(
        "$ne | $(round(td;digits=3)) $(round(tt;digits=3)) $(sp)x | $nd $nt $(nd==nt ? "OK" : "MISMATCH")"
    )
end
