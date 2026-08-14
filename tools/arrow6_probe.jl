# arrow6_probe2.jl — a FALSIFIABLE probe for arrow 6 (MeTTa-IL -> MORK/PathMap).
#
# The old evidence was "mc_run's :direct lane DEFERS (fib 2)" — mc_run was DELETED 2026-08-14 with
# the MeTTa->MM2 arrow, so that sentence can no longer be re-run. This replaces it.
#
# EVERY question is independently guarded: a probe that aborts at Q1 tells you one thing, a probe
# that answers all four tells you WHERE the arrow breaks. That distinction is the whole point.
using MeTTaCore
const MC = MeTTaCore

ask(label, f) = try
    print(label, " -> "); println(f())
catch e
    println(label, " -> 🔴 RAISED: ", first(replace(sprint(showerror, e), "\n" => " | "), 260))
end

println("="^78); println("ARROW 6 PROBE — MeTTa-IL -> MORK/PathMap"); println("="^78)

PROG  = "(= (inc \$n) (+ \$n 1))"
QUERY = "!(inc 41)"
println("program: ", PROG, "    query: ", QUERY)

sp = MC.Eval.Space(); MC.Eval.load_core_stdlib!(sp)
il = MC.compile_definition(sp, PROG)

println("\n-- arrows 1-4 : MeTTa -> IR -> A-normal -> MeTTa-IL --")
ask("Q1  compile_definition", () -> il === nothing ? "DECLINED" :
    "OK  atoms=$(length(il.atoms))  clauses=$(length(il.clauses))  wire=$(repr(il.wire))")
ask("Q1b IL atom", () -> il === nothing ? "n/a" : string(first(il.atoms)))

println("\n-- arrow 5 (CONTROL — must stay green, else the probe proves nothing) --")
ask("Q2  compile_run on Eval.Space", () -> begin
    r = MC.compile_run(PROG * "\n" * QUERY)
    "answers=$(r.answers)  compiled=$(r.compiled)  fell_back=$(r.fell_back)"
end)

println("\n-- arrow 6 : the same IL against a MORK-backed CoreSpace --")
cs = MC.new_core_space()
ask("Q3  core_add!(cs, IL atoms)", () -> begin
    n0 = length(MC.core_atoms(cs))
    for a in il.atoms; MC.core_add!(cs, a); end
    n1 = length(MC.core_atoms(cs))
    "trie atoms $n0 -> $n1" * (n1 > n0 ? "   THE STORE HALF WORKS" : "   NOTHING LANDED")
end)
ask("Q4  RETRIEVAL core_match", () -> begin
    hits = MC.core_match(cs, MC.parse_metta("(= (inc \$n) \$b)")[1])
    "hits=$(length(hits))" * (isempty(hits) ? "" : "   first=$(first(hits))")
end)
ask("Q5  EVALUATION load_metta!(cs, query)", () -> string(MC.load_metta!(cs, QUERY)))

println("\n-- does the DECLINE the ledger asserts still hold? --")
ask("Q6  space_ledger", () -> begin
    led = MC.space_ledger()
    string(led)
end)

println("\n", "="^78)
println("READ: Q1/Q2 green + Q3/Q4 green + Q5 RAISED  => arrow 6 is a ROUTING gap, not a store gap.")
println("      Q5 returning [42]                      => arrow 6 is ROUTED (update the ledger).")
println("="^78)
