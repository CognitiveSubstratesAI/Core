using MeTTaCore
const MC = MeTTaCore
# `String(::Atom)` does not exist — `string(::Atom)` does. That MethodError is what made the previous
# harness report MATCH=0 DIFF=8 while measuring nothing: the ORACLE threw on every row.
norm(v) = sort(String[strip(string(x)) for x in v])

CASES = [
 ("arith",        "(= (inc \$n) (+ \$n 1))\n!(inc 41)\n"),
 ("two args",     "(= (dbl \$n) (+ \$n \$n))\n!(dbl 21)\n"),
 ("identity",     "(= (idq \$x) \$x)\n!(idq 7)\n"),
 ("nested arith", "(= (f \$n) (* (+ \$n 1) 2))\n!(f 20)\n"),
 ("chained call", "(= (g \$x) (+ \$x 1))\n(= (h \$x) (g \$x))\n!(h 41)\n"),
 ("multi-clause", "(= (c 1) a)\n(= (c 1) b)\n!(c 1)\n"),
 ("no rule",      "!(nope 3)\n"),
 ("fact only",    "(edge a b)\n!(edge a b)\n"),
]

ok = 0; diff = 0
rows = Tuple{String,Vector{String},Vector{String},Vector{String},String}[]
for (l, src) in CASES
    interp = try
        sp = MC.Eval.Space(); MC.Eval.load_core_stdlib!(sp)
        norm(MC.Eval.load_metta!(sp, src))
    catch e; String["ORACLE-ERR:" * first(sprint(showerror, e), 30)]; end
    ev = try
        r = MC.compile_run(src)
        isempty(r.answers) ? String[] : norm(r.answers[end][2])
    catch e; String["ERR:" * first(sprint(showerror, e), 30)]; end
    mk = try
        r = MC.compile_run(src; backend = :mork)
        isempty(r.answers) ? String[] : norm(r.answers[end][2])
    catch e; String["ERR:" * first(sprint(showerror, e), 30)]; end
    v = (interp == mk) ? "MATCH" : "DIFF"
    v == "MATCH" ? (global ok += 1) : (global diff += 1)
    push!(rows, (l, interp, ev, mk, v))
end

println("="^100)
println(rpad("CASE",14), rpad("INTERPRETER",22), rpad(":eval (arrow 5)",22), rpad(":mork (ARROW 6)",22), "vs INTERP")
println("="^100)
for (l,i,e,m,v) in rows
    println(rpad(l,14), rpad(string(i),22), rpad(string(e),22), rpad(string(m),22), v)
end
println("="^100)
println("ARROW 6 vs INTERPRETER:  MATCH=$ok  DIFF=$diff  of $(length(CASES))")
println("\nA DIFF is not automatically a bug — a shape Emit.jl DECLINES has no compiled rule, so the")
println("query is NotReducible and returns itself. Compare the :eval column to tell decline from defect.")
