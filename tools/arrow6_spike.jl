using MeTTaCore
const MC = MeTTaCore
const IV=MC.Eval; const IF=MC.CompilerFrontend; const IA=MC.CompilerANormal; const IE=MC.CompilerEmit
ask(l,f) = try; print(l," -> "); println(f()); catch e; println(l," -> RAISED: ",first(replace(sprint(showerror,e),"\n"=>" | "),240)); end
_parse(sp,t) = begin
    toks=IV.tokenize(t); i=Ref(1); out=MC.StandardMeTTa.Atom[]
    while i[] <= length(toks); toks[i[]]=="!" && (i[]+=1); i[]>length(toks) && break
        push!(out, IV.parse_from(toks,i,sp.tokens)); end
    out
end
println("="^72); println("STEP 0 — does Emit.jl's MM2 actually RUN on a CoreSpace?"); println("="^72)
SRC = "(= (inc \$n) (+ \$n 1))\n"
sp = IV.Space(); IV.load_core_stdlib!(sp)
cls = nothing; r = nothing
ask("1 A-normalize", () -> (global cls = IA.translate_program(IF.lower_program(_parse(sp,SRC))); "clauses=$(length(cls))"))
ask("2 emit_program", () -> (global r = IE.emit_program(cls); "fields=$(propertynames(r))  emitted=$(r.emitted)"))
ask("2b the emitted MM2", () -> begin
    for f in propertynames(r); v=getproperty(r,f); v isa AbstractVector{<:AbstractString} && return join(v,"\n     "); end
    "no string-vector field: $(propertynames(r))"
end)
ask("3 run on CoreSpace", () -> begin
    cs = MC.new_core_space()
    rules = String[]
    for f in propertynames(r); v=getproperty(r,f); v isa AbstractVector{<:AbstractString} && (rules=v; break); end
    # ⚠️ exec text goes in via MORK's OWN ingestion, not load_metta!/core_add! — that is how the
    # working (~>) lane does it (MeTTaIL.jl:153). core_add! does not preserve MORK pattern variables.
    for rule in rules; MC.space_add_all_sexpr!(cs.inner, rule); end
    MC.space_add_all_sexpr!(cs.inner, "(inc 41)")
    n = MC.core_calculus!(cs, 1000)
    "steps=$n  atoms=$([string(a) for a in MC.core_atoms(cs)])"
end)
println("\nREAD: 42 in the atoms => Emit.jl's output RUNS on MORK; the wire is real work.")
