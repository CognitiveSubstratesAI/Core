#!/usr/bin/env julia
# JET (@report_opt: runtime dispatch / optimization failures) + AllocCheck (static alloc sites)
# on the hot binding/reduce functions. Run with the Core project + global env stacked:
#   JULIA_LOAD_PATH="@:@v#.#:@stdlib" julia --project=. tools/jet_alloc_probe.jl
using MeTTaCore, JET, AllocCheck
const SM = MeTTaCore.Eval
const SA = MeTTaCore.StandardMeTTa
using .SA: Atom, Sym, Var, Expression, Bindings

b   = Bindings()
ax  = Expression(Atom[Sym("f"), Var("x"), Sym("g")])
v   = Var("x"); val = Sym("v")
sp  = SM.Space(); SM.load_core_stdlib!(sp)
consop = Sym("cons-atom")

cases = [
    (SM.subst,           (ax, b),         "subst(Expr,Bindings)"),
    (SM.merge_bindings,  (b, b),          "merge_bindings"),
    (SM.add_var_binding, (b, v, val),     "add_var_binding"),
    (SM.match_atoms,     (ax, ax),        "match_atoms(Expr,Expr)"),
    (SM.atom_types,      (consop, sp),    "atom_types(cons-atom)"),
]

println("######## JET @report_opt — runtime dispatch / opt failures ########")
for (f, args, lbl) in cases
    println("\n=== $lbl ===")
    try
        r = JET.report_opt(f, Tuple{map(typeof,args)...})
        io = IOBuffer(); show(io, r); s = String(take!(io))
        n = length(collect(eachmatch(r"runtime dispatch", s)))
        println("runtime-dispatch reports: ", n)
        for ln in split(s,'\n'); occursin("runtime dispatch", ln) && println("   ", strip(ln)); end
    catch e; println("ERR ", first(sprint(showerror,e),200)) end
end

println("\n######## AllocCheck — static allocation sites ########")
for (f, args, lbl) in cases
    println("\n=== $lbl ===")
    try
        allocs = check_allocs(f, Tuple{map(typeof,args)...})
        println(length(allocs), " allocation site(s)")
        seen = Set{String}()
        for a in allocs
            loc = isempty(a.backtrace) ? "?" : string(a.backtrace[1])
            loc in seen && continue; push!(seen, loc)
            println("   ", loc)
            length(seen) >= 8 && break
        end
    catch e; println("ERR ", first(sprint(showerror,e),200)) end
end
