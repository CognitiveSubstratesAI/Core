# Type-stability probe (perf-tips §"type stability"): @code_warntype the hot binding/reduce
# functions; flag instabilities (Any / Core.Box / wide Union) that force boxing + allocation.
using MeTTaCore, InteractiveUtils
const SM = MeTTaCore.Eval
const SA = MeTTaCore.StandardMeTTa
using .SA: Atom, Sym, Var, Expression, Bindings

probe(f, args, label) = begin
    io = IOBuffer()
    try
        code_warntype(io, f, Tuple{map(typeof, args)...})
    catch e
        print(io, "ERR $e")
    end
    s = String(take!(io))
    # count instability markers
    anys = count(c -> c == "::Any", split(s))
    boxes = occursin("Box", s) ? count(_->true, findall("Box", s)) : 0
    unions = length(findall("Union{", s))
    println(
        "── $label : ::Any=$(length(collect(eachmatch(r"::Any\b", s))))  Box=$boxes  Union{=$unions"
    )
    for ln in split(s, '\n')
        (occursin("::Any", ln) || occursin("Box", ln)) && println("    ", strip(ln))
    end
end

b = Bindings()
ax = Expression(Atom[Sym("f"), Var("x"), Sym("g")])
v = Var("x");
val = Sym("v")
probe(SM.subst, (ax, b), "subst(Expr, Bindings)")
probe(SM.add_var_binding, (b, v, val), "add_var_binding(Bindings, Var, Sym)")
probe(SM.merge_bindings, (b, b), "merge_bindings(Bindings, Bindings)")
probe(SM.match_atoms, (ax, ax), "match_atoms(Expr, Expr)")
probe(SM.collect_vars, (ax,), "collect_vars(Expr)")
println("\n=== Bindings field types (perf-tips: concrete containers?) ===")
println("  var_to_slot :: ", fieldtype(Bindings, :var_to_slot))
println(
    "  slots       :: ",
    fieldtype(Bindings, :slots),
    "   (isconcretetype: ",
    isconcretetype(fieldtype(Bindings, :slots)),
    ")"
)
println(
    "  Expression.children :: ",
    fieldtype(Expression, :children),
    "   (eltype concrete: ",
    isconcretetype(eltype(fieldtype(Expression, :children))),
    ")"
)
