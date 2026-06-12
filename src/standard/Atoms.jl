## Standard MeTTa — typed atom model + bindings + matcher.
##
## Faithful port of the reference representations (NO `Any` in the core):
##   - hyperon-experimental: `enum Atom { Symbol, Expression, Variable, Grounded }`
##     (hyperon-atom/src/lib.rs:827) + `struct Bindings { binding_by_var, bindings }`
##     (hyperon-atom/src/matcher.rs:141) — variables share slots, which is how it
##     represents the `$x = $y` variable-equality relation.
##   - CeTTa: tagged union `struct Atom { AtomKind kind; ... }` with a typed grounded
##     union `GroundedKind` (src/atom.h:44).
## Matching/binding algorithm follows docs/metta.md §Matching (match_atoms /
## merge_bindings / add_var_binding / add_var_equality) verbatim.
##
## This module is standalone — it does NOT touch eval_metta / eval_nd.

module StandardMeTTa

export Atom, Sym, Var, Expression, Grounded, metatype, isvar
export Bindings, resolve, match_atoms, merge_bindings, add_var_binding, add_var_equality

# ── Atom: a typed sum-type (Julia's faithful equivalent of hyperon's `enum Atom`) ──
abstract type Atom end

"Symbol — an id/concept. Two symbols with the same name are equal. (hyperon SymbolAtom)"
struct Sym <: Atom
    name::String
end

"Variable — name + uniqueness id for hygiene/alpha-renaming. (hyperon VariableAtom)"
struct Var <: Atom
    name::String
    id::UInt64
end
Var(name::AbstractString) = Var(String(name), UInt64(0))   # id 0 = named, not yet made-unique

"Expression — typed children (NOT Vector{Any}). (hyperon ExpressionAtom)"
struct Expression <: Atom
    children::Vector{Atom}
end
Expression(xs::Atom...) = Expression(collect(Atom, xs))

"Grounded — a typed host value. (hyperon Grounded(Box<dyn GroundedAtom>) / CeTTa typed union)"
struct Grounded{T} <: Atom
    value::T
end

# structural equality + hashing (so atoms work as Dict keys / in Sets)
Base.:(==)(a::Sym, b::Sym)           = a.name == b.name
Base.:(==)(a::Var, b::Var)           = a.name == b.name && a.id == b.id
Base.:(==)(a::Expression, b::Expression) = a.children == b.children
Base.:(==)(a::Grounded, b::Grounded) = a.value == b.value
Base.hash(a::Sym, h::UInt)      = hash(a.name, hash(:Sym, h))
Base.hash(a::Var, h::UInt)      = hash(a.id, hash(a.name, hash(:Var, h)))
Base.hash(a::Expression, h::UInt) = hash(a.children, hash(:Expression, h))
Base.hash(a::Grounded, h::UInt) = hash(a.value, hash(:Grounded, h))

# meta-types (metta.md §Elementary types)
metatype(::Sym)      = :Symbol
metatype(::Var)      = :Variable
metatype(::Expression) = :Expression
metatype(::Grounded) = :Grounded
isvar(a::Atom) = a isa Var

# readable printing
Base.show(io::IO, a::Sym)  = print(io, a.name)
Base.show(io::IO, a::Var)  = print(io, "\$", a.name, a.id == 0 ? "" : string("#", a.id))
Base.show(io::IO, a::Expression) = print(io, "(", join(string.(a.children), " "), ")")
Base.show(io::IO, a::Grounded) = print(io, a.value)

# ── Bindings ──────────────────────────────────────────────────────────────────
# Variables map to shared integer slots; a slot holds an optional bound value.
# Two variables in the SAME slot are equal ($x = $y) — faithful to hyperon's
# `binding_by_var: HashMap<VariableAtom, usize>` + `bindings: HoleyVec<Binding>`.
mutable struct Bindings
    var_to_slot::Dict{Var,Int}
    slots::Vector{Union{Atom,Nothing}}   # value of slot, or nothing = equality-class only
end
Bindings() = Bindings(Dict{Var,Int}(), Union{Atom,Nothing}[])
Base.copy(b::Bindings) = Bindings(copy(b.var_to_slot), copy(b.slots))

"Resolve a variable to its bound value (or `nothing` if unbound)."
resolve(b::Bindings, v::Var) = haskey(b.var_to_slot, v) ? b.slots[b.var_to_slot[v]] : nothing

# give `var` a slot with value `val` (var was unbound, or its slot had no value)
function _bind_value!(b::Bindings, var::Var, val::Atom)
    if haskey(b.var_to_slot, var)
        b.slots[b.var_to_slot[var]] = val
    else
        push!(b.slots, val)
        b.var_to_slot[var] = length(b.slots)
    end
    b
end

# union the slots of `a` and `c` (they become equal); keep the non-nothing value if any
function _union_slots!(b::Bindings, a::Var, c::Var)
    sa = get(b.var_to_slot, a, 0)
    sc = get(b.var_to_slot, c, 0)
    if sa == 0 && sc == 0
        push!(b.slots, nothing); s = length(b.slots)
        b.var_to_slot[a] = s; b.var_to_slot[c] = s
    elseif sc == 0
        b.var_to_slot[c] = sa
    elseif sa == 0
        b.var_to_slot[a] = sc
    elseif sa != sc
        val = b.slots[sa] !== nothing ? b.slots[sa] : b.slots[sc]
        b.slots[sa] = val
        for (v, s) in b.var_to_slot          # repoint every var in slot sc → sa
            s == sc && (b.var_to_slot[v] = sa)
        end
    end
    b
end

# metta.md §add_var_binding
# occurs check: does `v` appear anywhere inside `a`? (prevents the cyclic binding $v <- (… $v …))
_occurs(v::Var, a::Atom) = a isa Var ? a == v : (a isa Expression && any(c -> _occurs(v, c), a.children))

function add_var_binding(b::Bindings, var::Var, val::Atom)::Vector{Bindings}
    prev = resolve(b, var)
    if prev === nothing
        _occurs(var, val) && return Bindings[]      # occurs check — reject (unify $v with (… $v …) fails)
        return [_bind_value!(copy(b), var, val)]
    elseif prev == val
        return [b]
    else
        out = Bindings[]
        for m in match_atoms(prev, val)
            append!(out, merge_bindings(b, m))
        end
        return out
    end
end

# metta.md §add_var_equality
function add_var_equality(b::Bindings, a::Var, c::Var)::Vector{Bindings}
    av, cv = resolve(b, a), resolve(b, c)
    if av === nothing || cv === nothing || av == cv
        return [_union_slots!(copy(b), a, c)]
    else
        out = Bindings[]
        for m in match_atoms(av, cv)
            append!(out, merge_bindings(b, m))
        end
        return out
    end
end

# enumerate `right`'s relations and fold them into `left` (metta.md §merge_bindings)
function merge_bindings(left::Bindings, right::Bindings)::Vector{Bindings}
    # group right's variables by slot
    by_slot = Dict{Int,Vector{Var}}()
    for (v, s) in right.var_to_slot
        push!(get!(by_slot, s, Var[]), v)
    end
    result = [left]
    for (s, vars) in by_slot
        v1 = vars[1]
        for v in vars[2:end]                       # equality relations $v1 = $v
            result = _flat([add_var_equality(r, v1, v) for r in result])
        end
        val = right.slots[s]
        if val !== nothing                          # assignment relation $v1 <- val
            result = _flat([add_var_binding(r, v1, val) for r in result])
        end
    end
    return result
end
_flat(xss) = (out = Bindings[]; for xs in xss; append!(out, xs); end; out)

# metta.md §match_atoms — two-sided unification over meta-types
function match_atoms(left::Atom, right::Atom)::Vector{Bindings}
    ml, mr = metatype(left), metatype(right)
    if ml === :Symbol && mr === :Symbol
        return left == right ? [Bindings()] : Bindings[]
    elseif ml === :Variable && mr === :Variable
        return add_var_equality(Bindings(), left, right)
    elseif ml === :Variable
        return add_var_binding(Bindings(), left, right)
    elseif mr === :Variable
        return add_var_binding(Bindings(), right, left)
    elseif ml === :Expression && mr === :Expression && length(left.children) == length(right.children)
        result = [Bindings()]
        for i in eachindex(left.children)
            sub = match_atoms(left.children[i], right.children[i])
            result = _flat([merge_bindings(a, b) for a in result for b in sub])
            isempty(result) && return result
        end
        return result
    elseif ml === :Grounded && mr === :Grounded
        return left == right ? [Bindings()] : Bindings[]   # default: value equality
    else
        return Bindings[]
    end
end

end # module
