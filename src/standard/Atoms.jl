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
export Bindings,
    Binding, resolve, match_atoms, merge_bindings, add_var_binding, add_var_equality
export is_present, canonical_var

# ── Atom: a typed sum-type (Julia's faithful equivalent of hyperon's `enum Atom`) ──
abstract type Atom end

"Symbol — an id/concept. Two symbols with the same name are equal. (hyperon SymbolAtom)"
# name is a Julia `Symbol` — interned BY THE RUNTIME (the native analog of CeTTa's `sym_id`): `==` is a
# pointer compare (~10–20× over String memcmp) and `hash` is ~3× cheaper (the index Dict keys). Construct
# from a String via the interning ctor below; all `Sym("lit")` sites keep working unchanged.
struct Sym <: Atom
    name::Symbol
end
Sym(s::AbstractString) = Sym(Symbol(s))

"Variable — name + uniqueness id for hygiene/alpha-renaming. (hyperon VariableAtom)"
struct Var <: Atom
    name::String
    id::UInt64
end
Var(name::AbstractString) = Var(String(name), UInt64(0))   # id 0 = named, not yet made-unique

"Expression — typed children (NOT Vector{Any}). (hyperon ExpressionAtom)"
# `has_vars` is a CACHED bit (CeTTa's ATOM_FLAG_HAS_VARS, atom.h:52): does this subtree contain ANY Var?
# Computed bottom-up at construction (OR of children; children cache their own flag ⇒ O(arity) per node).
# Lets `subst`/`collect_vars` short-circuit a GROUND subtree in O(1) instead of recursing over the abstract
# `Atom` element type — that recursion is dynamic-dispatch-boxed (~32 B/node, AllocCheck-confirmed), which is
# the O(term-size)/step allocation on ground-heavy reduction. Derived from children ⇒ NOT part of ==/hash.
struct Expression <: Atom
    children::Vector{Atom}
    has_vars::Bool
    Expression(xs::Vector{Atom}) = new(xs, _any_has_vars(xs))
end
Expression(xs::Atom...) = Expression(collect(Atom, xs))
@inline _has_vars(a::Atom)::Bool =
    a isa Var ? true : (a isa Expression ? a.has_vars : false)
_any_has_vars(xs::Vector{Atom})::Bool = any(_has_vars, xs)

"Grounded — a typed host value. (hyperon Grounded(Box<dyn GroundedAtom>) / CeTTa typed union)"
struct Grounded{T} <: Atom
    value::T
end

# structural equality + hashing (so atoms work as Dict keys / in Sets)
Base.:(==)(a::Sym, b::Sym) = a.name == b.name
Base.:(==)(a::Var, b::Var) = a.name == b.name && a.id == b.id
Base.:(==)(a::Expression, b::Expression) = a.children == b.children
# strict Bool (`=== true`): `.value::Any`, so `a.value == b.value` can widen to `Union{Missing,Bool}`
# (a grounded atom wrapping `missing`), which throws in a boolean context (e.g. add_var_binding's
# `elseif prev == val`). Both references return a strict bool for grounded eq — hyperon `eq_gnd → bool`
# (hyperon-atom/src/lib.rs:414), CeTTa `atom_eq → bool` (atom.c:1603). `=== true` preserves == semantics for
# all normal values (NaN≠NaN, 0.0==-0.0 unchanged) and maps the missing/non-Bool case to `false`.
Base.:(==)(a::Grounded, b::Grounded) = (a.value == b.value) === true
Base.hash(a::Sym, h::UInt) = hash(a.name, hash(:Sym, h))
Base.hash(a::Var, h::UInt) = hash(a.id, hash(a.name, hash(:Var, h)))
Base.hash(a::Expression, h::UInt) = hash(a.children, hash(:Expression, h))
Base.hash(a::Grounded, h::UInt) = hash(a.value, hash(:Grounded, h))

# meta-types (metta.md §Elementary types)
metatype(::Sym) = :Symbol
metatype(::Var) = :Variable
metatype(::Expression) = :Expression
metatype(::Grounded) = :Grounded
isvar(a::Atom) = a isa Var

# readable printing
Base.show(io::IO, a::Sym) = print(io, a.name)
Base.show(io::IO, a::Var) = print(io, "\$", a.name, a.id == 0 ? "" : string("#", a.id))
Base.show(io::IO, a::Expression) = print(io, "(", join(string.(a.children), " "), ")")
Base.show(io::IO, a::Grounded) = print(io, a.value)

# ── Bindings ──────────────────────────────────────────────────────────────────
# FLAT min-rooted forwarding (CeTTa-style data-driven; src/match.h `Binding *entries`). An append-only
# `Vector{Binding}`: `Binding(var, val::Atom)` = `var` bound to a value; `Binding(var, val::Var)` = `var`
# forwards to a canonically-SMALLER root, representing the $x=$y equality class. The class VALUE lives on
# its root. Replaces the Dict{Var,Int}+slots union-find: `copy` is a flat array copy (the #1-alloc fix),
# equality is an append (no interior repoint), and `canonical_var` is a 1-hop walk (chains kept root-
# flattened by always forwarding the larger root → the smaller). Append-only ⇒ trail-ready (Step 3).
struct Binding
    var::Var
    val::Union{Atom, Var}
end
mutable struct Bindings
    entries::Vector{Binding}
    # 🔴 ROADMAP 7.B — THE ⊥ THIS DERIVATION CONSUMED, or `nothing`. WFS says `true ∧ undefined` is
    # UNDEFINED, but our conjunction encoding is `(let $c A B)`: when A yields a bottom, `unify` binds
    # it to `$c` and B's value is returned, so the undefinedness VANISHES. XSB gold program p31 is the
    # measured case — `q(A) :- p(A), eq(A,b)` with `p(b)` undefined answered TRUE.
    #
    # ⚠️ WHY A FIELD ON *BINDINGS* AND NOT AN AMBIENT REGISTER. The scope has to be PER DERIVATION.
    # Measured: `p :- para.` + `p :- True.` correctly yields `[undefined, True]` ⇒ TRUE, because
    # distinct derivations put distinct answers in one set. A register read at answer production would
    # mark BOTH and break that. `Bindings` is already the per-derivation channel — `finished_result`
    # carries `mb` along exactly the derivation that bound the ⊥.
    #
    # ⚠️ AND WHY `Atom`, NOT `DelayDNF`. `Delays.jl` is included long after this file; a typed DNF
    # field here would invert the layering. A WFSBottom atom already CARRIES its DNF, so the bottom
    # itself is the carrier and `Atom` is all this layer needs to know.
    delay::Union{Atom, Nothing}
end
Bindings() = Bindings(Binding[], nothing)
Base.copy(b::Bindings) = Bindings(copy(b.entries), b.delay)

# canonical (min id,name) representative of v's equality class: follow forwarding edges to the root.
function canonical_var(b::Bindings, v::Var)::Var
    cur = v
    while true
        nxt = nothing
        for e in b.entries
            if e.var === cur && e.val isa Var
                nxt = e.val::Var
                break
            end
        end
        nxt === nothing && return cur
        cur = nxt
    end
end

# is `v` present at all (bound OR in an equality class)? — distinct from `resolve === nothing`, which is
# also nothing for a value-less var merely equated to another (formal=actual). MUST check both ends: a var
# can appear as a forwarding SOURCE (`e.var`) or as the class ROOT, i.e. a forwarding TARGET (`e.val`).
is_present(b::Bindings, v::Var) = any(e -> e.var === v || e.val === v, b.entries)

"Resolve a variable to its bound value (or `nothing` if unbound / equality-only)."
function resolve(b::Bindings, v::Var)::Union{Atom, Nothing}
    r = canonical_var(b, v)                          # the class value lives on the root
    for e in b.entries
        if e.var === r && e.val isa Atom
            return e.val::Atom
        end
    end
    nothing
end

# metta.md §add_var_binding
# occurs check: does `v` appear anywhere inside `a`? (prevents the cyclic binding $v <- (… $v …))
function _occurs(v::Var, a::Atom)
    a isa Var && return a == v
    if a isa Expression
        @inbounds for c in a.children
            _occurs(v, c) && return true
        end
    end
    return false
end

function add_var_binding(b::Bindings, var::Var, val::Atom)::Vector{Bindings}
    prev = resolve(b, var)
    if prev === nothing
        _occurs(var, val) && return Bindings[]      # occurs check — reject (unify $v with (… $v …) fails)
        nb = copy(b)
        push!(nb.entries, Binding(canonical_var(nb, var), val))   # value on the root
        return [nb]
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

# metta.md §add_var_equality — append a root→root forwarding edge (no interior mutation)
function add_var_equality(b::Bindings, a::Var, c::Var)::Vector{Bindings}
    av, cv = resolve(b, a), resolve(b, c)
    if av === nothing || cv === nothing || av == cv
        nb = copy(b)
        r1 = canonical_var(nb, a)
        r2 = canonical_var(nb, c)
        if r1 !== r2
            (r2.id, r2.name) < (r1.id, r1.name) && ((r1, r2) = (r2, r1))   # r1 = smaller = new root
            push!(nb.entries, Binding(r2, r1))                              # r2 → r1 (larger → smaller)
            val = av !== nothing ? av : cv                                  # preserve the class value
            (val !== nothing && resolve(nb, r1) === nothing) &&
                push!(nb.entries, Binding(r1, val))
        end
        return [nb]
    else
        out = Bindings[]
        for m in match_atoms(av, cv)
            append!(out, merge_bindings(b, m))
        end
        return out
    end
end

# group right's vars by equality-class root (shared by the trail fast path + the branching fallback)
function _right_relations(right::Bindings)
    by_root = Dict{Var, Vector{Var}}()
    seen = Set{Var}()
    for e in right.entries
        for v in (e.val isa Var ? (e.var, e.val::Var) : (e.var,))
            v in seen && continue
            push!(seen, v)
            push!(get!(by_root, canonical_var(right, v), Var[]), v)
        end
    end
    by_root
end

# Append-only in-place extension `root <- val`. :ok (extended/no-op), :fail (occurs check),
# :fork (value conflict → caller must use the branching path). Appends only ⇒ trail-resettable.
function _extend_bind_inplace!(b::Bindings, root::Var, val::Atom)::Symbol
    prev = resolve(b, root)
    prev === nothing || return (prev == val ? :ok : :fork)
    _occurs(root, val) && return :fail
    push!(b.entries, Binding(canonical_var(b, root), val))
    :ok
end

# Append-only in-place equality root↔v. :ok, or :fork (both sides bound to conflicting values).
function _extend_eq_inplace!(b::Bindings, a::Var, c::Var)::Symbol
    av, cv = resolve(b, a), resolve(b, c)
    (av !== nothing && cv !== nothing && av != cv) && return :fork
    r1 = canonical_var(b, a)
    r2 = canonical_var(b, c)
    if r1 !== r2
        (r2.id, r2.name) < (r1.id, r1.name) && ((r1, r2) = (r2, r1))
        push!(b.entries, Binding(r2, r1))
        val = av !== nothing ? av : cv
        (val !== nothing && resolve(b, r1) === nothing) &&
            push!(b.entries, Binding(r1, val))
    end
    :ok
end

# fold `right`'s relations into `left` (metta.md §merge_bindings).
# TRAIL FAST PATH: fold deterministically by appending to `left` IN PLACE, copy the SURVIVOR once, then
# `resize!` `left` back to its checkpoint length — observationally PURE on `left` (append-only ⇒ the undo
# is O(1)), so the per-candidate copies collapse to one-per-surviving-merge. A relation that FORKS (value
# conflict needing match_atoms) bails to the branching path, which is the original copying fold.
function merge_bindings(left::Bindings, right::Bindings)::Vector{Bindings}
    by_root = _right_relations(right)
    checkpoint = length(left.entries)
    forked = false
    ok = true
    for (root, vars) in by_root
        for v in vars                              # equality relations within the class
            v === root && continue
            _extend_eq_inplace!(left, root, v) === :fork && (forked=true; break)
        end
        forked && break
        val = resolve(right, root)                 # assignment relation root <- val
        if val !== nothing
            s = _extend_bind_inplace!(left, root, val)
            s === :fail && (ok=false; break)
            s === :fork && (forked=true; break)
        end
    end
    if !forked
        if !ok
            resize!(left.entries, checkpoint)
            return Bindings[]
        end
        length(left.entries) == checkpoint && return Bindings[left]   # no-op merge — share left (no copy)
        result = Bindings[copy(left)]                                  # copy SURVIVOR only (left extended)
        resize!(left.entries, checkpoint)                             # O(1) undo — left restored
        return result
    end
    resize!(left.entries, checkpoint)                      # undo partial fast-path appends
    _merge_branching(left, right, by_root)                 # SLOW PATH (rare value-conflict fork)
end

# original copying fold — correct for the forking case (each add_var_* may yield 0/1/many results)
function _merge_branching(left::Bindings, right::Bindings, by_root)::Vector{Bindings}
    result = [left]
    for (root, vars) in by_root
        for v in vars
            v === root && continue
            result = _flat([add_var_equality(r, root, v) for r in result])
        end
        val = resolve(right, root)
        if val !== nothing
            result = _flat([add_var_binding(r, root, val) for r in result])
        end
    end
    result
end
_flat(xss) = (
    out=Bindings[];
    for xs in xss
        append!(out, xs)
    end;
    out
)

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
    elseif ml === :Expression && mr === :Expression &&
        length(left.children) == length(right.children)
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
