# src/eval/EvalND.jl
#
# OutcomeSet evaluator — the nondeterministic, binding-carrying core that the reference MeTTa
# interpreters all use (hyperon-experimental's `interpret`, PeTTa's Prolog backtracking, CeTTa's
# `OutcomeSet`). Core's legacy `eval_metta` returns a single value with no bindings, which fails
# MeTTa's defining semantic — see docs/CONFORMANCE_AUDIT.md and docs/E1_SCOPE.md §2c.
#
# Model (CeTTa's `Outcome{atom, env}` / `OutcomeSet`): `eval_nd(expr, space, env)` returns a
# `Vector{Tuple{value, bindings}}` — every result paired with the bindings that produced it.
# `eval_nd_results` drops the bindings at the top (CeTTa's `ResultSet`).
#
# STATUS: foundation. Proven on the conformance fixtures (croaks-fanout, (f (superpose x)) fanout,
# the frog/green tutorial — binding propagation through `if`). NOT yet wired into `eval_metta`, and
# does NOT yet cover every special form (let/let*/match/collapse/case/chain/…) or variable HYGIENE
# (alpha-renaming a rule's vars per application). Those are the next steps before switch-over.

const _NDEnv = Dict{Symbol, Any}
const _NDOut = Tuple{Any, _NDEnv}

_nd_isvar(x) = x isa Symbol && (startswith(string(x), "\$") || startswith(string(x), "__var_"))
_nd_vname(x) = (s = string(x); startswith(s, "\$") ? Symbol(s[2:end]) :
                               startswith(s, "__var_") ? Symbol(s[7:end]) : Symbol(s))

# substitute bound vars in a term
_nd_subst(t, e) = _nd_isvar(t) ? (haskey(e, _nd_vname(t)) ? e[_nd_vname(t)] : t) :
                  (t isa Vector ? Any[_nd_subst(x, e) for x in t] : t)

# unify a against b extending env e; return extended env or nothing
function _nd_uni(a, b, e)
    _nd_isvar(a) && haskey(e, _nd_vname(a)) && (a = e[_nd_vname(a)])
    _nd_isvar(b) && haskey(e, _nd_vname(b)) && (b = e[_nd_vname(b)])
    if _nd_isvar(a)
        e2 = copy(e); e2[_nd_vname(a)] = b; e2
    elseif _nd_isvar(b)
        e2 = copy(e); e2[_nd_vname(b)] = a; e2
    elseif a isa Vector && b isa Vector
        length(a) == length(b) || return nothing
        for (x, y) in zip(a, b); e = _nd_uni(x, y, e); e === nothing && return nothing; end; e
    else
        isequal(a, b) ? e : nothing
    end
end
function _nd_unify_list(ps, vs, e)
    for (p, v) in zip(ps, vs); e = _nd_uni(p, v, e); e === nothing && return nothing; end; e
end
# merge two envs, keeping only consistent bindings (returns nothing on conflict)
function _nd_merge(e1, e2)
    m = copy(e1)
    for (k, v) in e2
        haskey(m, k) ? (u = _nd_uni(m[k], v, m); u === nothing && return nothing; m = u) : (m[k] = v)
    end; m
end
# cartesian product of argument outcome-sets, threading consistent bindings (the join over shared vars)
function _nd_cart(argsets, env0)
    combos = Tuple{Vector{Any}, _NDEnv}[(Any[], env0)]
    for aset in argsets
        nw = Tuple{Vector{Any}, _NDEnv}[]
        for (vals, e) in combos, (v, ve) in aset
            m = _nd_merge(e, ve); m === nothing && continue
            push!(nw, (vcat(vals, [v]), m))
        end
        combos = nw
    end
    combos
end
function _nd_grounded(head, vals)
    raw = try GROUNDED_REGISTRY[string(head)](to_sexpr_atom.(vals)) catch; nothing end
    (raw === nothing || raw == "NotReducible" || raw === :NotReducible) && return vcat([head], vals)
    raw isa String ? from_sexpr(raw) : raw isa Vector{String} ? from_sexpr.(raw) : raw
end
_nd_true(v)  = v === true  || v === :True  || v == Symbol("True")
_nd_false(v) = v === false || v === :False || v == Symbol("False")

# variable hygiene: alpha-rename a term's variables to fresh names, sharing one remap across a rule's
# params + body so each application gets independent variables (required for nested same-name recursion).
const _ND_GENSYM = Ref(0)
_nd_fresh(t, rm = Dict{Symbol, Symbol}()) =
    _nd_isvar(t) ? (n = _nd_vname(t); haskey(rm, n) || (rm[n] = Symbol("_g", (_ND_GENSYM[] += 1))); Symbol("\$", rm[n])) :
    (t isa Vector ? Any[_nd_fresh(x, rm) for x in t] : t)

# Special forms the legacy eval_metta implements that eval_nd does NOT (yet) — delegated to eval_metta
# as a single outcome so eval_nd is a COMPLETE evaluator (prerequisite for the wire-in). Nondeterminism
# still flows through the forms eval_nd handles itself; these are evaluated deterministically for now.
const _ND_LEGACY_FORMS = Set(Symbol.([
    "function", "return", "eval", "evalc", "unquote", "noreduce-eq", "noeval", "do", "begin",
    "import!", "git-import!", "bind!", "with-space", "add-atom", "remove-atom",
    "decimate-importance!", "normalize-attention!", "exec", "get-atoms", "new-space",
    "get-type-space", "get-type", "type-cast", "add-reduct", "for-each-in-atom",
    "foldl-atom", "map-atom", "filter-atom"]))

"""
    eval_nd(expr, space, env=Dict()) -> Vector{Tuple{value, bindings}}

Nondeterministic, binding-carrying evaluation (CeTTa `OutcomeSet`). Each outcome is a value paired
with the bindings that produced it. Fans out over superpose, over facts/rules that unify, and through
`if`; threads bindings via consistent merge across arguments (the join on shared variables).
"""
function eval_nd(@nospecialize(x), space::CoreSpace, e::_NDEnv = _NDEnv())
    _nd_isvar(x) && return haskey(e, _nd_vname(x)) ? _NDOut[(e[_nd_vname(x)], e)] : _NDOut[(x, e)]
    (x isa Number || x isa Bool) && return _NDOut[(x, e)]
    if x isa Symbol
        for r in core_rules(space, x); isempty(r[1]) && return eval_nd(r[2], space, e); end
        return _NDOut[(x, e)]
    end
    (!(x isa Vector) || isempty(x)) && return _NDOut[(x, e)]
    h = x[1]; a = x[2:end]
    (h === :empty || h === Symbol("empty")) && return _NDOut[]
    h === :quote && return _NDOut[(length(a) >= 1 ? a[1] : nothing, e)]          # unevaluated
    (h === :Error || h === Symbol("Error")) && return _NDOut[(vcat([Symbol("Error")], a), e)]
    if h === :superpose
        o = _NDOut[]
        for el in (isempty(a) ? [] : (a[1] isa Vector ? a[1] : [a[1]])); append!(o, eval_nd(el, space, e)); end
        return o
    end
    if h === :if && length(a) >= 3
        o = _NDOut[]
        for (cv, ce) in eval_nd(a[1], space, e)
            br = _nd_true(cv) ? a[2] : _nd_false(cv) ? a[3] : nothing
            br === nothing && continue
            append!(o, eval_nd(_nd_subst(br, ce), space, ce))
        end
        return o
    end
    if h === :collapse && length(a) >= 1
        # gather the whole outcome set into ONE tuple result (CeTTa: stream → list)
        return _NDOut[(Any[v for (v, _) in eval_nd(a[1], space, e)], e)]
    end
    if h === :let && length(a) >= 3
        # (let pat val body): for each outcome of val, unify pat against it, eval body under the binding
        o = _NDOut[]
        for (vv, ve) in eval_nd(a[2], space, e)
            e2 = _nd_uni(_nd_subst(a[1], ve), vv, ve); e2 === nothing && continue
            append!(o, eval_nd(_nd_subst(a[3], e2), space, e2))
        end
        return o
    end
    if h === :chain && length(a) >= 3
        # (chain val var body): eval val, bind var to each outcome, eval body
        o = _NDOut[]
        for (vv, ve) in eval_nd(_nd_subst(a[1], e), space, e)
            e2 = _nd_uni(_nd_subst(a[2], ve), vv, ve); e2 === nothing && continue
            append!(o, eval_nd(_nd_subst(a[3], e2), space, e2))
        end
        return o
    end
    if h === :unify && length(a) >= 4
        # (unify a b then else): if a unifies with b, eval `then` under the bindings, else `else`
        e2 = _nd_uni(_nd_subst(a[1], e), _nd_subst(a[2], e), e)
        return e2 === nothing ? eval_nd(_nd_subst(a[4], e), space, e) : eval_nd(_nd_subst(a[3], e2), space, e2)
    end
    if h === Symbol("let*") && length(a) >= 2
        # (let* ((p1 v1) (p2 v2) …) body): sequential bindings, fanning out at each step
        bs = a[1]; bd = a[2]
        go(i, env) = i > length(bs) ? eval_nd(_nd_subst(bd, env), space, env) :
            (o = _NDOut[]; for (vv, ve) in eval_nd(_nd_subst(bs[i][2], env), space, env)
                 e2 = _nd_uni(_nd_subst(bs[i][1], ve), vv, ve); e2 === nothing && continue
                 append!(o, go(i + 1, e2)); end; o)
        return go(1, e)
    end
    if (h === :case || h === :switch) && length(a) >= 2
        # (case expr ((pat1 body1) …)): per outcome of expr, eval the first matching clause's body
        cls = a[2]; o = _NDOut[]
        for (vv, ve) in eval_nd(_nd_subst(a[1], e), space, e)
            for cl in cls
                (cl isa Vector && length(cl) >= 2) || continue
                e2 = _nd_uni(_nd_subst(cl[1], ve), vv, ve)
                if e2 !== nothing; append!(o, eval_nd(_nd_subst(cl[2], e2), space, e2)); break; end
            end
        end
        return o
    end
    if (h === :match || h === Symbol("match")) && length(a) >= 3
        # (match <space> pat tpl): for each space atom unifying with pat, eval tpl under the bindings.
        # <space> currently treated as the current space (&self); named-space lookup is future work.
        o = _NDOut[]; pat = _nd_subst(a[2], e)
        for cand in core_match(space, pat)
            e2 = _nd_uni(pat, cand, e); e2 === nothing && continue
            append!(o, eval_nd(_nd_subst(a[3], e2), space, e2))
        end
        return o
    end
    # legacy special forms eval_nd doesn't implement: delegate the whole bound expr to eval_metta
    # as a single outcome (keeps eval_nd complete; nondeterminism flows through the forms above).
    if h isa Symbol && h in _ND_LEGACY_FORMS
        return _NDOut[(eval_metta(_nd_subst(vcat([h], a), e), space), e)]
    end
    # function application: fan out over args (consistent merge), then over all unifying rules
    o = _NDOut[]
    argsets = [eval_nd(_nd_subst(ai, e), space, e) for ai in a]
    for (vals, ee) in _nd_cart(argsets, e)
        if h isa Symbol && is_grounded(string(h))
            push!(o, (_nd_grounded(h, vals), ee))
        else
            matched = false
            for (ps, bd) in core_rules(space, h)
                length(ps) == length(vals) || continue
                rm = Dict{Symbol, Symbol}()                       # hygiene: fresh vars per application
                ps2 = Any[_nd_fresh(p, rm) for p in ps]
                bd2 = _nd_fresh(bd, rm)
                e2 = _nd_unify_list(ps2, vals, ee); e2 === nothing && continue
                matched = true
                append!(o, eval_nd(_nd_subst(bd2, e2), space, e2))
            end
            # unreduced: substitute the head too (a var head may have been bound by evaluating the
            # other elements — e.g. `($x (green $x))` → `(Fritz T)`).
            matched || push!(o, (vcat([_nd_subst(h, ee)], vals), ee))
        end
    end
    o
end

"""    eval_nd_results(expr, space) -> Vector{Any}

Top-level nondeterministic eval: the result values with bindings dropped (CeTTa `ResultSet`).
"""
eval_nd_results(@nospecialize(expr), space::CoreSpace = default_space()) =
    Any[v for (v, _) in eval_nd(expr, space)]
