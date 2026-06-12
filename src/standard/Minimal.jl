## Standard MeTTa — Minimal instruction set, as a continuation-passing stack machine.
##
## FAITHFUL port of hyperon-experimental's interpreter.rs (the actual handler functions,
## not the prose spec): the execution is a stack of frames, each frame carrying an atom,
## its variables, a link to the previous frame, and a `ret` continuation invoked when the
## frame it pushed finishes. `interpret` loops over the plan (a list of (Frame, Bindings))
## until frames are finished with no previous frame = final results.
##   - interpret_stack  ← interpreter.rs:374
##   - eval / eval_impl ← :492 / :504   (query = (= atom $X) ← :604)
##   - chain            ← :687  (chain_ret :675)
##   - function/return  ← function_to_stack :704 / function_ret :723
##   - unify            ← :809
##   - cons/decons      ← :858 / :843
##   - collapse/superpose-bind ← :746 / :893
##
## Standalone — does NOT touch eval_metta / eval_nd. Built on the typed StandardMeTTa atoms.

module Minimal

include("Atoms.jl")
using .StandardMeTTa

export interpret, bare_eval, Space, add_atom!, Operation, PLUS, MINUS, LT, is_executable
export metta_run, metta_results

# instruction symbols
const EVAL = Sym("eval"); const EVALC = Sym("evalc"); const CHAIN = Sym("chain")
const FUNCTION = Sym("function"); const RETURN = Sym("return"); const UNIFY = Sym("unify")
const CONS = Sym("cons-atom"); const DECONS = Sym("decons-atom")
const COLLAPSE_BIND = Sym("collapse-bind"); const SUPERPOSE_BIND = Sym("superpose-bind")
const EMPTY = Sym("Empty"); const NOT_REDUCIBLE = Sym("NotReducible"); const ERROR = Sym("Error")
const MINIMAL_OPS = Set(String[ "eval","evalc","chain","function","unify",
                                 "cons-atom","decons-atom","collapse-bind","superpose-bind" ])

# ── helpers ───────────────────────────────────────────────────────────────────
head_name(a::Atom) = (a isa Expression && !isempty(a.children) && a.children[1] isa Sym) ?
                     (a.children[1]::Sym).name : ""
is_minimal_op(a::Atom) = head_name(a) in MINIMAL_OPS
args(a::Expression) = a.children[2:end]

error_atom(a::Atom, msg::AbstractString) = Expression(ERROR, a, Sym(String(msg)))

"Recursively replace bound variables by their values (hyperon apply_bindings_to_atom)."
function subst(a::Atom, b::Bindings)
    if a isa Var
        v = resolve(b, a)
        return v === nothing ? a : subst(v, b)
    elseif a isa Expression
        return Expression(Atom[subst(c, b) for c in a.children])
    else
        return a
    end
end

function collect_vars!(s::Set{Var}, a::Atom)
    a isa Var && (push!(s, a); return s)
    a isa Expression && (for c in a.children; collect_vars!(s, c); end)
    s
end
collect_vars(a::Atom) = collect_vars!(Set{Var}(), a)

# ── Stack frame (interpreter.rs `Stack`) ──────────────────────────────────────
mutable struct Frame
    atom::Atom
    vars::Set{Var}
    prev::Union{Frame,Nothing}
    ret::Function          # continuation invoked (by interpret_stack) when a child finishes
    finished::Bool
    depth::Int
end
const Plan = Vector{Tuple{Frame,Bindings}}

no_handler(::Frame, ::Atom, ::Bindings) = nothing   # a finished child with no_handler just pops

# finished_result (interpreter.rs:474): a finished frame holding `atom`, linked to `prev`
finished_result(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}) =
    Tuple{Frame,Bindings}[(Frame(atom, Set{Var}(), prev, no_handler, true, 0), b)]

# ── the dispatch step (interpreter.rs interpret_stack:374) ────────────────────
function interpret_stack(f::Frame, b::Bindings, space)::Vector{Tuple{Frame,Bindings}}
    if f.finished
        f.prev === nothing && return [(f, b)]                  # final result
        atom = subst(f.atom, b)                                # apply bindings on the way up
        cont = f.prev.ret(f.prev, atom, b)
        return cont === nothing ? Tuple{Frame,Bindings}[] : [cont]
    end
    name = head_name(f.atom)
    if name == "cons-atom";    return cons_atom(f, b)
    elseif name == "decons-atom"; return decons_atom(f, b)
    elseif name == "unify";    return unify_op(f, b)
    elseif name == "eval";     return eval_op(f, b, space)
    elseif name == "chain";    return setup_chain(f.atom, b, f.prev, f.depth)
    elseif name == "function"; return setup_function(f.atom, b, f.prev, f.depth)
    elseif name == "collapse-bind";  return collapse_bind_op(f, b, space)
    elseif name == "superpose-bind"; return superpose_bind_op(f, b, space)
    else
        return finished_result(f.atom, b, f.prev)              # not a minimal op → data, as-is
    end
end

# ── instructions that finish without continuations ────────────────────────────

# unify (interpreter.rs:809): match atom~pattern; per match emit `then` w/ bindings, else `else_`
function unify_op(f::Frame, b::Bindings)
    a = f.atom
    (a isa Expression && length(a.children) == 5) ||
        return finished_result(error_atom(a, "expected (unify <atom> <pattern> <then> <else>)"), b, f.prev)
    atom, pattern, then, else_ = a.children[2], a.children[3], a.children[4], a.children[5]
    matches = match_atoms(subst(atom, b), subst(pattern, b))
    out = Tuple{Frame,Bindings}[]
    for m in matches
        for mb in merge_bindings(b, m)
            append!(out, finished_result(subst(then, mb), mb, f.prev))
        end
    end
    isempty(out) ? finished_result(subst(else_, b), b, f.prev) : out
end

# decons-atom (interpreter.rs:843): non-empty expr → (head (tail...)); empty → error
function decons_atom(f::Frame, b::Bindings)
    a = f.atom
    (a isa Expression && length(a.children) == 2) ||
        return finished_result(error_atom(a, "expected (decons-atom <expr>)"), b, f.prev)
    e = subst(a.children[2], b)
    (e isa Expression && !isempty(e.children)) ||
        return finished_result(error_atom(a, "expected: (decons-atom (: <expr> Expression)), found: $(a)"), b, f.prev)
    head = e.children[1]; tail = Expression(e.children[2:end])
    finished_result(Expression(head, tail), b, f.prev)
end

# cons-atom (interpreter.rs:858): (cons-atom head (tail...)) → (head tail...)
function cons_atom(f::Frame, b::Bindings)
    a = f.atom
    (a isa Expression && length(a.children) == 3) ||
        return finished_result(error_atom(a, "expected (cons-atom <head> <tail>)"), b, f.prev)
    head = subst(a.children[2], b); tail = subst(a.children[3], b)
    (tail isa Expression) ||
        return finished_result(error_atom(a, "expected: (cons-atom <head> (: <tail> Expression))"), b, f.prev)
    finished_result(Expression(Atom[head; tail.children]), b, f.prev)
end

# ── grounded functions + space (the layer eval needs) ────────────────────────
# Idiomatic Julia: a grounded operation is `Grounded{Operation}`; multiple dispatch +
# parametric Grounded{T} replace hyperon's `Box<dyn GroundedAtom>` / downcast.
struct ExecOk; results::Vector{Atom}; end
struct ExecNoReduce end
struct ExecRuntime; msg::String; end
const ExecResult = Union{ExecOk,ExecNoReduce,ExecRuntime}

struct Operation
    name::String
    fn::Function          # (args::Vector{Atom}) -> ExecResult
end
Base.show(io::IO, o::Operation) = print(io, o.name)

is_executable(a::Atom) = a isa Grounded && a.value isa Operation
execute(g::Grounded, opargs::Vector{Atom})::ExecResult = g.value.fn(opargs)

# arithmetic (normal order — eval passes args UNreduced; non-numbers ⇒ NoReduce ⇒ NotReducible)
function _num_binop(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        length(xs) == 2 || return ExecNoReduce()
        x, y = xs[1], xs[2]
        (x isa Grounded && x.value isa Number && y isa Grounded && y.value isa Number) || return ExecNoReduce()
        ExecOk(Atom[Grounded(f(x.value, y.value))])
    end))
end
const PLUS  = _num_binop("+", +)
const MINUS = _num_binop("-", -)
# comparisons return the True/False SYMBOLS (so unify against `True` works)
function _num_cmp(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        length(xs) == 2 || return ExecNoReduce()
        x, y = xs[1], xs[2]
        (x isa Grounded && x.value isa Number && y isa Grounded && y.value isa Number) || return ExecNoReduce()
        ExecOk(Atom[f(x.value, y.value) ? Sym("True") : Sym("False")])
    end))
end
const LT = _num_cmp("<", <)

mutable struct Space
    atoms::Vector{Atom}
end
Space() = Space(Atom[])
add_atom!(s::Space, a::Atom) = (push!(s.atoms, a); s)

const _VAR_COUNTER = Ref(UInt64(0))
freshvar(name) = (_VAR_COUNTER[] += UInt64(1); Var(name, _VAR_COUNTER[]))

# alpha-rename every variable in `a` to a fresh one (hyperon make_variables_unique) — hygiene,
# so a rule matched repeatedly (recursion) doesn't clash its own variables across levels.
function rename_fresh(a::Atom, m::Dict{Var,Var})
    if a isa Var
        return get!(() -> freshvar(a.name), m, a)
    elseif a isa Expression
        return Expression(Atom[rename_fresh(c, m) for c in a.children])
    else
        return a
    end
end

# query (= pattern $X) → the matching binding sets (interpreter.rs query:604, naive linear match).
# Each stored atom's variables are freshened before matching (interpreter.rs make_variables_unique).
function query(space::Space, pattern::Atom)::Vector{Bindings}
    out = Bindings[]
    for stored in space.atoms
        append!(out, match_atoms(pattern, rename_fresh(stored, Dict{Var,Var}())))
    end
    out
end

# eval (interpreter.rs eval_impl:504) — ONE step, normal-order
function eval_op(f::Frame, b::Bindings, space)
    a = f.atom
    (a isa Expression && length(a.children) == 2) ||
        return finished_result(error_atom(a, "expected (eval <atom>)"), b, f.prev)
    to_eval = subst(a.children[2], b)
    if to_eval isa Expression && !isempty(to_eval.children) && is_executable(to_eval.children[1])
        r = execute(to_eval.children[1]::Grounded, Atom[to_eval.children[2:end]...])
        if r isa ExecOk
            isempty(r.results) && return finished_result(EMPTY, b, f.prev)
            out = Tuple{Frame,Bindings}[]
            for res in r.results; append!(out, eval_result(res, b, f.prev, f.depth + 1)); end
            return out
        elseif r isa ExecNoReduce
            return finished_result(NOT_REDUCIBLE, b, f.prev)            # NoReduce/IncorrectArgument
        else
            return finished_result(error_atom(to_eval, (r::ExecRuntime).msg), b, f.prev)
        end
    elseif is_minimal_op(to_eval)
        return [(Frame(to_eval, collect_vars(to_eval), f.prev, no_handler, false, f.depth + 1), b)]
    else
        space === nothing && return finished_result(NOT_REDUCIBLE, b, f.prev)
        X = freshvar("X")
        results = query(space::Space, Expression(Sym("="), to_eval, X))
        out = Tuple{Frame,Bindings}[]
        for qb in results, mb in merge_bindings(b, qb)
            x = resolve(mb, X); x === nothing && continue
            append!(out, eval_result(subst(x, mb), mb, f.prev, f.depth + 1))
        end
        return isempty(out) ? finished_result(NOT_REDUCIBLE, b, f.prev) : out
    end
end

# ── pushing nested computations + continuations (chain / function) ────────────
# Idiomatic Julia: continuations are CLOSURES stored in Frame.ret (no Rust mem::swap /
# Rc<RefCell> placeholder dance). A frame's ret runs when the child it pushed finishes;
# ret returns a single (Frame,Bindings) to continue, or nothing to drop. Fan-out is
# preserved because a fanned-out child yields several finished frames, each firing ret.

# set up `atom` to be evaluated (interpreter.rs atom_to_stack:640)
function push_nested(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)::Vector{Tuple{Frame,Bindings}}
    name = head_name(atom)
    if name == "chain";        return setup_chain(atom, b, prev, depth)
    elseif name == "function"; return setup_function(atom, b, prev, depth)
    else;                      return [(Frame(atom, collect_vars(atom), prev, no_handler, false, depth), b)]
    end
end

# function-special-when-returned (interpreter.rs eval_result:559): a returned `function`
# op is set up (looped), not treated as data.
function eval_result(res::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)
    head_name(res) == "function" ? setup_function(res, b, prev, depth) : finished_result(res, b, prev)
end

# chain (interpreter.rs chain:687 / chain_ret:675): one-step nested, bind var, subst templ, EXECUTE it
function setup_chain(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)
    (atom isa Expression && length(atom.children) == 4) ||
        return finished_result(error_atom(atom, "expected (chain <nested> <var> <templ>)"), b, prev)
    nested, var, templ = atom.children[2], atom.children[3], atom.children[4]
    var isa Var ||
        return finished_result(error_atom(atom, "chain: second argument must be a variable"), b, prev)
    cont = function (self::Frame, result::Atom, rb::Bindings)
        bs = add_var_binding(rb, var, result)
        isempty(bs) && return nothing
        nb = bs[1]
        pushed = push_nested(subst(templ, nb), nb, self.prev, depth)
        isempty(pushed) ? nothing : pushed[1]
    end
    parent = Frame(atom, Set{Var}(), prev, cont, false, depth)
    push_nested(nested, b, parent, depth + 1)
end

# function/return (interpreter.rs function_to_stack:704 / function_ret:723): loop until (return x)
function setup_function(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)
    (atom isa Expression && length(atom.children) == 2) ||
        return finished_result(error_atom(atom, "expected (function <body>)"), b, prev)
    body = atom.children[2]
    fret = function (self::Frame, result::Atom, rb::Bindings)
        if result isa Expression && length(result.children) == 2 && result.children[1] == RETURN
            return (Frame(result.children[2], Set{Var}(), self.prev, no_handler, true, depth), rb)  # return x
        elseif is_minimal_op(result)
            pushed = push_nested(result, rb, self, depth + 1)                                        # loop
            isempty(pushed) ? nothing : pushed[1]
        else
            return (Frame(error_atom(atom, "NoReturn"), Set{Var}(), self.prev, no_handler, true, depth), rb)
        end
    end
    fframe = Frame(atom, Set{Var}(), prev, fret, false, depth)
    push_nested(body, b, fframe, depth + 1)
end

# ── collapse-bind / superpose-bind (nondeterminism capture/restore) ───────────
# collapse-bind (interpreter.rs:746): collect ALL alternatives of nested into one expression
# of (atom bindings) pairs. hyperon detects "all alternatives done" via Rc::into_inner refcounting
# on shared frames; idiomatic Julia instead runs a NESTED complete interpretation (same semantics,
# no ownership tricks). bindings are carried as a Grounded{Bindings} atom.
function collapse_bind_op(f::Frame, b::Bindings, space)
    a = f.atom
    (a isa Expression && length(a.children) == 2) ||
        return finished_result(error_atom(a, "expected (collapse-bind <atom>)"), b, f.prev)
    results = interpret(a.children[2], space, b)                 # all (atom, bindings) alternatives
    pairs = Atom[Expression(atom, Grounded(bnd)) for (atom, bnd) in results]
    finished_result(Expression(pairs), b, f.prev)               # one result = the collapsed list
end

# superpose-bind (interpreter.rs:893): the complement — put each (atom bindings) pair back into the
# plan as a separate alternative, restoring its bindings.
function superpose_bind_op(f::Frame, b::Bindings, space)
    a = f.atom
    (a isa Expression && length(a.children) == 2) ||
        return finished_result(error_atom(a, "expected (superpose-bind <collapsed>)"), b, f.prev)
    list = subst(a.children[2], b)
    (list isa Expression) ||
        return finished_result(error_atom(a, "superpose-bind: expected an expression"), b, f.prev)
    out = Tuple{Frame,Bindings}[]
    for pair in list.children
        (pair isa Expression && length(pair.children) == 2) || continue
        atom, bnd = pair.children[1], pair.children[2]
        stored = (bnd isa Grounded && bnd.value isa Bindings) ? bnd.value : Bindings()
        for mb in merge_bindings(b, stored)
            append!(out, finished_result(subst(atom, mb), mb, f.prev))
        end
    end
    out
end

# ── driver (interpreter.rs InterpreterState loop) ─────────────────────────────
"Run the minimal-MeTTa machine on `atom`; returns the list of (result, bindings)."
function interpret(atom::Atom, space=nothing, b::Bindings=Bindings())::Vector{Tuple{Atom,Bindings}}
    plan = Tuple{Frame,Bindings}[(Frame(atom, collect_vars(atom), nothing, no_handler, false, 0), b)]
    out = Tuple{Atom,Bindings}[]
    steps = 0
    while !isempty(plan)
        (steps += 1) > 100_000 && error("minimal interpreter step limit")
        f, fb = pop!(plan)
        for (nf, nb) in interpret_stack(f, fb, space)
            if nf.finished && nf.prev === nothing
                push!(out, (nf.atom, nb))
            else
                push!(plan, (nf, nb))
            end
        end
    end
    out
end

"Convenience: run and return just the result atoms."
bare_eval(atom::Atom, space=nothing) = first.(interpret(atom, space))

# ═══════════════════════════════════════════════════════════════════════════════
# The `metta` interpreter driver (metta.md §Interpretation) — UNTYPED (Phase 1a).
# A direct RECURSIVE port of the pseudocode (metta / interpret_expression /
# interpret_tuple / metta_call), treating every type as %Undefined%. This reduces
# to normal form, in applicative order, nondeterministically. The gradual type
# system (type_cast / check_argument_type / BadArgType) is Phase 1b.
# ═══════════════════════════════════════════════════════════════════════════════
const _RESULT = Tuple{Atom,Bindings}
is_error_atom(a::Atom) = a isa Expression && !isempty(a.children) && a.children[1] == ERROR
is_empty_atom(a::Atom) = a == EMPTY

const _METTA_STEPS = Ref(0)
const _METTA_MAX = 5_000_000

"Public entry: fully evaluate `atom` in `space`; returns the result set (atoms)."
metta_run(atom::Atom, space::Space, b::Bindings=Bindings()) = first.(metta_results(atom, space, b))
"Fully evaluate `atom`; returns (atom, bindings) result set."
function metta_results(atom::Atom, space::Space, b::Bindings=Bindings())::Vector{_RESULT}
    _METTA_STEPS[] = 0
    metta_eval(atom, space, b)
end

# metta(atom, %Undefined%, space, bindings)  (metta.md:240)
function metta_eval(atom::Atom, space::Space, b::Bindings)::Vector{_RESULT}
    a = subst(atom, b)
    (is_empty_atom(a) || is_error_atom(a)) && return _RESULT[(a, b)]
    (a isa Expression && !isempty(a.children)) ? interpret_expression(a, space, b) : _RESULT[(a, b)]
end

# interpret_expression (metta.md:316) — untyped: evaluate the tuple, then metta_call each result
function interpret_expression(a::Expression, space::Space, b::Bindings)::Vector{_RESULT}
    out = _RESULT[]
    for (t, tb) in interpret_tuple(a, space, b)
        (is_empty_atom(t) || is_error_atom(t)) ? push!(out, (t, tb)) : append!(out, metta_call(t, space, tb))
    end
    out
end

# interpret_tuple (metta.md:358) — evaluate every element (applicative order), reassemble
function interpret_tuple(a::Atom, space::Space, b::Bindings)::Vector{_RESULT}
    (a isa Expression) || return metta_eval(a, space, b)
    isempty(a.children) && return _RESULT[(a, b)]                       # () → ()
    head, tail = a.children[1], Expression(a.children[2:end])
    out = _RESULT[]
    for (h, hb) in metta_eval(head, space, b)
        if is_empty_atom(h) || is_error_atom(h)
            push!(out, (h, hb)); continue
        end
        for (t, tb) in interpret_tuple(tail, space, hb)
            if is_empty_atom(t) || is_error_atom(t)
                push!(out, (t, tb))
            else
                tchildren = t isa Expression ? t.children : Atom[t]
                push!(out, (Expression(Atom[h; tchildren]), tb))
            end
        end
    end
    out
end

# metta_call (metta.md:509) — reduce: grounded → native, else → (= atom $X) query; recurse metta
function metta_call(a::Atom, space::Space, b::Bindings)::Vector{_RESULT}
    (_METTA_STEPS[] += 1) > _METTA_MAX && error("metta: step limit reached (non-termination?)")
    is_error_atom(a) && return _RESULT[(a, b)]
    (a isa Expression && !isempty(a.children)) || return _RESULT[(a, b)]
    op, opargs = a.children[1], a.children[2:end]
    out = _RESULT[]
    if is_executable(op)
        r = execute(op::Grounded, Atom[opargs...])
        if r isa ExecOk
            for res in r.results; append!(out, metta_eval(res, space, b)); end
        elseif r isa ExecNoReduce
            return _RESULT[(a, b)]                                       # not reducible → as-is
        else
            return _RESULT[(error_atom(a, (r::ExecRuntime).msg), b)]
        end
    else
        X = freshvar("X")
        qres = query(space, Expression(Sym("="), a, X))
        if !isempty(qres)
            for qb in qres, mb in merge_bindings(b, qb)
                x = resolve(mb, X); x === nothing && continue
                append!(out, metta_eval(x, space, mb))
            end
        else
            push!(out, (a, b))                                          # non-reducible → as-is
        end
    end
    isempty(out) ? _RESULT[(EMPTY, b)] : out
end

end # module
