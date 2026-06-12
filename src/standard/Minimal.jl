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

export interpret, bare_eval

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
    elseif name == "eval";     return finished_result(error_atom(f.atom, "eval not yet ported — Phase 0c"), b, f.prev)
    elseif name == "chain";    return finished_result(error_atom(f.atom, "chain not yet ported — Phase 0c"), b, f.prev)
    elseif name == "function"; return finished_result(error_atom(f.atom, "function not yet ported — Phase 0c"), b, f.prev)
    elseif name == "collapse-bind" || name == "superpose-bind"
        return finished_result(error_atom(f.atom, "$(name) not yet ported — Phase 0d"), b, f.prev)
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

end # module
