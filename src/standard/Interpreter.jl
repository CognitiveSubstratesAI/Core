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

module Interpreter

include("Atoms.jl")
using .StandardMeTTa

export interpret, bare_eval, Space, add_atom!, Operation, PLUS, MINUS, LT, is_executable
export metta_run, metta_results, parse_program, load_metta!, load_core_stdlib!, tokenize, metta_debug!

# instruction symbols
const EVAL = Sym("eval"); const EVALC = Sym("evalc"); const CHAIN = Sym("chain")
const FUNCTION = Sym("function"); const RETURN = Sym("return"); const UNIFY = Sym("unify")
const CONS = Sym("cons-atom"); const DECONS = Sym("decons-atom")
const COLLAPSE_BIND = Sym("collapse-bind"); const SUPERPOSE_BIND = Sym("superpose-bind")
const EMPTY = Sym("Empty"); const NOT_REDUCIBLE = Sym("NotReducible"); const ERROR = Sym("Error")
const MINIMAL_OPS = Set(String[ "eval","evalc","chain","function","unify",
                                 "cons-atom","decons-atom","collapse-bind","superpose-bind" ])

# ── LangDef disable-to-prove hook (CeTTa-adopted, langdef_pack.{c,h}) ───────────
# A covered HE-rule branch fires ONLY when its rule is enabled, so disabling a rule (via
# CORE_LANGDEF_DISABLED_RULES — comma-separated rule names — or the test helpers below) cannot be
# compensated by a legacy code path. Default (env empty) → all enabled → each dispatch condition is
# IDENTICAL to before → the 234 conformance matrix is unaffected at default by construction.
const _LANGDEF_DISABLED = Ref{Union{Nothing, Set{String}}}(nothing)
function _langdef_disabled()::Set{String}
    s = _LANGDEF_DISABLED[]
    s === nothing || return s
    e = get(ENV, "CORE_LANGDEF_DISABLED_RULES", "")
    s = isempty(e) ? Set{String}() : Set(String.(strip.(split(e, ','))))
    _LANGDEF_DISABLED[] = s
    s
end
@inline rule_enabled(name::String)::Bool = !(name in _langdef_disabled())
langdef_disable!(names::String...) = (_LANGDEF_DISABLED[] = Set(collect(names)); nothing)  # disable-to-prove
langdef_reset!() = (_LANGDEF_DISABLED[] = nothing; nothing)                                 # re-read env on next check

# ── helpers ───────────────────────────────────────────────────────────────────
head_name(a::Atom) = (a isa Expression && !isempty(a.children) && a.children[1] isa Sym) ?
                     (a.children[1]::Sym).name : ""
is_minimal_op(a::Atom) = head_name(a) in MINIMAL_OPS
args(a::Expression) = a.children[2:end]

# hyperon/CeTTa store the error message as a grounded String (not a symbol) — Expression(ERROR, a, "msg").
# Matches the parsed string-literal form so error-asserting tests gate exactly; if-error etc. match the
# Error HEAD so control flow is unaffected. See docs/STDLIB_FAITHFULNESS_REFERENCE.md (ERROR REPRESENTATION).
error_atom(a::Atom, msg::AbstractString) = Expression(ERROR, a, Grounded(String(msg)))

# canonical representative of a var's equality class (smallest id, then name) — used when the
# slot has no value but the var is equal to another (formal-arg = actual-arg matches as $a=$b)
function _slot_rep(b::Bindings, v::Var)
    haskey(b.var_to_slot, v) || return v
    s = b.var_to_slot[v]; rep = v
    for (vv, ss) in b.var_to_slot
        ss == s && (vv.id < rep.id || (vv.id == rep.id && vv.name < rep.name)) && (rep = vv)
    end
    rep
end

# Depth guard for the recursive atom-walkers. StackOverflowError CANNOT be caught in Julia (the stack is
# already exhausted), so it must be PREVENTED: bail at a generous depth (cyclic/pathological atoms — e.g.
# a mutable state whose value references itself — hit this instead of crashing). Real atoms are shallow.
const _MAX_ATOM_DEPTH = 10_000

"Recursively replace bound variables by their values (hyperon apply_bindings_to_atom)."
function subst(a::Atom, b::Bindings, d::Int=0)
    d > _MAX_ATOM_DEPTH && return a
    if a isa Var
        v = resolve(b, a)
        v !== nothing && return subst(v, b, d + 1)
        rep = _slot_rep(b, a)                  # unbound but maybe equal to another var → representative
        return rep == a ? a : rep
    elseif a isa Expression
        return Expression(Atom[subst(c, b, d + 1) for c in a.children])
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

# ── per-step binding-narrowing (the step the faithful Minimal port had OMITTED) ───────────────
# hyperon `Bindings::apply_and_retain` (matcher.rs:693) / `narrow_vars` (:518); CeTTa eval.c
# materialize-into-term + variant-factor. Keep only bindings for vars in `live`; drop the rest.
# Removed vars carrying a value are materialized (via `subst`) into retained values, and the
# result atom is independently materialized by the caller's `subst(f.atom, b)` — so nothing a
# live var references is lost. WITHOUT this, bindings accumulate every var ever bound and
# `copy(Bindings)` grows per step → reduce-to's O(n⁴) (see METTA_COMPILATION_INTEGRATION §6d).
# This is NOT a 1:1 transplant of hyperon's per-stack-type var threading: it uses ONE sound
# over-approximation (`_cumvars` below) that keeps ≥ what hyperon keeps, so it can never drop a
# binding a pending frame still needs — it only drops fresh sub-evaluation-internal vars.
function narrow_bindings(b::Bindings, live)::Bindings
    slot_live = Dict{Int,Vector{Var}}()
    any_drop = false
    for (v, s) in b.var_to_slot
        if v in live
            push!(get!(slot_live, s, Var[]), v)
        else
            any_drop = true
        end
    end
    any_drop || return b                                   # nothing dead → no allocation (fast path)
    nb = Bindings()
    for (s, vars) in slot_live
        val = b.slots[s]
        if val === nothing
            length(vars) < 2 && continue                   # lone value-less var ≡ unbound → drop
            v1 = vars[1]
            for i in 2:length(vars)
                r = add_var_equality(nb, v1, vars[i]); isempty(r) || (nb = r[1])
            end
        else
            sval = subst(val, b)                           # materialize removed vars referenced in value
            for v in vars
                r = add_var_binding(nb, v, sval); isempty(r) || (nb = r[1])
            end
        end
    end
    nb
end

# cumulative live-var set for a frame = its atom's vars ∪ its parent's live set (hyperon
# Stack::add_vars_it :111, but a plain union — not hyperon's per-stack-type logic). Because a
# frame's set is fixed when it is built, fresh vars introduced by a child sub-evaluation are
# absent from the parent's set and get dropped when the child returns (narrow_bindings above).
_cumvars(prev::Union{Frame,Nothing}, atom::Atom)::Set{Var} =
    prev === nothing ? collect_vars(atom) : union!(collect_vars(atom), prev.vars)

# ── the dispatch step (interpreter.rs interpret_stack:374) ────────────────────
function interpret_stack(f::Frame, b::Bindings, space)::Vector{Tuple{Frame,Bindings}}
    if f.finished
        f.prev === nothing && return [(f, b)]                  # final result
        atom = subst(f.atom, b)                                # apply bindings on the way up (materialize)
        nb = narrow_bindings(b, f.prev.vars)                   # drop bindings no pending frame references
        cont = f.prev.ret(f.prev, atom, nb)                    # (apply_and_retain, interpreter.rs:387)
        return cont === nothing ? Tuple{Frame,Bindings}[] : [cont]
    end
    name = head_name(f.atom)
    if name == "cons-atom";    return cons_atom(f, b)
    elseif name == "decons-atom"; return decons_atom(f, b)
    elseif name == "unify";    return unify_op(f, b)
    elseif name == "eval";     return eval_op(f, b, space)
    elseif name == "chain" && rule_enabled("HES_Chain"); return setup_chain(f.atom, b, f.prev, f.depth)
    elseif name == "function"; return setup_function(f.atom, b, f.prev, f.depth)
    elseif name == "collapse-bind";  return collapse_bind_op(f, b, space)
    elseif name == "superpose-bind"; return superpose_bind_op(f, b, space)
    elseif name == "metta";            return metta_instr(f, b, space)            # metta driver (stack-machine)
    elseif name == "interpret-tuple";  return interpret_tuple_instr(f, b, space)
    elseif name == "interpret-function"; return interpret_function_instr(f, b, space)
    elseif name == "interpret-args";   return interpret_args_instr(f, b, space)
    elseif name == "metta-call";       return metta_call_instr(f, b, space)
    elseif name == "return-on-error";  return return_on_error_instr(f, b)
    elseif name == "args-cont";        return args_cont_instr(f, b)
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
    satom = subst(atom, b)
    out = Tuple{Frame,Bindings}[]
    # hyperon: a Grounded Space implements a custom match_ → `unify` QUERIES the space (used by get-doc)
    if satom isa Grounded && satom.value isa Space
        for mb in _match_pat(satom.value::Space, subst(pattern, b), b)
            append!(out, finished_result(subst(then, mb), mb, f.prev))
        end
        return isempty(out) ? finished_result(subst(else_, b), b, f.prev) : out
    end
    for m in match_atoms(satom, subst(pattern, b))
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
# grounded success: result atoms, each optionally with bindings to propagate to the caller
# (hyperon execute_bindings). `binds[i]` aligns with `results[i]`; empty `binds` = no propagation.
struct ExecOk; results::Vector{Atom}; binds::Vector{Bindings}; end
ExecOk(results::Vector{Atom}) = ExecOk(results, Bindings[])
struct ExecNoReduce end
struct ExecRuntime; msg::String; end
const ExecResult = Union{ExecOk,ExecNoReduce,ExecRuntime}

struct Operation
    name::String
    fn::Function          # (args::Vector{Atom}) -> ExecResult
end
"A grounded op that also receives the context Space (for assertEqual / context-space / etc.)."
struct SpaceOp
    name::String
    fn::Function          # (args::Vector{Atom}, space) -> ExecResult
end
Base.show(io::IO, o::Operation) = print(io, o.name)
Base.show(io::IO, o::SpaceOp) = print(io, o.name)

# State atom (hyperon StateAtom space.rs:38 / CeTTa StateCell atom.h:146): a MUTABLE cell wrapping a
# value AND its `(StateMonad T)` type. Shared+mutable: change-state! mutates `value` in place, so every
# reference (e.g. via a bound token) sees the update. `==` is by CONTENT (value+type), NOT cell identity
# — so two distinct `(new-state (A B))` are equal (space.rs derived PartialEq compares the inner tuple).
# Wrapped in `Grounded{StateCell}`; the Ref-like mutability comes from `mutable struct`.
mutable struct StateCell
    value::Atom
    vtype::Atom          # (StateMonad T) — intrinsic type, returned by get-type
end
Base.:(==)(a::StateCell, b::StateCell) = a.value == b.value && a.vtype == b.vtype
Base.hash(c::StateCell, h::UInt) = hash(c.vtype, hash(c.value, hash(:StateCell, h)))
Base.show(io::IO, c::StateCell) = print(io, "(State ", c.value, ")")

is_executable(a::Atom) = a isa Grounded && (a.value isa Operation || a.value isa SpaceOp)
execute(g::Grounded, opargs::Vector{Atom}, space)::ExecResult =
    g.value isa SpaceOp ? g.value.fn(opargs, space) : g.value.fn(opargs)

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
    tokens::Dict{String,Atom}     # bind! token table: token-name → atom (parse-time substitution)
    imported::Set{String}         # modules already imported here — re-import is ignored (+ cycle guard)
    lib_count::Int                # leading atoms that came from an imported LIBRARY (stdlib). Core keeps
                                  # the library flattened (so &self/match/query stay single-space), but
                                  # `get-atoms` returns only atoms[lib_count+1:end] — the space's OWN
                                  # atoms — mirroring hyperon where get-atoms excludes dependency spaces.
    # ── first-argument index (the "Control" half of Algorithm=Logic+Control). `query` is on the hot
    # path of every reduction; a naive O(all-atoms) scan (interpreter.rs's reference path) made deep
    # programs (e.g. reduct) quadratic. EVERY faithful peer indexes: hyperon's AtomIndex (a
    # discrimination trie), CeTTa's eq_idx (hash-bucketed equations), the legacy CoreSpace rule_cache
    # (functor Dict). We index by (outer-head-sym, 2nd-child-head-sym): rules `(= (f …) …)` bucket
    # under (=,f), type-anns `(: x T)` under (:,x). Atoms whose discriminant isn't concrete (var head,
    # var/var-headed 2nd child, <2 children) live in `wildcard` and are checked on every query —
    # they can match any discriminant (e.g. a var-LHS rule `(= $x …)`). `atoms` stays authoritative
    # (get-atoms/lib_count/order); the index is a parallel acceleration kept in sync at add/remove.
    index::Dict{Tuple{String,String},Vector{Atom}}
    wildcard::Vector{Atom}
end
Space() = Space(Atom[], Dict{String,Atom}(), Set{String}(), 0, Dict{Tuple{String,String},Vector{Atom}}(), Atom[])
Space(atoms::Vector{Atom}) = (s = Space(); for a in atoms; add_atom!(s, a); end; s)

# discriminant head of an atom-position: a Sym's name, or an Expression's Sym head; else nothing.
_idx_head(x::Atom)::Union{String,Nothing} =
    x isa Sym ? x.name :
    (x isa Expression && !isempty(x.children) && x.children[1] isa Sym) ? (x.children[1]::Sym).name :
    nothing
# (outer-head, 2nd-child-head) discriminant; nothing ⇒ not indexable ⇒ wildcard bucket.
function _index_key(a::Atom)::Union{Tuple{String,String},Nothing}
    (a isa Expression && length(a.children) >= 2 && a.children[1] isa Sym) || return nothing
    sub = _idx_head(a.children[2]); sub === nothing && return nothing
    ((a.children[1]::Sym).name, sub)
end
function add_atom!(s::Space, a::Atom)
    push!(s.atoms, a)
    k = _index_key(a)
    k === nothing ? push!(s.wildcard, a) : push!(get!(() -> Atom[], s.index, k), a)
    s
end
function remove_atom!(s::Space, a::Atom)
    filter!(x -> x != a, s.atoms)
    k = _index_key(a)
    if k === nothing
        filter!(x -> x != a, s.wildcard)
    else
        b = get(s.index, k, nothing); b !== nothing && filter!(x -> x != a, b)
    end
    s
end

const _VAR_COUNTER = Ref(UInt64(0))
freshvar(name) = (_VAR_COUNTER[] += UInt64(1); Var(name, _VAR_COUNTER[]))

# alpha-rename every variable in `a` to a fresh one (hyperon make_variables_unique) — hygiene,
# so a rule matched repeatedly (recursion) doesn't clash its own variables across levels.
function rename_fresh(a::Atom, m::Dict{Var,Var}, d::Int=0)
    d > _MAX_ATOM_DEPTH && return a
    if a isa Var
        return get!(() -> freshvar(a.name), m, a)
    elseif a isa Expression
        return Expression(Atom[rename_fresh(c, m, d + 1) for c in a.children])
    else
        return a
    end
end

# query (= pattern $X) → the matching binding sets (interpreter.rs query:604, naive linear match).
# Each stored atom's variables are freshened before matching (interpreter.rs make_variables_unique).
function query(space::Space, pattern::Atom)::Vector{Bindings}
    out = Bindings[]
    k = _index_key(pattern)
    if k === nothing                                   # non-discriminable pattern (var head) → full scan (rare)
        for stored in space.atoms
            append!(out, match_atoms(pattern, rename_fresh(stored, Dict{Var,Var}())))
        end
        return out
    end
    b = get(space.index, k, nothing)                   # same-discriminant atoms — the (= (f …) …) rules for this f
    if b !== nothing
        for stored in b
            append!(out, match_atoms(pattern, rename_fresh(stored, Dict{Var,Var}())))
        end
    end
    for stored in space.wildcard                       # + var-headed atoms, which can match any discriminant
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
        r = execute(to_eval.children[1]::Grounded, Atom[to_eval.children[2:end]...], space)
        if r isa ExecOk
            isempty(r.results) && return finished_result(EMPTY, b, f.prev)
            out = Tuple{Frame,Bindings}[]
            for (j, res) in enumerate(r.results)
                if j <= length(r.binds)
                    for mb in merge_bindings(b, r.binds[j]); append!(out, eval_result(res, mb, f.prev, f.depth + 1)); end
                else
                    append!(out, eval_result(res, b, f.prev, f.depth + 1))
                end
            end
            return out
        elseif r isa ExecNoReduce
            return finished_result(NOT_REDUCIBLE, b, f.prev)            # NoReduce/IncorrectArgument
        else
            return finished_result(error_atom(to_eval, (r::ExecRuntime).msg), b, f.prev)
        end
    elseif is_minimal_op(to_eval)
        return [(Frame(to_eval, _cumvars(f.prev, to_eval), f.prev, no_handler, false, f.depth + 1), b)]
    else
        (space === nothing || (to_eval isa Expression && !isempty(to_eval.children) && to_eval.children[1] isa Var)) &&
            return finished_result(NOT_REDUCIBLE, b, f.prev)   # variable-headed expr not reducible
        X = freshvar("X")
        results = query(space::Space, Expression(Sym("="), to_eval, X))
        out = Tuple{Frame,Bindings}[]
        for qb in results, mb in merge_bindings(b, qb)
            # resolve-filter (mirrors hyperon interpreter.rs query:619 `resolve(&var_x)→None`): drop a query match
            # where the rewrite-RHS X is TRULY unbound — a bare variable space atom binds itself to the whole
            # `(= …)` query, leaving X free, which would leak as a spurious `$X` and shadow grounded ops. Uses
            # `haskey(var_to_slot)` NOT `resolve===nothing`: Core's resolve also returns nothing for X equated to a
            # var (no value), but those (e.g. `(= (id $x) $x)` → a var) are LEGIT and must be KEPT. (See :564, :883.)
            haskey(mb.var_to_slot, X) || continue
            x = subst(X, mb)
            append!(out, eval_result(x, mb, f.prev, f.depth + 1))
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
    if name == "chain" && rule_enabled("HES_Chain"); return setup_chain(atom, b, prev, depth)
    elseif name == "function"; return setup_function(atom, b, prev, depth)
    else;                      return [(Frame(atom, _cumvars(prev, atom), prev, no_handler, false, depth), b)]
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
    parent = Frame(atom, _cumvars(prev, atom), prev, cont, false, depth)
    push_nested(subst(nested, b), b, parent, depth + 1)   # apply bindings so a var-bound minimal op evaluates
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
    fframe = Frame(atom, _cumvars(prev, atom), prev, fret, false, depth)
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

# ═══════════════════════════════════════════════════════════════════════════════
# THE METTA DRIVER AS STACK-MACHINE INSTRUCTIONS (hyperon interpret_expression/tuple/args/function/
# metta_call, ported as instructions so the applicative-order DEPTH lives in the heap `plan`, NOT the
# Julia call stack — this is what stops the StackOverflow class). Each handler builds the emitted
# minimal-instruction program (idiomatic Julia: Expression builders, not Rust's call_native!/iterators)
# and push_nests it. The crucial step is metta-call's "reduce-again": it pushes `(metta result)` as a
# FRAME, never a recursive Julia call.
_ret(x::Atom) = Expression(RETURN, x)
_metta(atom::Atom, typ::Atom) = Expression(Sym("metta"), atom, typ)
_op(name::String, args::Atom...) = Expression(Atom[Sym(name); collect(Atom, args)])
_chain(nested::Atom, v::Var, templ::Atom) = Expression(CHAIN, nested, v, templ)

# (metta <atom> <type>) — interpret_expression (interpreter.rs:1110). Leaf/cast cases finish as-is; an
# expression emits the tuple path (typed/function path added next increment).
function metta_instr(f::Frame, b::Bindings, space)
    a = f.atom
    (a isa Expression && length(a.children) == 3) ||
        return finished_result(error_atom(a, "expected (metta atom type)"), b, f.prev)
    atom = subst(a.children[2], b); typ = a.children[3]
    (is_empty_atom(atom) || is_error_atom(atom)) && return finished_result(atom, b, f.prev)
    (typ == ATOM_T || typ == metatype_sym(atom) || atom isa Var) && return finished_result(atom, b, f.prev)
    (atom isa Expression && !isempty(atom.children)) || return finished_result(atom, b, f.prev)
    if is_minimal_op(atom)                  # embedded minimal instruction → run it, then re-metta its result
        r = freshvar("r")                   # (a rule body like let*'s chain rewrites to (let …) which must reduce)
        return push_nested(_chain(atom, r, _metta(r, typ)), b, f.prev, f.depth + 1)
    end
    op = atom.children[1]; nargs = length(atom.children) - 1
    ftypes = op isa Var ? Atom[] :
        filter(t -> is_function_type(t) && length(fn_arg_types(t)) == nargs, atom_types(op, space))
    if !isempty(ftypes)                                       # TYPED path: type-check, then interpret-function
        out = Tuple{Frame,Bindings}[]; errs = Tuple{Frame,Bindings}[]
        for ft in ftypes
            te = type_check_errors(atom, ft::Expression, space)
            if !isempty(te); for e in te; append!(errs, finished_result(e, b, f.prev)); end; continue; end
            rt = fn_ret_type(ft::Expression); rt == Sym("Expression") && (rt = UNDEF)
            reduced = freshvar("reduced"); result = freshvar("result")
            prog = _chain(_op("interpret-function", atom, ft, rt), reduced,
                     _chain(_op("metta-call", reduced, rt), result, result))
            append!(out, push_nested(prog, b, f.prev, f.depth + 1))
        end
        !isempty(out) && return out                          # some function type applied
        !isempty(errs) && return errs                        # all rejected → type errors (BadArgType)
    end
    reduced = freshvar("reduced"); result = freshvar("result")  # untyped tuple path
    prog = _chain(_op("interpret-tuple", atom), reduced,
              _chain(_op("metta-call", reduced, typ), result, result))
    push_nested(prog, b, f.prev, f.depth + 1)
end

# (interpret-function <expr> <op_type> <ret_type>) (interpreter.rs:1224): evaluate op, then args by their
# declared types, then build (op . evaluated-args).
function interpret_function_instr(f::Frame, b::Bindings, space)
    a = f.atom
    expr = subst(a.children[2], b); op_type = a.children[3]
    (expr isa Expression && op_type isa Expression) ||
        return finished_result(error_atom(a, "interpret-function"), b, f.prev)
    op = expr.children[1]; theargs = Expression(expr.children[2:end])
    arg_types = Expression(fn_arg_types(op_type::Expression))
    h = freshvar("h"); targs = freshvar("targs"); res = freshvar("res")
    prog = _chain(_metta(op, UNDEF), h,
             _op("return-on-error", h,
               _chain(_op("interpret-args", theargs, arg_types), targs,
                 _op("return-on-error", targs,
                   _chain(_op("cons-atom", h, targs), res, res)))))
    push_nested(prog, b, f.prev, f.depth + 1)
end

# (interpret-args <args-expr> <types-expr>) (interpreter.rs:1352): metta each arg by its type (Atom-typed
# ⇒ UNEVALUATED, lazy), short-circuit on Empty/Error, cons up. Recursion on the tail is the
# `(interpret-args tail)` FRAME. Finishes with the evaluated-args expression, or an Empty/Error.
function interpret_args_instr(f::Frame, b::Bindings, space)
    a = f.atom
    argsx = subst(a.children[2], b); typesx = a.children[3]
    (argsx isa Expression) || return finished_result(error_atom(a, "interpret-args"), b, f.prev)
    isempty(argsx.children) && return finished_result(Expression(Atom[]), b, f.prev)   # no args → ()
    types = typesx isa Expression ? typesx.children : Atom[]
    ahead = argsx.children[1]; atail = Expression(argsx.children[2:end])
    thead = isempty(types) ? UNDEF : types[1]
    ttail = Expression(isempty(types) ? Atom[] : types[2:end])
    rhead = freshvar("rhead"); rtail = freshvar("rtail"); res = freshvar("res")
    recursion = _chain(_op("interpret-args", atail, ttail), rtail,
                  _op("return-on-error", rtail,
                    _chain(_op("cons-atom", rhead, rtail), res, res)))
    # args-cont = hyperon's `(if-equal rhead ahead <recursion> (return-on-error rhead <recursion>))`:
    # only error-check an arg that CHANGED (was evaluated); an UNEVALUATED Atom-typed arg (rhead==ahead),
    # even if error-shaped (e.g. assertEqual's expected (Error …) literal), is a legit value to pass on.
    prog = _chain(_metta(ahead, thead), rhead, _op("args-cont", rhead, ahead, recursion))
    push_nested(prog, b, f.prev, f.depth + 1)
end

# (args-cont <rhead> <ahead> <recursion>): rhead unchanged (Atom-typed, unevaluated) → run recursion;
# else rhead was evaluated → propagate if it's Empty/Error, otherwise run recursion.
function args_cont_instr(f::Frame, b::Bindings)
    a = f.atom
    rhead = subst(a.children[2], b); ahead = subst(a.children[3], b); recursion = a.children[4]
    (rhead != ahead && (is_empty_atom(rhead) || is_error_atom(rhead))) ?
        finished_result(rhead, b, f.prev) : push_nested(subst(recursion, b), b, f.prev, f.depth)
end

# (interpret-tuple <expr>) — interpret_tuple (interpreter.rs:1191): metta each element, cons up, short-
# circuit on Empty/Error. The recursion on `tail` is the `(interpret-tuple tail)` FRAME, not a Julia call.
function interpret_tuple_instr(f::Frame, b::Bindings, space)
    a = f.atom
    expr = subst(a.children[2], b)
    (expr isa Expression) || return finished_result(expr, b, f.prev)
    isempty(expr.children) && return finished_result(expr, b, f.prev)        # () → ()
    head = expr.children[1]; tail = Expression(expr.children[2:end])
    rhead = freshvar("rhead"); rtail = freshvar("rtail"); res = freshvar("res")
    prog = _chain(_metta(head, UNDEF), rhead,
              _op("return-on-error", rhead,
                _chain(_op("interpret-tuple", tail), rtail,
                  _op("return-on-error", rtail,
                    _chain(_op("cons-atom", rhead, rtail), res, res)))))
    push_nested(prog, b, f.prev, f.depth + 1)
end

# (return-on-error <atom> <then>) (interpreter.rs:1398): Empty/Error → finish with it; else → run `then`.
function return_on_error_instr(f::Frame, b::Bindings)
    a = f.atom
    atom = subst(a.children[2], b); then = a.children[3]
    (is_empty_atom(atom) || is_error_atom(atom)) ?
        finished_result(atom, b, f.prev) : push_nested(subst(then, b), b, f.prev, f.depth)
end

# (metta-call <atom> <type>) — metta_call (interpreter.rs:1415): grounded → execute; else → query
# (= atom $X). Each result is RE-MET TA'd via a pushed `(metta result type)` FRAME (reduce-again) — so a
# deep MeTTa recursion grows the heap plan, not the Julia stack. Non-reducible → finish as-is.
function metta_call_instr(f::Frame, b::Bindings, space)
    a = f.atom
    atom = subst(a.children[2], b); typ = a.children[3]
    _METTA_DEBUG[] && println("metta_call: ", atom)
    is_error_atom(atom) && return finished_result(atom, b, f.prev)
    (atom isa Expression && !isempty(atom.children)) || return finished_result(atom, b, f.prev)
    op = atom.children[1]
    op isa Var && return finished_result(atom, b, f.prev)
    out = Tuple{Frame,Bindings}[]
    if is_executable(op)
        r = execute(op::Grounded, Atom[atom.children[2:end]...], space)
        if r isa ExecOk
            isempty(r.results) && return finished_result(EMPTY, b, f.prev)
            for (j, res) in enumerate(r.results)
                bset = (j <= length(r.binds)) ? merge_bindings(b, r.binds[j]) : Bindings[b]
                for mb in bset; append!(out, push_nested(_metta(res, typ), mb, f.prev, f.depth + 1)); end
            end
            return out
        elseif r isa ExecNoReduce
            return finished_result(atom, b, f.prev)
        else
            return finished_result(error_atom(atom, (r::ExecRuntime).msg), b, f.prev)
        end
    else
        X = freshvar("X")
        qres = query(space::Space, Expression(Sym("="), atom, X))
        reduced = false
        for qb in qres, mb in merge_bindings(b, qb)
            haskey(mb.var_to_slot, X) || continue        # resolve-filter (identical to Interpreter.jl :309)
            reduced = true
            append!(out, push_nested(_metta(subst(X, mb), typ), mb, f.prev, f.depth + 1))
        end
        reduced || return finished_result(atom, b, f.prev)                   # no real rewrite survived → non-reducible
        return out
    end
end

# Public entry for the new stack-machine driver (parallels metta_run; used to validate equivalence).
metta_run_sm(atom::Atom, space::Space, b::Bindings=Bindings()) =
    Atom[subst(at, bnd) for (at, bnd) in interpret(_metta(atom, UNDEF), space, b) if !is_empty_atom(at)]

# ── driver (interpreter.rs InterpreterState loop) ─────────────────────────────
const _DIAG_STEPS = Ref(0)   # diagnostic: cumulative interpret() reduction steps (reset/read externally)

"Run the minimal-MeTTa machine on `atom`; returns the list of (result, bindings)."
function interpret(atom::Atom, space=nothing, b::Bindings=Bindings())::Vector{Tuple{Atom,Bindings}}
    plan = Tuple{Frame,Bindings}[(Frame(atom, collect_vars(atom), nothing, no_handler, false, 0), b)]
    out = Tuple{Atom,Bindings}[]
    steps = 0
    while !isempty(plan)
        _DIAG_STEPS[] += 1                                  # diagnostic step counter (tooling for the parked perf track)
        # Cap 100K→512K (2026-06-13): MetaMo's decision composites (metamoStep/metamoGovern) genuinely need
        # >100K reduction steps — MEASURED convergent, not an expansion bug (magusScore ~36-46K, 1.3× across
        # inputs; all sub-helpers + the fold bounded). The real cost is PER-STEP (let*-nesting + per-call
        # rule-lookup overhead, the parked perf track); this cap comes back DOWN once that's optimized.
        # Bounded-generous over measured need (~120-300K) so a real runaway still fires in minutes, not an hour.
        (steps += 1) > 512_000 && error("minimal interpreter step limit")
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
# The `metta` interpreter driver (metta.md §Interpretation) — gradual types (Phase 1b).
# Recursive port of the type-directed pseudocode. An expected TYPE threads through: when
# an argument's declared type is `Atom`, metta returns it UNEVALUATED (metta.md:255) — the
# lazy-argument mechanism `if`/`let`/`case` rely on. Minimal instructions are recognized
# as embedded ops and run on the minimal machine (normal order).
# ═══════════════════════════════════════════════════════════════════════════════
const _RESULT = Tuple{Atom,Bindings}
is_error_atom(a::Atom) = a isa Expression && !isempty(a.children) && a.children[1] == ERROR
is_empty_atom(a::Atom) = a == EMPTY

const UNDEF  = Sym("%Undefined%")
const ATOM_T = Sym("Atom")
const ARROW  = Sym("->")
metatype_sym(a::Atom) = Sym(String(metatype(a)))
is_function_type(t::Atom) = t isa Expression && !isempty(t.children) && t.children[1] == ARROW
fn_arg_types(t::Expression) = t.children[2:end-1]
fn_ret_type(t::Expression)  = t.children[end]

# Step counter — bounds NON-termination (the iterative driver can't stack-overflow, so this is the only
# bound needed for the reduce-chain; the subst/rename_fresh depth guards remain for pathological atoms).
const _METTA_STEPS = Ref(0)
# Step cap for the reduce-chain. 0 = UNLIMITED, the default — mirroring hyperon (max_stack_depth default
# 0 = unlimited) and CeTTa (fuel default -1 = unlimited); upstream does NOT cap by default. Settable via
# `metta_max_steps!(n)` when a non-termination bound is wanted. (Previously an always-on 5_000_000, a
# Core-specific divergence from upstream — see cross-check, project_pln_layer1_build.)
const _METTA_MAX = Ref(0)
"Set the reduce-chain step cap; 0 = unlimited (default). Mirrors hyperon `set_max_stack_depth` semantics."
metta_max_steps!(n::Int=0) = (_METTA_MAX[] = n)
const _METTA_DEBUG = Ref(false)
"Toggle metta reduction tracing — prints each metta_call (use to detect where evaluation goes wrong)."
metta_debug!(on::Bool=true) = (_METTA_DEBUG[] = on)

# Intrinsic types of grounded ops (hyperon: the op's `type_()` method, NOT a stdlib atom). Kept OUT of
# the space so they never appear in `match &self` — e.g. d4's type-reasoning rule matches every
# `(: X (-> a b))` decl and infinite-loops on a polymorphic arrow, so state-op types as space atoms
# would break it. Stored as source strings, parsed FRESH per lookup for variable hygiene.
const _GROUNDED_OP_TYPES = Dict{Atom,String}()       # populated after the ops are defined (below)
_parse_type(s::AbstractString)::Atom = parse_from(tokenize(s), Ref(1))

# the declared types of `atom`: intrinsic grounded-op type (if any) + space decls (: atom $T)
function atom_types(atom::Atom, space::Space)::Vector{Atom}
    T = freshvar("T"); out = Atom[]
    haskey(_GROUNDED_OP_TYPES, atom) && push!(out, _parse_type(_GROUNDED_OP_TYPES[atom]))
    for qb in query(space, Expression(Sym(":"), atom, T))
        t = resolve(qb, T); t !== nothing && push!(out, t)
    end
    out
end

# match_types with bindings (metta.md:298 + binding threading): the binding sets under which the two
# types unify (empty = no match). %Undefined%/Atom on either side matches with no new binding. Applying
# `b` first lets a type variable bound by an earlier argument constrain a later one (polymorphism).
function match_types_b(t1::Atom, t2::Atom, b::Bindings)::Vector{Bindings}
    (t1 == UNDEF || t1 == ATOM_T || t2 == UNDEF || t2 == ATOM_T) && return Bindings[b]
    out = Bindings[]
    for m in match_atoms(subst(t1, b), subst(t2, b)); append!(out, merge_bindings(b, m)); end
    out
end

# actual type(s) of an argument (hyperon get_atom_types_internal types.rs:376):
# Variable → %Undefined% (NOT a (: $v $T) query — that spuriously matches every decl);
# Grounded → its grounded type; Symbol/Expression → declared types, else %Undefined%.
function arg_actual_types(arg::Atom, space::Space)::Vector{Atom}
    arg isa Var && return Atom[UNDEF]                            # types.rs:386 — variables have no types
    if arg isa Grounded
        arg.value isa Bool && return Atom[Sym("Bool")]
        arg.value isa Number && return Atom[Sym("Number")]
        arg.value isa AbstractString && return Atom[Sym("String")]
        arg.value isa StateCell && return Atom[arg.value.vtype]   # intrinsic (StateMonad T) (space.rs:55)
        arg.value isa Space && return Atom[Sym("SpaceType")]      # DynSpace.type_() = ATOM_TYPE_SPACE (hyperon-space/lib.rs:18)
    end
    # Expression: infer its return type by applying the HEAD's function type to the args. The head's types
    # are got recursively (types.rs:400-403 op_value_types) — so an EXPRESSION head like `(curry +)` has
    # its type INFERRED, enabling higher-order/curried application `((curry +) 2)`.
    if arg isa Expression && !isempty(arg.children)
        head = arg.children[1]; nargs = length(arg.children) - 1
        head_types = head isa Expression ? arg_actual_types(head, space) : atom_types(head, space)
        func_types = filter(is_function_type, head_types)
        if !isempty(func_types)                 # a function application
            for ft in filter(t -> length(fn_arg_types(t)) == nargs, func_types)
                r = Bindings(); ok = true
                for i in 1:nargs
                    matched = false
                    for ai in arg_actual_types(arg.children[i+1], space)
                        ms = match_types_b(fn_arg_types(ft)[i], ai, r)
                        isempty(ms) || (r = ms[1]; matched = true; break)
                    end
                    matched || (ok = false; break)
                end
                ok && return Atom[subst(fn_ret_type(ft), r)]
            end
            return Atom[]                       # function head but no overload fits (arity/args) → ill-typed
        end
    end
    ts = atom_types(arg, space)
    isempty(ts) ? Atom[UNDEF] : ts
end

# check_if_function_type_is_applicable arg loop (metta.md:384): thread type-variable bindings across
# args; an arg with no matching actual type under any threaded binding → BadArgType. Returns the errors
# only when NO valid type-assignment path survives (so a polymorphic (-> $t $t Bool) enforces same $t).
function type_check_errors(a::Expression, ftype::Expression, space::Space)::Vector{Atom}
    ats = fn_arg_types(ftype); errs = Atom[]; results = Bindings[Bindings()]
    for i in 1:length(ats)
        actuals = arg_actual_types(a.children[i+1], space)
        next = Bindings[]
        for r in results
            isempty(actuals) && (push!(next, r); continue)   # ill-typed sub-arg: stay permissive (gradual)
            for at in actuals
                ms = match_types_b(ats[i], at, r)
                isempty(ms) ?
                    push!(errs, Expression(ERROR, a, Expression(Sym("BadArgType"), Grounded(i), subst(ats[i], r), at))) :
                    append!(next, ms)
            end
        end
        results = next
        isempty(results) && return errs                 # no valid path → these BadArgType errors
    end
    Atom[]                                               # a path survived → applicable, no error
end

const _STEP = Tuple{Atom,Atom,Bindings,Bool}   # (atom, next-type, bindings, is_final)

# ITERATIVE driver. The deep reduce-chain (rewrite → re-reduce → rewrite …) is a worklist LOOP, so it
# never grows the Julia call stack (Julia has no TCO). interpret_function/args/tuple still recurse, but
# only by atom NESTING depth (shallow), and they call `_reduce` (iterative) for each sub-evaluation. This
# mirrors hyperon's iterative interpret_stack and follows the Julia team's "rewrite recursion as an
# explicit loop" guidance — replacing the recursive metta.md pseudocode port that overflowed the stack.
# The reduce-CHAIN is iterative (the worklist), but interpret_function/args/tuple call _reduce for
# nested sub-evaluation, so NESTED _reduce calls still grow the Julia call stack (= the atom-application
# nesting depth of a deep MeTTa recursion). Julia's StackOverflowError is UNCATCHABLE, so — per the Julia
# team's guidance and exactly like hyperon's interpret_stack `max_stack_depth` (interpreter.rs:392) — we
# BOUND the nesting and fail SAFE with (Error … StackOverflow) instead of corrupting the process.
const _REDUCE_DEPTH = Ref(0)
const _REDUCE_MAX_DEPTH = 1200          # well under Julia's frame limit (incl. JIT frames), far above any real program
function _reduce(atom::Atom, type::Atom, space::Space, b::Bindings)::Vector{_RESULT}
    _REDUCE_DEPTH[] += 1
    try
        _REDUCE_DEPTH[] > _REDUCE_MAX_DEPTH &&
            return _RESULT[(error_atom(atom, "StackOverflow"), b)]
        work = _STEP[(atom, type, b, false)]
        final = _RESULT[]
        while !isempty(work)
            (a, t, bb, _) = pop!(work)
            for (r, nt, rb, isfinal) in metta_step(a, t, space, bb)
                isfinal ? push!(final, (r, rb)) : push!(work, (r, nt, rb, false))
            end
        end
        return final
    finally
        _REDUCE_DEPTH[] -= 1
    end
end

"Public entry: fully evaluate `atom` in `space`; result set (final bindings applied, Empty filtered)."
metta_run(atom::Atom, space::Space, b::Bindings=Bindings()) =
    Atom[subst(at, bnd) for (at, bnd) in metta_results(atom, space, b) if !is_empty_atom(at)]
"Fully evaluate `atom`; returns (atom, bindings) result set."
function metta_results(atom::Atom, space::Space, b::Bindings=Bindings())::Vector{_RESULT}
    interpret(_metta(atom, UNDEF), space, b)          # routed to the iterative stack machine (no overflow)
end

# ONE reduction step (metta.md:240). Returns each result tagged: is_final=true → terminal; false →
# "reduce again" (the loop re-feeds it). No recursion into the reduce-chain.
function metta_step(atom::Atom, type::Atom, space::Space, b::Bindings)::Vector{_STEP}
    _METTA_MAX[] > 0 && (_METTA_STEPS[] += 1) > _METTA_MAX[] && error("metta: step limit reached (non-termination?)")
    a = subst(atom, b)
    (is_empty_atom(a) || is_error_atom(a)) && return _STEP[(a, type, b, true)]
    (type == ATOM_T || type == metatype_sym(a) || a isa Var) && return _STEP[(a, type, b, true)]
    (a isa Expression && !isempty(a.children)) ? interpret_expr_step(a, type, space, b) : _STEP[(a, type, b, true)]
end

# interpret_expression (metta.md:316) as ONE step — type-directed; minimal ops + rewrites tagged "reduce"
function interpret_expr_step(a::Expression, type::Atom, space::Space, b::Bindings)::Vector{_STEP}
    if is_minimal_op(a)                                  # embedded minimal instruction (normal order)
        out = _STEP[]
        for (r, rb) in interpret(a, space, b); push!(out, (r, type, rb, false)); end
        return isempty(out) ? _STEP[(EMPTY, type, b, true)] : out
    end
    op = a.children[1]; nargs = length(a.children) - 1
    # variable-headed expr: skip type lookup (its query would spuriously match), still evaluate the tuple
    ftypes = op isa Var ? Atom[] :
        filter(t -> is_function_type(t) && length(fn_arg_types(t)) == nargs, atom_types(op, space))
    if !isempty(ftypes)
        out = _STEP[]; errs = _STEP[]
        for f in ftypes
            te = type_check_errors(a, f::Expression, space)    # metta.md:384 check_argument_type → BadArgType
            if !isempty(te); for e in te; push!(errs, (e, type, b, true)); end; continue; end
            rt = fn_ret_type(f::Expression)
            rt == Sym("Expression") && (rt = UNDEF)     # metta.md:341 — don't treat Expression like Atom
            for (fa, fb) in interpret_function(a, f, space, b)   # arg-eval (recursive, bounded by nesting)
                (is_empty_atom(fa) || is_error_atom(fa)) ? push!(out, (fa, type, fb, true)) :
                    append!(out, metta_call_step(fa, rt, space, fb))
            end
        end
        !isempty(out) && return out                     # some type applied → its results
        !isempty(errs) && return errs                   # all types rejected the args → type errors
    end
    out = _STEP[]                                        # no applicable function type → untyped tuple
    for (t, tb) in interpret_tuple(a, space, b)
        (is_empty_atom(t) || is_error_atom(t)) ? push!(out, (t, type, tb, true)) :
            append!(out, metta_call_step(t, type, space, tb))
    end
    out
end

# interpret_function (metta.md:452): evaluate op, then the args by their declared types
function interpret_function(a::Expression, f::Expression, space::Space, b::Bindings)::Vector{_RESULT}
    op = a.children[1]; theargs = Atom[a.children[2:end]...]; ats = Atom[fn_arg_types(f)...]
    out = _RESULT[]
    for (h, hb) in _reduce(op, UNDEF, space, b)
        if is_empty_atom(h) || is_error_atom(h); push!(out, (h, hb)); continue; end
        for (targs, tb) in interpret_args(theargs, ats, space, hb)
            (is_empty_atom(targs) || is_error_atom(targs)) ? push!(out, (targs, tb)) :
                push!(out, (Expression(Atom[h; (targs::Expression).children]), tb))
        end
    end
    out
end

# interpret_args (metta.md:480): evaluate each arg with its expected type (Atom ⇒ unevaluated)
function interpret_args(theargs::Vector{Atom}, types::Vector{Atom}, space::Space, b::Bindings)::Vector{_RESULT}
    isempty(theargs) && return _RESULT[(Expression(Atom[]), b)]
    arg = theargs[1]; rest = Atom[theargs[2:end]...]
    atype = isempty(types) ? UNDEF : types[1]
    rtypes = isempty(types) ? Atom[] : Atom[types[2:end]...]
    out = _RESULT[]
    for (h, hb) in _reduce(arg, atype, space, b)
        if (is_empty_atom(h) || is_error_atom(h)) && h != arg; push!(out, (h, hb)); continue; end
        for (t, tb) in interpret_args(rest, rtypes, space, hb)
            (is_empty_atom(t) || is_error_atom(t)) ? push!(out, (t, tb)) :
                push!(out, (Expression(Atom[h; (t::Expression).children]), tb))
        end
    end
    out
end

# interpret_tuple (metta.md:358) — untyped fallback: evaluate every element, reassemble
function interpret_tuple(a::Atom, space::Space, b::Bindings)::Vector{_RESULT}
    (a isa Expression) || return _reduce(a, UNDEF, space, b)
    isempty(a.children) && return _RESULT[(a, b)]                       # () → ()
    head, tail = a.children[1], Expression(a.children[2:end])
    out = _RESULT[]
    for (h, hb) in _reduce(head, UNDEF, space, b)
        if is_empty_atom(h) || is_error_atom(h); push!(out, (h, hb)); continue; end
        for (t, tb) in interpret_tuple(tail, space, hb)
            (is_empty_atom(t) || is_error_atom(t)) ? push!(out, (t, tb)) :
                push!(out, (Expression(Atom[h; (t isa Expression ? t.children : Atom[t])]), tb))
        end
    end
    out
end

# metta_call (metta.md:509) as ONE rewrite — grounded → native, else → (= atom $X) query. Rewrite
# results are tagged "reduce again" (is_final=false) and re-fed by the loop; terminals are is_final=true.
function metta_call_step(a::Atom, type::Atom, space::Space, b::Bindings)::Vector{_STEP}
    a = subst(a, b)                                       # apply bindings before query/dispatch
    _METTA_DEBUG[] && println("metta_call: ", a)
    is_error_atom(a) && return _STEP[(a, type, b, true)]
    (a isa Expression && !isempty(a.children)) || return _STEP[(a, type, b, true)]
    op, opargs = a.children[1], a.children[2:end]
    op isa Var && return _STEP[(a, type, b, true)]       # variable-headed expr not reducible
    out = _STEP[]
    if is_executable(op)
        r = execute(op::Grounded, Atom[opargs...], space)
        if r isa ExecOk
            for (j, res) in enumerate(r.results)
                if j <= length(r.binds)
                    for mb in merge_bindings(b, r.binds[j]); push!(out, (res, type, mb, false)); end
                else
                    push!(out, (res, type, b, false))
                end
            end
        elseif r isa ExecNoReduce
            return _STEP[(a, type, b, true)]                             # not reducible → as-is
        else
            return _STEP[(error_atom(a, (r::ExecRuntime).msg), type, b, true)]
        end
    else
        X = freshvar("X")
        qres = query(space, Expression(Sym("="), a, X))
        reduced = false
        for qb in qres, mb in merge_bindings(b, qb)
            haskey(mb.var_to_slot, X) || continue        # resolve-filter (identical to Interpreter.jl :309)
            reduced = true
            push!(out, (subst(X, mb), type, mb, false))                 # rewrite result → reduce again
        end
        reduced || push!(out, (a, type, b, true))                       # no real rewrite survived → non-reducible
    end
    isempty(out) ? _STEP[(EMPTY, type, b, true)] : out
end

# ═══════════════════════════════════════════════════════════════════════════════
# Parser (metta.md §Syntax) — MeTTa text → typed Atom. Grounded atoms are built by a
# token registry (regex/string → constructor), exactly as the spec describes.
# ═══════════════════════════════════════════════════════════════════════════════
const TIMES  = _num_binop("*", *)
const DIVIDE = _num_binop("/", /)
const MOD    = _num_binop("%", %)
const GT = _num_cmp(">", >); const LE = _num_cmp("<=", <=); const GE = _num_cmp(">=", >=)
const EQ_OP = Grounded(Operation("==", xs ->
    length(xs) == 2 ? ExecOk(Atom[xs[1] == xs[2] ? Sym("True") : Sym("False")]) : ExecNoReduce()))
# Bool logic (grounded; True/False are symbols)
_to_bool(a::Atom) = a == Sym("True") ? true : a == Sym("False") ? false : nothing
function _bool_binop(name, f)
    Grounded(Operation(name, function (xs)
        length(xs) == 2 || return ExecNoReduce()
        x = _to_bool(xs[1]); y = _to_bool(xs[2])
        (x === nothing || y === nothing) ? ExecNoReduce() : ExecOk(Atom[f(x, y) ? Sym("True") : Sym("False")])
    end))
end
const AND = _bool_binop("and", &)
const OR  = _bool_binop("or", |)
const NOT = Grounded(Operation("not", xs -> (length(xs) == 1 && _to_bool(xs[1]) !== nothing) ?
    ExecOk(Atom[_to_bool(xs[1]) ? Sym("False") : Sym("True")]) : ExecNoReduce()))
const ID  = Grounded(Operation("id", xs -> length(xs) == 1 ? ExecOk(Atom[xs[1]]) : ExecNoReduce()))

# if-equal (grounded): then if a==b else else (branches returned UNevaluated)
const IF_EQUAL = Grounded(Operation("if-equal",
    xs -> length(xs) == 4 ? ExecOk(Atom[xs[1] == xs[2] ? xs[3] : xs[4]]) : ExecNoReduce()))

# structural helpers for atom-subst / sealed
_replace_var(a::Atom, v::Var, val::Atom) =
    a isa Var ? (a == v ? val : a) :
    a isa Expression ? Expression(Atom[_replace_var(c, v, val) for c in a.children]) : a
_rename_with(a::Atom, m::Dict{Var,Var}) =
    a isa Var ? get(m, a, a) :
    a isa Expression ? Expression(Atom[_rename_with(c, m) for c in a.children]) : a

# atom-subst (grounded): replace var (2nd) by value (1st) in template (3rd)
const ATOM_SUBST = Grounded(Operation("atom-subst", function (xs)
    (length(xs) == 3 && xs[2] isa Var) || return ExecNoReduce()
    ExecOk(Atom[_replace_var(xs[3], xs[2]::Var, xs[1])])
end))
# sealed (grounded): rename all vars in the expr to fresh ones EXCEPT the listed ones
# (spec: "replaces every var … except list of variables to ignore"). Local scoping.
function _seal_rename(a::Atom, ignore::Set{Var}, m::Dict{Var,Var})
    if a isa Var
        a in ignore && return a
        return get!(() -> freshvar(a.name), m, a)
    elseif a isa Expression
        return Expression(Atom[_seal_rename(c, ignore, m) for c in a.children])
    else
        return a
    end
end
const SEALED = Grounded(Operation("sealed", function (xs)
    (length(xs) == 2 && xs[1] isa Expression) || return ExecNoReduce()
    ignore = Set{Var}(v for v in xs[1].children if v isa Var)
    ExecOk(Atom[_seal_rename(xs[2], ignore, Dict{Var,Var}())])
end))
# size-atom / index-atom / get-metatype (grounded)
const SIZE_ATOM = Grounded(Operation("size-atom", xs ->
    (length(xs) == 1 && xs[1] isa Expression) ? ExecOk(Atom[Grounded(length(xs[1].children))]) : ExecNoReduce()))
const INDEX_ATOM = Grounded(Operation("index-atom", function (xs)
    (length(xs) == 2 && xs[1] isa Expression && xs[2] isa Grounded && xs[2].value isa Integer) || return ExecNoReduce()
    i = xs[2].value
    (0 <= i < length(xs[1].children)) ? ExecOk(Atom[xs[1].children[i+1]]) :
        ExecOk(Atom[Expression(ERROR, Expression(Sym("index-atom"), xs[1], xs[2]), Sym("IndexOutOfBounds"))])
end))
const GET_METATYPE = Grounded(Operation("get-metatype",
    xs -> length(xs) == 1 ? ExecOk(Atom[metatype_sym(xs[1])]) : ExecNoReduce()))

# assertEqual / assertEqualToResult / context-space (space-aware: they call the evaluator)
const UNIT = Expression(Atom[])     # () — unit; assert success
_assert_fail(name, a, b) = Expression(ERROR, Expression(Sym(name), a, b), Sym("AssertionFailed"))
const ASSERT_EQUAL = Grounded(SpaceOp("assertEqual", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    Set(metta_run(xs[1], space)) == Set(metta_run(xs[2], space)) ?
        ExecOk(Atom[UNIT]) : ExecOk(Atom[_assert_fail("assertEqual", xs[1], xs[2])])
end))
const ASSERT_EQUAL_TO_RESULT = Grounded(SpaceOp("assertEqualToResult", function (xs, space)
    (length(xs) == 2 && xs[2] isa Expression) || return ExecNoReduce()
    Set(metta_run(xs[1], space)) == Set(xs[2].children) ?
        ExecOk(Atom[UNIT]) : ExecOk(Atom[_assert_fail("assertEqualToResult", xs[1], xs[2])])
end))
# alpha-equality: canonicalize variables by first-encounter order so alpha-equivalent atoms compare
# equal (a freshly-renamed $t' from type-checking ≡ the literal $t in an expected result). hyperon's
# assertAlphaEqualToResult (stdlib.metta:1173) compares result sets up to variable renaming.
function _alpha_canon(a::Atom, m::Dict{Var,Int})
    if a isa Var
        return Var("\$α", UInt64(get!(m, a, length(m))))   # name+id determined purely by encounter order
    elseif a isa Expression
        return Expression(Atom[_alpha_canon(c, m) for c in a.children])
    else
        return a
    end
end
_alpha1(a::Atom) = _alpha_canon(a, Dict{Var,Int}())          # each atom canonicalized independently
# Multiset set ops on collapsed-list Expressions (hyperon atom.rs UniqueAtomOp/UnionAtomOp/
# IntersectionAtomOp/SubtractionAtomOp). Element identity = alpha-equivalence (via _alpha1). unique =
# dedup-keep-first; union = concat; intersection/subtraction = multiset min-multiplicity / difference.
const UNIQUE_ATOM = Grounded(Operation("unique-atom", function (xs::Vector{Atom})
    (length(xs) == 1 && xs[1] isa Expression) || return ExecNoReduce()
    seen = Set{Atom}(); out = Atom[]
    for c in xs[1].children; k = _alpha1(c); (k in seen) || (push!(seen, k); push!(out, c)); end
    ExecOk(Atom[Expression(out)])
end))
const UNION_ATOM = Grounded(Operation("union-atom", function (xs::Vector{Atom})
    (length(xs) == 2 && xs[1] isa Expression && xs[2] isa Expression) || return ExecNoReduce()
    ExecOk(Atom[Expression(Atom[xs[1].children; xs[2].children])])
end))
const INTERSECTION_ATOM = Grounded(Operation("intersection-atom", function (xs::Vector{Atom})
    (length(xs) == 2 && xs[1] isa Expression && xs[2] isa Expression) || return ExecNoReduce()
    cnt = Dict{Atom,Int}(); for c in xs[2].children; k = _alpha1(c); cnt[k] = get(cnt, k, 0) + 1; end
    out = Atom[]; for c in xs[1].children; k = _alpha1(c); (get(cnt, k, 0) > 0) && (push!(out, c); cnt[k] -= 1); end
    ExecOk(Atom[Expression(out)])
end))
const SUBTRACTION_ATOM = Grounded(Operation("subtraction-atom", function (xs::Vector{Atom})
    (length(xs) == 2 && xs[1] isa Expression && xs[2] isa Expression) || return ExecNoReduce()
    cnt = Dict{Atom,Int}(); for c in xs[2].children; k = _alpha1(c); cnt[k] = get(cnt, k, 0) + 1; end
    out = Atom[]; for c in xs[1].children; k = _alpha1(c); (get(cnt, k, 0) > 0) ? (cnt[k] -= 1) : push!(out, c); end
    ExecOk(Atom[Expression(out)])
end))
const ASSERT_ALPHA_EQUAL_TO_RESULT = Grounded(SpaceOp("assertAlphaEqualToResult", function (xs, space)
    (length(xs) == 2 && xs[2] isa Expression) || return ExecNoReduce()
    Set(_alpha1(x) for x in metta_run(xs[1], space)) == Set(_alpha1(x) for x in xs[2].children) ?
        ExecOk(Atom[UNIT]) : ExecOk(Atom[_assert_fail("assertAlphaEqualToResult", xs[1], xs[2])])
end))
# get-atoms (hyperon space.rs:127, type (-> Space Atom)): one result per atom of the space, variables
# freshened (make_variables_unique). NOTE: Core FLATTENS imported stdlib into &self rather than keeping
# it as a grounded child-space (hyperon's model), so `(get-atoms &self)` here returns the flattened rules
# — the f1 directive that expects an empty &self at start-up stays a documented known-gap.
const GET_ATOMS = Grounded(SpaceOp("get-atoms", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space
    own = @view tgt.atoms[(tgt.lib_count + 1):end]          # own atoms only — not the imported library
    ExecOk(Atom[rename_fresh(a, Dict{Var,Var}()) for a in own])
end))
const CONTEXT_SPACE = Grounded(SpaceOp("context-space", (xs, space) -> ExecOk(Atom[Grounded(space)])))
# all binding sets under which `pat` matches some atom of `space`, extending `b0`
function _match_pat(space::Space, pat::Atom, b0::Bindings)::Vector{Bindings}
    out = Bindings[]
    for atom in space.atoms, mb in match_atoms(subst(pat, b0), rename_fresh(atom, Dict{Var,Var}()))
        append!(out, merge_bindings(b0, mb))
    end
    out
end
# match (grounded): (match <space> <pattern> <template>). A `(, p1 p2 …)` pattern is a CONJUNCTION —
# all sub-patterns must match with consistent bindings (a join). Carries bindings to the caller.
const MATCH = Grounded(SpaceOp("match", function (xs, space)
    length(xs) == 3 || return ExecNoReduce()
    tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space  # named space or &self
    pat, tmpl = xs[2], xs[3]
    binds = Bindings[Bindings()]
    if pat isa Expression && !isempty(pat.children) && pat.children[1] == Sym(",")
        for p in pat.children[2:end]                        # conjunctive: thread bindings across patterns
            binds = Bindings[mb for r in binds for mb in _match_pat(tgt, p, r)]
        end
    else
        binds = _match_pat(tgt, pat, Bindings())
    end
    ExecOk(Atom[subst(tmpl, mb) for mb in binds], binds)
end))
# superpose (grounded): turn a tuple into a nondeterministic result (each child a separate result)
const SUPERPOSE = Grounded(Operation("superpose",
    xs -> (length(xs) == 1 && xs[1] isa Expression) ? ExecOk(collect(Atom, xs[1].children)) : ExecNoReduce()))
# collapse (grounded SpaceOp): collect all results of evaluating the arg into one tuple
const COLLAPSE = Grounded(SpaceOp("collapse", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    ExecOk(Atom[Expression(Atom[metta_run(xs[1], space)...])])
end))
# get-type (grounded SpaceOp): the type(s) of the argument
const GET_TYPE = Grounded(SpaceOp("get-type",
    (xs, space) -> length(xs) == 1 ? ExecOk(arg_actual_types(xs[1], space)) : ExecNoReduce()))
# foldl-atom (grounded SpaceOp): fold $op (using vars $a=accumulator, $b=item) over $list from $init
const FOLDL_ATOM = Grounded(SpaceOp("foldl-atom", function (xs, space)
    (length(xs) == 5 && xs[1] isa Expression && xs[3] isa Var && xs[4] isa Var) || return ExecNoReduce()
    list, acc, avar, bvar, op = xs[1], xs[2], xs[3], xs[4], xs[5]
    for item in list.children
        rs = metta_run(_replace_var(_replace_var(op, avar, acc), bvar, item), space)
        acc = isempty(rs) ? EMPTY : rs[1]
    end
    ExecOk(Atom[acc])
end))
# case (grounded SpaceOp): evaluate $atom, return the body of the first case pattern it matches
const CASE = Grounded(SpaceOp("case", function (xs, space)
    (length(xs) == 2 && xs[2] isa Expression) || return ExecNoReduce()
    results = metta_run(xs[1], space); isempty(results) && (results = Atom[Expression(Atom[])])  # Empty→()
    out = Atom[]; binds = Bindings[]
    for res in results, clause in xs[2].children
        (clause isa Expression && length(clause.children) == 2) || continue
        ms = match_atoms(clause.children[1], res)
        if !isempty(ms)
            push!(out, subst(clause.children[2], ms[1])); push!(binds, ms[1]); break
        end
    end
    ExecOk(out, binds)
end))

# ── State atoms (hyperon space.rs:55-122 / CeTTa eval.c:8323). new-state wraps a value + its
# (StateMonad T) type; get-state reads it; change-state! MUTATES the shared cell in place. No type-check
# inside change-state! — the generic checker emits (BadArgType 2 …) from its stdlib (-> (StateMonad $t)
# $t (StateMonad $t)) signature (matches space.rs: BadArgType comes from the interpreter, not the op).
const NEW_STATE = Grounded(SpaceOp("new-state", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    ts = arg_actual_types(xs[1], space)
    vt = isempty(ts) ? UNDEF : ts[1]
    ExecOk(Atom[Grounded(StateCell(xs[1], Expression(Sym("StateMonad"), vt)))])
end))
const GET_STATE = Grounded(Operation("get-state", function (xs::Vector{Atom})
    (length(xs) == 1 && xs[1] isa Grounded && xs[1].value isa StateCell) || return ExecNoReduce()
    ExecOk(Atom[(xs[1].value::StateCell).value])
end))
const CHANGE_STATE = Grounded(Operation("change-state!", function (xs::Vector{Atom})
    (length(xs) == 2 && xs[1] isa Grounded && xs[1].value isa StateCell) || return ExecNoReduce()
    (xs[1].value::StateCell).value = xs[2]      # mutate the shared cell in place (all refs see it)
    ExecOk(Atom[xs[1]])                          # return the state atom
end))
const NOP = Grounded(Operation("nop", (xs::Vector{Atom}) -> ExecOk(Atom[Expression(Atom[])])))  # arg reduced for effect → ()
# println! / trace! — hyperon debug ops (string.rs PrintlnOp `(-> %Undefined% (->))` / debug.rs TraceOp
# `(-> %Undefined% Atom %Undefined%)`). These are in HYPERON's stdlib (grounded), so they belong in
# Minimal's CORE grounded set, not CoreExtensions. println! evaluates its arg, prints it, returns unit;
# trace! prints arg0 (evaluated message), returns arg1 (Atom-typed = raw, then re-mettad by the driver).
_print_form(a::Atom) = (a isa Grounded && a.value isa AbstractString) ? a.value : string(a)
const PRINTLN_BANG = Grounded(Operation("println!", function (xs::Vector{Atom})
    length(xs) == 1 || return ExecNoReduce()
    println(_print_form(xs[1])); ExecOk(Atom[Expression(Atom[])])
end))
const TRACE_BANG = Grounded(Operation("trace!", function (xs::Vector{Atom})
    length(xs) == 2 || return ExecNoReduce()
    println(_print_form(xs[1])); ExecOk(Atom[xs[2]])
end))
# bind! (hyperon module.rs:250): register a token → atom in the space's token table. The parser
# substitutes the token in every SUBSEQUENT atom (parse-time, via the incremental load_metta! loop).
const BIND_TOKEN = Grounded(SpaceOp("bind!", function (xs, space)
    (length(xs) == 2 && xs[1] isa Sym) || return ExecNoReduce()
    space.tokens[(xs[1]::Sym).name] = xs[2]
    ExecOk(Atom[Expression(Atom[])])            # unit ()
end))
# Intrinsic state-op types (hyperon type_()): kept out of the space (see atom_types) so they don't
# break d4's `(match &self (: $impl (-> $cause $type)) …)` reasoning rule.
_GROUNDED_OP_TYPES[NEW_STATE]    = "(-> \$t (StateMonad \$t))"
_GROUNDED_OP_TYPES[GET_STATE]    = "(-> (StateMonad \$t) \$t)"
_GROUNDED_OP_TYPES[CHANGE_STATE] = "(-> (StateMonad \$t) \$t (StateMonad \$t))"

# ── Named spaces (hyperon: new-space / add-atom; `&self` = the current space). A space is a
# Grounded{Space}; `&self`/`&kb` resolve (parse-time tokens) to such a handle. add-atom/match take the
# space as their first arg and operate on it (falling back to the context space when it isn't a handle).
const NEW_SPACE = Grounded(Operation("new-space", (xs::Vector{Atom}) -> ExecOk(Atom[Grounded(Space())])))
const ADD_ATOM = Grounded(SpaceOp("add-atom", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space
    add_atom!(tgt, xs[2])
    ExecOk(Atom[Expression(Atom[])])             # unit ()
end))
const REMOVE_ATOM = Grounded(SpaceOp("remove-atom", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space
    remove_atom!(tgt, xs[2])
    ExecOk(Atom[Expression(Atom[])])
end))

# import! (hyperon): load module `<name>.metta` (found on the module search path). `(import! &kb mod)`
# loads it into a NEW space bound to the &kb token; `(import! &self mod)` loads it into the current space.
# Module search path for `import!`. Defaults to the two dirs that ship with the package — `src/standard/`
# (stdlib.metta, CoreExtensions.metta) and `lib/` (the algorithm modules: metamo, MOSES, pln, …) — so a
# fresh space can resolve `!(import! &self (library metamo))` with NO host setup. The host/REPL may still
# prepend extra dirs. While a module loads, its own directory is pushed (see `_load_module_file!`) so the
# module's relative `import!`s (e.g. metamo.metta's `(import! &self "config.metta")`) resolve self-contained.
const _MODULE_PATH = Ref(String[
    @__DIR__,                                              # src/standard/
    normpath(joinpath(@__DIR__, "..", "..", "lib")),      # <pkg>/lib/
])
# Load a module file into `sp`, with its containing dir on the search path for the duration so the module's
# own relative `import!`s resolve. try/finally keeps the global path balanced even if loading throws.
function _load_module_file!(sp, file::String)
    d = dirname(file)
    pushed = !(d in _MODULE_PATH[]); pushed && push!(_MODULE_PATH[], d)
    try load_metta!(sp, read(file, String)) finally pushed && filter!(!=(d), _MODULE_PATH[]) end
end
# module spec → name, accepting all the forms the reference impls take: a bare symbol (`f1_moduleA`),
# a string (hyperon's stated target form; PeTTa coerces via atom_string), or a `(library X)` spec
# (PeTTa/CeTTa). Cross-checked vs CeTTa eval.c resolve_import_destination + PeTTa metta.pl importer_helper.
function _import_modname(mod::Atom)::Union{String,Nothing}
    mod isa Sym && return mod.name
    mod isa Grounded && mod.value isa AbstractString && return mod.value
    if mod isa Expression && length(mod.children) == 2 && mod.children[1] == Sym("library")
        c = mod.children[2]
        c isa Sym && return c.name
        c isa Grounded && c.value isa AbstractString && return c.value
    end
    nothing
end
const IMPORT = Grounded(SpaceOp("import!", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    target, mod = xs[1], xs[2]
    modname = _import_modname(mod)
    modname === nothing && return ExecRuntime("import!: expects a module name (symbol, string, or (library X))")
    file = nothing
    for d in _MODULE_PATH[]
        # accept: an explicit/relative `<name>.metta` file, a bare `<name>`, or the `<name>/<name>.metta`
        # entry-in-dir convention Core's multi-file algorithm libs use (lib/metamo/metamo.metta).
        for cand in (modname, modname * ".metta", joinpath(modname, modname * ".metta"))
            p = isabspath(cand) ? cand : joinpath(d, cand); isfile(p) && (file = p; break)
        end
        file !== nothing && break
    end
    file === nothing && return ExecRuntime("import!: module not found: $modname")
    if target isa Grounded && target.value isa Space
        tgt = target.value::Space
        modname in tgt.imported && return ExecOk(Atom[Expression(Atom[])])  # already imported → ignore (dedup + cycle guard)
        push!(tgt.imported, modname)                            # record BEFORE loading (guards cycles)
        _load_module_file!(tgt, file)                           # &self: import into the current space
    elseif target isa Sym
        newsp = Space(); push!(newsp.imported, modname)
        _load_module_file!(newsp, file)
        space.tokens[(target::Sym).name] = Grounded(newsp)      # &kb: bind the token to a fresh space
    else
        return ExecRuntime("import!: first argument must be a space token")
    end
    ExecOk(Atom[Expression(Atom[])])
end))

# token registry: operator words → their grounded atoms (the tokenizer constructors)
const TOKEN_REGISTRY = Dict{String,Atom}(
    "+" => PLUS, "-" => MINUS, "*" => TIMES, "/" => DIVIDE, "%" => MOD,
    "<" => LT, ">" => GT, "<=" => LE, ">=" => GE, "==" => EQ_OP,
    "and" => AND, "or" => OR, "not" => NOT, "id" => ID,
    "if-equal" => IF_EQUAL, "atom-subst" => ATOM_SUBST, "sealed" => SEALED,
    "size-atom" => SIZE_ATOM, "index-atom" => INDEX_ATOM, "get-metatype" => GET_METATYPE,
    "assertEqual" => ASSERT_EQUAL, "assertEqualToResult" => ASSERT_EQUAL_TO_RESULT,
    "assertAlphaEqualToResult" => ASSERT_ALPHA_EQUAL_TO_RESULT, "get-atoms" => GET_ATOMS,
    "context-space" => CONTEXT_SPACE, "match" => MATCH,
    "superpose" => SUPERPOSE, "collapse" => COLLAPSE,
    "unique-atom" => UNIQUE_ATOM, "union-atom" => UNION_ATOM,
    "intersection-atom" => INTERSECTION_ATOM, "subtraction-atom" => SUBTRACTION_ATOM,
    "get-type" => GET_TYPE, "foldl-atom" => FOLDL_ATOM, "case" => CASE,
    "new-state" => NEW_STATE, "get-state" => GET_STATE, "change-state!" => CHANGE_STATE, "nop" => NOP,
    "println!" => PRINTLN_BANG, "trace!" => TRACE_BANG,
    "bind!" => BIND_TOKEN, "new-space" => NEW_SPACE, "add-atom" => ADD_ATOM, "remove-atom" => REMOVE_ATOM,
    "import!" => IMPORT)
# add-atom/remove-atom take the atom UNEVALUATED (hyperon AddAtomOp type_ = (-> Space Atom (->))) — the
# atom is stored as-is, not reduced. Atom-typed 2nd arg ⇒ the driver passes it unevaluated. Intrinsic
# (kept out of the space). Defined here, after the ops exist.
_GROUNDED_OP_TYPES[ADD_ATOM]    = "(-> %Undefined% Atom (->))"
_GROUNDED_OP_TYPES[REMOVE_ATOM] = "(-> %Undefined% Atom (->))"
_GROUNDED_OP_TYPES[TRACE_BANG]  = "(-> %Undefined% Atom %Undefined%)"   # arg1 raw so (trace! msg (quote …)) works
# == is polymorphic same-type (hyperon (-> $t $t Bool)) → the checker emits (BadArgType 2 …) on a
# mismatch like (== 5 "S"). Now safe: the iterative driver doesn't overflow on the typed path (this
# crashed the recursive driver). Intrinsic (out of the space, can't disturb match &self).
_GROUNDED_OP_TYPES[EQ_OP]       = "(-> \$t \$t Bool)"

function tokenize(s::AbstractString)::Vector{String}
    cs = collect(s); n = length(cs); toks = String[]; i = 1
    while i <= n
        c = cs[i]
        if isspace(c); i += 1
        elseif c == ';'; while i <= n && cs[i] != '\n'; i += 1; end
        elseif c == '(' || c == ')'; push!(toks, string(c)); i += 1
        elseif c == '"'
            i += 1; buf = Char[]
            while i <= n && cs[i] != '"'
                if cs[i] == '\\' && i < n                   # decode escapes (hyperon text.rs:550-573):
                    i += 1; d = cs[i]                        #   \n \t \r → control char; \" \\ \' → literal
                    push!(buf, d == 'n' ? '\n' : d == 't' ? '\t' : d == 'r' ? '\r' : d)
                else
                    push!(buf, cs[i])
                end
                i += 1
            end
            i += 1
            push!(toks, "\"" * String(buf))                # leading-quote marks a string token
        else
            j = i
            while j <= n && !isspace(cs[j]) && cs[j] != '(' && cs[j] != ')' && cs[j] != ';'; j += 1; end
            push!(toks, String(cs[i:j-1])); i = j
        end
    end
    toks
end

function parse_atom(tok::String, tokens::Dict{String,Atom}=_NO_TOKENS)::Atom
    startswith(tok, "\"") && return Grounded(tok[nextind(tok, 1):end])      # string
    startswith(tok, "\$") && return Var(tok[nextind(tok, 1):end])           # variable
    haskey(tokens, tok) && return tokens[tok]                              # bind! token (parse-time subst)
    haskey(TOKEN_REGISTRY, tok) && return TOKEN_REGISTRY[tok]               # grounded operator
    let n = tryparse(Int, tok); n !== nothing && return Grounded(n); end     # integer
    let f = tryparse(Float64, tok); f !== nothing && return Grounded(f); end # float
    Sym(tok)
end
const _NO_TOKENS = Dict{String,Atom}()

function parse_from(toks::Vector{String}, i::Base.RefValue{Int}, tokens::Dict{String,Atom}=_NO_TOKENS)::Atom
    tok = toks[i[]]
    if tok == "("
        i[] += 1; ch = Atom[]
        while i[] <= length(toks) && toks[i[]] != ")"; push!(ch, parse_from(toks, i, tokens)); end
        i[] <= length(toks) && (i[] += 1)
        return Expression(ch)
    else
        i[] += 1; return parse_atom(tok, tokens)
    end
end

"Parse a MeTTa program into (is_directive, atom) pairs (`!` at top level = directive)."
function parse_program(text::AbstractString)::Vector{Tuple{Bool,Atom}}
    toks = tokenize(text); i = Ref(1); out = Tuple{Bool,Atom}[]
    while i[] <= length(toks)
        directive = false
        toks[i[]] == "!" && (directive = true; i[] += 1)
        i[] > length(toks) && break
        push!(out, (directive, parse_from(toks, i)))
    end
    out
end

"""Load MeTTa text into `space`: add definitions/data, run `!`-directives; return directive results.
INCREMENTAL parse-eval (hyperon/CeTTa Tokenizer model): each atom is parsed THEN evaluated before the
next is parsed, so a `bind!` directive registers its token in `space.tokens` in time for the parser to
substitute that token in every following atom (parse-time substitution)."""
function load_metta!(space::Space, text::AbstractString; as_library::Bool=false)::Vector{Atom}
    get!(space.tokens, "&self", Grounded(space))    # `&self` (parse-time) resolves to the current space
    results = Atom[]; toks = tokenize(text); i = Ref(1)
    while i[] <= length(toks)
        directive = false
        toks[i[]] == "!" && (directive = true; i[] += 1)
        i[] > length(toks) && break
        atom = parse_from(toks, i, space.tokens)        # substitute bound tokens at parse time
        directive ? append!(results, metta_run(atom, space)) : add_atom!(space, atom)
    end
    # mark everything loaded so far as imported-library content, hidden from `get-atoms` (hyperon: a
    # dependency lives in a child space and is not returned by get-atoms of the importing space).
    as_library && (space.lib_count = length(space.atoms))
    results
end

# Load the Core MeTTa stdlib into `space` (as library content, hidden from get-atoms): the hyperon-faithful
# stdlib.metta PLUS CoreExtensions.metta (Core-convention MeTTa-rule helpers like `member` that aren't in
# hyperon's stdlib). The 234/234 conformance matrix must stay green with CoreExtensions.metta loaded.
function load_core_stdlib!(space::Space)
    load_metta!(space, read(joinpath(@__DIR__, "stdlib.metta"), String); as_library=true)
    load_metta!(space, read(joinpath(@__DIR__, "CoreExtensions.metta"), String); as_library=true)
    space
end

# ── Core grounded extensions (additive; NOT part of the hyperon-faithful core) ──
include("CoreExtensions.jl")
include("CoreNumericOps.jl")   # MeTTa↔Julia numeric adapter (numpy-equivalent grounded ops)
include("CoreMathOps.jl")      # hyperon math library (sqrt/pow/log/trig/…) as grounded ops

# ── Precompile workload ───────────────────────────────────────────────────────
# The evaluator's hot methods (parse → load_metta! → metta_run → interpret/match/subst over the Atom
# union + _STEP/_RESULT tuples) compile lazily on first call — ~21s of cold-start latency paid on every
# fresh `julia` test process. Running a representative eval HERE, during precompilation, traces those
# specializations into the package image so cold test/CI starts warm. Defensive: a workload error must
# never break the build, so the whole region is guarded.
using PrecompileTools: @setup_workload, @compile_workload
@setup_workload begin
    stdlib = try read(joinpath(@__DIR__, "stdlib.metta"), String) catch; ""; end
    @compile_workload begin
        try
            sp = Space(); isempty(stdlib) || load_metta!(sp, stdlib)
            # arithmetic / comparison / Bool — grounded dispatch
            load_metta!(sp, "!(+ 1 (* 2 3))")
            load_metta!(sp, "!(if (and (< 1 2) (not False)) yes no)")
            # let / let* — chain/decons-atom/unify hygiene
            load_metta!(sp, "!(let* ((\$x 5) (\$y (* \$x 2))) (+ \$x \$y))")
            # list ops — car/cdr/map/filter/foldl over the Expression path
            load_metta!(sp, "!(map-atom (1 2 3) \$v (eval (+ \$v 1)))")
            load_metta!(sp, "!(filter-atom (1 2 3 4) \$v (eval (> \$v 2)))")
            load_metta!(sp, "!(foldl-atom (1 2 3 4) 0 \$a \$b (+ \$a \$b))")
            load_metta!(sp, "!(case 2 ((1 one) (2 two)))")
            # rule rewrite + match + get-type (query path, binding propagation, type lookup)
            load_metta!(sp, "(= (f \$x) (g \$x))")
            load_metta!(sp, "!(f 42)")
            load_metta!(sp, "(rel a b)")
            load_metta!(sp, "!(match &self (rel \$x b) \$x)")
            load_metta!(sp, "!(get-type 5)")
            # type-checking → BadArgType, and nondeterminism → superpose/collapse
            load_metta!(sp, "!(+ 1 foo)")
            load_metta!(sp, "!(collapse (superpose (1 2 3)))")
        catch
        end
    end
end

end # module
