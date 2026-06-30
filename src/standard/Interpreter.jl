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
export interpret_max_steps!, metta_max_steps!

# instruction symbols
const EVAL = Sym("eval"); const EVALC = Sym("evalc"); const CHAIN = Sym("chain")
const FUNCTION = Sym("function"); const RETURN = Sym("return"); const UNIFY = Sym("unify")
const CONS = Sym("cons-atom"); const DECONS = Sym("decons-atom")
const COLLAPSE_BIND = Sym("collapse-bind"); const SUPERPOSE_BIND = Sym("superpose-bind")
const EMPTY = Sym("Empty"); const NOT_REDUCIBLE = Sym("NotReducible"); const ERROR = Sym("Error")
const MINIMAL_OPS = Set(Symbol[ Symbol("eval"),Symbol("evalc"),Symbol("chain"),Symbol("function"),Symbol("unify"),
                                 Symbol("cons-atom"),Symbol("decons-atom"),Symbol("collapse-bind"),Symbol("superpose-bind") ])

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
                     (a.children[1]::Sym).name : Symbol("")
is_minimal_op(a::Atom) = head_name(a) in MINIMAL_OPS
args(a::Expression) = a.children[2:end]

# hyperon/CeTTa store the error message as a grounded String (not a symbol) — Expression(ERROR, a, "msg").
# Matches the parsed string-literal form so error-asserting tests gate exactly; if-error etc. match the
# Error HEAD so control flow is unaffected. See docs/STDLIB_FAITHFULNESS_REFERENCE.md (ERROR REPRESENTATION).
error_atom(a::Atom, msg::AbstractString) = Expression(ERROR, a, Grounded(String(msg)))

# canonical representative of a var's equality class (smallest id, then name) — used when the slot has
# no value but the var is equal to another (formal-arg = actual-arg matches as $a=$b). Min-rooted
# forwarding keeps the root == the (id,name)-minimum of the class, so this is just canonical_var.
_slot_rep(b::Bindings, v::Var) = canonical_var(b, v)

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
        # structural sharing (same pattern as rename_fresh; mirrors hyperon apply_bindings_to_atom's
        # `updated` flag in Core's immutable model): rebuild ONLY subtrees that actually changed. An
        # Expression with no bound var inside returns the SAME object → zero allocation (was: rebuild every
        # node every call — the top materialization allocator). Identity-safe: subst returns the input var
        # object for unbound vars (rep == a ? a : rep), so `!==` means a real substitution occurred.
        kids = a.children
        newkids = nothing                       # allocate lazily, only on first changed child
        for i in eachindex(kids)
            sc = subst(kids[i], b, d + 1)
            if sc !== kids[i]
                newkids === nothing && (newkids = copy(kids))
                newkids[i] = sc
            end
        end
        return newkids === nothing ? a : Expression(newkids)
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

# Finished frames never use `.vars` for membership (only pending frames are narrowed against), and
# `.vars` is never mutated after construction (verified: read-only at narrow_bindings + _cumvars) — so
# all finished frames SHARE one immutable empty set instead of allocating Set{Var}() per result. This
# was a top per-step allocator on deep proof search (finished_result fires on every reduction result).
const EMPTY_VARS = Set{Var}()

# finished_result (interpreter.rs:474): a finished frame holding `atom`, linked to `prev`
finished_result(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}) =
    Tuple{Frame,Bindings}[(Frame(atom, EMPTY_VARS, prev, no_handler, true, 0), b)]

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
    # group present vars by equality-class root, flag any dead (forwarding model: enumerate every var
    # appearing as a source OR a forwarding target — the analog of the old `for (v,s) in var_to_slot`).
    # FLAT scratch (measured on obc: ≤11 roots, ≤28 seen per call) — parallel Vectors + linear lookup
    # replace Dict{Var,Vector{Var}}+Set{Var}: cheaper than hashing at these sizes and far less alloc per
    # step. `live` stays a Set (membership target, up to ~113 — a linear scan there WOULD regress).
    seen = Var[]; roots = Var[]; groups = Vector{Var}[]
    any_drop = false
    @inbounds for e in b.entries
        for v in (e.val isa Var ? (e.var, e.val::Var) : (e.var,))
            v in seen && continue; push!(seen, v)
            if v in live
                r = canonical_var(b, v)
                idx = 0
                for j in eachindex(roots); roots[j] == r && (idx = j; break); end
                idx == 0 ? (push!(roots, r); push!(groups, Var[v])) : push!(groups[idx], v)
            else
                any_drop = true
            end
        end
    end
    any_drop || return b                                   # nothing dead → no allocation (fast path)
    nb = Bindings()
    @inbounds for k in eachindex(roots)
        root = roots[k]; vars = groups[k]
        val = resolve(b, root)
        if val === nothing
            length(vars) < 2 && continue                   # lone value-less var ≡ unbound → drop
            v1 = vars[1]
            for i in 2:length(vars)                        # re-root the equality among the LIVE vars
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
# When the atom introduces NO var the parent doesn't already have, SHARE the parent's set instead of
# deep-copying it (Set `union!` is O(n); the set is immutable/read-only — verified: only read in
# narrow_bindings + here, never mutated). This is the O(1)-clone case hyperon gets free from im::HashSet;
# it avoids the per-frame copy of the ≤113-var cumulative set.
function _cumvars(prev::Union{Frame,Nothing}, atom::Atom)::Set{Var}
    prev === nothing && return collect_vars(atom)
    pv = prev.vars
    _atom_introduces_var(atom, pv) || return pv
    union!(collect_vars(atom), pv)
end

# does `a` contain any Var not already in `pv`? walks the atom WITHOUT allocating its var set
function _atom_introduces_var(a::Atom, pv::Set{Var})::Bool
    a isa Var && return !(a in pv)
    if a isa Expression
        @inbounds for c in a.children
            _atom_introduces_var(c, pv) && return true
        end
    end
    return false
end

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
    if name === Symbol("cons-atom");    return cons_atom(f, b)
    elseif name === Symbol("decons-atom"); return decons_atom(f, b)
    elseif name === Symbol("unify");    return unify_op(f, b)
    elseif name === Symbol("eval");     return eval_op(f, b, space)
    elseif name === Symbol("evalc");    return evalc_op(f, b, space)
    elseif name === Symbol("chain") && rule_enabled("HES_Chain"); return setup_chain(f.atom, b, f.prev, f.depth)
    elseif name === Symbol("function"); return setup_function(f.atom, b, f.prev, f.depth)
    elseif name === Symbol("collapse-bind");  return collapse_bind_op(f, b, space)
    elseif name === Symbol("superpose-bind"); return superpose_bind_op(f, b, space)
    elseif name === Symbol("metta");            return metta_instr(f, b, space)            # metta driver (stack-machine)
    elseif name === Symbol("interpret-tuple");  return interpret_tuple_instr(f, b, space)
    elseif name === Symbol("interpret-function"); return interpret_function_instr(f, b, space)
    elseif name === Symbol("interpret-args");   return interpret_args_instr(f, b, space)
    elseif name === Symbol("metta-call");       return metta_call_instr(f, b, space)
    elseif name === Symbol("return-on-error");  return return_on_error_instr(f, b)
    elseif name === Symbol("args-cont");        return args_cont_instr(f, b)
    elseif name === Symbol("metta-noreduce");   return metta_noreduce_instr(f, b)        # NotReducible backstop
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
    index::Dict{Tuple{Symbol,Symbol},Vector{Atom}}
    wildcard::Vector{Atom}
end
Space() = Space(Atom[], Dict{String,Atom}(), Set{String}(), 0, Dict{Tuple{Symbol,Symbol},Vector{Atom}}(), Atom[])
Space(atoms::Vector{Atom}) = (s = Space(); for a in atoms; add_atom!(s, a); end; s)
# Bounded display: a Space embedded in a result/error atom (e.g. `&self` passed as an argument to an
# undefined op, which then echoes back) must NOT dump its entire atom list — the default struct show
# recurses the whole KB and stack-overflows the REPL render. Core is single-flattened-space, so a grounded
# Space displays as `&self` (matches hyperon's output for the self space).
Base.show(io::IO, ::Space) = print(io, "&self")

# discriminant head of an atom-position: a Sym's name, or an Expression's Sym head; else nothing.
_idx_head(x::Atom)::Union{Symbol,Nothing} =
    x isa Sym ? x.name :
    (x isa Expression && !isempty(x.children) && x.children[1] isa Sym) ? (x.children[1]::Sym).name :
    nothing
# (outer-head, 2nd-child-head) discriminant; nothing ⇒ not indexable ⇒ wildcard bucket.
function _index_key(a::Atom)::Union{Tuple{Symbol,Symbol},Nothing}
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
# Structural sharing: a ground subtree (no Var) has nothing to rename, so we return the SAME
# immutable atom instead of rebuilding it — eliminates the per-stored-atom Expression+array
# allocation on the match hot path (Profile: rename_fresh was a top self-time frame; ground data
# atoms are the common case). A fresh Expression is allocated only along paths where a Var actually
# changed. Safe because atoms are immutable and ground atoms carry no variable that could clash.
# small flat var-map: a Vector{Pair} avoids Dict's hash-table + bucket allocation (Profile re-attribution
# on `9c27b1a`: the per-stored-rule `Dict{Var,Var}()` was the #1 alloc + self-time site). Stored rules carry
# ~1-2 vars, so a linear `===`-scan beats both hashing and a `==` string-compare. INVARIANT: repeated
# occurrences of a var in an atom flowing through eval are the SAME object — the parser interns vars per
# parse (verified `$x===$x`), `freshvar` mints one object per key, and `subst` returns the input var object
# for unbound vars, so identity is preserved end-to-end. (A `==` scan would also be correct, but identity is
# already guaranteed, making `===` both safe and ~free.)
const VarRenameMap = Vector{Pair{Var,Var}}
function _rename_get!(m::VarRenameMap, v::Var)::Var
    @inbounds for i in eachindex(m)
        m[i].first === v && return m[i].second
    end
    fv = freshvar(v.name); push!(m, v => fv); fv
end

function rename_fresh(a::Atom, m::VarRenameMap=VarRenameMap(), d::Int=0)
    d > _MAX_ATOM_DEPTH && return a
    if a isa Var
        return _rename_get!(m, a)
    elseif a isa Expression
        kids = a.children
        newkids = nothing                       # allocate lazily, only on first changed child
        for i in eachindex(kids)
            rc = rename_fresh(kids[i], m, d + 1)
            if rc !== kids[i]
                newkids === nothing && (newkids = copy(kids))
                newkids[i] = rc
            end
        end
        return newkids === nothing ? a : Expression(newkids)   # share `a` if no Var was renamed
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
            append!(out, match_atoms(pattern, rename_fresh(stored)))
        end
        return out
    end
    b = get(space.index, k, nothing)                   # same-discriminant atoms — the (= (f …) …) rules for this f
    if b !== nothing
        for stored in b
            append!(out, match_atoms(pattern, rename_fresh(stored)))
        end
    end
    for stored in space.wildcard                       # + var-headed atoms, which can match any discriminant
        append!(out, match_atoms(pattern, rename_fresh(stored)))
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
            # `is_present` NOT `resolve===nothing`: Core's resolve also returns nothing for X equated to a
            # var (no value), but those (e.g. `(= (id $x) $x)` → a var) are LEGIT and must be KEPT. (See :564, :883.)
            is_present(mb, X) || continue
            x = subst(X, mb)
            append!(out, eval_result(x, mb, f.prev, f.depth + 1))
        end
        return isempty(out) ? finished_result(NOT_REDUCIBLE, b, f.prev) : out
    end
end

# evalc — evaluate the body in the supplied space context. For the in-self (&self) case (the only one
# Core's libs use) that is the current interpreter space, so delegate to eval's logic on (eval <body>).
# evalc was in MINIMAL_OPS with NO dispatch branch, so a bare (evalc …) was re-fed to the interpreter
# loop until the step ceiling — a hang on trivial input vs hyperon/CeTTa's 7. (2026-06-30; matches both.)
function evalc_op(f::Frame, b::Bindings, space)
    a = f.atom
    (a isa Expression && length(a.children) == 3) ||
        return finished_result(error_atom(a, "expected (evalc <atom> <space>)"), b, f.prev)
    f.atom = Expression(EVAL, a.children[2])   # (evalc body space) → (eval body); same frame + continuation
    return eval_op(f, b, space)
end

# ── pushing nested computations + continuations (chain / function) ────────────
# Idiomatic Julia: continuations are CLOSURES stored in Frame.ret (no Rust mem::swap /
# Rc<RefCell> placeholder dance). A frame's ret runs when the child it pushed finishes;
# ret returns a single (Frame,Bindings) to continue, or nothing to drop. Fan-out is
# preserved because a fanned-out child yields several finished frames, each firing ret.

# set up `atom` to be evaluated (interpreter.rs atom_to_stack:640)
function push_nested(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)::Vector{Tuple{Frame,Bindings}}
    name = head_name(atom)
    if name === Symbol("chain") && rule_enabled("HES_Chain"); return setup_chain(atom, b, prev, depth)
    elseif name === Symbol("function"); return setup_function(atom, b, prev, depth)
    else;                      return [(Frame(atom, _cumvars(prev, atom), prev, no_handler, false, depth), b)]
    end
end

# function-special-when-returned (interpreter.rs eval_result:559): a returned `function`
# op is set up (looped), not treated as data.
function eval_result(res::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)
    head_name(res) === Symbol("function") ? setup_function(res, b, prev, depth) : finished_result(res, b, prev)
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
            return (Frame(result.children[2], EMPTY_VARS, self.prev, no_handler, true, depth), rb)  # return x
        elseif is_minimal_op(result)
            pushed = push_nested(result, rb, self, depth + 1)                                        # loop
            isempty(pushed) ? nothing : pushed[1]
        else
            return (Frame(error_atom(atom, "NoReturn"), EMPTY_VARS, self.prev, no_handler, true, depth), rb)
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
# ═══════════════════════════════════════════════════════════════════════════════
# SLG VARIANT TABLING (opt-in; default OFF) — SWI-Prolog §7.1 memoisation in the top-down interpreter.
# `table!(head)` marks a predicate tabled; a tabled goal's FULLY-REDUCED answer set is computed ONCE and
# replayed on every variant re-call, turning exponential recomputation (fib) into linear. The interpreter is
# already a CPS stack machine, so this rides the existing nested-`interpret` pattern (cf. collapse_bind_op).
#   DEFAULT-OFF GUARANTEE: with no head registered the hook in metta_instr is always false ⇒ the 234
#   conformance reduction path is byte-identical by construction (the disable-to-prove pattern).
#   SCOPE: memoisation only. A left-recursive goal that re-enters an IN-PROGRESS variant falls through to
#   normal reduction (no suspend-on-variant yet — that needs the worklist/dynamic-SCC completion machinery;
#   §7.2). Handles the fib/ackermann class. Variant key = the substituted goal (ground ⇒ identity; non-ground
#   canonicalization is TODO). Table is global+session-scoped; cleared by table!/untable_all! (TODO: per-space
#   + IDG invalidation on space mutation, §7.7).
const _TABLED_HEADS = Set{Symbol}()
const _ANSWER_TABLE = Dict{Atom,Vector{Atom}}()
const _TABLE_INPROG = Set{Atom}()
const _PARTIAL = Dict{Atom,Vector{Atom}}()   # a leader's accumulating answer set during completion
const _PARTIAL_READ = Set{Atom}()            # tabled keys whose partials a consumer read ⇒ self-recursive
const _GEN_STACK = Atom[]                     # in-progress leaders (generators), in call order
const _COMPONENT = Dict{Atom,Atom}()          # key → SCC root (union-find; merged on a cross-leader cycle)
_table_reset!() = (empty!(_ANSWER_TABLE); empty!(_TABLE_INPROG); empty!(_PARTIAL); empty!(_PARTIAL_READ);
                   empty!(_GEN_STACK); empty!(_COMPONENT))
_scc_root(k::Atom)::Atom = (r = get(_COMPONENT, k, k); r == k ? k : (_COMPONENT[k] = _scc_root(r)))
"Mark predicate `head` (a Symbol) for tabled (memoised) execution; clears the answer table."
table!(head::Symbol) = (push!(_TABLED_HEADS, head); _table_reset!(); nothing)
"Disable all tabling and clear the answer table."
untable_all!() = (empty!(_TABLED_HEADS); _table_reset!(); nothing)
@inline is_tabled(atom::Atom)::Bool = !isempty(_TABLED_HEADS) && head_name(atom) in _TABLED_HEADS
# MeTTa surface for the directive (the analog of SWI `:- table fib/1`): `!(table! fib)` marks the `fib`
# predicate tabled, so a program/server enables tabling without a Julia call. Registered in TOKEN_REGISTRY.
const TABLE_DECL = Grounded(Operation("table!", xs ->
    (length(xs) == 1 && xs[1] isa Sym) ?
        (table!((xs[1]::Sym).name); ExecOk(Atom[Expression(Atom[])])) : ExecNoReduce()))

_replay(answers::Vector{Atom}, b::Bindings, prev) =
    isempty(answers) ? finished_result(EMPTY, b, prev) :
    reduce(vcat, (finished_result(ans, b, prev) for ans in answers))

# Canonicalize a tabled goal to its VARIANT KEY. Cross-checked vs SWI-Prolog boot/tabling.pl `start_tabling`
# + the C `$tbl_variant_table`: SWI variant-matches the goal up to variable RENAMING and does NOT reduce
# args (Prolog's is/2 pre-evaluates them before the call). MeTTa nests the arithmetic IN the goal
# (`(fib (- n 1))`) with no is/2-before-call split, so we (a) REDUCE the args — the MeTTa analog of Prolog's
# pre-call arg eval — then (b) RENAME vars by first occurrence (= SWI's variant canonicalization). Result:
# `(fib (- 20 2))` and `(fib (- 19 1))` both key to `(fib 18)` (halves the table → O(n)), and `(fib $x)` /
# `(fib $y)` share one table.
function _variant_rename(a::Atom)::Atom
    seen = Dict{Var,Var}(); n = Ref(0)
    rn(x::Atom) = x isa Var ? get!(() -> (n[] += 1; Var("_v", UInt64(n[]))), seen, x) :
                  (x isa Expression ? Expression(Atom[rn(c) for c in x.children]) : x)
    rn(a)
end
function _canonical_goal(atom::Atom, space, b::Bindings)::Atom
    g = subst(atom, b)
    (g isa Expression && !isempty(g.children)) || return _variant_rename(g)
    rargs = Atom[c isa Var ? c : (rs = metta_run(c, space); isempty(rs) ? c : rs[1]) for c in g.children[2:end]]
    _variant_rename(Expression(Atom[g.children[1]; rargs]))
end

# Suspend-on-variant via NAIVE FIXPOINT — the simplification of SWI completion (boot/tabling.pl
# run_leader/`completion` resumes a delimited continuation off a worklist; we re-run the leader pass instead:
# correct for a single SCC, no continuation machinery). A tabled goal is the LEADER of its variant; a re-entry
# of an IN-PROGRESS variant is a CONSUMER that reads the leader's PARTIAL answers — so left-recursion SUSPENDS
# (returns partials) instead of looping. A leader that no consumer re-read (fib) finishes in ONE pass.
#   SCOPE: single self-recursive SCC, naive (re-derives each round, not semi-naive), ground/enumerable answer
#   atoms. No mutual-SCC merging (SWI's dynamic SCC), no WFS negation (§7.6), no answer subsumption (§7.3).

# One resolution pass for the leader: apply key's `(= key body)` rules and reduce each body. A recursive
# sub-call to an in-progress variant hits the hook → consumer → reads partials. Returns this pass's answers.
function _leader_pass(key::Atom, typ::Atom, space::Space)::Vector{Atom}
    out = Atom[]; X = freshvar("X")
    for qb in query(space, Expression(Sym("="), key, X)), mb in merge_bindings(Bindings(), qb)
        is_present(mb, X) || continue
        for (at, bnd) in interpret(_metta(subst(X, mb), typ), space, mb)
            is_empty_atom(at) || push!(out, subst(at, bnd))
        end
    end
    unique(out)
end

# Dynamic-SCC completion — the SOUNDNESS extension over single-goal suspend. SWI completes an ENTIRE SCC
# together (boot/tabling.pl `completion` → `$tbl_table_complete_all(SCC)`); finalising one goal before a
# mutually-dependent partner makes the partner's table unsound. We track the in-progress GENERATOR stack
# (_GEN_STACK) + a union-find of SCC roots (_COMPONENT): when a CONSUMER re-enters a goal that is an ANCESTOR
# on the stack (a cross-leader cycle), every generator from that ancestor up is unioned into one component.
# The component ROOT drives a joint naive fixpoint over ALL members and completes them together; a non-root
# member is a FOLLOWER that returns its partials and stays in-progress for the root to finish. A lone,
# non-self-recursive goal (fib) is a singleton root ⇒ ONE pass (no regression). SCOPE caveats unchanged:
# naive (not semi-naive), no WFS tnot (§7.6), no answer subsumption (§7.3), ground/enumerable answer atoms.
function tabled_eval(atom::Atom, typ::Atom, space::Space, b::Bindings, prev)
    key = _canonical_goal(atom, space, b)
    haskey(_ANSWER_TABLE, key) && return _replay(_ANSWER_TABLE[key], b, prev)    # complete ⇒ replay
    if key in _TABLE_INPROG                                                       # CONSUMER (variant re-entry):
        push!(_PARTIAL_READ, key)                                                #   flag self-recursion,
        ki = findfirst(g -> g == key, _GEN_STACK)                                #   union key..top into one SCC
        if ki !== nothing
            root = _scc_root(key)
            for j in ki+1:length(_GEN_STACK)
                _COMPONENT[_scc_root(_GEN_STACK[j])] = root
            end
        end
        return _replay(get(_PARTIAL, key, Atom[]), b, prev)                      #   answer from partials (suspend)
    end
    push!(_TABLE_INPROG, key); push!(_GEN_STACK, key)                            # become a GENERATOR
    _PARTIAL[key] = Atom[]; _COMPONENT[key] = key; delete!(_PARTIAL_READ, key)
    local ans::Vector{Atom} = Atom[]
    try
        _PARTIAL[key] = _leader_pass(key, typ, space)                           # initial pass (may merge me up)
        if _scc_root(key) != key                                                 # I became a FOLLOWER ⇒
            return _replay(_PARTIAL[key], b, prev)                              #   ancestor root finishes me
        end
        comp() = Atom[g for g in _GEN_STACK if _scc_root(g) == key]            # I am the ROOT: my SCC members
        members = comp()
        if !(length(members) == 1 && !(key in _PARTIAL_READ))                    # singleton+no self-rec ⇒ 1 pass
            while true                                                           # joint naive fixpoint over SCC
                grew = false
                for m in members
                    np = _leader_pass(m, typ, space); n0 = length(_PARTIAL[m])
                    _PARTIAL[m] = unique(vcat(_PARTIAL[m], np))
                    length(_PARTIAL[m]) != n0 && (grew = true)
                end
                grew || break
                members = comp()                                                # component may have grown
            end
        end
        ans = _PARTIAL[key]
        for m in comp(); _ANSWER_TABLE[m] = _PARTIAL[m]; end                     # complete ALL members together
    finally
        if _scc_root(key) == key                                                # only the ROOT cleans its SCC
            done = Atom[g for g in _GEN_STACK if _scc_root(g) == key]
            filter!(g -> _scc_root(g) != key, _GEN_STACK)
            for m in done
                delete!(_TABLE_INPROG, m); delete!(_PARTIAL, m); delete!(_COMPONENT, m); delete!(_PARTIAL_READ, m)
            end
        end
    end
    _replay(ans, b, prev)
end

function metta_instr(f::Frame, b::Bindings, space)
    a = f.atom
    # spec (metta.md:191) is 3-arg `(metta <atom> <type> <space>)`; Core threads `space` as a Julia param so
    # its internal builders use the 2-arg `(metta atom type)` form. Accept BOTH: the optional 3rd operand, when
    # a grounded Space, becomes the eval context (matches hyperon metta_sym :940); a non-space/&self 3rd arg
    # falls back to the ambient context space (Core's single-space model). This also fixes the prior hard
    # rejection of the canonical 3-arg form, which embedded the whole &self Space into an Error atom.
    (a isa Expression && (length(a.children) == 3 || length(a.children) == 4)) ||
        return finished_result(error_atom(a, "expected (metta atom type [space])"), b, f.prev)
    atom = subst(a.children[2], b); typ = a.children[3]
    if length(a.children) == 4
        s3 = subst(a.children[4], b)
        s3 isa Grounded && s3.value isa Space && (space = s3.value::Space)
    end
    (is_empty_atom(atom) || is_error_atom(atom)) && return finished_result(atom, b, f.prev)
    (typ == ATOM_T || typ == metatype_sym(atom) || atom isa Var) && return finished_result(atom, b, f.prev)
    (atom isa Expression && !isempty(atom.children)) || return finished_result(atom, b, f.prev)
    # SLG tabling (opt-in; default-OFF ⇒ is_tabled is false ⇒ never fires ⇒ 234 path unchanged): route a
    # tabled goal to the leader/consumer driver — memoise + suspend-on-variant (left-recursion terminates).
    (space !== nothing && is_tabled(atom)) && return tabled_eval(atom, typ, space, b, f.prev)
    if is_minimal_op(atom)                  # embedded minimal instruction → run it, then re-metta its result
        r = freshvar("r")                   # (a rule body like let*'s chain rewrites to (let …) which must reduce)
        # NotReducible backstop (hyperon metta_call_return interpreter.rs:1456): if the embedded minimal op
        # bottoms out in the INTERNAL NOT_REDUCIBLE sentinel, surface the ORIGINAL atom unchanged (keep-form,
        # matches hyperon — no engine shows the bare sentinel to the user); else re-metta r as before.
        return push_nested(_chain(atom, r, _op("metta-noreduce", atom, r, typ)), b, f.prev, f.depth + 1)
    end
    op = atom.children[1]; nargs = length(atom.children) - 1
    # No space ⇒ no type system (bare/minimal eval, e.g. interpret(atom)/bare_eval(atom) with the
    # space=nothing default): skip the typed-function path entirely (atom_types/type_check_errors
    # require ::Space). Falls through to the untyped tuple/grounded path below.
    ftypes = (op isa Var || space === nothing) ? Atom[] :
        filter(t -> is_function_type(t) && length(fn_arg_types(t)) == nargs, atom_types(op, space))
    if !isempty(ftypes)                                       # TYPED path: type-check, then interpret-function
        out = Tuple{Frame,Bindings}[]; errs = Tuple{Frame,Bindings}[]
        for ft in ftypes
            # ftypes non-empty ⇒ line-565 guard took the filter branch ⇒ space was non-nothing ⇒ a real
            # Space. The ::Space narrow is a runtime no-op that lets the checker resolve type_check_errors.
            te = type_check_errors(atom, ft::Expression, space::Space)
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

# (metta-noreduce <orig> <r> <typ>) — hyperon's metta_call_return NOT_REDUCIBLE backstop (interpreter.rs:1456).
# The metta driver re-mettas the result `r` of an embedded minimal op; if that result is the INTERNAL
# NOT_REDUCIBLE sentinel, hyperon surfaces the ORIGINAL atom unchanged rather than the bare sentinel. Without
# this, Core leaked `NotReducible` to the user (e.g. !(eval (A B C)) → NotReducible vs hyperon's (eval (A B C))).
# Internal NotReducible propagation (chain/switch's if-equal on NotReducible) is untouched — this only fires
# at the metta re-reduction seam.
function metta_noreduce_instr(f::Frame, b::Bindings)
    a = f.atom
    r = subst(a.children[3], b)
    r == NOT_REDUCIBLE ? finished_result(a.children[2], b, f.prev) :
                         push_nested(_metta(r, a.children[4]), b, f.prev, f.depth)
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
        # No space ⇒ no `=` rule base to query (bare/minimal eval): no rewrites, atom returned as-is.
        qres = space === nothing ? Bindings[] : query(space::Space, Expression(Sym("="), atom, X))
        reduced = false
        for qb in qres, mb in merge_bindings(b, qb)
            is_present(mb, X) || continue                # resolve-filter (identical to Interpreter.jl :309)
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
        _INTERPRET_MAX[] > 0 && (steps += 1) > _INTERPRET_MAX[] && error("minimal interpreter step limit (raise via interpret_max_steps!(n); 0 = unlimited)")
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
const ERROR_TYPE = Sym("ErrorType")   # hyperon ATOM_TYPE_ERROR — the type of an (Error …) atom
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
# Step cap for the MINIMAL machine's `interpret` loop (~line 724) — the iterative driver's runaway guard.
# Was hard-coded 512K; now configurable (same pattern as _METTA_MAX) so heavy-but-finite workloads can
# raise it. Default 512K (bounded-generous over measured need); 0 = unlimited (mirrors hyperon/CeTTa).
# e.g. ECAN's 100-tick heartbeat stress test legitimately exceeds 512K — a signal for the parked
# per-step-cost optimization, NOT a reason to keep the default permanently high.
const _INTERPRET_MAX = Ref(512_000)
"Set the minimal-machine `interpret` step cap; 0 = unlimited. Default 512_000."
interpret_max_steps!(n::Int=512_000) = (_INTERPRET_MAX[] = n)
const _METTA_DEBUG = Ref(false)
"Toggle metta reduction tracing — prints each metta_call (use to detect where evaluation goes wrong)."
metta_debug!(on::Bool=true) = (_METTA_DEBUG[] = on)

# Intrinsic types of grounded ops (hyperon: the op's `type_()` method, NOT a stdlib atom). Kept OUT of
# the space so they never appear in `match &self` — e.g. d4's type-reasoning rule matches every
# `(: X (-> a b))` decl and infinite-loops on a polymorphic arrow, so state-op types as space atoms
# would break it. Stored as source strings, parsed FRESH per lookup for variable hygiene.
const _GROUNDED_OP_TYPES = Dict{Atom,String}()       # populated after the ops are defined (below)
_parse_type(s::AbstractString)::Atom = parse_from(tokenize(s), Ref(1))
# Parse-once cache for grounded-op intrinsic types. `atom_types` runs on every typed eval step;
# re-tokenizing+parsing the type SOURCE STRING per lookup was the `Vector{Char}` churn AllocCheck/Profile
# flagged. We memoize the parsed Atom and return it directly — byte-identical structure to a fresh parse
# (same `Var("t",0)`, so type-matching is unchanged; atoms are immutable and bindings are per-call, so
# the shared object is safe). Eval is serialized under the server LOCK, so the lazy fill needs no extra
# guard. (NOT rename_fresh'd: that would assign new Var ids and change matching behavior — preserve parity.)
const _GROUNDED_OP_TYPE_CACHE = Dict{Atom,Atom}()

# the declared types of `atom`: intrinsic grounded-op type (if any) + space decls (: atom $T)
function atom_types(atom::Atom, space::Space)::Vector{Atom}
    T = freshvar("T"); out = Atom[]
    haskey(_GROUNDED_OP_TYPES, atom) &&
        push!(out, get!(() -> _parse_type(_GROUNDED_OP_TYPES[atom]), _GROUNDED_OP_TYPE_CACHE, atom))
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
    is_error_atom(arg) && return Atom[ERROR_TYPE]               # (Error …) : ErrorType (hyperon ATOM_TYPE_ERROR) —
                                                                # so an Error LITERAL passed where a concrete type is
                                                                # expected fails type-check → (BadArgType i T ErrorType),
                                                                # matching hyperon. (Atom-typed args still bypass via
                                                                # match_types_b's Atom short-circuit, so assertEqual etc. are unaffected.)
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
            is_present(mb, X) || continue                # resolve-filter (identical to Interpreter.jl :309)
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
const NOT = Grounded(Operation("not", xs -> (length(xs) == 1 && (tb = _to_bool(xs[1])) !== nothing) ?
    ExecOk(Atom[tb ? Sym("False") : Sym("True")]) : ExecNoReduce()))
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
    # Core's number model is Float64, so computed indices arrive as integral Floats (e.g. (ceil 4.75) → 5.0,
    # (+ $i 1) → Float). Accept any integral Real (Int or 4.0), matching hyperon/CeTTa's grounded index-atom
    # semantics in Core's number model — without this, the canonical op no-ops on every computed index,
    # forcing packages to hand-roll a recursive nth. Non-integral / Inf / NaN still don't reduce.
    (length(xs) == 2 && xs[1] isa Expression && xs[2] isa Grounded &&
        xs[2].value isa Real && isinteger(xs[2].value)) || return ExecNoReduce()
    i = Int(xs[2].value)
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
    ExecOk(Atom[rename_fresh(a) for a in own])
end))
const CONTEXT_SPACE = Grounded(SpaceOp("context-space", (xs, space) -> ExecOk(Atom[Grounded(space)])))
# all binding sets under which `pat` matches some atom of `space`, extending `b0`
function _match_pat(space::Space, pat::Atom, b0::Bindings)::Vector{Bindings}
    out = Bindings[]
    for atom in space.atoms, mb in match_atoms(subst(pat, b0), rename_fresh(atom))
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
# collapse (grounded SpaceOp): collect all results of evaluating the arg into one tuple.
# `reverse`: interpret()'s plan is a LIFO stack, so metta_run yields the nondeterministic alternatives in
# REVERSE generation order; collapse freezes that order into a VALUE (unlike top-level display, where order is
# cosmetic), diverging from hyperon+CeTTa which both give forward/source order — e.g. (collapse (superpose
# (1 2 3)))→(1 2 3), not (3 2 1). Reversing here restores forward order for superpose, rule-fanout, AND match.
const COLLAPSE = Grounded(SpaceOp("collapse", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    ExecOk(Atom[Expression(reverse(metta_run(xs[1], space)))])
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
    space.tokens[string((xs[1]::Sym).name)] = xs[2]   # tokens table is String-keyed (parser uses raw text)
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
    mod isa Sym && return string(mod.name)          # Sym name is a Symbol → String for the module path
    mod isa Grounded && mod.value isa AbstractString && return mod.value
    if mod isa Expression && length(mod.children) == 2 && mod.children[1] == Sym("library")
        c = mod.children[2]
        c isa Sym && return string(c.name)
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
        space.tokens[string((target::Sym).name)] = Grounded(newsp)      # &kb: bind the token to a fresh space
    else
        return ExecRuntime("import!: first argument must be a space token")
    end
    ExecOk(Atom[Expression(Atom[])])
end))

# (mork-closure): OPT-IN substrate route — compute the MM2 forward-rewriting closure of this Space's relational
# rules on the MORK lane and materialize the derived atoms back into the Space, then continue in the interpreter.
# The implementation (`mc_closure!`) lives in the parent MeTTaCore (MM2Router, loaded after this); a hook bridges
# the module order — MM2Router populates `_MORK_CLOSURE_HOOK[]` at load. See `MM2Router.mc_closure!`.
const _MORK_CLOSURE_HOOK = Ref{Function}(_ -> error("mork-closure: substrate route not wired (load order)"))
const MORK_CLOSURE = Grounded(SpaceOp("mork-closure", function (xs, space)
    _MORK_CLOSURE_HOOK[](space)                      # materialize the MORK closure into `space` (side effect)
    ExecOk(Atom[Expression(Atom[])])                 # unit ()
end))

# token registry: operator words → their grounded atoms (the tokenizer constructors)
const TOKEN_REGISTRY = Dict{String,Atom}(
    "mork-closure" => MORK_CLOSURE,
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
    "import!" => IMPORT, "table!" => TABLE_DECL)
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
