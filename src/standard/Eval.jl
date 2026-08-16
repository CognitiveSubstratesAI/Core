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

module Eval

# `StandardMeTTa` (the grammar's four ATOM kinds) is no longer INCLUDED here — it was hoisted to
# `MeTTaCore.jl`, ABOVE the store/parser/primitives, on 2026-07-29. It is standalone and never
# depended on this module; nesting it here made the grammar's type a private member of the evaluator,
# which forced `CoreSpace` to invent `SExprConvertible` (SYMBOL and VARIABLE collapsed into one Julia
# `Symbol`, hence `__var_`) and forced the compiler lane to depend on this module to reach a grounded
# op. Now it is a sibling both lanes use. `using ..StandardMeTTa` = the PARENT's copy, so there is
# exactly one atom type in the process.
using ..StandardMeTTa

export interpret, bare_eval, Space, add_atom!, Operation, PLUS, MINUS, LT, is_executable
export metta_run, metta_results, parse_program, load_metta!, load_core_stdlib!, tokenize, metta_debug!
export interpret_max_steps!, metta_max_steps!
export table!, untable_all!, auto_table!

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

# ── the WELD: name => live, injected by LangDefPack.jl ────────────────────────────
#
# `rule_enabled` used to be `!(name in _langdef_disabled())`, which FAILED OPEN in two ways:
#   * a MISTYPED rule name is not in the disabled set, so it read as ENABLED — a disable-to-prove
#     test could silently prove nothing (`langdef_disable!("HES_Chian")` disabled no branch at all);
#   * a rule the table marks `live = false` still ran, because the table was never consulted.
# The table already had the correct predicate (`langdef_rule_enabled`, LangDefPack.jl:123, which
# returns `r.live`) — the interpreter simply reimplemented a weaker one and never called it. That is
# GUARANTEE-vs-CONVENTION: the mechanism looked welded and was not.
#
# Direction matters. This submodule is deliberately SELF-CONTAINED, and it is included at
# MeTTaCore.jl:62 while LangDefPack.jl is included at :69 — so it cannot reference the table, at load
# time or otherwise, without inverting that dependency. Instead it declares an INJECTION POINT which
# LangDefPack.jl fills at its own load time. Eval still reaches out to nothing.
const _LANGDEF_LIVE = Dict{String, Bool}()

"Register the rule table (called by LangDefPack.jl at load). Idempotent; last registration wins."
function _langdef_register!(pairs)
    empty!(_LANGDEF_LIVE)
    for (name, live) in pairs
        _LANGDEF_LIVE[String(name)] = live
    end
    _LANGDEF_LIVE
end

"""
    rule_enabled(name) -> Bool

True iff `name` is a KNOWN live rule that is not currently disabled.

FAILS CLOSED: an unregistered name raises rather than defaulting to enabled, so a typo in a
disable-to-prove test surfaces immediately instead of quietly proving nothing.
"""
@inline function rule_enabled(name::String)::Bool
    live = get(_LANGDEF_LIVE, name, nothing)
    if live === nothing
        isempty(_LANGDEF_LIVE) && error(
            "rule_enabled(\"$name\"): the LangDef rule table was never registered. " *
            "LangDefPack.jl must call Eval._langdef_register! at load; without it every " *
            "gated branch would fall open.")
        error("rule_enabled(\"$name\"): not a rule in HE_SMALL_STEP_RULES. Known rules: " *
              join(sort(collect(keys(_LANGDEF_LIVE))), ", ") *
              ". (A mistyped name previously read as ENABLED, so a disable-to-prove test could " *
              "silently prove nothing.)")
    end
    live::Bool || return false          # table says the rule is structural, not executable
    !(name in _langdef_disabled())
end
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
        # has_vars fast path (CeTTa match.c:891 `if (!atom_has_vars(atom)) return atom;`): a GROUND subtree
        # can never change under substitution — return it in O(1), skipping the abstract-`Atom` recursion whose
        # dynamic-dispatch boxing (~32 B/node, AllocCheck-confirmed) is the O(term-size)/step ground-reduction cost.
        a.has_vars || return a
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
    a isa Expression || return s
    a.has_vars || return s                    # ground subtree ⇒ no vars, O(1) (has_vars fast path)
    for c in a.children; collect_vars!(s, c); end
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
    tco::Bool              # PROVENANCE: set true ONLY on driver-generated metta reduce-again frames (metta_instr →
                           # push_nested tco=true), never derivable from atom syntax. The TCO frame-collapse
                           # (:~1440) collapses ONLY tco frames, so a user-written `(chain (metta-call…) $r $r)`
                           # (same shape, tco=false) is immune — a GUARANTEE, not a shape-match convention.
    # Default tco=false so every existing 6-arg `Frame(a,v,p,r,f,d)` construction stays valid & non-collapsible.
    Frame(a::Atom, v::Set{Var}, p::Union{Frame,Nothing}, r::Function, f::Bool, d::Int, tco::Bool=false) =
        new(a, v, p, r, f, d, tco)
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

"""Minimum `children` length each minimal-MeTTa instruction reads — the arity guard's table.

🔴 WHY THE DISPATCHER NEEDS ONE. `interpret_stack` dispatches on HEAD NAME ALONE. Every instruction
function then indexes `a.children[…]` at fixed positions, so ANY atom that happens to carry an
instruction's name in head position — with the wrong arity — crashes the interpreter with a
`BoundsError` instead of being returned as data.

MEASURED 2026-08-10, and it is reachable from ordinary MeTTa, not a synthetic input:

    !(match &self \$a \$a)            ⟹ BoundsError, 2-element children at index [3]
    the offending atom: (return-on-error (-> Atom Atom %Undefined%))

That is `stdlib.metta:332`'s own type declaration `(: return-on-error (-> Atom Atom %Undefined%))`
with the `:` head stripped, fed back through evaluation. A bare-variable `match` returns every atom in
the space, stdlib's declarations included — so a MeTTa program can crash the evaluator by looking at
the standard library.

MeTTa's answer for an ill-formed head is NOT a crash: an atom that is not a well-formed operation is
DATA, returned unreduced. That is exactly what this dispatcher's own `else` branch already does, so
the fix routes short atoms there rather than inventing a behaviour.

⚠️ SEVEN ENTRIES, EVERY ONE MEASURED — AND THE FIRST TWO ATTEMPTS ARE WHY IT SAYS SO. Attempt one
guessed all seventeen by regex-extracting the max `children[N]` each function reads; the extraction
used a crude body extent that bled into neighbours, several minimums came out TOO HIGH, and the guard
rejected VALID atoms — 36 test failures, `bin/health` 3/5, `!(norm (3 4))` returning nothing. Attempt
two cut back to the single entry a real crash had demonstrated.

This table is attempt three, and it is not read off the code at all. It is MEASURED: every
instruction the dispatcher knows, evaluated at every arity 0..6, recording which shapes throw
(`scratchpad/probe_arity_sweep.jl`, and the property test in `test/standard/test_instr_arity.jl` that
keeps it true). The result was worth having:

    the 10 PUBLIC instructions (eval, chain, unify, cons-atom, …)   crash at NO arity — already
                                                                    defensive, and correctly get no
                                                                    entry here
    6 INTERNAL ones (interpret-tuple/function/args, metta-call,     crash at 13 shapes between them
     args-cont, metta-noreduce)

So the over-guarding that broke 36 tests came entirely from entries for instructions that never
needed one. Under-guarding is safe — an atom behaves as it does today; over-guarding rejects working
programs. Measurement is what tells the two apart, and reading the bodies would not have: the crashes
are in the INTERNAL continuations, which no arity table in the §3 spec covers."""
const _INSTR_MIN_CHILDREN = Dict{Symbol, Int}(
    Symbol("return-on-error")    => 3,
    Symbol("interpret-tuple")    => 2,
    Symbol("interpret-function") => 3,
    Symbol("interpret-args")     => 3,
    Symbol("metta-call")         => 3,
    Symbol("args-cont")          => 4,
    Symbol("metta-noreduce")     => 4,
)

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
    # ARITY GUARD — see `_INSTR_MIN_CHILDREN`. An atom carrying an instruction's NAME but not its
    # SHAPE is data, exactly as the `else` branch below treats an unknown head. Without this the
    # instruction functions index past the end and the interpreter dies on a `BoundsError`.
    if f.atom isa Expression
        req = get(_INSTR_MIN_CHILDREN, name, 0)
        req > 0 && length((f.atom::Expression).children) < req &&
            return finished_result(f.atom, b, f.prev)
    end
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
    e == UNDEFINED && return finished_result(UNDEFINED, b, f.prev)   # WFS bottom contagious through strict ops
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
    (head == UNDEFINED || tail == UNDEFINED) && return finished_result(UNDEFINED, b, f.prev)   # WFS bottom contagious
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
        (x == UNDEFINED || y == UNDEFINED) && return ExecOk(Atom[UNDEFINED])   # WFS bottom is contagious through strict ops
        (x isa Grounded && x.value isa Number && y isa Grounded && y.value isa Number) || return ExecNoReduce()
        ExecOk(Atom[Grounded(f(x.value, y.value))])
    end))
end
# `/` and `%` do NOT use Julia's operators: Int÷Int must be INTEGER division and a zero divisor
# must be a DivisionByZero decision, not Inf/NaN or an escaping host DivideError. Both come from
# NumericSeam, the single owner (see its docstring for the hyperon/LeaTTa/CeTTa basis).
using ..NumericSeam: SeamError, seam_div, seam_mod

function _num_binop_seam(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        length(xs) == 2 || return ExecNoReduce()
        x, y = xs[1], xs[2]
        (x == UNDEFINED || y == UNDEFINED) && return ExecOk(Atom[UNDEFINED])
        (x isa Grounded && x.value isa Number && y isa Grounded && y.value isa Number) || return ExecNoReduce()
        r = f(x.value, y.value)
        r isa SeamError && return ExecOk(Atom[Expression(Atom[
            Sym("Error"), Expression(Atom[Sym(name), x, y]), Sym("DivisionByZero")])])
        ExecOk(Atom[Grounded(r)])
    end))
end

const PLUS  = _num_binop("+", +)
const MINUS = _num_binop("-", -)
# comparisons return the True/False SYMBOLS (so unify against `True` works)
function _num_cmp(name, f)
    Grounded(Operation(name, function (xs::Vector{Atom})
        length(xs) == 2 || return ExecNoReduce()
        x, y = xs[1], xs[2]
        (x == UNDEFINED || y == UNDEFINED) && return ExecOk(Atom[UNDEFINED])   # WFS bottom is contagious through strict ops
        (x isa Grounded && x.value isa Number && y isa Grounded && y.value isa Number) || return ExecNoReduce()
        ExecOk(Atom[f(x.value, y.value) ? Sym("True") : Sym("False")])
    end))
end
const LT = _num_cmp("<", <)

# ── THE STORE (Phase 2 of the MORK-backing migration) ─────────────────────────────────────────────
#
# 🔴 THE STORE IS NOT JUST `atoms`. `index`, `wildcard` and `bucket_trie` are storage ACCELERATION, and
# a trie-backed store has NONE of them — it has the trie. So they are this store's private business,
# not fields a foreign backend would leave empty. That distinction is the whole reason this struct
# exists: moving only `atoms` would have produced five renamed accessors, not a seam.
#
# `lib_count` is store-side too: it is an index INTO `atoms` (the leading run of imported-library
# atoms), meaningless without the vector it indexes.
#
# What deliberately STAYS on `Space`: `tokens`, `imported`, `type_epoch`, `revision` — runner state,
# fused into the space by Core (upstream `GroundingSpace` has only index/common/name and keeps the
# tokenizer on the runner). That fusion is exactly why `Space` must stay CONCRETE with the store
# swapped behind it, rather than `Space` becoming an abstract supertype: a foreign backend would
# otherwise have to supply all four or silently lack them.
# Verified upstream shape: CeTTa holds its backend vtable in a FIELD of one concrete `Space`
# (`space.h:169`, "share one runtime seam without confusing storage with execution"); MeTTaScript's
# `SpaceView` holds a `SpaceLike` in a private field. Neither subtypes its space.
#
# ⚠️ CONCRETE FIELD ON PURPOSE, FOR NOW. `store::VectorStore` is concrete, so this commit changes
# NOTHING about dispatch or allocation — the field move and the backend-swap are separate steps, and
# only the first is landing here. Making it `Space{S<:AbstractStore}` is then a one-line change with
# its own allocation gate, per `docs/specs/space_api_upstream_survey_2026-08-13.md` §9.3.
abstract type AbstractStore end

mutable struct VectorStore <: AbstractStore
    atoms::Vector{Atom}
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
    # Control accel #2 (CeTTa subst_tree, space.c:497): a LAZY per-bucket discrimination trie. The 2-symbol
    # `index` narrows to same-(head,arg1-head) atoms, but a WIDE bucket (many rules/facts sharing that key,
    # differing deeper) still costs O(bucket) rename+match per query. This trie prunes that scan by shared LHS
    # structure (a Var on EITHER side = wildcard) to a dup-free, order-preserved SUPERSET of matches; match_atoms
    # stays authoritative. Value = (trie-root, bucket-position map). Entry ABSENT ⇒ (re)build on next query;
    # invalidated (deleted) on any add/remove to the bucket. Built only for buckets over `_TRIE_MIN_BUCKET`
    # (small buckets keep the zero-overhead linear scan). Field is LAST + inner-ctor-defaulted ⇒ existing
    # 6/7-arg positional Space(...) calls keep working.
    bucket_trie::Dict{Tuple{Symbol,Symbol},Any}
    VectorStore(atoms, lib_count, index, wildcard) =
        new(atoms, lib_count, index, wildcard, Dict{Tuple{Symbol,Symbol},Any}())
end
VectorStore() = VectorStore(Atom[], 0, Dict{Tuple{Symbol,Symbol},Vector{Atom}}(), Atom[])

mutable struct Space
    store::VectorStore            # ← the swappable half. Concrete today; see the note above.
    tokens::Dict{String,Atom}     # bind! token table: token-name → atom (parse-time substitution)
    imported::Set{String}         # modules already imported here — re-import is ignored (+ cycle guard)
    type_epoch::Int               # monotonic; bumped ONLY when a (: …) type decl is added/removed (see
                                  # add_atom!/remove_atom!). Keys the arg_actual_types memo — actual types
                                  # derive solely from `:` decls, so cached types invalidate exactly on change.
    # monotonic mutation counter (bumped on EVERY add/remove). Stamps SLG answer-table entries (CeTTa
    # table_store.c:153 per-space `revision`): a tabled answer computed at revision r is stale once the space
    # mutates (r'≠r) and is auto-evicted on lookup — closes the "table can go silently stale" hole (§7.7).
    revision::Int
    Space(store::VectorStore, tokens, imported, type_epoch=0) =
        new(store, tokens, imported, type_epoch, 0)
end
# ⚠️ COMPATIBILITY CONSTRUCTOR — the 6/7-arg positional form is used at 14 sites across Core/src +
# Core/test and MUST keep working; the previous inner constructor's own comment records that this
# signature was already preserved deliberately once. It now packs the store instead of setting fields.
Space(atoms, tokens, imported, lib_count, index, wildcard, type_epoch=0) =
    Space(VectorStore(atoms, lib_count, index, wildcard), tokens, imported, type_epoch)
Space() = Space(VectorStore(), Dict{String,Atom}(), Set{String}(), 0)
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
# a `(: atom T)` type declaration — the ONLY atom shape whose add/remove changes actual-type inference
# (atom_types queries exactly `(: atom $T)`; Core has no (:< ) supertype closure). Bumps the memo epoch.
_is_type_decl(a::Atom)::Bool = a isa Expression && length(a.children) >= 2 &&
    a.children[1] isa Sym && (a.children[1]::Sym).name === Symbol(":")
function add_atom!(s::Space, a::Atom)
    push!(s.store.atoms, a)
    s.revision += 1                              # bump the mutation counter (SLG answer-table staleness stamp)
    k = _index_key(a)
    if k === nothing
        push!(s.store.wildcard, a)
    else
        push!(get!(() -> Atom[], s.store.index, k), a)
        isempty(s.store.bucket_trie) || delete!(s.store.bucket_trie, k)   # invalidate the bucket's discrimination trie
    end
    _is_type_decl(a) && (s.type_epoch += 1)      # invalidate the arg_actual_types memo for this space
    s
end
function remove_atom!(s::Space, a::Atom)
    filter!(x -> x != a, s.store.atoms)
    s.revision += 1
    k = _index_key(a)
    if k === nothing
        filter!(x -> x != a, s.store.wildcard)
    else
        b = get(s.store.index, k, nothing); b !== nothing && filter!(x -> x != a, b)
        isempty(s.store.bucket_trie) || delete!(s.store.bucket_trie, k)   # invalidate the bucket's discrimination trie
    end
    _is_type_decl(a) && (s.type_epoch += 1)
    s
end

# ── Store-accessor interface (Phase 1 of the MORK-backing migration) ──────────────────────────
# Every store access OUTSIDE the store's own methods (add_atom!/remove_atom!/query and the index
# internals) goes through these accessors, so a MORK-trie-backed store can satisfy the SAME
# interface without the eval loop or external callers reaching into `.atoms`/`.lib_count`. Today
# they wrap the Julia `Vector{Atom}` verbatim — ZERO behaviour change; Phase 2 adds MORK-backed
# methods. `.atoms` was reached directly at ~9 sites (get-atoms, _match_pat, fork-space,
# auto_table!, MM2Router own-atoms/dedup, the server's own-atom counts); all now route here.
all_atoms(s::Space) = s.store.atoms                                   # every atom, incl. the flattened library
own_atoms(s::Space) = @view s.store.atoms[(s.store.lib_count + 1):end]      # own atoms only (excludes imported library)
atom_count(s::Space) = length(s.store.atoms)
own_atom_count(s::Space) = length(s.store.atoms) - s.store.lib_count
contains_atom(s::Space, a::Atom) = any(==(a), s.store.atoms)
clone_store(s::Space) = (f = Space(copy(s.store.atoms)); f.store.lib_count = s.store.lib_count; f)
# 🔴 THE 10th CONTRACT OP, added 2026-08-15. `own_atoms`/`own_atom_count` READ `lib_count`, but
# nothing SET it — `load_metta!` wrote `space.store.lib_count` directly, the only store-field write
# outside this block. A trie-backed store cannot be dropped in while sealing the library boundary
# is inexpressible, so the seam needs this op regardless of which store implements it.
# Precedent for why field-reaching is not harmless: MettaJam reached for `Space.atoms` after the
# store seam landed and silently died, staying dead until `af05996`.
seal_library!(s::Space) = (s.store.lib_count = length(s.store.atoms); s)

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

# ── FAST-MATCH (opt-in, default OFF): skip rename_fresh when it is PROVABLY a no-op on the result ─────────
# `rename_fresh` exists to (a) separate the query's var namespace from the rule's, and (b) give a rule's
# UNBOUND RHS vars fresh identity so nondeterministic results don't conflate. Both are moot when the query
# GOAL is ground AND the rule is "closed" (vars(RHS) ⊆ vars(LHS)): matching a ground goal binds every rule
# var to a ground term ⇒ the RHS substitutes to a GROUND result — nothing unbound to freshen, no query var
# to separate. So skipping the rename yields a BYTE-IDENTICAL result (verified by the differential harness),
# while avoiding the per-call spine rebuild that the profile flagged as the top hot spot on var-heavy rules
# (fib's body). Gated behind `_FAST_MATCH[]` (default false) so the 234-conformance path is byte-identical
# by construction until the harness proves the fast path equivalent.
const _FAST_MATCH = Ref(false)
fast_match!(on::Bool = true) = (_FAST_MATCH[] = on)
const _CLOSED_RULE_MEMO = Dict{UInt,Bool}()      # objectid(stored) → vars(RHS)⊆vars(LHS); rules are stable objects
_is_eq_rule(a::Atom) = a isa Expression && length(a.children) == 3 &&
                       a.children[1] isa Sym && (a.children[1]::Sym).name == Symbol("=")
function _is_closed_rule(stored::Atom)::Bool
    _is_eq_rule(stored) || return false
    get!(_CLOSED_RULE_MEMO, objectid(stored)) do
        issubset(collect_vars(stored.children[3]), collect_vars(stored.children[2]))
    end
end
@inline _ground_atom(x::Atom)::Bool = x isa Var ? false : (x isa Expression ? !x.has_vars : true)

# ── per-bucket discrimination trie: a conservative candidate filter ─────────────────────────────────────
# Prunes a WIDE same-discriminant bucket by shared LHS structure. Tokens are the pre-order flattening of an
# atom; a Var (either side) is a WILDCARD. The stored trie routes each atom by its ground tokens (a stored Var
# → the `star` edge). Retrieval descends the query stream: a ground query token follows the matching concrete
# edge AND the star edge (a stored Var matches the query's whole subterm, so skip it); a query Var (or query
# exhaustion) collects the whole subtrie. Result = a duplicate-free SUPERSET of true matches (each stored atom
# lies on exactly one path, so it is collected ≤1×); match_atoms remains authoritative. Correctness: match_atoms
# succeeds ⇒ at every position one side is a Var or both are equal ground tokens ⇒ the atom is on a followed
# path ⇒ collected. So the filter never drops a match.
const _TRIE_MIN_BUCKET = 16                # build/use the trie only for buckets larger than this (CeTTa promotes at 16)
# Concrete, isbits token — NO `Any` (dense `Vector{_Tok}` + isbits `Dict` keys ⇒ zero boxing / no dynamic dispatch;
# what the JIT wants). A Var is a wildcard (`_KVAR`); a Sym/Grounded is keyed by the 64-bit hash of its name/value
# (a hash collision only WIDENS the candidate set — match_atoms stays authoritative — so a match is never dropped);
# an Expression by its arity. `kind` disambiguates hash spaces (a Sym and a Grounded with equal hashes stay separate).
const _KVAR  = 0x00
const _KSYM  = 0x01
const _KEXPR = 0x02
const _KGND  = 0x03
struct _Tok
    kind::UInt8
    pay::UInt64
end
@inline _tok(a::Atom)::_Tok =
    a isa Sym        ? _Tok(_KSYM,  hash(a.name)) :
    a isa Expression ? _Tok(_KEXPR, UInt64(length(a.children))) :
    a isa Grounded   ? _Tok(_KGND,  hash(a.value)) :
                       _Tok(_KVAR,  UInt64(0))               # Var (or unknown) = wildcard

function _flat_tokens!(toks::Vector{_Tok}, a::Atom, d::Int)
    if d > _MAX_ATOM_DEPTH
        push!(toks, _Tok(_KVAR, UInt64(0))); return          # depth cap → wildcard (conservative)
    elseif a isa Expression
        push!(toks, _Tok(_KEXPR, UInt64(length(a.children))))
        for c in a.children; _flat_tokens!(toks, c, d + 1); end
    else
        push!(toks, _tok(a))
    end
    return
end
_flat_tokens(a::Atom) = (t = _Tok[]; _flat_tokens!(t, a, 0); t)

function _skip_term(toks::Vector{_Tok}, i::Int)::Int         # advance past one whole term (isbits ⇒ alloc-free)
    @inbounds t = toks[i]
    if t.kind == _KEXPR
        i += 1
        for _ in 1:Int(t.pay); i = _skip_term(toks, i); end
        return i
    end
    i + 1
end

mutable struct _TNode
    atoms::Vector{Atom}                    # every stored atom routed through this node (⇒ query-var collect)
    concrete::Dict{_Tok,_TNode}
    star::Union{_TNode,Nothing}
    _TNode() = new(Atom[], Dict{_Tok,_TNode}(), nothing)
end

function _trie_insert!(root::_TNode, a::Atom)
    node = root
    push!(node.atoms, a)
    for t in _flat_tokens(a)
        if t.kind == _KVAR
            node.star === nothing && (node.star = _TNode())
            node = node.star
        else
            node = get!(_TNode, node.concrete, t)
        end
        push!(node.atoms, a)
    end
    return
end

function _trie_build(bucket::Vector{Atom})
    root = _TNode()
    pos = IdDict{Atom,Int}()
    for (i, a) in enumerate(bucket)
        pos[a] = i
        _trie_insert!(root, a)
    end
    (root, pos)
end

function _trie_collect!(acc::Vector{Atom}, node::_TNode, q::Vector{_Tok}, qi::Int)
    if qi > length(q) || (@inbounds q[qi].kind == _KVAR)
        append!(acc, node.atoms); return                     # query exhausted / query-var → all in subtrie
    end
    @inbounds t = q[qi]
    c = get(node.concrete, t, nothing)
    c !== nothing && _trie_collect!(acc, c, q, qi + 1)        # ground token → matching concrete edge
    node.star !== nothing && _trie_collect!(acc, node.star, q, _skip_term(q, qi))  # stored var → skip query subterm
    return
end

function _bucket_candidates(space::Space, k::Tuple{Symbol,Symbol}, b::Vector{Atom}, pattern::Atom)::Vector{Atom}
    entry = get(space.store.bucket_trie, k, nothing)
    if entry === nothing
        entry = _trie_build(b)
        space.store.bucket_trie[k] = entry
    end
    root, pos = entry::Tuple{_TNode,IdDict{Atom,Int}}
    acc = Atom[]
    _trie_collect!(acc, root, _flat_tokens(pattern), 1)
    sort!(acc; by = a -> get(pos, a, typemax(Int)))          # preserve linear-scan order (⇒ identical results)
    acc
end

# query (= pattern $X) → the matching binding sets (interpreter.rs query:604). Each stored atom's variables are
# freshened before matching (make_variables_unique). Same-discriminant atoms are scanned linearly for a small
# bucket, or pruned via the per-bucket discrimination trie for a wide one (identical results either way).
function query(space::Space, pattern::Atom)::Vector{Bindings}
    out = Bindings[]
    # FAST-MATCH (opt-in): for a `(= ground-goal $X)` query, a CLOSED rule's rename is a no-op on the (ground)
    # result ⇒ skip it. `gg` = the goal is ground (so no query var to separate). Default OFF ⇒ always renames.
    gg = _FAST_MATCH[] && _is_eq_rule(pattern) && _ground_atom(pattern.children[2])
    @inline prep(stored::Atom) = (gg && _is_closed_rule(stored)) ? stored : rename_fresh(stored)
    k = _index_key(pattern)
    if k === nothing                                   # non-discriminable pattern (var head) → full scan (rare)
        for stored in all_atoms(space)                 # contract, not the field (see MettaJam af05996)
            append!(out, match_atoms(pattern, prep(stored)))
        end
        return out
    end
    b = get(space.store.index, k, nothing)                   # same-discriminant atoms — the (= (f …) …) rules for this f
    if b !== nothing
        if length(b) > _TRIE_MIN_BUCKET                # wide bucket → prune the scan by shared LHS structure
            for stored in _bucket_candidates(space, k, b, pattern)
                append!(out, match_atoms(pattern, prep(stored)))
            end
        else                                           # small bucket → zero-overhead linear scan (unchanged)
            for stored in b
                append!(out, match_atoms(pattern, prep(stored)))
            end
        end
    end
    for stored in space.store.wildcard                       # + var-headed atoms, which can match any discriminant
        append!(out, match_atoms(pattern, prep(stored)))
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
# `tco` marks driver-generated metta reduce continuations (originates ONLY at metta_instr's reduce-prog push;
# users cannot invoke push_nested, so the flag is unforgeable). It flows to setup_chain, which marks the frame
# and propagates one hop to the `(chain (metta-call…) $r $r)` wrapper — see setup_chain.
function push_nested(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int, tco::Bool=false)::Vector{Tuple{Frame,Bindings}}
    name = head_name(atom)
    if name === Symbol("chain") && rule_enabled("HES_Chain"); return setup_chain(atom, b, prev, depth, tco)
    elseif name === Symbol("function"); return setup_function(atom, b, prev, depth)
    else;                      return [(Frame(atom, _cumvars(prev, atom), prev, no_handler, false, depth, tco), b)]
    end
end

# function-special-when-returned (interpreter.rs eval_result:559): a returned `function`
# op is set up (looped), not treated as data.
function eval_result(res::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int)
    head_name(res) === Symbol("function") ? setup_function(res, b, prev, depth) : finished_result(res, b, prev)
end

# chain (interpreter.rs chain:687 / chain_ret:675): one-step nested, bind var, subst templ, EXECUTE it.
# `tco`: when this chain is driver-generated (metta reduce-prog), mark the frame AND propagate the flag one hop
# to the templ — but STOP at the `metta-call` wrapper (its templ is the identity var, not another driver chain).
# That marks exactly the interpret-tuple/function outer chain and its `(chain (metta-call…) $r $r)` inner wrapper
# (the collapsible frame), and nothing downstream — so `tco` is a precise, unforgeable provenance signal.
function setup_chain(atom::Atom, b::Bindings, prev::Union{Frame,Nothing}, depth::Int, tco::Bool=false)
    (atom isa Expression && length(atom.children) == 4) ||
        return finished_result(error_atom(atom, "expected (chain <nested> <var> <templ>)"), b, prev)
    nested, var, templ = atom.children[2], atom.children[3], atom.children[4]
    var isa Var ||
        return finished_result(error_atom(atom, "chain: second argument must be a variable"), b, prev)
    propagate = tco && head_name(nested) !== Symbol("metta-call")   # C1(interpret-tuple)→C2(metta-call): yes; C2→templ: no
    cont = function (self::Frame, result::Atom, rb::Bindings)
        bs = add_var_binding(rb, var, result)
        isempty(bs) && return nothing
        nb = bs[1]
        pushed = push_nested(subst(templ, nb), nb, self.prev, depth, propagate)
        isempty(pushed) ? nothing : pushed[1]
    end
    parent = Frame(atom, _cumvars(prev, atom), prev, cont, false, depth, tco)
    push_nested(subst(nested, b), b, parent, depth + 1)   # apply bindings so a var-bound minimal op evaluates (nested runs plain: no tco)
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
# SLG VARIANT TABLING + WFS — extracted to its own file 2026-08-16, mirroring how SWI
# (`boot/tabling.pl` + `pl-tabling.c`) and CeTTa (`table_store.c`) separate it. Included
# INSIDE `module Eval`, so every name resolves exactly as before. Future SLG work lands there.
# ═══════════════════════════════════════════════════════════════════════════════
# tabling/ mirrors swipl-devel's own section boundaries (boot/tabling.pl + src/pl-tabling.c) so each
# §7 feature ports into the file its upstream section lives in. StandardOrder first: Aggregation's
# min/max are defined on `@<`/`@>`, not numeric comparison.
include("tabling/StandardOrder.jl")
include("tabling/Aggregation.jl")
include("tabling/Tripwires.jl")
include("Tabling.jl")
# ⚠️ AFTER Tabling.jl, not with its siblings: `Worklist` holds `Dependency`, and `Dependency` /
# `Continuation` (§1.0 step 1) still live in Tabling.jl. Step 4 needs the reverse order — the
# completion loop consumes the worklist — so those two structs move into the subfolder then.
include("tabling/Worklists.jl")
include("tabling/AnswerTrie.jl")

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
            append!(out, push_nested(prog, b, f.prev, f.depth + 1, true))   # tco=true: driver reduce-prog (see setup_chain)
        end
        !isempty(out) && return out                          # some function type applied
        !isempty(errs) && return errs                        # all rejected → type errors (BadArgType)
    end
    reduced = freshvar("reduced"); result = freshvar("result")  # untyped tuple path
    prog = _chain(_op("interpret-tuple", atom), reduced,
              _chain(_op("metta-call", reduced, typ), result, result))
    push_nested(prog, b, f.prev, f.depth + 1, true)   # tco=true: driver reduce-prog (see setup_chain)
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

# ── tail-call frame-collapse (TCO) ────────────────────────────────────────────
# The metta driver wraps every reduce-again in `(chain (metta-call reduced typ) result result)`. Left in place,
# ONE such frame is retained per recursion level (prev-chain grows O(N)) AND its cumulative live-var set
# `_cumvars` grows O(N), so `narrow_bindings` re-scans O(N) per finish ⇒ a tail-recursive MeTTa loop is O(N²)
# (measured 120× on the OmegaClaw agent tick). Re-anchoring the reduce-again PAST these frames elides them: the
# `result` var is a freshvar (appears only as this chain's var+templ), so forwarding the metta-call's result V
# to the grandparent is proper TCO — mirroring CeTTa's `goto tail_call` / typescript-metta's `reduceTrampoline`
# — and fixes BOTH the frame retention AND `_cumvars` growth in one move. Non-identity chains (interpret-tuple/
# args/cons continuations = genuine NON-tail positions) STOP the walk, so non-tail recursion still grows.
#
# ⚠️ TWO soundness conditions, each learned from a failing gate — the frame is NOT a pure pass-through:
#
#  (1) typ-GATE (LeaTTa `switch-minimal` regression): the frame's continuation runs `push_nested(V, …)`, which
#      SPECIAL-CASES a `function`/`chain`-headed V (:743-744) — EXECUTING it, not treating it as data. V is
#      function/chain-headed ONLY when the reduction LAZILY short-circuits (:1267-1269), requiring `typ ∈
#      {Atom, Expression}`. So collapse ONLY when `typ ∉ {Atom, Expression}`. Hot loops (untyped → %Undefined%,
#      numeric → Number) still collapse; lazy-typed stdlib helpers (switch/if-minimal, ret Atom) correctly skip.
#
#  (2) PROVENANCE flag (adversary counterexample): the frame's continuation also runs `add_var_binding($r, V)`.
#      For a driver frame $r is a fresh dead var (elision is invisible), but a USER can hand-write the SAME shape
#      `(chain (metta-call…) $r $r)` with $r SHARED with a sibling — there the binding is LIVE and eliding it
#      diverges (`(P mv mv)` → `(P mv $r)`). A syntactic shape-match cannot tell these apart. So the collapse
#      fires ONLY on frames carrying the `Frame.tco` flag, which originates SOLELY at the driver's reduce-prog
#      push below (users cannot invoke push_nested) — a GUARANTEE of driver provenance, not a shape convention.
const _TAIL_COLLAPSE = Ref(true)
const EXPRESSION_SYM = Sym("Expression")   # metatype tag of any function/chain expression (the lazy-return type)
"Enable/disable tail-call frame-collapse (TCO) at the metta reduce-again seam. Default ON. `false` = exact pre-TCO behavior (for oracle A/B / bisimulation)."
tail_collapse!(on::Bool=true) = (_TAIL_COLLAPSE[] = on)

# A driver-generated metta reduce continuation: `(chain (metta-call …) $r $r)` with an IDENTITY templ. The
# `fr.tco` PROVENANCE flag is the GUARANTEE (set only by the driver's reduce-prog push, unforgeable from atom
# syntax) — this is what makes a user-written `(chain (metta-call…) $r $r)` with a SHARED $r immune (that frame
# has tco=false, so its `add_var_binding($r, …)` is never elided). The syntactic checks (identity templ +
# metta-call nested) are defense-in-depth, disambiguating the wrapper (C2) from the outer chain (C1), both tco.
@inline function _is_metta_reduce_cont(fr::Frame)::Bool
    fr.tco || return false
    a = fr.atom
    (a isa Expression && length(a.children) == 4 && head_name(a) === Symbol("chain") &&
        a.children[3] isa Var && a.children[3] === a.children[4]) || return false
    n = a.children[2]
    n isa Expression && head_name(n) === Symbol("metta-call")
end

# Walk past consecutive identity metta-reduce continuations to the first real ancestor (the TCO anchor). Gated
# by `typ`: under a lazy-return type (Atom/Expression) the metta-call may surface a bare function/chain that the
# skipped frame's `push_nested` would EXECUTE — so we must NOT collapse there (safety depends on V, governed by
# THIS typ, so gating the current metta-call's typ suffices even for multi-frame walks).
@inline function _collapse_anchor(prev::Union{Frame,Nothing}, typ::Atom)::Union{Frame,Nothing}
    (_TAIL_COLLAPSE[] && typ != ATOM_T && typ != EXPRESSION_SYM) || return prev
    a = prev
    while a !== nothing && _is_metta_reduce_cont(a); a = a.prev; end
    a
end

# (metta-call <atom> <type>) — metta_call (interpreter.rs:1415): grounded → execute; else → query
# (= atom $X). Each result is RE-MET TA'd via a pushed `(metta result type)` FRAME (reduce-again) — so a
# deep MeTTa recursion grows the heap plan, not the Julia stack. Non-reducible → finish as-is. The reduce-again
# push anchors at `_collapse_anchor(f.prev, typ)` (TCO) so tail recursion does NOT retain the identity pass-through.
function metta_call_instr(f::Frame, b::Bindings, space)
    a = f.atom
    atom = subst(a.children[2], b); typ = a.children[3]
    _METTA_DEBUG[] && println("metta_call: ", atom)
    is_error_atom(atom) && return finished_result(atom, b, f.prev)
    (atom isa Expression && !isempty(atom.children)) || return finished_result(atom, b, f.prev)
    op = atom.children[1]
    op isa Var && return finished_result(atom, b, f.prev)
    anchor = _collapse_anchor(f.prev, typ)   # TCO: re-anchor past identity frames (gated: skip under lazy typ)
    out = Tuple{Frame,Bindings}[]
    if is_executable(op)
        r = execute(op::Grounded, Atom[atom.children[2:end]...], space)
        if r isa ExecOk
            isempty(r.results) && return finished_result(EMPTY, b, f.prev)
            for (j, res) in enumerate(r.results)
                bset = (j <= length(r.binds)) ? merge_bindings(b, r.binds[j]) : Bindings[b]
                for mb in bset; append!(out, push_nested(_metta(res, typ), mb, anchor, f.depth + 1)); end
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
            is_present(mb, X) || continue                # resolve-filter (identical to Eval.jl :309)
            reduced = true
            append!(out, push_nested(_metta(subst(X, mb), typ), mb, anchor, f.depth + 1))
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

"""
    _run_plan(plan, space) -> Vector{Tuple{Atom,Bindings}}

THE driver loop — run a plan of pending `(Frame,Bindings)` to exhaustion, collecting every frame that
finishes at the root (`prev === nothing`).

⚠️ EXTRACTED FROM `interpret` 2026-08-16 (tabling roadmap §1.0) SO THERE IS EXACTLY ONE DRIVER.
`interpret` seeds a plan from a fresh root frame; `resume_continuation` (`Tabling.jl`) seeds one from a
CAPTURED frame chain. Both must observe the same step cap, the same diagnostic counter and the same
finished/root discipline — a second hand-rolled loop is how those silently diverge. This is a pure
extraction: `interpret` below is the same function with its body moved here.
"""
function _run_plan(plan::Vector{Tuple{Frame,Bindings}}, space)::Vector{Tuple{Atom,Bindings}}
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

"Run the minimal-MeTTa machine on `atom`; returns the list of (result, bindings)."
interpret(atom::Atom, space=nothing, b::Bindings=Bindings())::Vector{Tuple{Atom,Bindings}} =
    _run_plan(Tuple{Frame,Bindings}[(Frame(atom, collect_vars(atom), nothing, no_handler, false, 0), b)], space)

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
# arg_actual_types memo (ADR-059). A GROUND atom's actual types are invariant until a `(: …)` decl mutates the
# space, so cache atom → (objectid(space), type_epoch, types). On a later reduction step the same ground
# subterm is a HIT instead of an O(term) re-query — collapsing the O(n²) re-descent (the dominant typed-program
# allocator, ~71–79% of typed-Peano alloc) to O(n). Byte-identical to recomputation (semantics-preserving):
# only `:`-decls change types and they bump type_epoch; the space objectid guards against a stale cross-space hit.
const _ATOM_TYPE_MEMO = Dict{Atom,Tuple{UInt,Int,Vector{Atom}}}()
const _TYPE_MEMO_ON = Ref(true)     # gate for one release; health 4/4 proves parity before it's load-bearing
const _TYPE_MEMO_CAP = 1 << 20      # bound growth on long-running servers (clears wholesale on overflow)
const _DECL_TYPE_MEMO = Dict{Atom,Tuple{UInt,Int,Vector{Atom}}}()   # declared-types memo (atom_types); same keying/invalidation as _ATOM_TYPE_MEMO

const NO_TYPES = Atom[]     # shared empty-types sentinel (no caller mutates an atom_types result); same
                            # zero-alloc convention as EMPTY_VARS — the early-return below is alloc-free.
# the declared types of `atom`: intrinsic grounded-op type (if any) + space decls (: atom $T)
function atom_types(atom::Atom, space::Space)::Vector{Atom}
    # A VARIABLE has no declared type (types.rs:386). The `(: $v $T)` query below would otherwise unify $v
    # with EVERY `(: X …)` decl in the space and return all their types — the "spuriously matches every decl"
    # hazard already noted at arg_actual_types. This surfaces when an expression has a VARIABLE HEAD, e.g. a
    # let* binding pair `($r1 (Add Z Z))`: its head `$r1` was typed by this query, and a 1-arg arrow decl like
    # `(: assert (-> Atom (->)))` matched the pair's arity and leaked its `(->)` return into inference,
    # producing a spurious `(BadArgType 1 Expression ->)` in unrelated type-checked code (regressed b5).
    # Guard is alloc-free (early return + no query) — the OLD path ran a full-space `(: $v $T)` scan per
    # var-headed subterm; measured atom_types(Var) 0 ns vs the query cost.
    atom isa Var && return NO_TYPES
    # DECLARED-type memo (mirrors the arg_actual_types memo, ADR-059): a ground atom's declared types depend
    # ONLY on the space's `:` decls (which bump type_epoch), so cache by (atom, space identity, epoch). The
    # head-op lookup in metta_instr runs atom_types(op) on EVERY application; memoising it collapses the
    # per-reduction `(: op $T)` space-query to a hit (the dominant cost on untyped/var-heavy libs like PLN).
    # Ground-only; a var-headed Expression recurses uncached exactly as before. Byte-identical to recomputation.
    if _TYPE_MEMO_ON[] && !(atom isa Expression && atom.has_vars)
        sid = objectid(space)
        hit = get(_DECL_TYPE_MEMO, atom, nothing)
        (hit !== nothing && hit[1] == sid && hit[2] == space.type_epoch) && return hit[3]
        res = _atom_types_uncached(atom, space)
        length(_DECL_TYPE_MEMO) < _TYPE_MEMO_CAP || empty!(_DECL_TYPE_MEMO)
        _DECL_TYPE_MEMO[atom] = (sid, space.type_epoch, res)
        return res
    end
    _atom_types_uncached(atom, space)
end
function _atom_types_uncached(atom::Atom, space::Space)::Vector{Atom}
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
    # GROUND-atom memo (ADR-059): a var-free atom's actual types depend ONLY on the space's `:` decls, so they
    # are stable until type_epoch changes. Cache by (space identity, epoch) ⇒ each distinct ground subterm is
    # typed ONCE, then hit on every later reduction step — the O(n²)→O(n) re-descent collapse (the dominant
    # typed-program allocator). `_has_vars` (the existing cached bit) is the cacheability predicate; a
    # var-containing arg recurses uncached exactly as before. Byte-identical to recomputation.
    if _TYPE_MEMO_ON[] && !(arg isa Expression && arg.has_vars)   # ground ⇒ memoisable (Var/Grounded returned above)
        sid = objectid(space)
        hit = get(_ATOM_TYPE_MEMO, arg, nothing)
        (hit !== nothing && hit[1] == sid && hit[2] == space.type_epoch) && return hit[3]
        res = _arg_actual_types_uncached(arg, space)
        length(_ATOM_TYPE_MEMO) < _TYPE_MEMO_CAP || empty!(_ATOM_TYPE_MEMO)   # bound growth (risk #3)
        _ATOM_TYPE_MEMO[arg] = (sid, space.type_epoch, res)
        return res
    end
    _arg_actual_types_uncached(arg, space)
end

# the uncached body (Expression head-type application + declared-type fallthrough); semantics UNCHANGED. The
# recursive arg_actual_types calls below re-enter the memoized entry above, so each ground child is a memo hit.
function _arg_actual_types_uncached(arg::Atom, space::Space)::Vector{Atom}
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
            is_present(mb, X) || continue                # resolve-filter (identical to Eval.jl :309)
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
# Kept for reference/back-compat; the REGISTRY binds the seam-routed pair below.
const DIVIDE = _num_binop("/", /)
const MOD    = _num_binop("%", %)
const DIVIDE_SEAM = _num_binop_seam("/", seam_div)
const MOD_SEAM    = _num_binop_seam("%", seam_mod)
const GT = _num_cmp(">", >); const LE = _num_cmp("<=", <=); const GE = _num_cmp(">=", >=)
const EQ_OP = Grounded(Operation("==", xs -> length(xs) != 2 ? ExecNoReduce() :
    (xs[1] == UNDEFINED || xs[2] == UNDEFINED) ? ExecOk(Atom[UNDEFINED]) :        # WFS bottom contagious through ==
    ExecOk(Atom[xs[1] == xs[2] ? Sym("True") : Sym("False")])))
# Bool logic (grounded; True/False are symbols)
_to_bool(a::Atom) = a == Sym("True") ? true : a == Sym("False") ? false : nothing
function _bool_binop(name, f)
    Grounded(Operation(name, function (xs)
        length(xs) == 2 || return ExecNoReduce()
        # WFS: an undefined operand makes and/or undefined. SOUND (never a wrong definite answer), but
        # OVER-CONSERVATIVE — full Kleene (⊥∧False=False, ⊥∨True=True) is a deferred precision refinement.
        (xs[1] == UNDEFINED || xs[2] == UNDEFINED) && return ExecOk(Atom[UNDEFINED])
        x = _to_bool(xs[1]); y = _to_bool(xs[2])
        (x === nothing || y === nothing) ? ExecNoReduce() : ExecOk(Atom[f(x, y) ? Sym("True") : Sym("False")])
    end))
end
const AND = _bool_binop("and", &)
const OR  = _bool_binop("or", |)
const NOT = Grounded(Operation("not", xs -> length(xs) != 1 ? ExecNoReduce() :
    xs[1] == UNDEFINED ? ExecOk(Atom[UNDEFINED]) :                                # ¬⊥ = ⊥ (WFS Kleene = plain propagate)
    (tb = _to_bool(xs[1])) !== nothing ? ExecOk(Atom[tb ? Sym("False") : Sym("True")]) : ExecNoReduce()))
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
const SIZE_ATOM = Grounded(Operation("size-atom", xs -> length(xs) != 1 ? ExecNoReduce() :
    xs[1] == UNDEFINED ? ExecOk(Atom[UNDEFINED]) :                                # WFS bottom contagious through strict ops
    xs[1] isa Expression ? ExecOk(Atom[Grounded(length(xs[1].children))]) : ExecNoReduce()))
const INDEX_ATOM = Grounded(Operation("index-atom", function (xs)
    any(a -> a == UNDEFINED, xs) && return ExecOk(Atom[UNDEFINED])   # WFS bottom contagious through strict ops
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
# sort-atom / sort-strings (hyperon string.rs:65 / stdlib.metta:1292 ; LeaTTa sortAtomOp): the expression
# with its children sorted by PRINTED form. Both names share one op (LeaTTa Stdlib.lean:247-248). A genuine
# primitive — Core has no atom-ordering op to compose from; CeTTa and LeaTTa both ground it.
const SORT_ATOM = Grounded(Operation("sort-atom", function (xs::Vector{Atom})
    (length(xs) == 1 && xs[1] isa Expression) || return ExecNoReduce()
    ExecOk(Atom[Expression(sort(xs[1].children; by=string))])
end))
const ASSERT_ALPHA_EQUAL_TO_RESULT = Grounded(SpaceOp("assertAlphaEqualToResult", function (xs, space)
    (length(xs) == 2 && xs[2] isa Expression) || return ExecNoReduce()
    Set(_alpha1(x) for x in metta_run(xs[1], space)) == Set(_alpha1(x) for x in xs[2].children) ?
        ExecOk(Atom[UNIT]) : ExecOk(Atom[_assert_fail("assertAlphaEqualToResult", xs[1], xs[2])])
end))
# ── space-argument resolution, failing CLOSED ─────────────────────────────────────────────────────
#
# `get-atoms`/`match`/`add-atom`/`remove-atom` each used to write
#     tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space
# which silently retargets the AMBIENT space whenever argument 1 is not a Space. For an unresolved
# token or an unbound variable that is the documented `&self` default and stays. But when argument 1
# is a Grounded holding a CONCRETE non-Space value, the caller unambiguously meant a specific space
# and named something else — and the op would carry on and report success against the wrong store.
#
# That is the fail-OPEN shape this project bans, in the worst possible place: the ambient space during
# a `lib/pln` evaluation is the RULE LIBRARY, so `(add-atom <not-a-space> (belief …))` writes a fact
# into the space that holds `(= (Truth_Deduction …) …)` and returns unit. Nothing would surface it.
#
# This distinction is also the precondition for a multi-backend Space (ADR-016): the moment a
# MORK-trie-backed store can be passed as an argument, "not the concrete `Space` struct" stops meaning
# "not a space" — and a silent fallback would send those writes to the interpreter's own store.
# Returns `nothing` for "a concrete value that is not a Space"; callers must refuse.
@inline function _space_arg(a::Atom, ambient::Space)::Union{Space,Nothing}
    a isa Grounded || return ambient                 # unresolved token / variable ⇒ &self, as before
    a.value isa Space ? a.value::Space : nothing     # concrete non-Space ⇒ caller fails closed
end

# get-atoms (hyperon space.rs:127, type (-> Space Atom)): one result per atom of the space, variables
# freshened (make_variables_unique). NOTE: Core FLATTENS imported stdlib into &self rather than keeping
# it as a grounded child-space (hyperon's model), so `(get-atoms &self)` here returns the flattened rules
# — the f1 directive that expects an empty &self at start-up stays a documented known-gap.
const GET_ATOMS = Grounded(SpaceOp("get-atoms", function (xs, space)
    length(xs) == 1 || return ExecNoReduce()
    tgt = _space_arg(xs[1], space)
    tgt === nothing && return ExecRuntime("get-atoms: first argument is not a Space")
    own = own_atoms(tgt)                                    # own atoms only — not the imported library
    ExecOk(Atom[rename_fresh(a) for a in own])
end))
const CONTEXT_SPACE = Grounded(SpaceOp("context-space", (xs, space) -> ExecOk(Atom[Grounded(space)])))
# all binding sets under which `pat` matches some atom of `space`, extending `b0`
function _match_pat(space::Space, pat::Atom, b0::Bindings)::Vector{Bindings}
    out = Bindings[]
    for atom in all_atoms(space), mb in match_atoms(subst(pat, b0), rename_fresh(atom))
        append!(out, merge_bindings(b0, mb))
    end
    out
end
# match (grounded): (match <space> <pattern> <template>). A `(, p1 p2 …)` pattern is a CONJUNCTION —
# all sub-patterns must match with consistent bindings (a join). Carries bindings to the caller.
const MATCH = Grounded(SpaceOp("match", function (xs, space)
    length(xs) == 3 || return ExecNoReduce()
    tgt = _space_arg(xs[1], space)                          # named space or &self
    tgt === nothing && return ExecRuntime("match: first argument is not a Space")
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
    # foldl FORKS over a nondeterministic op: each op result is an independent accumulator path.
    # Verified 3-engine (hyperon/CeTTa/MeTTa-TS): fold (superpose ((+ $a $b)(* $a $b))) over (1 2) → {0,2,2,3},
    # not one path. Deterministic ops (sum-list/product-list) keep exactly one accumulator, unchanged.
    accs = Atom[acc]
    for item in list.children
        next = Atom[]
        for a in accs
            rs = metta_run(_replace_var(_replace_var(op, avar, a), bvar, item), space)
            isempty(rs) ? push!(next, EMPTY) : append!(next, reverse(rs))   # reverse: forward order
        end
        accs = next
    end
    ExecOk(accs)
end))
# case (grounded SpaceOp): evaluate $atom, return the body of the first case pattern it matches
const CASE = Grounded(SpaceOp("case", function (xs, space)
    (length(xs) == 2 && xs[2] isa Expression) || return ExecNoReduce()
    # hyperon (stdlib.metta case §): an EMPTY result set matches the special `Empty` case pattern (NOT `()`).
    results = metta_run(xs[1], space); isempty(results) && (results = Atom[Sym("Empty")])
    out = Atom[]; binds = Bindings[]
    # case DISTRIBUTES over a nondeterministic scrutinee: EACH alternative independently yields its first
    # matching clause's body. Verified 4-engine (hyperon/CeTTa/MeTTa-TS/PeTTa): (superpose (a b c)) → [a,b,c],
    # not one result. A no-match alternative is dropped (hyperon/CeTTa arbiter). metta_run returns reverse
    # order, so iterate reversed to emit forward (cf. COLLAPSE above).
    for res in reverse(results)
        if res == UNDEFINED                                   # WFS bottom ⇒ undefined (no catch-all $other launder)
            push!(out, UNDEFINED); push!(binds, Bindings())
            continue
        end
        for clause in xs[2].children
            (clause isa Expression && length(clause.children) == 2) || continue
            ms = match_atoms(clause.children[1], res)
            if !isempty(ms)
                push!(out, subst(clause.children[2], ms[1])); push!(binds, ms[1])
                break                                         # first matching clause for THIS alternative
            end
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
# _collapse-add-next-atom-from-collapse-bind-result — the fold step upstream uses to turn
# `collapse-bind`'s `(Atom Bindings)` PAIRS into a plain tuple. Ported from hyperon
# `stdlib/core.rs:347-351`, typed there `(-> Expression Expression Atom)`, and used by upstream's own
# minimal-MeTTa definition of `collapse` (`stdlib.metta:1203-1209`).
#
# WHY IT EXISTS HERE: our INTERPRETER has a correct grounded `collapse` (COLLAPSE below), but the
# COMPILER lowers `collapse` into minimal MeTTa, where the only capture primitive is `collapse-bind` —
# which by contract returns pairs. Stripping them needs an append that minimal MeTTa does not have, so
# upstream grounds exactly this one step, and so do we.
const COLLAPSE_ADD_NEXT = Grounded(Operation("_collapse-add-next-atom-from-collapse-bind-result",
    function (xs::Vector{Atom})
        length(xs) == 2 || return ExecNoReduce()
        acc, item = xs[1], xs[2]
        acc isa Expression || return ExecNoReduce()
        # `item` is `(atom bindings)`; take the ATOM. Anything else passes through unchanged rather
        # than being silently dropped — a malformed pair is a bug to surface, not to hide.
        at = (item isa Expression && length((item::Expression).children) == 2) ?
             (item::Expression).children[1] : item
        # ⚠️ TWO DIFFERENCES THAT CANCEL, AND THAT IS A SMELL WORTH NAMING. This PREPENDS where
        # upstream's helper APPENDS, because `collapse_bind_op` yields alternatives in the opposite
        # order to hyperon's — which our own `COLLAPSE` already compensates for with
        # `reverse(metta_run(…))`. End to end the answer is right (5/5 engines agree on
        # `(collapse (match &self (foo $x) $x))` → `(bar baz)`), but a caller invoking THIS op directly
        # and expecting upstream's append semantics gets the other order.
        #
        # The principled fix is to make `collapse_bind_op` yield in hyperon's order and let this append
        # faithfully — one difference instead of two. Not done here because `collapse_bind_op` is under
        # test elsewhere and that is its own change with its own before/after.
        #
        # CeTTa has tests for exactly this surface (`tests/test_collapse_bind*.metta`,
        # `tests/test_collapse_add_next_atom_from_collapse_bind_result.metta`). They do NOT settle the
        # ordering question — they are written against CeTTa's symbolic `(Bindings …)` serialization,
        # so hyperon fails them too — but they do confirm our compiled lane and interpreter agree.
        # PREPENDS, where upstream's helper appends — the same
        # compensation our own `COLLAPSE` already makes. `collapse_bind_op` yields alternatives in the
        # opposite order to hyperon's, which is why `COLLAPSE` wraps `reverse(metta_run(…))`
        # (Eval.jl, `const COLLAPSE`). A fold that appended would produce `(baz bar)` where every other
        # engine returns `(bar baz)` — measured against hyperon, CeTTa, PeTTa and our interpreter.
        ExecOk(Atom[Expression(Atom[at, (acc::Expression).children...])])
    end))

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
# fork-space (hyperon; LeaTTa Eval.lean:776): a fresh space seeded with a SNAPSHOT of the parent's
# atoms — an INDEPENDENT copy, so a later add/remove on the fork does NOT propagate to the parent (the
# c2_spaces isolation contract: parent→(A), child→(A B), grandchild→(A)). `Space(atoms)` rebuilds the index;
# lib_count is preserved so `get-atoms` on the fork still excludes flattened library atoms.
const FORK_SPACE = Grounded(Operation("fork-space", function (xs::Vector{Atom})
    (length(xs) == 1 && xs[1] isa Grounded && xs[1].value isa Space) || return ExecNoReduce()
    parent = xs[1].value
    fork = clone_store(parent)
    ExecOk(Atom[Grounded(fork)])
end))
const ADD_ATOM = Grounded(SpaceOp("add-atom", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    tgt = _space_arg(xs[1], space)
    tgt === nothing && return ExecRuntime("add-atom: first argument is not a Space")
    add_atom!(tgt, xs[2])
    ExecOk(Atom[Expression(Atom[])])             # unit ()
end))
const REMOVE_ATOM = Grounded(SpaceOp("remove-atom", function (xs, space)
    length(xs) == 2 || return ExecNoReduce()
    tgt = _space_arg(xs[1], space)
    tgt === nothing && return ExecRuntime("remove-atom: first argument is not a Space")
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
    "+" => PLUS, "-" => MINUS, "*" => TIMES, "/" => DIVIDE_SEAM, "%" => MOD_SEAM,
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
    "sort-atom" => SORT_ATOM, "sort-strings" => SORT_ATOM,
    "get-type" => GET_TYPE, "foldl-atom" => FOLDL_ATOM, "case" => CASE,
    "new-state" => NEW_STATE, "get-state" => GET_STATE, "change-state!" => CHANGE_STATE, "nop" => NOP,
    "println!" => PRINTLN_BANG, "trace!" => TRACE_BANG,
    "_collapse-add-next-atom-from-collapse-bind-result" => COLLAPSE_ADD_NEXT,
    "bind!" => BIND_TOKEN, "new-space" => NEW_SPACE, "fork-space" => FORK_SPACE,
    # new-mork-space (c2_spaces): the corpus tests that the fork-space ISOLATION CONTRACT holds for
    # "MORK-backed" spaces identically to plain ones — an interpreter Space provides exactly that contract
    # (as does LeaTTa's proved model, whose new-mork-space is likewise a plain space). Core's real MORK
    # substrate is a separate lane (mc_run/DualTrack); backing this op with it is a future integration, not
    # required by the contract the op's stdlib semantics specify. So it aliases new-space here.
    "new-mork-space" => NEW_SPACE,
    "add-atom" => ADD_ATOM, "remove-atom" => REMOVE_ATOM,
    "import!" => IMPORT, "table!" => TABLE_DECL, "auto-table!" => AUTO_TABLE_DECL, "tnot" => TNOT)
# add-atom/remove-atom take the atom UNEVALUATED (hyperon AddAtomOp type_ = (-> Space Atom (->))) — the
# atom is stored as-is, not reduced. Atom-typed 2nd arg ⇒ the driver passes it unevaluated. Intrinsic
# (kept out of the space). Defined here, after the ops exist.
_GROUNDED_OP_TYPES[ADD_ATOM]    = "(-> %Undefined% Atom (->))"
_GROUNDED_OP_TYPES[REMOVE_ATOM] = "(-> %Undefined% Atom (->))"
# get-atoms returns the space's atoms as INERT DATA (hyperon GetAtomsOp::type_ = (-> Space Atom),
# interpreter.rs:1005 `typ == Atom ⇒ return result verbatim`). Without this the result took the untyped
# path and was re-mettad under the caller's %Undefined% type — so an enumerated stored rule like
# `(= (r) (add-atom &d …))` had its body RE-REDUCED and its side effect RE-FIRED (get-atoms returned
# `(= (r) ())`, the body reduced to unit). The `Atom` return type is load-bearing: it routes enumerated
# results through the type==Atom short-circuit so bodies are never reduced. Space arg = %Undefined%
# (a grounded Space's actual type is reported as SpaceType, not the stdlib `Space`, so a literal
# `(-> Space Atom)` mis-fires as BadArgType). Verified: enumeration inert + basic get-atoms unchanged,
# byte-matching hyperon/PeTTa/CeTTa. This was an original OMISSION at get-atoms' introduction (638bc7f);
# every sibling stored-atom op (add-atom/remove-atom/== /state) had its intrinsic type — get-atoms alone did not.
_GROUNDED_OP_TYPES[GET_ATOMS]   = "(-> %Undefined% Atom)"
_GROUNDED_OP_TYPES[TRACE_BANG]  = "(-> %Undefined% Atom %Undefined%)"   # arg1 raw so (trace! msg (quote …)) works
# == is polymorphic same-type (hyperon (-> $t $t Bool)) → the checker emits (BadArgType 2 …) on a
# mismatch like (== 5 "S"). Now safe: the iterative driver doesn't overflow on the typed path (this
# crashed the recursive driver). Intrinsic (out of the space, can't disturb match &self).
_GROUNDED_OP_TYPES[EQ_OP]       = "(-> \$t \$t Bool)"

# Hex digit → value, or -1. Allocation-free: the first version of the `\x`/`\u{}` decoding called
# `tryparse(UInt8, String(cs[j:j]); base=16)`, which allocates a 1-element Char slice AND a String PER
# DIGIT inside the lexer's inner loop. Nothing measured it; it was simply the wrong tool for reading
# one character.
@inline _hexval(c::Char)::Int =
    ('0' <= c <= '9') ? Int(c) - Int('0') :
    ('a' <= c <= 'f') ? Int(c) - Int('a') + 10 :
    ('A' <= c <= 'F') ? Int(c) - Int('A') + 10 : -1

# ⚠️ ESCAPE HANDLING vs UPSTREAM (hyperon-experimental `lib/src/metta/text.rs:534-600`).
# Decoded here: `\n` `\r` `\t` `\"` `\\` `\'`, plus `\xNN` (exactly two hex digits) and `\u{X…}`
# (BRACED, up to 8 hex digits — upstream's `parse_unicode_sequence` requires the braces; a bare
# `\u0041` is NOT a unicode escape there either). The `\x`/`\u` forms were added 2026-08-12 after a
# randomized wire-form property measured them decoding to the literal text `x41`/`u0041`.
#
# ONE DELIBERATE DIVERGENCE REMAINS: on a MALFORMED or UNKNOWN escape (`\q`, `\xZZ`, `\u{}`) upstream
# produces an "Invalid escape sequence" error node, while this drops the backslash and keeps the
# character. Not changed here because rejecting input that Core currently accepts is a behavioural
# change that needs its own corpus pass — recorded so it is a decision rather than an oversight.
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
                    if d == 'x' && i + 2 <= n                # \xNN — EXACTLY two hex digits, high<<4|low
                        hi = _hexval(cs[i+1]); lo = _hexval(cs[i+2])
                        if hi >= 0 && lo >= 0
                            push!(buf, Char((UInt32(hi) << 4) | UInt32(lo))); i += 2
                        else
                            push!(buf, d)                    # malformed: literal, see the note below
                        end
                    elseif d == 'u' && i + 1 <= n && cs[i+1] == '{'   # \u{X…} — BRACED, up to 8 hex digits
                        j = i + 2; acc = UInt32(0); ndig = 0; ok = true
                        while j <= n && cs[j] != '}'
                            dv = _hexval(cs[j])
                            (dv < 0 || ndig >= 8) && (ok = false; break)
                            acc = (acc << 4) | UInt32(dv); ndig += 1; j += 1
                        end
                        if ok && j <= n && cs[j] == '}' && ndig > 0 && acc <= 0x10FFFF
                            push!(buf, Char(acc)); i = j
                        else
                            push!(buf, d)
                        end
                    else
                        push!(buf, d == 'n' ? '\n' : d == 't' ? '\t' : d == 'r' ? '\r' : d)
                    end
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
function load_metta!(space::Space, text::AbstractString; as_library::Bool=false, auto_table::Bool=false)::Vector{Atom}
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
    as_library && seal_library!(space)
    auto_table && !as_library && auto_table!(space)   # opt-in: auto-table the just-loaded user program's pure fns
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
include("NumpyOps.jl")   # MeTTa↔Julia numeric adapter (numpy-equivalent grounded ops)
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
            # 🔴 THE ASSERT FAMILY — added 2026-08-15 after MEASURING where the cold start goes.
            # Phase breakdown of a cold `a1_symbols.metta` run (`julia --project=Core`, 2 runs):
            #     using MeTTaCore 2653 ms · Space() 1 ms · load_core_stdlib! 23 ms
            #     **run the file 3968 ms**  ⇒ TOTAL 6645 ms
            # The same file evaluates in 21-60 ms on the warm server, so those ~4 s are FIRST-CALL
            # JIT, not work — 60% of the cold start, and the largest single item.
            # ⚠️ THE WORKLOAD ABOVE MISSES THE PATH REAL FILES TAKE. It exercises the primitives
            # (arith, let*, map/filter/foldl, match, get-type, collapse) but NOT the assert family —
            # and `assertEqual` (127 uses) + `assertEqualToResult` (92) are what essentially every
            # conformance script and library test is BUILT from. `assertEqualToResult` reduces via
            # `collapse` + `subtraction-atom`/`union-atom` (stdlib.metta:39-47), a distinct chain
            # from anything above, so none of its specializations were being traced into the image.
            load_metta!(sp, "!(assertEqual (+ 1 2) 3)")
            load_metta!(sp, "!(assertEqualToResult (superpose (1 2)) (1 2))")
            load_metta!(sp, "!(assertAlphaEqual (foo \$x) (foo \$y))")
            # `match` against a populated space returning MULTIPLE results — the conformance corpus's
            # dominant shape (a1_symbols.metta is exactly this), distinct from the single-result
            # `(rel a b)` match above.
            load_metta!(sp, "(colour red) (colour green) (colour blue)")
            load_metta!(sp, "!(match &self (colour \$c) \$c)")
        catch
        end
    end
end

end # module
