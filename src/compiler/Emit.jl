# Emit.jl — the Core MeTTa compiler, stage 4: A-normalized clauses → executable exec rules.
#
# Stage 1 `IR.jl` (node set) → stage 2 `Frontend.jl` (resolution) → stage 3 `ANormal.jl` (goal lists)
# → THIS. The first stage whose output actually runs: it renders a compiled clause into MORK's exec
# calculus and hands it to `space_metta_calculus!` on a `CoreSpace`.
#
# ─── ONE EMITTER, ONE DECISION ───────────────────────────────────────────────────────────────────
# Every syntactic choice about the exec form — the source functor, the template functor, the
# priority, the arity — is made HERE and nowhere else. That is the point of having an IR at all.
# When the same decision is spelled out at N call sites it drifts: the source functor was hand-typed
# at four sites in this tree and three were wrong, and the upstream MORK binary panicked on all
# three (`sources.rs:233`). One emitter cannot drift from itself.
#
# ─── THE EXEC CONTRACT (verified against the upstream MORK binary, 2026-08-06) ────────────────────
#   (exec <loc> <pattern> <template>)
#   pattern  functor: `,` = plain trie patterns   |  `I` = TYPED sources only (BTM/ACT/z3/==/!=)
#   template functor: `,` = plain additions       |  `O` = typed sinks (`+` add, `-` remove, `pure`)
# A compiled MeTTa clause has PLAIN patterns, so it is always `,` on the source side. MEASURED:
#   (exec 0 (, (id $x)) (O (+ $x) (- (id $x))))  → runs; yields `a`,`b`; redexes deleted
#   (exec 0 (I (id $x)) (O (+ $x) (- (id $x))))  → panicked at kernel/src/sources.rs:233
#
# ─── RESULT-AS-LAST-ARGUMENT ─────────────────────────────────────────────────────────────────────
# `ANormal` lowers a MeTTa function to a relation by appending its output variable to the head
# (PeTTa `translate_clause/3`, `append(HeadArgs,[Out],FinalArgs)`). The emitter preserves that: a
# clause `f(a₁…aₙ, Out) :- G₁…Gₖ` becomes an exec whose SOURCE is the goal conjunction and whose
# TEMPLATE derives the head. Goals and head share one variable namespace, which resolution
# guaranteed — MORK variables are POSITIONAL, so a shared `$x` must be textually identical.
#
# ─── SCOPE, STATED HONESTLY ──────────────────────────────────────────────────────────────────────
# Emits the FORWARD-DERIVATION form for clauses whose goals are all `GCall`/`GUnify` — the fragment
# with a direct exec reading. `GBranch`/`GDisj`/`GFindall`/`GResidual` are NOT emitted; `emit_clause`
# returns `nothing` and `emit_program` counts them. That count is the coverage number, and it is
# reported rather than hidden: a compiler that silently drops what it cannot handle is how a lane
# comes to return `String[]` with an empty space.

module CompilerEmit

using ..CompilerIR
using ..CompilerANormal
import ..CompilerANormal: Goal, GUnify, GCall, GBranch, GDisj, GFindall, GResidual, ANClause

# MORK owns the pure-op namespace; the emitter validates every name it emits against it (below).
import MORK

# ── rendering IR back to s-expression text ───────────────────────────────────────────────────────
# Text, not bytes, for now: MORK's `space_add_all_sexpr!` is the stable entry, and the byte-level
# `Expr` path is an optimisation that must not be conflated with getting the semantics right.

"Render an IR node as MeTTa s-expression text."
function render end

render(a::IRSymbol)::String        = String(a.name)
render(a::IRPredefined)::String    = String(a.name)
render(a::IRResolvedSymbol)::String = String(a.name)

# A variable's TEXT is its written name. Resolution gave it a unique id for reasoning; the id must
# NOT reach the text, because two clauses that each wrote `$x` are separate rules and MORK scopes
# variables per rule. Within one clause, sameness of name is exactly sameness of variable — which is
# the invariant resolution established.
render(a::IRVariable)::String      = "\$" * String(a.name)

function render(a::IRGrounded)::String
    a.ty === GROUNDED_STRING && return "\"" * string(a.value) * "\""
    string(a.value)
end

render(a::IRExpression)::String =
    "(" * join(String[render(a.head); String[render(x) for x in a.args]], " ") * ")"

# Total, so an unhandled node is a visible marker rather than a MethodError mid-emit.
render(a::IRAtom)::String = "<unrenderable:" * string(nameof(typeof(a))) * ">"

# ── goals → exec source terms ────────────────────────────────────────────────────────────────────

"""
    render_goal(g) -> String | nothing

A goal as one exec SOURCE term. `nothing` means "not emittable in this form" and propagates up to
`emit_clause`, which then declines the whole clause rather than emitting a partial rule.

`GCall(f, args, out)` → `(f args… out)` — result-as-last-argument, so a functional call reads as a
relational pattern the trie can match.

`GUnify(l, r)` is NOT a source term: unification is expressed by the two sides SHARING A VARIABLE
NAME in the emitted text, so it is applied as a substitution before rendering (see `_unify_subst`)
and contributes no pattern of its own.
"""
function render_goal(g::GCall)::Union{String,Nothing}
    parts = String[String(g.head)]
    for a in g.args
        s = render(a); startswith(s, "<unrenderable") && return nothing
        push!(parts, s)
    end
    o = render(g.out); startswith(o, "<unrenderable") && return nothing
    push!(parts, o)
    "(" * join(parts, " ") * ")"
end
render_goal(::Goal)::Union{String,Nothing} = nothing

"""
    _unify_subst(goals) -> Dict{Base.Symbol,String}

Collapse `GUnify` goals into a variable→text substitution.

`let` was lowered to a unification goal; MORK has no unification GOAL, only shared variable names, so
the binding is discharged textually here. Only variable-headed unifications are handled — a
destructuring `let` (`(let (\$a \$b) …)`) yields a non-variable pattern and is declined upstream.
"""
function _unify_subst(goals::Vector{Goal})::Union{Dict{Base.Symbol,String},Nothing}
    sub = Dict{Base.Symbol,String}()
    for g in goals
        g isa GUnify || continue
        if g.lhs isa IRVariable
            s = render(g.rhs); startswith(s, "<unrenderable") && return nothing
            sub[(g.lhs::IRVariable).name] = s
        elseif g.rhs isa IRVariable
            s = render(g.lhs); startswith(s, "<unrenderable") && return nothing
            sub[(g.rhs::IRVariable).name] = s
        else
            return nothing            # structural unification — not expressible as a rename
        end
    end
    sub
end

"Apply a variable substitution to rendered text. Longest names first so `\$x1` is not clobbered by `\$x`."
function _apply_subst(txt::String, sub::Dict{Base.Symbol,String})::String
    isempty(sub) && return txt
    for k in sort(collect(keys(sub)); by = s -> -length(String(s)))
        txt = replace(txt, "\$" * String(k) => sub[k])
    end
    txt
end

# ── grounded arithmetic → the `pure` sink ────────────────────────────────────────────────────────
# An arithmetic call must COMPUTE, not match. Emitted as a source pattern, `(+ $x 1 $out)` would look
# for a stored atom of that shape and find nothing. MORK's answer is the `pure` sink: the value is
# computed write-side in the TEMPLATE.
#
# Contract (MORK `kernel/Pure.jl` PureSink): leaves are wrapped `<t>_from_string`, the root
# `<t>_to_string`, nesting allowed. Mode is INFERRED, not declared — i64 for `+ - * %`; any `/` or
# float literal forces f64 and propagates up. `%` is int-only and `/` is float-only in MeTTa's own
# semantics, so a tree mixing them is un-typeable and REJECTED rather than guessed.

const _ARITH_I64 = Dict{Base.Symbol,String}(
    :+ => "sum_i64", :- => "sub_i64", :* => "product_i64", :% => "mod_i64", :/ => "div_i64")
const _ARITH_F64 = Dict{Base.Symbol,String}(
    :+ => "sum_f64", :- => "sub_f64", :* => "product_f64", :/ => "div_f64")   # no `%` on floats

const _ARITH_CASTS = ("i64_to_string", "i64_from_string", "f64_to_string", "f64_from_string")

# ── VALIDATE THE NAMES AGAINST MORK'S OWN REGISTRY, AT LOAD ──────────────────────────────────────
# MORK owns the pure-op namespace (`MORK.PURE_OPS`, 369 ops). Every name above must exist there or
# the emitter produces a rule that is syntactically fine and semantically dead — the sink would have
# no function to apply, and nothing would say so.
#
# This must be a RUNTIME query, not a source grep: several ops (the shifts, and others) are GENERATED
# at the end of `Pure.jl` rather than written as literals, so `sum_i64` and `product_i64` do not
# appear in the file's text at all while being perfectly well registered. Asking the source would
# have "proved" they were missing. Ask the runtime.
#
# Fails at MODULE LOAD, not at emit time: a name typo is a build error, never a silently dead rule.
function _validate_pure_ops()
    missing_ops = String[]
    for tbl in (_ARITH_I64, _ARITH_F64), op in values(tbl)
        haskey(MORK.PURE_OPS, op) || push!(missing_ops, op)
    end
    for c in _ARITH_CASTS
        haskey(MORK.PURE_OPS, c) || push!(missing_ops, c)
    end
    isempty(missing_ops) ||
        error("CompilerEmit: these pure ops are NOT in MORK.PURE_OPS — the emitter would produce " *
              "dead rules: " * join(sort(unique(missing_ops)), ", "))
    nothing
end
_validate_pure_ops()

is_arith(name::Base.Symbol)::Bool = haskey(_ARITH_I64, name)

"""
    _arith_env(goals) -> Dict{Base.Symbol,GCall} | nothing

Map each temporary produced by an ARITHMETIC goal back to the goal that produced it.

A-normalization flattened `(+ \$x 1)` into a goal sequence threading fresh temps; the `pure` sink
wants the TREE back. This is the inverse map, and `_arith_tree` walks it to re-nest.
"""
function _arith_env(goals::Vector{Goal})
    env = Dict{Base.Symbol,GCall}()
    for g in goals
        g isa GCall || continue
        is_arith(g.head) || continue
        g.out isa IRVariable || return nothing
        env[(g.out::IRVariable).name] = g
    end
    env
end

"Does this arithmetic tree require f64? Any `/`, or any float literal, forces it — and propagates."
function _needs_f64(node::IRAtom, env::Dict{Base.Symbol,GCall})::Bool
    node isa IRGrounded && return node.ty === GROUNDED_FLOAT
    node isa IRVariable || return false
    g = get(env, (node::IRVariable).name, nothing)
    g === nothing && return false
    g.head === :/ && return true
    any(a -> _needs_f64(a, env), g.args)
end

"Is `%` present anywhere in the tree? (int-only; cannot coexist with a float mode)"
function _has_mod(node::IRAtom, env::Dict{Base.Symbol,GCall})::Bool
    node isa IRVariable || return false
    g = get(env, (node::IRVariable).name, nothing)
    g === nothing && return false
    g.head === :% && return true
    any(a -> _has_mod(a, env), g.args)
end

"""
    _arith_tree(node, env, float, sub) -> String | nothing

Render an arithmetic tree as a nested pure-op expression, wrapping non-arith leaves in
`<t>_from_string`. `nothing` if any node falls outside the arithmetic fragment.
"""
function _arith_tree(node::IRAtom, env::Dict{Base.Symbol,GCall}, float::Bool,
                     sub::Dict{Base.Symbol,String})::Union{String,Nothing}
    cast = float ? "f64_from_string" : "i64_from_string"
    if node isa IRVariable
        g = get(env, (node::IRVariable).name, nothing)
        if g === nothing
            return "($cast " * _apply_subst(render(node), sub) * ")"   # a real input variable
        end
        tbl = float ? _ARITH_F64 : _ARITH_I64
        op = get(tbl, g.head, nothing)
        op === nothing && return nothing                                # e.g. `%` under f64
        parts = String[op]
        for a in g.args
            s = _arith_tree(a, env, float, sub); s === nothing && return nothing
            push!(parts, s)
        end
        return "(" * join(parts, " ") * ")"
    end
    s = render(node); startswith(s, "<unrenderable") && return nothing
    "($cast " * _apply_subst(s, sub) * ")"
end

# ── clauses → exec rules ─────────────────────────────────────────────────────────────────────────

"""
    emit_clause(clause; priority=0) -> String | nothing

One A-normalized clause as one exec rule, or `nothing` if it falls outside the emittable fragment.

    (= (f a₁…aₙ) body)   ⟹   (exec <priority> (, (f a₁…aₙ) G₁…Gₖ) (O (+ Out) (- (f a₁…aₙ))))

**REDUCTION, NOT FORWARD-DERIVATION.** MeTTa `(=)` is demand-driven reduction to normal form: the
REDEX is matched and CONSUMED, and the reduct is produced. It is not a Datalog rule deriving a head
from a body. An earlier draft of this function emitted `(exec 0 (, goals) (, (head Out)))` — the
arrow backwards — and on `(= (ancestor \$x \$y) (parent \$x \$y))` it produced a rule that queried
`parent` facts to derive `ancestor`. That is Datalog semantics, and this project has a standing
prohibition on treating `(=)` that way.

So the SOURCE is the redex `(f a₁…aₙ)` plus whatever goals compute the body, and the TEMPLATE is a
typed sink: `(+ Out)` adds the reduct, `(- (f a₁…aₙ))` deletes the redex that fired.

Note the redex carries NO appended output variable. Result-as-last-argument is how a FUNCTION CALL
becomes a matchable relational goal (`ANormal`'s `GCall`); the redex itself is the surface term as it
appears in the space, arity n.

FUNCTORS: source `,` (plain patterns — `I` means "typed source" and makes upstream MORK panic,
`sources.rs:233`), template `O` (typed sinks, required for `+`/`-`). Both verified against the
upstream binary; see the exec contract at the head of this file.
"""
function emit_clause(clause::ANClause; priority::Integer = 0,
                     funs::Set{Base.Symbol} = Set{Base.Symbol}())::Union{String,Nothing}
    sub = _unify_subst(clause.goals)
    sub === nothing && return nothing

    # ── 🔴 NO CALL IN A BODY CAN FIRE UNDER THE CURRENT CONVENTION ───────────────────────────────
    # A `GCall` renders as a source PATTERN with result-as-last-argument — `(f a₁…aₙ Out)`. For that
    # to match, an atom of that shape must EXIST in the space. Nothing ever puts one there:
    #
    #   `(= (g) 1000.0)`  emits  (exec 0 (, (g)) (O (+ 1000.0)))
    #
    # i.e. reduction CONSUMES `(g)` and adds a BARE `1000.0`. It never creates `(g 1000.0)`. So a
    # caller sourcing on `(g $t)` can never match its callee's output. The two halves do not
    # compose: reduction is term rewriting, the call convention assumes a persisted relation.
    #
    # MEASURED 2026-08-06, `lib/ecan/ECAN_Policies.metta` — 23 of 25 heads agreed, and the survivor
    # was exactly this:
    #     (= (apply-normalization!) (let $n (normalize-attention! (ecan-target-sti-sum)) True))
    #   emitted  (exec 0 (, (apply-normalization!) (ecan-target-sti-sum $__t3)) (O (+ True)))
    #   `(ecan-target-sti-sum $__t3)` matches nothing → rule never fires → `True` never produced,
    #   with no diagnostic. The interpreter yields `True`.
    #
    # So DECLINE ANY CLAUSE WITH A CALL IN ITS BODY. What remains — the fragment that genuinely runs
    # — is call-free reduction: constants and data-term bodies.
    #
    # ⚠️ ORDER IS LOAD-BEARING: this check must run AFTER the arithmetic path below, never before.
    # An arithmetic body IS a sequence of `GCall`s (`GCall(:+, …)`), but those are computed WRITE-SIDE
    # in the `pure` sink and need no source pattern, so the objection above does not apply to them.
    # Placing this loop first silently declined every arithmetic clause — MEASURED: `(inc 41)` went
    # from `42` back to an unreduced `(inc 41)`. Caught only because a regression test executed it.
    #
    # ⚠️ This is a real boundary, not a bug to patch. The existing lane stops in the same place:
    # its ZAM gate 4 rejects nested rule-head calls (`_mm2_head_below_top`), filed under the
    # innermost-evaluation-order problem. Crossing it needs a call convention that is chosen rather
    # than inherited — most likely driver-style residualization — and that is a design task.
    #
    # Until then the honest behaviour is to decline: a rule that cannot fire is WORSE than an absent
    # one, because coverage counts it as compiled and the failure is silent.

    # THE REDEX — the surface term as it appears in the space, arity n, no appended output.
    redex_parts = String[String(clause.name)]
    for a in clause.head_args
        s = render(a); startswith(s, "<unrenderable") && return nothing
        push!(redex_parts, _apply_subst(s, sub))
    end
    redex = "(" * join(redex_parts, " ") * ")"

    # ARITHMETIC BODY — the value is COMPUTED, not matched, so it becomes a `pure` sink in the
    # template rather than a source pattern. Detected by the clause's output resolving into the
    # arithmetic goal env; a mixed body (arith goals AND relational goals) is declined rather than
    # half-emitted.
    env = _arith_env(clause.goals)
    env === nothing && return nothing
    if !isempty(env)
        n_arith = length(env)
        n_goals = count(g -> g isa GCall, clause.goals)
        n_arith == n_goals || return nothing        # mixed relational + arithmetic — out of scope
        float = _needs_f64(clause.out, env)
        # `%` is int-only; if the same tree also forces f64 it is un-typeable, not a guess to make.
        float && _has_mod(clause.out, env) && return nothing
        tree = _arith_tree(clause.out, env, float, sub)
        tree === nothing && return nothing
        cast = float ? "f64_to_string" : "i64_to_string"
        return "(exec $priority (, $redex) (O (pure \$__r \$__r ($cast $tree))))"
    end

    for g in clause.goals
        g isa GCall && return nothing
    end

    # Goals that must hold to compute the body. The redex leads the conjunction: it is what the rule
    # fires on, and putting it first means the trie narrows on it before any goal is considered.
    srcs = String[redex]
    for g in clause.goals
        g isa GUnify && continue                    # discharged into `sub`
        s = render_goal(g)
        s === nothing && return nothing             # a goal outside the fragment ⇒ decline the clause
        push!(srcs, _apply_subst(s, sub))
    end

    out = _apply_subst(render(clause.out), sub)
    startswith(out, "<unrenderable") && return nothing

    "(exec $priority (, " * join(srcs, " ") * ") (O (+ " * out * ")))"
end

"""
    clause_redex(clause) -> String | nothing

The redex pattern this clause fires on — `(f a₁…aₙ)`. Needed by `emit_program` to emit ONE deletion
rule per distinct redex, rather than one per clause.
"""
function clause_redex(clause::ANClause)::Union{String,Nothing}
    sub = _unify_subst(clause.goals)
    sub === nothing && return nothing
    parts = String[String(clause.name)]
    for a in clause.head_args
        s = render(a); startswith(s, "<unrenderable") && return nothing
        push!(parts, _apply_subst(s, sub))
    end
    "(" * join(parts, " ") * ")"
end

"""
    emit_program(clauses) -> (rules, emitted, declined, deletions)

Emit every clause it can, as a TWO-STAGE program.

## Why two stages — a measured correctness bug, not a style choice

MeTTa is nondeterministic: when two clauses both match a redex, BOTH contribute answers. Emitting
each clause as a self-contained `(O (+ reduct) (- redex))` breaks that, because whichever rule fires
first deletes the redex and the others never match. MEASURED 2026-08-06 on

    (= (f 0) zero)
    (= (f \$x) other)

    interpreter  !(f 0)  ->  [other, zero]      <- correct
    compiled     space   ->  ["other"]          <- `zero` silently LOST

It does not show up on clauses with DISJOINT patterns (`(= (colour red) …)` / `(= (colour blue) …)`
both emit fine), which is exactly why a passing single-clause test proves nothing here.

## The fix, from upstream's own corpus

`MORK/kernel/resources/grounding.mm2` runs a staged pipeline — compute at `exec 0`/`1`/`2`, then
CLEAN UP at `exec 3` with a deletion-only rule `(exec 3 (, (NormalizedResult \$n \$x)) (O (- …)))`.
Additions in one stage, removals in the next, so every producer sees intact input.

Applied here:
  * stage `priority`     — every clause, ADD-ONLY: `(O (+ reduct))` / `(O (pure …))`
  * stage `priority + 1` — ONE deletion per DISTINCT redex: `(O (- redex))`

Deduplicating by redex text is what makes it once-per-redex rather than once-per-clause; two clauses
sharing a redex pattern must not both delete it.

## Known limitation, stated rather than hidden

A redex that matches NO clause is still deleted at the cleanup stage, whereas MeTTa leaves an
irreducible expression as itself. The single-stage form had the complementary flaw (it only deleted
on a fire, but lost answers). This is the same trade the existing reduction lane makes, and closing
it needs a fired-marker the exec calculus does not currently carry.
"""
function emit_program(clauses::Vector{ANClause}; priority::Integer = 0,
                      extra_funs::Set{Base.Symbol} = Set{Base.Symbol}())
    # The defined heads — a call to one of these is a legitimate source pattern, because some rule
    # produces it. Anything else must be a MORK pure op or the clause is declined (`emit_clause`).
    #
    # `extra_funs` MATTERS AND ITS ABSENCE IS A MEASUREMENT TRAP. MeTTa libraries call across files:
    # `lib/pln/*.metta` calls heads defined in sibling files. Scoping the set to ONE `emit_program`
    # call makes every cross-file call look unexecutable. MEASURED 2026-08-06: per-file scoping
    # reported 31.5% corpus coverage against 51.2% with the whole corpus in scope — a 20-point
    # artifact of how the measurement was driven, not a property of the compiler. Callers compiling
    # a multi-file program must pass every head in that program.
    funs = union(Set{Base.Symbol}(cl.name for cl in clauses), extra_funs)
    rules = String[]; declined = ANClause[]; redexes = String[]; seen = Set{String}()
    for cl in clauses
        r = emit_clause(cl; priority = priority, funs = funs)
        if r === nothing
            push!(declined, cl); continue
        end
        push!(rules, r)
        rx = clause_redex(cl)
        if rx !== nothing && !(rx in seen)
            push!(seen, rx); push!(redexes, rx)
        end
    end
    # Cleanup stage — one per distinct redex, AFTER every producer has fired.
    deletions = String["(exec $(priority + 1) (, $rx) (O (- $rx)))" for rx in redexes]
    (; rules = vcat(rules, deletions), emitted = length(rules),
       declined, deletions = length(deletions))
end

"""
    decline_reason(clause) -> Symbol

WHY this clause was not emitted. A count of declines says the compiler is incomplete; a reason says
WHERE to work next, which is the difference between a statistic and a plan.

  `:emitted`          — it was emitted (not declined)
  `:call_in_body`     — calls another defined function. THE BULK. Blocked on the call convention:
                        reduction consumes the redex and adds a bare value, so a caller's
                        `(f args result)` pattern can never match its callee's output.
  `:control_flow`     — `GBranch`/`GDisj`/`GFindall` — `if`/`case`/`superpose`/`collapse`.
  `:residual`         — a node A-normalization could not flatten (variable/compound head).
  `:mixed_arithmetic` — arithmetic mixed with relational goals in one body.
  `:structural_unify` — a destructuring `let` whose pattern is not a plain variable.
  `:ground_fact`      — no goals and nothing to compute; it is DATA, not a rule.

Ranking declines by reason is how the next fragment gets chosen by what actually blocks the corpus,
rather than by which feature sounds most impressive.
"""
function decline_reason(clause::ANClause)::Base.Symbol
    _unify_subst(clause.goals) === nothing && return :structural_unify
    gs = all_goals(clause.goals)
    any(g -> g isa GResidual, gs) && return :residual
    any(g -> g isa GBranch || g isa GDisj || g isa GFindall, gs) && return :control_flow
    env = _arith_env(clause.goals)
    env === nothing && return :structural_unify
    if !isempty(env)
        length(env) == count(g -> g isa GCall, clause.goals) || return :mixed_arithmetic
        return :emitted
    end
    any(g -> g isa GCall, clause.goals) && return :call_in_body
    :emitted
end

"""
    decline_histogram(clauses) -> Dict{Symbol,Int}

Declines grouped by reason across a whole program — the actionable form of "27.5% coverage".
"""
function decline_histogram(clauses::Vector{ANClause})::Dict{Base.Symbol,Int}
    h = Dict{Base.Symbol,Int}()
    for cl in clauses
        emit_clause(cl; funs = Set{Base.Symbol}(c.name for c in clauses)) === nothing || continue
        r = decline_reason(cl)
        h[r] = get(h, r, 0) + 1
    end
    h
end

export render, render_goal, emit_clause, emit_program, decline_reason, decline_histogram

end # module CompilerEmit
