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

# ── JOIN ORDERING — the single largest lever on this substrate ───────────────────────────────────
# MORK's own wiki (`MORK.wiki/Backward-Forward-Chainer-optimization.md`) records a **~1500×** speedup
# from reordering conjuncts ALONE — same rules, same engine, same answers:
#
#     BEFORE  (, (sol $ski $shi (c: … $b) $f) (decFn $shi $hi) (lte $hi $ki))
#     AFTER   (, (gte $ki $hi) (incFn $hi $shi) (sol $ski $shi (c: … $b) $f))
#     16s → milliseconds;  imim1: 25m5s → 0.885s
#
# Their diagnosis was 220M trie transitions against only 10K unifications — nearly all the time in
# trie SEARCH, because a conjunct iterated a variable that a later conjunct would have bound.
#
# We already own a cost-based planner: `MorkSupercompiler/src/planner/` (891 LOC — Selectivity,
# QueryPlanner, Statistics), wired into SCPipeline stage 2, MGCompiler and Stepper. The emitter was
# the one consumer that did not call it, so it emitted conjuncts in whatever order A-normalization
# produced. MEASURED before this: the compiled lane ran ECAN_Policies in 28.5 ms against the
# interpreter's 10.9 ms — a comparison taken on an UNPLANNED join, and therefore not a fair verdict
# on the execution model.
import MorkSupercompiler: JoinNode, plan_join_order, SAtom, EFF_READ

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

"""Escape a string for the IL wire form, matching what `Eval.tokenize` decodes and what upstream
hyperon's `parse_string` accepts (`lib/src/metta/text.rs:550-573`).

🔴 MEASURED — the write side escaped NOTHING while the read side has decoded escapes all along:

    Grounded("has\"quote")   wrote  "has"quote"    read back  "has"      TRUNCATED
    Grounded("back\\slash")   wrote  "back\\slash"    read back  "backslash" CORRUPTED

The backslash case is the worse one: it comes back a plausible-looking string with a character silently
removed, so nothing downstream can tell. A randomized `parse(il_text(a)) == a` property found both;
neither corpus did, because no corpus script contains a quote or a backslash inside a string literal.

Newline/tab are escaped too, though a raw one happens to survive our lexer: IL clauses are LINE-ORIENTED
on the wire, so a literal newline inside a clause would split it for any line-based consumer."""
_escape_il_string(s::AbstractString)::String = replace(String(s),
    "\\" => "\\\\", "\"" => "\\\"", "\n" => "\\n", "\r" => "\\r", "\t" => "\\t")

function render(a::IRGrounded)::String
    # Escaped via the shared `_escape_il_string` — the two producers must agree on the wire form,
    # and `test_emit_il.jl` asserts that. Unescaped, a string containing `"` or `\\` is
    # truncated or silently corrupted on read (measured 2026-08-12).
    a.ty === GROUNDED_STRING && return "\"" * _escape_il_string(string(a.value)) * "\""
    string(a.value)
end

function render(a::IRExpression)::String
    # The unit atom: head is the unwritable `UNIT_HEAD` sentinel and there are no args. Rendering the
    # head would produce `(())`, and rendering it as `:Nil` used to produce `(Nil)` — a DIFFERENT atom.
    _is_unit(a) && return "()"
    "(" * join(String[render(a.head); String[render(x) for x in a.args]], " ") * ")"
end

"An `IRExpression` that IS the unit atom `()` — the sentinel head, no arguments."
_is_unit(a::IRExpression)::Bool =
    isempty(a.args) && a.head isa IRSymbol && (a.head::IRSymbol).name === UNIT_HEAD

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

"""
Apply a variable substitution to rendered text, matching WHOLE variable names only.

⚠️ THE PREVIOUS IMPLEMENTATION CORRUPTED ANY VARIABLE THAT HAD A SUBSTITUTED NAME AS A PREFIX, and its
docstring claimed a protection the body did not provide: *"longest names first so `\$x1` is not
clobbered by `\$x`"*. Sorting by length only helps when `x1` is ITSELF a key. When the substitution is
just `x → pinned`, a plain `replace` rewrites `\$x1` too. MEASURED 2026-08-07 end-to-end:

    (= (bug \$x1) (let \$x pinned (pair \$x \$x1)))
      before  (exec 0 (, (bug pinned1)) (O (+ (pair pinned pinned1))))
      after   (exec 0 (, (bug \$x1))    (O (+ (pair pinned \$x1))))

`\$x1` is a DIFFERENT variable and the head argument. Corrupting it to the literal `pinned1` turned a
rule matching any `(bug …)` into one matching a single atom that never occurs. Silent, and invisible
to coverage — the clause still counted as emitted. `\$xs` and `\$x_2` failed identically.

ONE PASS over whole `\$name` tokens, each looked up independently: order-insensitive by construction,
so a substitution can no longer partially rewrite a name it does not own. The real fix is to
substitute on the typed IR by `NodeId` — variable IDENTITY, which the frontend already resolves —
rather than on rendered text at all; this makes the text path correct in the meantime.
"""
function _apply_subst(txt::String, sub::Dict{Base.Symbol,String})::String
    isempty(sub) && return txt
    replace(txt, r"\$[A-Za-z_][A-Za-z0-9_\-]*" =>
                 m -> String(get(sub, Base.Symbol(SubString(m, 2)), m)))
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

# ── join ordering ────────────────────────────────────────────────────────────────────────────────

"""
Variables mentioned in a rendered source term, as bare names (`\$x` → `\"x\"`).

NO CAPTURE GROUP, deliberately. `m.captures[1]` is typed `Union{Nothing,SubString}` because a group
may not participate, so building a `Set{String}` from it makes `convert(String, nothing)` reachable —
JET reported exactly that as a possible error (2026-08-07). The group here can never fail to
participate, but the TYPE says otherwise, which is both a latent `MethodError` and a type
instability. Matching the whole `\$name` and dropping the sigil is provably `String`.
"""
_term_vars(s::AbstractString)::Set{String} =
    Set{String}(String(SubString(m.match, 2)) for m in eachmatch(r"\$[A-Za-z_][A-Za-z0-9_\-]*", s))

"""
    _plan_sources(srcs) -> Vector{String}

Reorder exec source conjuncts by the cost-based planner, leaving `srcs[1]` (the redex) pinned first.

THE REDEX IS PINNED, and that is deliberate: it is what the rule fires on, so narrowing the trie on
it before anything else is always right, and it is the only conjunct guaranteed present.

Everything after it is planned. Variable flow is computed the way `build_join_nodes` does it — a
variable is INTRODUCED by the first conjunct that mentions it and CONSTRAINS every later one — and
`plan_join_order` then greedily picks the lowest effective cardinality given what is already bound,
penalising unbound dependencies (`UNBOUND_DEP_PENALTY = 4`).

Cardinality is a static placeholder: at emit time there is no space to count against, so every
conjunct is given equal weight and the ordering is driven purely by variable binding. That is the
part the wiki's example turns on — `(gte \$ki \$hi)` first because `\$ki` is already bound, not
because it is smaller. When emission gains access to live statistics, pass real counts here instead.
"""
function _plan_sources(srcs::Vector{String})::Vector{String}
    length(srcs) <= 2 && return srcs                # redex + at most one goal: nothing to order
    redex, rest = srcs[1], srcs[2:end]

    bound = _term_vars(redex)                       # the redex binds first
    nodes = JoinNode[]
    introduced = copy(bound)
    for s in rest
        vs = _term_vars(s)
        out = setdiff(vs, introduced)               # variables this conjunct introduces
        inn = intersect(vs, introduced)             # variables it constrains
        union!(introduced, out)
        push!(nodes, JoinNode(SAtom(s), 1, out, inn, EFF_READ))
    end
    perm = try
        plan_join_order(nodes)
    catch
        return srcs                                 # planner unavailable ⇒ emit unplanned, never fail
    end
    (length(perm) == length(rest) && sort(perm) == collect(1:length(rest))) || return srcs
    String[redex; rest[perm]]
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
                     publish::Bool = false,
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
        # A CALLED head must also publish `(=val redex v)`. The `pure` sink's first argument is the
        # TEMPLATE (grounding.mm2:36-40 writes `(NormalizedResult $name (f64 $res))` that way), so the
        # keyed form is a second sink over the same expression rather than a second stage.
        pure1 = "(pure \$__r \$__r ($cast $tree))"
        publish || return "(exec $priority (, $redex) (O $pure1))"
        pure2 = "(pure (=val $redex \$__r2) \$__r2 ($cast $tree))"
        return "(exec $priority (, $redex) (O $pure1 $pure2))"
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

    # Conjunct ORDER is the largest performance lever on this substrate (~1500x upstream). See
    # `_plan_sources` — the redex stays pinned first, the rest go through the cost-based planner.
    srcs = _plan_sources(srcs)
    tmpl = publish ? "(+ " * out * ") (+ (=val " * redex * " " * out * "))" : "(+ " * out * ")"
    "(exec $priority (, " * join(srcs, " ") * ") (O " * tmpl * ")"[1:end] * ")"
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


# ── THE STAGED CALL CONVENTION ───────────────────────────────────────────────────────────────────
#
# `emit_clause` declines every clause whose body calls another defined function, because a reduction
# consumes its redex and adds a BARE value: `(= (g) 42)` turns `(g)` into `42` and never creates
# anything a caller could match. The fix is a KEYED RESULT — reduction additionally publishes
# `(=val (g) 42)`, which IS matchable — plus staging so the callee publishes before the caller looks.
#
# Four stages, the shape of upstream `MORK/kernel/resources/grounding.mm2` (exec 0/1/2 add-only,
# exec 3 deletes only intermediates):
#
#   DEMAND   (exec d (, (f)) (O (+ (g))))                              -- (f) present ⇒ want (g)
#   PRODUCE  (exec p (, (g)) (O (+ 42) (+ (=val (g) 42))))             -- bare answer + keyed result
#   CONSUME  (exec q (, (f) (=val (g) $t)) (O (+ $t) (+ (=val (f) $t))))
#   CLEANUP  (exec c (, (=val $__k $__v)) (O (- (=val $__k $__v))))    -- intermediates only
#
# PRODUCE and CONSUME are the SAME rule: a non-leaf consumes its callees' keyed results and produces
# its own. Only the stage number differs.
#
# WHY `(=val k v)` AND NOT RESULT-AS-LAST-ARGUMENT. `GCall` renders `(g $t)`, and `SPECMAP:84` flags
# these as two competing conventions to be chosen between deliberately. Result-as-last-argument
# cannot work here for the reason above, and it also COLLIDES with data: `(parent $x $y)` is a fact,
# and appending an output turns a 2-ary fact into a 3-ary pattern that matches nothing (this exact
# bug shipped once). Keying on the whole redex has neither problem, and `(=val …)` doubles as the
# fired-marker the exec calculus otherwise lacks.

"""
    _call_term(g, sub) -> String | nothing

The CALLEE TERM of a call — `(g a\$_1…a\$_n)`, arity n, NO appended output. This is what DEMAND adds
and what the `(=val …)` key is built from, so it must be byte-identical to the callee's own redex as
`clause_redex` renders it — the two are matched against each other through the trie.
"""
function _call_term(g::GCall, sub::Dict{Base.Symbol,String})::Union{String,Nothing}
    parts = String[String(g.head)]
    for a in g.args
        s = render(a); startswith(s, "<unrenderable") && return nothing
        push!(parts, _apply_subst(s, sub))
    end
    "(" * join(parts, " ") * ")"
end

"""
    _call_graph(clauses, funs) -> Dict{Symbol,Set{Symbol}}

head ⇒ the defined heads its clauses call. Calls to MORK pure ops are excluded: nothing publishes a
`(=val …)` for them, so they can never be staged.
"""
function _call_graph(clauses::Vector{ANClause},
                     funs::Set{Base.Symbol})::Dict{Base.Symbol,Set{Base.Symbol}}
    g = Dict{Base.Symbol,Set{Base.Symbol}}()
    for cl in clauses
        s = get!(() -> Set{Base.Symbol}(), g, cl.name)
        for goal in cl.goals
            goal isa GCall && goal.head in funs && push!(s, goal.head)
        end
    end
    g
end

"""
    _cyclic_heads(graph) -> Set{Symbol}

Heads that lie on, or reach, a call cycle. Staging assigns each head a stage from its call DEPTH, and
a cycle has no finite depth — so recursive heads are excluded and keep the honest decline. Direct
self-recursion counts: a head calling itself is a 1-cycle.

Declining is the correct behaviour rather than a gap to paper over. A recursive call needs a fixpoint
at ONE stage (or a trampoline), not a deeper stage; emitting it with a made-up depth would produce a
rule that fires once and then silently stops, which is worse than not emitting it.
"""
function _cyclic_heads(graph::Dict{Base.Symbol,Set{Base.Symbol}})::Set{Base.Symbol}
    color = Dict{Base.Symbol,Int}()             # 0 unvisited · 1 on the current path · 2 finished
    bad = Set{Base.Symbol}()
    function dfs(n::Base.Symbol)::Bool          # true ⇒ n lies on or reaches a cycle
        c = get(color, n, 0)
        c == 1 && (push!(bad, n); return true)  # back edge
        c == 2 && return n in bad
        color[n] = 1
        hit = false
        for k in get(graph, n, Base.Symbol[])
            haskey(graph, k) || continue
            dfs(k) && (hit = true)
        end
        color[n] = 2
        hit && push!(bad, n)
        hit
    end
    for n in keys(graph); dfs(n); end
    bad
end

"""
    _call_levels(graph, cyclic) -> Dict{Symbol,Int}

Longest call depth: 0 for a head that calls nothing, else `1 + max(level(callee))`. Cyclic heads are
skipped. This is `KBSaturation._stratify`'s job — dependency graph ⇒ strata under a strictly-greater
constraint — reused in shape, with producer/consumer edges in place of negation edges.
"""
function _call_levels(graph::Dict{Base.Symbol,Set{Base.Symbol}},
                      cyclic::Set{Base.Symbol})::Dict{Base.Symbol,Int}
    lvl = Dict{Base.Symbol,Int}()
    function level(n::Base.Symbol)::Int
        haskey(lvl, n) && return lvl[n]
        lvl[n] = 0
        best = 0
        for k in get(graph, n, Base.Symbol[])
            (haskey(graph, k) && !(k in cyclic)) || continue
            best = max(best, level(k) + 1)
        end
        lvl[n] = best
    end
    for n in keys(graph)
        n in cyclic || level(n)
    end
    lvl
end

"""
Does `node` mention any variable in `names`? Used to reject the one staged shape that cannot work:
arithmetic FEEDING a call.

    (= (f \$x) (g (+ \$x 1)))        DEMAND would have to add `(g \$__t1)` before `\$__t1` is computed

DEMAND fires on the redex alone, so a callee term containing a not-yet-computed value would be added
with an unbound variable — matching everything, or nothing. Arithmetic AFTER a call is fine, because
the CONSUME rule already has the result bound by its `(=val …)` source. Declining the feeding shape is
honest; handling it needs a compute stage ahead of DEMAND.
"""
function _mentions_var(node::IRAtom, names::Set{Base.Symbol})::Bool
    node isa IRVariable && return (node::IRVariable).name in names
    for c in children(node)
        _mentions_var(c, names) && return true
    end
    false
end

"""
    emit_clause_staged(clause, level, lmax; priority, funs) -> Vector{String} | nothing

A clause whose body calls defined functions, as DEMAND + PRODUCE/CONSUME rules. `nothing` when it
falls outside the staged fragment — an arithmetic body (the `pure` sink path in `emit_clause` already
handles it), a call to an undefined head, or anything unrenderable.

STAGE NUMBERING, and why it degenerates correctly. With `L = level(head)` and `M = lmax`:

    DEMAND          priority + (M − L)     callers demand BEFORE callees, so depth descends
    PRODUCE/CONSUME priority + M + L       callees publish BEFORE callers read, so depth ascends
    CLEANUP         priority + 2M + 1      (emitted by `emit_program`)

When no clause has a call, `M = 0` and every head has `L = 0`, so PRODUCE lands on `priority` and
CLEANUP on `priority + 1` — exactly the two-stage scheme this file already used. The staged numbering
is a generalisation of it, not a replacement, which is why call-free clauses keep byte-identical
output when nothing in the program is staged.
"""
function emit_clause_staged(clause::ANClause, level::Integer, lmax::Integer;
                            priority::Integer = 0,
                            funs::Set{Base.Symbol} = Set{Base.Symbol}())::Union{Vector{String},Nothing}
    sub = _unify_subst(clause.goals)
    sub === nothing && return nothing

    env = _arith_env(clause.goals)
    env === nothing && return nothing

    # ── ARITHMETIC AND CALLS MAY NOW SHARE A BODY ────────────────────────────────────────────────
    # Two guards used to forbid it independently: `n_arith == n_goals` in `emit_clause` and
    # `g.head in funs` here, whose comment read "a pure op publishes no `(=val …)`". True — but a pure
    # op does not NEED one. It is COMPUTED in the `pure` sink, exactly as the call-free arithmetic
    # path already does; only a call to a DEFINED function needs a keyed result. The boundary was
    # drawn before staging existed and nothing re-examined it after.
    #
    # MEASURED 2026-08-07 over the corpus: 65 declined clauses have no blocker but this, 121 once
    # comparisons are included. The declines were reported as `mixed_arithmetic`, and a probe of mine
    # mis-attributed them to "undefined head" by checking `MORK.PURE_OPS` (whose keys are `sum_i64`,
    # not `+`) instead of `_ARITH_I64`.
    calls = GCall[]
    for g in clause.goals
        g isa GCall && push!(calls, g)
    end
    isempty(calls) && return nothing             # no call ⇒ the plain path already emits it

    staged = GCall[]
    for g in calls
        if g.head in funs
            push!(staged, g)                     # needs DEMAND + a `(=val …)` source
        elseif is_arith(g.head)
            continue                             # computed in the `pure` sink below
        else
            return nothing                       # genuinely unsupported head
        end
    end
    isempty(staged) && return nothing            # all-arithmetic ⇒ `emit_clause`'s own path owns it

    # Arithmetic FEEDING a call cannot be staged — see `_mentions_var`.
    if !isempty(env)
        avars = Set{Base.Symbol}(keys(env))
        for g in staged, a in g.args
            _mentions_var(a, avars) && return nothing
        end
    end

    redex_parts = String[String(clause.name)]
    for a in clause.head_args
        s = render(a); startswith(s, "<unrenderable") && return nothing
        push!(redex_parts, _apply_subst(s, sub))
    end
    redex = "(" * join(redex_parts, " ") * ")"

    srcs = String[redex]; demands = String[]
    for g in clause.goals
        g isa GUnify && continue
        if g isa GCall
            is_arith(g.head) && continue         # COMPUTED, not matched — no source, no demand
            ct = _call_term(g, sub); ct === nothing && return nothing
            o = _apply_subst(render(g.out), sub)
            startswith(o, "<unrenderable") && return nothing
            push!(demands, "(+ " * ct * ")")
            push!(srcs, "(=val " * ct * " " * o * ")")
        else
            s = render_goal(g); s === nothing && return nothing
            push!(srcs, _apply_subst(s, sub))
        end
    end

    # The reduct: matched directly, or COMPUTED when the body ends in arithmetic. `_arith_tree` renders
    # a variable it does not own as "a real input variable", which is precisely what a `(=val …)`
    # source binds — so a call result flows into the arithmetic with no extra machinery.
    local tmpl::String
    if isempty(env)
        out = _apply_subst(render(clause.out), sub)
        startswith(out, "<unrenderable") && return nothing
        tmpl = "(+ " * out * ") (+ (=val " * redex * " " * out * "))"
    else
        float = _needs_f64(clause.out, env)
        float && _has_mod(clause.out, env) && return nothing   # `%` is int-only; un-typeable
        tree = _arith_tree(clause.out, env, float, sub)
        tree === nothing && return nothing
        cast = float ? "f64_to_string" : "i64_to_string"
        tmpl = "(pure \$__r \$__r ($cast $tree)) " *
               "(pure (=val $redex \$__r2) \$__r2 ($cast $tree))"
    end

    srcs = _plan_sources(srcs)
    String[
        "(exec $(priority + lmax - level) (, $redex) (O " * join(demands, " ") * "))",
        "(exec $(priority + lmax + level) (, " * join(srcs, " ") * ") (O " * tmpl * "))",
    ]
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

    # CONTROL-FLOW EXPANSION RUNS FIRST, and the order is load-bearing. `_call_graph` walks only the
    # TOP-LEVEL goal list, so a `GCall` nested inside a branch arm is invisible to it — build the graph
    # before expanding and those calls get no stage and never compile. Expanding first is what makes
    # `if`/`case`/`superpose` bodies stageable at all.
    paths = Vector{Vector{ANClause}}()          # one entry per SOURCE clause, ≥1 path each
    for cl in clauses
        e = expand_control(cl)
        push!(paths, e === nothing ? ANClause[cl] : e)   # unexpandable ⇒ carried, declines as before
    end
    flat = ANClause[p for ps in paths for p in ps]

    # Call depth drives stage assignment. Cyclic heads get no depth and keep the plain path's decline.
    graph  = _call_graph(flat, funs)
    cyclic = _cyclic_heads(graph)
    levels = _call_levels(graph, cyclic)
    lmax   = isempty(levels) ? 0 : maximum(values(levels))
    # Heads someone actually calls. Only these publish `(=val …)`; publishing for every head would
    # double the write volume of a 1000-clause program to produce keys nothing ever reads.
    called = Set{Base.Symbol}()
    for (_, cs) in graph, c in cs
        push!(called, c)
    end

    rules = String[]; declined = ANClause[]; redexes = String[]; seen = Set{String}()
    nemit = 0; nstaged = 0; nexpanded = 0
    for (i, cl) in enumerate(clauses)
        ps = paths[i]
        got = String[]; rxs = String[]; ok = true; staged_here = false
        for pc in ps
            lv = get(levels, pc.name, 0)
            # A call-free clause emits at its own level; `lmax + lv` is `priority` when nothing is staged.
            one = emit_clause(pc; priority = priority + lmax + lv,
                              publish = pc.name in called, funs = funs)
            g = if one !== nothing
                String[one]
            elseif pc.name in cyclic
                nothing                              # recursion: no finite stage exists
            else
                emit_clause_staged(pc, lv, lmax; priority = priority, funs = funs)
            end
            # PARTIAL EXPANSION IS NEVER EMITTED. Three arms of four is a silently dropped answer, and
            # a rule that cannot fire is worse than an absent one — so one failing path fails the clause.
            g === nothing && (ok = false; break)
            one === nothing && (staged_here = true)
            append!(got, g)
            rx = clause_redex(pc)
            rx === nothing || push!(rxs, rx)
        end
        if !ok
            push!(declined, cl); continue
        end
        staged_here && (nstaged += 1)
        length(ps) > 1 && (nexpanded += 1)
        nemit += 1                                   # EMITTED counts SOURCE CLAUSES, not rules
        append!(rules, got)
        for rx in rxs                                # each arm specialises the redex differently
            rx in seen || (push!(seen, rx); push!(redexes, rx))
        end
    end

    # Cleanup — AFTER every producer has fired, at one stage past the deepest PRODUCE/CONSUME.
    cstage = priority + 2 * lmax + 1
    deletions = String["(exec $(cstage) (, $rx) (O (- $rx)))" for rx in redexes]
    if nstaged > 0
        # Intermediates only, never source atoms — the `grounding.mm2` discipline. One generic rule
        # rather than one per key: `(=val …)` is our own vocabulary, so nothing else can match it.
        push!(deletions, "(exec $(cstage) (, (=val \$__k \$__v)) (O (- (=val \$__k \$__v))))")
    end
    (; rules = vcat(rules, deletions), emitted = nemit, staged = nstaged, expanded = nexpanded,
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
    decline_histogram(clauses) -> (; paths, fully, expanded)

Declines grouped by reason across a whole program. Returns TWO tallies, because one of them
answers "what do I build next" and the other does not:

  * `paths`  — blocked EXECUTION PATHS per reason. Expansion MULTIPLIES clauses (fib becomes two),
               so a clause with three paths blocked three ways contributes three entries here.
  * `fully`  — clauses that fixing ONE class would fully unblock, i.e. where EVERY blocked path
               shares the same reason. **This is the aiming number.** fib is the counter-example:
               path 1 blocks on `call_in_body`, path 2 on `mixed_arithmetic`, so fib appears twice
               in `paths` and in NEITHER row of `fully` — fixing either class alone still leaves it
               declined.
  * `expanded` — how many declining clauses `expand_control` successfully expanded.

🔴 THIS FUNCTION USED TO REPORT SOMETHING ELSE, AND IT DROVE TWO WRONG PLANS IN TWO DAYS.
It called `emit_clause` on the RAW clause, so a clause carrying a `GBranch` was attributed
`control_flow` — even though `emit_program` runs `expand_control` FIRST (`:815`) and the real
blocker lies inside an arm. MEASURED on the 26-script conformance corpus when the expansion was
added here:

    reason              RAW (pre-expansion)     AFTER expand_control
    control_flow                 7                       0     <- vanishes entirely
    call_in_body                18                      27     <- becomes the largest class
    mixed_arithmetic             2                       8
    residual                    23                      24

`control_flow` going to ZERO is `expand_control` working exactly as `b6c0d6c` intended — control
flow COMPILES, and a stale histogram was hiding that. The ranking also INVERTED: `residual` was
cited at 57.5% and aimed at; the real top class is `call_in_body`. This index has recorded that
ranking inverting once before, which is why the reason is recomputed here rather than cached.

⚠️ `fully` is deliberately NOT derivable from `paths`. Summing paths per reason answers "how much
work is blocked", never "which clauses a fix releases", and only the second one is a plan.

⚠️ AND `fully` MEANS "ALL **BLOCKED** PATHS AGREE", NOT "one fix from correct". A clause may have
some paths emitting and some blocked; only the blocked ones are counted. For a two-armed `if` with
one arm emitting and one blocked, that is not a working function. Nor is the class a WORK ITEM — it
is a symptom label, and nothing here checks that twenty `call_in_body` clauses need the same fix.

── WHAT THE NUMBERS ACTUALLY REST ON (measured by construction 2026-08-15, three probes) ─────────
Read these before citing any row above; each retired a ranking this histogram had produced.

 1. CONTROL FLOW COMPILES. `expand_control` (`b6c0d6c`) removes every `GBranch` in the corpus —
    `control_flow` goes 7 -> 0 once expansion runs. It was never a blocker; it was this function
    reporting the first reason on an unexpanded clause.

 2. `Emit.jl` EMITS A BODY ONLY IF EVERY CALL IS ONE OF `+ - * % /`, OR THERE ARE NO CALLS AT ALL.
    Verified directly: `(= (green \$x) (frog \$x))` DECLINES — one call, no arithmetic, no branch, no
    recursion, the floor case. `(= (g \$x) \$x)` emits (no call). `(= (inc \$n) (+ \$n 1))` emits.
    So `call_in_body` and `mixed_arithmetic` are ONE wall reported from two sides, and the
    A/B/C shape split in the corpus measures composition, not difficulty.

 3. `_ARITH_I64` IS A TYPED ADMISSION GATE, NOT A LIST — and this is the one that would have shipped
    a silent defect. Adding `:< => "lt_i64"` at runtime makes the clause EMIT:
        (exec 0 (, (m \$x)) (O (pure \$__r \$__r (i64_to_string (lt_i64 ...)))))
    …and then it RUNS, consumes the redex, and WRITES NOTHING. steps=1, trie still holds `(m 1)`,
    interpreter says `True`. No error. `lt_i64` returns the raw byte `\x01` (vendored note,
    `PureOpArity.jl:520`) and the emitter hardcodes `i64_to_string`, which cannot render it.
    🔴 `PURE_OPS` HAS NO BOOL RENDERER AT ALL — only `i8/i16/i32/i64/i128/f32/f64_to_string`. So a
    predicate's result cannot round-trip through the `pure` sink, and THAT is why exactly five ops
    are in this table: they are the ones whose results the sink can render.
    ⇒ comparisons are a DESIGN question (a Bool cast that yields the SYMBOL `True`, matchable by a
    `GUnify`), not a missing dictionary row. The table should carry name -> (op, result cast) so a
    row without a cast fails AT EMISSION rather than dropping an answer at runtime.
"""
function decline_histogram(clauses::Vector{ANClause})
    funs = Set{Base.Symbol}(c.name for c in clauses)   # hoisted: was rebuilt PER CLAUSE (O(n^2))
    paths = Dict{Base.Symbol,Int}(); fully = Dict{Base.Symbol,Int}(); expanded = 0
    for cl in clauses
        emit_clause(cl; funs = funs) === nothing || continue
        e = expand_control(cl)
        if e === nothing                                # unexpandable — attribute the clause itself
            r = decline_reason(cl)
            paths[r] = get(paths, r, 0) + 1
            fully[r] = get(fully, r, 0) + 1
            continue
        end
        expanded += 1
        reasons = Base.Symbol[]
        for p in e
            emit_clause(p; funs = funs) === nothing || continue
            push!(reasons, decline_reason(p))
        end
        isempty(reasons) && continue                    # every path emits after expansion
        for r in reasons
            paths[r] = get(paths, r, 0) + 1
        end
        u = unique(reasons)
        length(u) == 1 && (fully[u[1]] = get(fully, u[1], 0) + 1)
    end
    (; paths, fully, expanded)
end

export render, render_goal, emit_clause, emit_clause_staged, emit_program, decline_reason, decline_histogram

end # module CompilerEmit
