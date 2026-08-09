# EmitIL.jl — the Core MeTTa compiler, stage 4a: A-normal goal lists → MINIMAL MeTTa (the MeTTa-IL).
#
# ─── THIS IS THE ARROW FIGURE 2 HAS ──────────────────────────────────────────────────────────────
# Hyperon Deep-Dive Whitepaper v5 §3.1 Fig 2 has exactly ONE compile arrow, MeTTa → MeTTa-IL. MM2
# kernels reach a node by a DASHED "runs on" edge — a peer, never a compilation target. Until now the
# compiler went `ANormal → Emit` directly, i.e. straight to MM2 exec atoms with no IR in between.
#
# The defect was never that `Emit.jl` emits MM2. SPECMAP C6, from the 2026-08-07 audit:
#
#     "Fig-2 REQUIRES an MM2 emitter; what it forbids is reaching MM2 WITHOUT PASSING THROUGH THE IR.
#      Emit.jl is the right component in the wrong POSITION; the fix is inserting the IR above it,
#      not deleting it."
#
# So this file goes BETWEEN them. `Emit.jl` keeps its job and gains a legitimate position.
# Full design + diagrams: `Core/docs/architecture/COMPILER_IL_STAGE.md`.
#
# ─── WHICH "MeTTa-IL" (SPECMAP C7 — three artifacts share the name) ──────────────────────────────
#   * Hyperon MINIMAL MeTTa — `eval/evalc/chain/unify/function/return/cons-atom/decons-atom/
#     collapse-bind/superpose-bind`. ← THIS is the target. `Eval.jl:40` MINIMAL_OPS already
#     implements and evaluates them, so the output is executable the moment it is produced.
#   * F1R3FLY MeTTaIL/GSLT — `theory`/equations/`~>` rewrites. That is what `MeTTaIL.jl` is. It
#     contains NONE of the instructions above and is NOT this stage; do not route through it.
#   * Fig-2 §3.3 "MeTTa-IL" — the ROLE (a compiler-friendly IR); minimal MeTTa is its concrete form.
#
# ─── THE ONE IDEA ────────────────────────────────────────────────────────────────────────────────
# A goal list is a CONJUNCTION. In minimal MeTTa a conjunction is a right-nested `chain`: bind an
# intermediate to a variable, continue with the template. A-normal form has already named every
# intermediate, so the two line up exactly — which is why this stage is a fold and not a rewrite.
#
#     (= (f $x …) (function ⟨chain of goals … (return $out)⟩))
#
# Instruction semantics are taken from the NORMATIVE table, `docs/specs/metta grammar/
# metta_language_spec.md` §3 (`chain` is 3-ary, `unify` is 4-ary), cross-checked against Eval.jl.
#
# ─── WHY THIS TARGET COVERS MORE THAN MM2 ────────────────────────────────────────────────────────
# `Emit.jl:30-31` states its own scope: it emits only clauses whose goals are ALL `GCall`/`GUnify`;
# `GBranch`/`GDisj`/`GFindall`/`GResidual` are declined. Minimal MeTTa has native forms for three of
# those four — `unify` is 4-ary so branches are native, `collapse-bind` is findall, and disjunction is
# just several `(=)` clauses. So 2-of-6 goal types becomes 5-of-6.
#
# ⚠️ That is a PREDICTION TO MEASURE on the corpus, not a claim. The ratchet reports the real number.
module CompilerEmitIL

using ..CompilerIR
using ..CompilerANormal
using ..CompilerEmit: render          # reuse the renderer — a second one would drift from the first

export emit_il_clause, emit_il_program, ILResult

"Result of lowering a program to minimal MeTTa. `declined` carries a REASON per clause, never a bare count."
struct ILResult
    clauses::Vector{String}
    emitted::Int
    expanded::Int                                       # extra clauses produced by GDisj expansion
    declined::Vector{Tuple{Base.Symbol, String}}        # (clause head, why)
end

# ── GDisj: an EMISSION decision, made here ───────────────────────────────────────────────────────
# `(superpose-bind …)` is NOT the right instruction: the spec table says it consumes "the result of
# collapse-bind", not an arbitrary branch list. Native MeTTa nondeterminism is MULTIPLE `(=)` clauses
# (§2.1 — several matching equalities yield several results), which is exactly what GDisj's own
# docstring says this decision should be:
#
#     "whether a disjunction becomes several MM2 exec rules or one is an EMISSION decision, and this
#      stage must not pre-empt it."
#
# So: one clause per branch, with the surrounding goals duplicated into each. Recursive, because a
# branch may itself contain a disjunction. `limit` is a runaway guard — a cross product of nested
# disjunctions is exponential, and silently emitting 10k clauses would be worse than declining.
function _expand_disj(gs::Vector{Goal}, limit::Int = 64)::Union{Vector{Vector{Goal}}, Nothing}
    i = findfirst(g -> g isa GDisj, gs)
    i === nothing && return Vector{Goal}[gs]
    d = gs[i]::GDisj
    out = Vector{Goal}[]
    for b in d.branches
        merged = vcat(gs[1:i - 1], b, gs[i + 1:end])
        sub = _expand_disj(merged, limit)
        sub === nothing && return nothing
        append!(out, sub)
        length(out) > limit && return nothing
    end
    out
end

# ── the fold: goals[i:end] → a right-nested chain terminating in `tail` ──────────────────────────
# Returns `nothing` if any goal in the sequence cannot be lowered, so a clause is declined WHOLE
# rather than emitted half-formed. A partially-lowered clause that still parses is the worst outcome:
# it counts as coverage and computes the wrong answer.
function _seq(gs::Vector{Goal}, i::Int, tail::String)::Union{String, Nothing}
    i > length(gs) && return tail
    cont = _seq(gs, i + 1, tail)
    cont === nothing && return nothing
    _instr(gs[i], cont)
end

_render_args(args::Vector{IRAtom})::String = join(String[render(a) for a in args], " ")

"`(unify <atom> <pattern> <then> <else>)` — spec §3. A failed unification yields `Empty`, Core's own
`EMPTY` sentinel (`Eval.jl:39`), so a non-matching clause contributes no result rather than erroring."
_instr(g::GUnify, cont::String)::String =
    "(unify " * render(g.lhs) * " " * render(g.rhs) * " " * cont * " (return Empty))"

"""`(chain (eval (f a b)) \$out ⟨cont⟩)` — spec §3: interpret the atom, substitute `<var>` in the template.

NOTE the direction. `ANormal` performs the functional→relational lowering (result-as-last-argument,
`f(a,b,Out)`) because Prolog and MM2 need a relation. Minimal MeTTa is FUNCTIONAL, so this stage puts
the result back where it belongs: `out` becomes the chain's binding variable, not an extra argument.
A-normal form is still the right input — it named the intermediate, which is precisely what `chain`
needs."""
_instr(g::GCall, cont::String)::String =
    "(chain (eval (" * String(g.head) * (isempty(g.args) ? "" : " " * _render_args(g.args)) * ")) " *
    render(g.out) * " " * cont * ")"

"""Branch — the condition's own goals run first, then a 4-ary `unify` against `True`.

`Emit.jl` declines this shape entirely: an MM2 exec atom has no then/else. Minimal MeTTa's `unify` IS
4-ary, so the branch is native. Both arms continue into `cont`, which duplicates the continuation
into each — correct, and the cost of not having a join point in a tree-shaped IL."""
function _instr(g::GBranch, cont::String)::Union{String, Nothing}
    thn = _seq(g.then, 1, cont); thn === nothing && return nothing
    els = _seq(g.els,  1, cont); els === nothing && return nothing
    _seq(g.cond, 1, "(unify " * render(g.condval) * " True " * thn * " " * els * ")")
end

"""`collapse` — `(chain (collapse-bind (function ⟨body … (return tmpl)⟩)) \$out ⟨cont⟩)`.

Spec §3: `collapse-bind` interprets an atom and returns a tuple of ALL its results. The body is a goal
sequence, so it is wrapped in `function`/`return` to become one interpretable atom."""
function _instr(g::GFindall, cont::String)::Union{String, Nothing}
    body = _seq(g.body, 1, "(return " * render(g.template) * ")")
    body === nothing && return nothing
    "(chain (collapse-bind (function " * body * ")) " * render(g.out) * " " * cont * ")"
end

# GDisj never reaches here — `_expand_disj` removes it before the fold. If one survives, that is a bug
# in the expansion, not a shape to improvise around, so decline loudly rather than guess.
_instr(::GDisj, ::String)::Nothing = nothing

# GResidual is, by definition, a node A-normalization could not flatten. Declining is the honest
# outcome; it is COUNTED, and the interpreter fallback still handles the clause.
_instr(::GResidual, ::String)::Nothing = nothing

"Why a clause could not be lowered — a reason string, so declines are diagnosable rather than a tally."
function _decline_reason(gs::Vector{Goal})::String
    for g in gs
        g isa GResidual && return "GResidual (unflattened node: " * string(nameof(typeof(g.node))) * ")"
    end
    for g in gs
        g isa GDisj && isempty((g::GDisj).branches) && return "GDisj with zero branches (emits nothing)"
    end
    any(g -> g isa GDisj, gs) && return "GDisj expansion exceeded the 64-clause limit"
    "a nested goal could not be lowered"
end

"""
    emit_il_clause(c::ANClause) -> Union{Vector{String}, Nothing}

Lower one A-normal clause to minimal-MeTTa `(= head body)` clauses. Returns several when the clause
contains a `GDisj` (one per branch), or `nothing` if it cannot be lowered at all.
"""
function emit_il_clause(c::ANClause)::Union{Vector{String}, Nothing}
    variants = _expand_disj(c.goals)
    variants === nothing && return nothing
    head = "(" * String(c.name) * (isempty(c.head_args) ? "" : " " * _render_args(c.head_args)) * ")"
    out = String[]
    for gs in variants
        body = _seq(gs, 1, "(return " * render(c.out) * ")")
        body === nothing && return nothing            # decline the clause WHOLE, never half of it
        push!(out, "(= " * head * " (function " * body * "))")
    end
    # A GDisj with ZERO branches expands to zero variants, so the loop above runs no iterations and
    # `out` is empty. Without this guard the clause counted as EMITTED while producing nothing —
    # measured on the corpus as "expanded = -1", which is how the bug surfaced at all. Emitting
    # nothing is not success; it is the silent-drop failure this stage exists to avoid.
    isempty(out) && return nothing
    out
end

"""
    emit_il_program(clauses) -> ILResult

Lower a whole program. Declines are recorded with reasons and never dropped: a stage that silently
discards what it cannot handle is how a lane comes to return `String[]` against a populated space.
"""
function emit_il_program(clauses::Vector{ANClause})::ILResult
    out = String[]
    declined = Tuple{Base.Symbol, String}[]
    nemit = 0
    nexpanded = 0
    for c in clauses
        r = emit_il_clause(c)
        if r === nothing
            push!(declined, (c.name, _decline_reason(c.goals)))
        else
            nemit += 1
            nexpanded += length(r) - 1
            append!(out, r)
        end
    end
    ILResult(out, nemit, nexpanded, declined)
end

end # module CompilerEmitIL
