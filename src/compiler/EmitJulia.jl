# EmitJulia.jl — the Core MeTTa compiler, stage 4c: A-normal clauses → JULIA CLOSURES.
#
# ─── WHY A THIRD EMITTER ─────────────────────────────────────────────────────────────────────────
# NOT for coverage. `Emit.jl`'s own §3.6 note settles that exam: "COVERAGE % IS NOT THE METRIC …
# widen ONLY when a NAMED control path that needs a PROPERTY is blocked". And the numbers agree —
# the residual-free CEILING is 758 (1000 clauses less the 242 carrying a `GResidual`), and `EmitIL`
# already reaches 742. Maximum possible gain over IL: SIXTEEN clauses. Coverage cannot justify this.
#
# What justifies it is DELIVERY and CONSTANT FACTOR:
#
#   1. DELIVERY. `Eval.rule_results` is the single equation-lookup seam, and a compiled head placed
#      there is reached by EVERY existing interpreter consumer WITHOUT A REWRITE — WorldModel keeps
#      calling `Interpreter` and gets compiled code underneath. That is what makes the standing
#      "compiler primary, interpreter fallback" directive true in practice rather than in routing.
#      No other emitter can produce that number: MM2 and IL are targets, not executors.
#   2. CONSTANT FACTOR. A closure runs as native Julia; the IL lane runs IL TEXT through the minimal
#      interpreter. If a closure is not faster than that, this emitter has no reason to exist —
#      which is why `tools/bench_fib.jl` closure-vs-interpreter is an ACCEPTANCE GATE, not a nicety.
#   3. And what MM2 structurally CANNOT do: `Emit.jl` records `GUnify`+`GFindall` = 73 of 279 blocked
#      paths on ECAN+PLN, "FREE on `Eval` and ABSENT from MM2 BY CONSTRUCTION". §3.6 scopes MM2 to
#      hot loops and says general symbolic code "belongs on the resolution engine". A closure over
#      `Eval` IS the resolution engine, compiled.
#
# ─── 🔴 THE TWO-BUILDER SPLIT, WHICH IS THE EASY MISTAKE ─────────────────────────────────────────
# `EmitIL` warns, and it is MEASURED: "The switch needs the SAME two-renderer split on the atom side:
# a `render`-equivalent builder for GCall/GUnify/GBranch/GFindall sites and this one for GResidual.
# Doing it with a single builder is the easy mistake, AND THE RATCHET WILL APPLAUD IT." Teaching the
# operand builder about `IRSpecial` widened MM2 376 → 378 while emitting a `match` its target could
# not run; it was given back. So:
#     operand positions (GCall args/out, GUnify sides) → `_atom_of(a, false)`   NO specials
#     GResidual nodes, which are handed to `interpret`  → `_atom_of(a, true)`   specials OK
# The interpreter can run an `IRSpecial`; a compiled operand slot cannot.
#
# ─── THE CONTRACT ────────────────────────────────────────────────────────────────────────────────
# A compiled head returns `Eval.CompiledOk(results, binds)` or `Eval.ExecNoReduce()`. `CompiledOk`'s
# inner constructor REQUIRES one binding per result — the seam is BINDING-VALUED, and returning bare
# atoms reproduces the `(pair $w schiphol)` substitution defect for the third time. See
# `docs/architecture/COMPILED_HEAD_SEAM.md`.
module CompilerEmitJulia

using ..StandardMeTTa
import ..CompilerANormal: Goal, GUnify, GCall, GBranch, GDisj, GFindall, GResidual, ANClause
import ..CompilerIR: IRAtom
import ..CompilerEmitIL: _atom_of
# 🔴 IMPORTED EXPLICITLY, NOT ASSUMED. First run died on `UndefVarError: freshvar` — the guessed-name
# class again. These five live in TWO modules: `match_atoms`/`is_present` in Atoms.jl (StandardMeTTa),
# `rename_fresh`/`freshvar`/`subst` in Eval.jl. Located before importing, not after failing.
import ..Eval: rename_fresh, freshvar, subst, CompiledOk, ExecNoReduce

export emit_julia_clause, emit_julia_program

"Goal kinds this stage handles. GBranch/GDisj/GFindall are MILESTONE 2 — declined, never dropped."
_supported(g::Goal)::Bool = g isa GUnify || g isa GCall || g isa GResidual

"""
    emit_julia_clause(cl) -> Union{Atom, Nothing}

Compile ONE clause to the RULE ATOM `(= (name head_args…) out)` it denotes. `nothing` = declined.

🔴 WHY AN ATOM AND NOT A HAND-ROLLED UNIFIER. `Eval.query` matches `(= call X)` against a stored rule
with `match_atoms(pattern, rename_fresh(stored))`. A compiled head that unified argument-by-argument
would be a REIMPLEMENTATION of that, and any divergence surfaces late and expensively in a
differential. Holding the rule atom and running the SAME matcher gives parity BY CONSTRUCTION — and
gets `rename_fresh` right, which a hand-rolled loop silently would not: without it a clause's
variables are shared across calls and capture each other.

⚠️ DECLINES on `cl.nested_head`, as `EmitIL` does: `name` + `head_args` cannot reconstruct
`(= (((curry \$f) \$x) \$y) …)`, and guessing yields a body referencing unbound variables.
`head_pattern` is the eventual fix; not this milestone.
"""
function emit_julia_clause(cl::ANClause)::Union{Atom, Nothing}
    cl.nested_head && return nothing
    all(_supported, cl.goals) || return nothing
    isempty(cl.goals) || return nothing          # MILESTONE 1a: fact clauses; the goal loop lands next
    parts = Atom[Sym(String(cl.name))]
    for a in cl.head_args                        # operand position ⇒ NO specials (two-builder split)
        v = _atom_of(a, false); v === nothing && return nothing
        push!(parts, v)
    end
    out = _atom_of(cl.out, false); out === nothing && return nothing
    Expression(Atom[Sym("="), Expression(parts), out])
end

"""
    emit_julia_program(clauses) -> Dict{Symbol, Function}

Group by HEAD and build one closure per head over ALL its clauses.

🔴 ALL-OR-NOTHING PER HEAD, NOT PER CLAUSE. If a head has five clauses and only four compile,
registering it would DROP the fifth's answers — the seam shadows the head, so the interpreter never
sees the rules the closure does not carry. A head is registered only if EVERY one of its clauses
emitted. (`docs/architecture/COMPILED_HEAD_SEAM.md`, "the unit is the HEAD".)
"""
function emit_julia_program(clauses::Vector{ANClause})
    by_head = Dict{Base.Symbol, Vector{Atom}}()
    declined = Set{Base.Symbol}()
    for cl in clauses
        r = emit_julia_clause(cl)
        r === nothing ? push!(declined, cl.name) : push!(get!(by_head, cl.name, Atom[]), r)
    end
    for h in declined                            # any declined clause disqualifies the whole head
        delete!(by_head, h)
    end
    Dict{Base.Symbol, Function}(h => _seam_fn(h, rules) for (h, rules) in by_head)
end

"""
    _seam_fn(head, rules) -> Function

The registered function, in the SEAM's OWN SIGNATURE: `(args::Vector{Atom}, space)` ->
`CompiledOk` | `ExecNoReduce`, which is what `Eval.compiled_head` calls. The adapter lives HERE, not
in the caller: a test that rebuilds the call atom itself would be reconstructing what the seam
already had, and a nested or unusual head could differ from what `compiled_head` actually saw.

`nothing` from the matcher ⇒ `ExecNoReduce` ⇒ NotReducible: the call returns ITSELF, never `Empty`.
"""
function _seam_fn(head::Base.Symbol, rules::Vector{Atom})
    inner = _head_closure(rules)
    function (args::Vector{Atom}, space)
        call = isempty(args) ? Sym(String(head)) :
               Expression(Atom[Sym(String(head)), args...])
        r = inner(call, space)
        r === nothing && return ExecNoReduce()
        CompiledOk(Atom[a for (a, _) in r], Bindings[b for (_, b) in r])
    end
end

"""
Build the per-head matcher. Runs the interpreter's OWN matcher against each rule atom and returns the
UNION of every clause's answers — MeTTa's collect-all semantics, the same shape `query` produces.

Returns `nothing` when no clause matched, which the caller turns into `ExecNoReduce` ⇒ NotReducible
(the call returns itself), NOT `Empty`.
"""
function _head_closure(rules::Vector{Atom})
    function (call::Atom, space)
        out = Tuple{Atom, Bindings}[]
        for r in rules
            X = freshvar("X")
            pattern = Expression(Atom[Sym("="), call, X])
            for mb in match_atoms(pattern, rename_fresh(r))
                is_present(mb, X) || continue    # resolve-filter, exactly as `query`'s consumers do
                push!(out, (subst(X, mb), mb))
            end
        end
        isempty(out) ? nothing : out
    end
end

end # module
