# test_instr_arity.jl — NO INSTRUCTION, AT ANY ARITY, MAY CRASH THE INTERPRETER.
#
# ─── THE PROPERTY, AND WHY IT IS A PROPERTY AND NOT A LIST OF CASES ──────────────────────────────
# `interpret_stack` dispatches on HEAD NAME ALONE. Every instruction function then indexes
# `a.children[…]` at fixed positions, so any atom carrying an instruction's name with the wrong shape
# indexes past the end and kills the evaluator. MeTTa's answer for an ill-formed head is not a crash:
# it is DATA, returned unreduced — exactly what the dispatcher's own `else` branch does for an
# unknown head.
#
# This enumerates the whole dispatch surface — every instruction × arity 0..6 — rather than the cases
# someone thought of. That distinction is the point of the file:
#
#   MEASURED 2026-08-10, first run: 13 crashing shapes across 6 instructions.
#   The bug that started it was found by ACCIDENT — `!(match &self $a $a)` in an unrelated test
#   returned every atom in the space, stdlib's own `(: return-on-error (-> Atom Atom %Undefined%))`
#   among them, and evaluating it dispatched `return-on-error` on a 2-child atom.
#
# ⚠️ AND THE MEASUREMENT CONTRADICTED TWO READINGS OF THE CODE. A regex over the function bodies
# produced minimums for all seventeen instructions; using them OVER-guarded and broke 36 tests plus
# `bin/health` (3/5). The truth is narrower and could not be read off the §3 spec at all:
#
#   the 10 PUBLIC instructions   crash at NO arity — already defensive, no guard needed
#   6 INTERNAL continuations     crash — interpret-tuple/function/args, metta-call, args-cont,
#                                metta-noreduce, none of which appear in any arity table
#
# So a guard table derived from the specification would have missed every real case and added seven
# wrong ones. Hence: measure, and keep measuring.
#
# ─── AND STATIC ANALYSIS DOES NOT SUBSTITUTE FOR IT. MEASURED, SO NOBODY REPEATS THE EXPERIMENT ──
# JET was installed and run against this exact crashing shape. RESULT: it reports the BoundsError
# ZERO times — a runtime index on a runtime-length vector is not a type error — and its three actual
# reports were ALL FALSE POSITIVES, each checked by execution:
#
#   Atoms.jl:150   `prev == val` :: Union{Missing,Bool} in a boolean context.  FALSE — Atoms.jl:69 is
#                  `(a.value == b.value) === true`, and its comment documents THIS hazard as already
#                  fixed, citing hyperon `eq_gnd → bool` and CeTTa `atom_eq → bool`. JET sees the
#                  union inside `==` and does not carry the `=== true` through.
#   Eval.jl:737    `setproperty!` on `Nothing` in `_trie_insert!`.             FALSE — guarded by
#                  `node.star === nothing && (node.star = _TNode())`; Julia does not narrow a MUTABLE
#                  FIELD through a guard, so inference keeps the union.
#   Eval.jl:763-4  `_trie_collect!` with a `Nothing` node.                     FALSE — same shape,
#                  guarded by `node.star !== nothing &&`. 200 atoms × 4 trie-driven match shapes: no
#                  throw, 230 results.
#
# Score on this codebase: 3 reports, 0 defects, and the real one missed. The trie sites do leave a
# genuine (small) type-stability wart — `node.star` read twice through a `Union` — but touching the
# eval core without a MEASURED need is against standing guidance, and no measurement says it matters.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

"Every head `interpret_stack` dispatches on (Eval.jl `interpret_stack`, the if/elseif chain)."
const _IA_NAMES = ["cons-atom", "decons-atom", "unify", "eval", "evalc", "chain", "function",
                   "collapse-bind", "superpose-bind", "metta", "interpret-tuple",
                   "interpret-function", "interpret-args", "metta-call", "return-on-error",
                   "args-cont", "metta-noreduce"]

@testset "instruction arity — an ill-formed operation is DATA, never a crash" begin
    crashed = Tuple{String, Int, String}[]
    for nm in _IA_NAMES, n in 0:6
        atom = Expression(Atom[Sym(nm); [Sym("a$k") for k in 1:n]])
        try
            bare_eval(atom, Space())
        catch e
            push!(crashed, (nm, n, first(sprint(showerror, e), 60)))
        end
    end
    for (nm, n, e) in crashed
        @info "instruction CRASHES" instruction=nm arity=n error=e
    end
    @test isempty(crashed)

    # ANTI-VACUITY. Without this the testset passes if `_IA_NAMES` is emptied or the loop is broken —
    # the same trap as every other differential here. 17 instructions × 7 arities.
    @test length(_IA_NAMES) == 17

    # …and the guard must NOT have gone the other way. A WELL-FORMED instruction still evaluates:
    # over-guarding is the failure mode that broke 36 tests, and it looks identical to success here
    # unless something asserts the positive.
    @test bare_eval(Expression(Atom[Sym("cons-atom"), Sym("a"), Expression(Atom[Sym("b")])]),
                    Space()) == Atom[Expression(Atom[Sym("a"), Sym("b")])]
    let sp = Space()
        add_atom!(sp, Expression(Atom[Sym("="), Expression(Atom[Sym("f")]), Sym("q")]))
        @test bare_eval(Expression(Atom[Sym("eval"), Expression(Atom[Sym("f")])]), sp) == Atom[Sym("q")]
    end
end
