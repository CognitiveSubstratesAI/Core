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
using ..StandardMeTTa: Atom, Sym, Var, Expression   # typed atom model — same idiom as Frontend.jl:38

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
#
# `fail` is the FAILURE continuation — where a non-matching `unify` goes. It is a parameter and not
# the constant `(return Empty)` because a branch's condition must fall through to the NEXT ARM, not
# out of the clause. Hardcoding it was a wrong-answer bug (see `_instr(::GBranch, …)`).
function _seq(gs::Vector{Goal}, i::Int, tail::String, fail::String)::Union{String, Nothing}
    i > length(gs) && return tail
    cont = _seq(gs, i + 1, tail, fail)
    cont === nothing && return nothing
    _instr(gs[i], cont, fail)
end

_render_args(args::Vector{IRAtom})::String = join(String[render(a) for a in args], " ")

"""Render a node for THIS target, falling back to the shared renderer.

⚠️ WHY NOT ADD AN `IRSpecial` METHOD TO `CompilerEmit.render` — which is where it naturally belongs
and where the first version of this put it. `render` is SHARED with the MM2 emitter, and that
emitter's decline test is literally `startswith(render(a), "<unrenderable")`. Teaching the shared
function to render a special form therefore does not just help this stage — it silently WIDENS MM2,
which has no `match` instruction and cannot execute one. MEASURED 2026-08-10: the shared-method
version raised MM2 coverage 376 -> 378, two clauses that now emit a form their target cannot run.
Neither the suite nor the ratchet could tell those two apart from a real gain.

So the special-form rendering lives HERE, in the target that has an instruction for it, and the MM2
emitter keeps rejecting exactly what it rejected before."""
_render_il(a::IRAtom)::String =
    a isa IRSpecial ?
        (isempty((a::IRSpecial).args) ? "(" * String((a::IRSpecial).surface) * ")" :
         "(" * String((a::IRSpecial).surface) * " " *
         join(String[_render_il(x) for x in (a::IRSpecial).args], " ") * ")") :
    a isa IRExpression ?
        "(" * join(String[_render_il(x) for x in
                          IRAtom[(a::IRExpression).head; (a::IRExpression).args]], " ") * ")" :
    render(a)

"""IR node → a typed `StandardMeTTa.Atom`, the STRUCTURAL counterpart of `_render_il`.

🔴 WHY THIS EXISTS: THE COMPILE LANE CURRENTLY LAUNDERS IL THROUGH TEXT. `emit_il_clause` builds a
`String`, and `CompileLane` re-parses it with `load_metta!` — so a value survives only if
`parse(show(v)) ≡ v`. MEASURED 2026-08-11: `Grounded{Space}` prints as `&self` for EVERY space and
`Grounded{StateCell}` prints as `(State v)` and re-parses as a plain Expression. Two guards
(`_unroundtrippable`, `_name_spaces`) exist solely to survive a round-trip the internal lane should
not be doing. `render` stays — the IL IS the distributed artifact and must serialize — but
serialization should be the WIRE, not the transport (struct in memory, bytes on the wire).

⚠️ THIS IS DELIBERATELY TEXT-EQUIVALENT, NOT TEXT-IMPROVED. Every case mirrors `_render_il`/`render`
exactly, including the lossy ones: an `IRPredefined` becomes `Sym(name)` rather than the grounded
operation it names, and an `IRGrounded` string keeps its quotes. That is the point — the switch to
structural emission has to be provably behaviour-preserving FIRST (`test_emit_il.jl` asserts
`string(_il_atom(a)) == _render_il(a)` over the corpus). Fixing the lossy cases is the NEXT change,
and it will be visible as an intentional divergence rather than hidden inside a refactor.

Returns `nothing` for a node `render` cannot handle, mirroring its `<unrenderable:…>` marker — the
caller declines exactly as it does today.

🔴 TRAP FOR THE SWITCH-OVER, FOUND BEFORE MAKING IT: THERE ARE **TWO** RENDERERS AND THEY DIFFER.
`_instr(::GResidual, …)` renders through `_render_il`, which HANDLES `IRSpecial`; every other
`_instr` renders through the shared `render`, which does NOT and yields `<unrenderable:IRSpecial>`.
This function mirrors `_render_il`. So converting every site to it in one sweep would make an
`IRSpecial` renderable in `GCall`/`GUnify`/`GBranch` argument positions where the emitter declines
today — A COVERAGE INCREASE HIDDEN INSIDE A REFACTOR, which is the one thing the text-equivalence
rule above exists to prevent, and which the ratchet would report as a WIN.

The asymmetry is deliberate and load-bearing: `render` is SHARED with the MM2 emitter, whose decline
test is `startswith(render(a), "<unrenderable")`, so teaching it `IRSpecial` silently widens MM2 into
emitting a `match` its target cannot run — measured 2026-08-10 at MM2 376 → 378, and given back.

⇒ The switch needs the SAME two-renderer split on the atom side: a `render`-equivalent builder for the
`GCall`/`GUnify`/`GBranch`/`GFindall` sites and this one for `GResidual`. Doing it with a single
builder is the easy mistake, and the ratchet will applaud it."""
function _il_atom(a::IRAtom)::Union{Atom, Nothing}
    if a isa IRSpecial
        kids = Atom[Sym(String((a::IRSpecial).surface))]
        for x in (a::IRSpecial).args
            c = _il_atom(x); c === nothing && return nothing; push!(kids, c)
        end
        return Expression(kids)
    elseif a isa IRExpression
        kids = Atom[]
        for x in IRAtom[(a::IRExpression).head; (a::IRExpression).args]
            c = _il_atom(x); c === nothing && return nothing; push!(kids, c)
        end
        return Expression(kids)
    elseif a isa IRSymbol       ; return Sym(String((a::IRSymbol).name))
    elseif a isa IRPredefined   ; return Sym(String((a::IRPredefined).name))
    elseif a isa IRResolvedSymbol; return Sym(String((a::IRResolvedSymbol).name))
    elseif a isa IRVariable     ; return Var(String((a::IRVariable).name))
    elseif a isa IRGrounded
        # mirror `render(::IRGrounded)`: a STRING keeps its quotes in the text form, so the
        # text-equivalent atom is the quoted SYMBOL, not a Grounded string. Improving this is the
        # next change, not this one.
        return (a::IRGrounded).ty === GROUNDED_STRING ?
               Sym("\"" * string((a::IRGrounded).value) * "\"") :
               Sym(string((a::IRGrounded).value))
    end
    nothing                                   # ⇒ `<unrenderable:…>` in the text path
end

"`(unify <atom> <pattern> <then> <else>)` — spec §3. A failed unification yields `Empty`, Core's own
`EMPTY` sentinel (`Eval.jl:39`), so a non-matching clause contributes no result rather than erroring."
_instr(g::GUnify, cont::String, fail::String)::String =
    "(unify " * render(g.lhs) * " " * render(g.rhs) * " " * cont * " " * fail * ")"

"""`(chain (metta (f a b) %Undefined% &self) \$out ⟨cont⟩)` — spec §3: interpret the atom, substitute
`<var>` in the template.

NOTE the direction. `ANormal` performs the functional→relational lowering (result-as-last-argument,
`f(a,b,Out)`) because Prolog and MM2 need a relation. Minimal MeTTa is FUNCTIONAL, so this stage puts
the result back where it belongs: `out` becomes the chain's binding variable, not an extra argument.
A-normal form is still the right input — it named the intermediate, which is precisely what `chain`
needs.

⚠️ THIS EMITTED `eval` UNTIL 2026-08-11, and **`metta`, NOT `eval`**, is the correction.

🔴 `eval` MAKES ONE STEP; A CHAIN TEMPLATE NEEDS THE VALUE. `metta.txt:96` defines them apart:
`(eval <atom>)` "makes one step of the evaluation", `(metta <atom> <type> <space>)` "evaluate <atom>
in MeTTa interpreter using <space> as a context". A `GCall` wants the callee's RESULT; one step gives
the callee's BODY.

MEASURED 2026-08-11 on `c3_pln_stv`'s own definitions — and note how it hides:

    (chain (eval (TV X)) \$t \$t)                 ⟶ (stv 0.5 0.8)      looks CORRECT
    (chain (eval (TV X)) \$t (eval (s-tv \$t)))   ⟶ the whole chain UNREDUCED, with \$t bound to
                                                  `(match &self (.tv …))` — TV's BODY, not its value
    (chain (metta (TV X) %Undefined% &self) \$t
           (metta (s-tv \$t) %Undefined% &self))  ⟶ 0.5, matching `(s-tv (TV X))`

With a TRIVIAL template the driver keeps interpreting and the answer looks right; it only breaks when
the template does further work, which is every non-trivial clause. That is why this survived a
coverage ratchet, a corpus differential and a fuzz differential: the shape is right, the values are
wrong only in composition.

This is the single root behind `c3_pln_stv` (`(stv NotReducible NotReducible)`) and
`e1_kb_write`'s conjunction — `NotReducible` was a downstream symptom of binding the body, not the
disease.

⚠️ `%Undefined%` IS THE RIGHT TYPE ARGUMENT and not a placeholder: the emitter has no type
information at a call site, and `%Undefined%` is exactly MeTTa's "no expectation" meta-type
(`metta_language_spec.md` §2.4). `&self` is the context space, which re-parses to whatever space the
clause is loaded into — correct by construction, and the same property `_name_spaces` relies on."""
_instr(g::GCall, cont::String, ::String)::String =
    "(chain (metta (" * String(g.head) * (isempty(g.args) ? "" : " " * _render_args(g.args)) *
    ") %Undefined% &self) " * render(g.out) * " " * cont * ")"

"""Branch — condition goals, then a 4-ary `unify` against `True`, JOINED before the continuation.

`Emit.jl` declines this shape entirely: an MM2 exec atom has no then/else. Minimal MeTTa's `unify` is
4-ary, so the branch itself is native.

⚠️ THE JOIN IS NOT COSMETIC. The first version of this function threaded `cont` into BOTH arms, with
a comment calling that "the cost of not having a join point". Minimal MeTTa has a join point —
`function`/`return` makes a value out of a sub-computation — and not using it made the emitted term
DOUBLE per nesting level. MEASURED 2026-08-09 on the emitter itself: one `if` 271 chars, two nested
576. That is exponential in branch depth, and it is what killed the conformance run: the process sat
at 98% CPU inside `Eval.subst` (`Eval.jl:151`), recursing through a term that had blown up, until it
was killed at 21 minutes with no output.

So the arms are closed into a value and bound ONCE:

    (chain (function (unify cv True ⟨then…(return out)⟩ ⟨else…(return out)⟩)) out ⟨cont⟩)

`cont` now appears exactly once regardless of nesting, which is the whole point of a join."""
function _instr(g::GBranch, cont::String, ::String)::Union{String, Nothing}
    ret = "(return " * render(g.out) * ")"
    thn = _seq(g.then, 1, ret, "(return Empty)"); thn === nothing && return nothing
    # An EMPTY `els` means "no further arm" — failing there yields Empty, it does not fall out of the
    # clause. A non-empty `els` is the NEXT ARM and is itself a GBranch.
    els = isempty(g.els) ? "(return Empty)" : _seq(g.els, 1, ret, "(return Empty)")
    els === nothing && return nothing
    # `cond` carries the REAL test (a GUnify). Its success continuation is the then-arm and its
    # FAILURE continuation is the else-arm — that threading is the whole fix.
    body = _seq(g.cond, 1, thn, els); body === nothing && return nothing
    "(chain (function " * body * ") " * render(g.out) * " " * cont * ")"
end

"""`collapse` — `(chain (collapse-bind (function ⟨body … (return tmpl)⟩)) \$out ⟨cont⟩)`.

Spec §3: `collapse-bind` interprets an atom and returns a tuple of ALL its results. The body is a goal
sequence, so it is wrapped in `function`/`return` to become one interpretable atom."""
function _instr(g::GFindall, cont::String, ::String)::Union{String, Nothing}
    body = _seq(g.body, 1, "(return " * render(g.template) * ")", "(return Empty)")
    body === nothing && return nothing
    "(chain (collapse-bind (function " * body * ")) " * render(g.out) * " " * cont * ")"
end

# GDisj never reaches here — `_expand_disj` removes it before the fold. If one survives, that is a bug
# in the expansion, not a shape to improvise around, so decline loudly rather than guess.
_instr(::GDisj, ::String, ::String)::Nothing = nothing

"""A residual is, by definition, a node A-normalization could not flatten — so declining is the
default and the honest outcome. It is COUNTED, and the interpreter fallback still handles the clause.

ONE EXCEPTION, AND IT IS TARGET-SPECIFIC ON PURPOSE: `match`. A-normalization has no lowering for it
and never will — `match` searches a SPACE, and a space is not in the term. But THIS target does have
one, because minimal MeTTa's `eval` is precisely the instruction that reaches into the atomspace, and
a `match` under it is no less minimal than the `(eval (f args))` every `GCall` already emits.
MEASURED on our engine: `(chain (eval (match &self (likes \$x \$y) (\$x \$y))) \$o \$o)` returns the
same two answers as `match` called directly. That is why this lives here and not in `ANormal.jl` —
MM2 has no `eval`, so widening the shared stage would emit a form its target cannot run.

⚠️ THE GUARD IS THE WHOLE DESIGN, not a safety net. A COMPILED program's `&self` does NOT hold the
source rules — it holds the EMITTED IL clauses in their place. So a `match` whose pattern can bind a
RULE reads a space the source never had, and would silently answer differently. Measured over the
corpus: 180 of 182 `match` patterns are DATA-shaped (`(ChemRule \$p \$r \$w)`, `(Concentration
Tension \$v)`) and 2 are rule-shaped. Only a pattern with a SYMBOL head other than `=`/`:` is
lowered; a bare variable or a variable head is declined, because either can bind a rule."""
function _instr(g::GResidual, cont::String, ::String)::Union{String, Nothing}
    n = g.node
    inner = _lowerable_match(n)         ? "(eval " * _render_il(n) * ")" :
            _is_minimal_instruction(n)  ? _render_il(n) :
            _var_headed_call(n)         ? "(metta " * _render_il(n) * " %Undefined% &self)" :
                                          nothing
    inner === nothing && return nothing
    # THE RENDER GUARD, and it closes a CLASS rather than the instance that produced it. Lowering a
    # node VERBATIM is only sound if it renders; `_render_il` is total and marks what it cannot render
    # instead of throwing. MEASURED 2026-08-10: the first `match` lowering had no `IRSpecial` renderer,
    # emitted the marker AS A SYMBOL, and produced
    #   `(function (chain (eval <unrenderable:IRSpecial>) NotReducible (return NotReducible)))`
    # — well-formed, executable, and wrong. The coverage ratchet scored it identically to the working
    # version. Any future verbatim lowering gets this check for free by going through here.
    occursin("<unrenderable", inner) && return nothing
    o = render(g.out); occursin("<unrenderable", o) && return nothing
    "(chain " * inner * " " * o * " " * cont * ")"
end

"""A VARIABLE-HEADED application in value position — `(\$f \$x \$y)` — which `metta` can dispatch.

This is the largest single decline class: CODEMAP records **97 of 153 residuals** as variable-headed
expressions in value position, and every higher-order shape in `d2_higherfunc.metta` is one —
`(= (((curry \$f) \$x) \$y) (\$f \$x \$y))`, `(= ((curry-a \$f \$a) \$b) (\$f \$a \$b))`.

`ANormal` cannot build a `GCall` from it: there is no static head. `ANormal.jl:208` says so and names
the reference answer — "PeTTa handles that case with `partial/2` closures at RUNTIME; we have no
closure representation yet, and inventing one here would be exactly the kind of unreferenced
improvisation this file avoids." That was right. The point is that we no longer have to invent one:
`metta` IS runtime dispatch, and it is one of the thirteen instructions, so nothing is invented.

MEASURED 2026-08-11, all four against the source as oracle — including the control, because the risk
here is OVER-reduction, not under:

    (= (apply2 \$f \$x \$y) (\$f \$x \$y))   !(apply2 + 1 2)              source 3     · metta IL 3
                                          !(apply2 is Socrates Human)  source True  · metta IL True
    (= ((curry-a \$f \$a) \$b) (\$f \$a \$b))  !((curry-a is Socrates) Human)  source True  · metta IL True
    CONTROL — a PARTIAL application must stay UNREDUCED:
                                          !(curry-a is Socrates)
                                          source `(curry-a is Socrates)` · metta IL the same

That control is why `metta` is the right instruction and `eval` is not: `metta` returns a term
unchanged when nothing reduces (`metta.txt:352` `interpret_args` relies on exactly this), so a partial
application stays a partial application instead of collapsing to `NotReducible`.

⚠️ POSITION, NOT SHAPE, licenses this — CODEMAP row 221 states the rule: "The tempting one-line fix —
'variable-headed expressions are data' — is WRONG: `for-each-in-atom` has `(let \$_ (\$func \$head) …)`,
the same shape in VALUE position, and it IS a dynamic call. POSITION decides." A `GResidual` reaching
here came from `translate_expr`, i.e. VALUE position, which is the position where it is a call. Head
patterns never arrive here — `constrain_args` handles those."""
_var_headed_call(n::IRAtom)::Bool =
    n isa IRExpression && (n::IRExpression).head isa IRVariable

# 🛑 DO NOT WIDEN THIS TO AN EXPRESSION HEAD. Tried 2026-08-11, MEASURED, REVERTED.
#
# The reasoning looked airtight: `((curry f) x)` in value position is a runtime dispatch exactly as
# `($f x)` is, `metta` resolves both, and it is the second-largest IL decline class (25 of 70). It
# raised coverage and broke the LeaTTa PROVED corpus — `test_stdlib.metta` 0 → 1 extra error:
#
#     (= (overlap-857 $l1 $l2) (foldl-atom $l1 (() () $l2) $accum $elem …))
#
# `(() () $l2)` is `foldl-atom`'s INITIAL ACCUMULATOR — a DATA TUPLE. Its head is the empty
# expression `()`, so "head isa IRExpression" catches it and wraps data in a call.
#
# THE ASYMMETRY IS THE POINT: a VARIABLE head is unambiguously a dynamic call — nothing else can sit
# there. An EXPRESSION head is ambiguous: a curried application AND a data tuple have the same shape,
# and value position does not separate them (CODEMAP row 221's "POSITION decides" settles pattern-vs-
# value, not this). Widening needs a predicate that tells a curried application from a tuple; there
# is none yet, and coverage is not a reason to guess.
#
# ⚠️ IT ALSO SURFACED A LATENT RENDERING DEFECT, currently masked by these clauses being declined:
# the empty expression `()` lowers to `IRExpression(IRSymbol(:Nil), [])` and RENDERS AS `(Nil)`, which
# does not round-trip — `(Nil)` re-parses as a one-element expression containing the symbol `Nil`, not
# as `()`. Any future work here must fix that first.

const _MINIMAL_KINDS = (SPECIAL_CHAIN, SPECIAL_EVAL, SPECIAL_FUNCTION, SPECIAL_RETURN)

"""Whether this residual is a MINIMAL-MeTTa INSTRUCTION written directly in the source.

`chain` / `eval` / `function` / `return` are not forms this stage has to lower — they ARE the target
language, four of the thirteen instructions in `metta_language_spec.md` §3. A-normalization makes them
residuals because it has no relational reading of them (`chain` BINDS a variable in its template, and
`function`/`return` are a join point, neither of which is a Prolog goal), and that is correct for the
MM2 target, which has none of them. Here the right lowering is the identity.

⚠️ NO `eval` WRAPPER, unlike `match`. `chain`'s first argument is INTERPRETED by definition, so
`(chain (function (return a)) \$o \$o)` runs the inner instruction directly. `match` needs the wrapper
because it is an atomspace operation rather than an instruction; these do not.

⚠️ ONLY `chain`'s ARGUMENTS ARE LEFT ALONE upstream — `ANormal._KEEP_WHOLE` is `(SPECIAL_CHAIN,)`,
because `chain`'s third argument is a TEMPLATE with a bound variable and hoisting out of a binder's
scope is a wrong answer. The other three DO get A-normalized there and are then re-rendered whole
here, so their argument is evaluated more than once. That is measured WASTE and not a wrong answer
(verified against the interpreter with a nondeterministic argument, where duplicated branches would
have surfaced as duplicated answers); the alternative — widening `_KEEP_WHOLE` — cost MM2 four
clauses, which the coverage ratchet caught and the suite did not."""
_is_minimal_instruction(n::IRAtom)::Bool =
    n isa IRSpecial && (n::IRSpecial).kind in _MINIMAL_KINDS

"Whether this residual is a `match` whose pattern provably cannot bind a `(=)` rule or a `(:)` type."
function _lowerable_match(n::IRAtom)::Bool
    n isa IRSpecial || return false
    (n::IRSpecial).kind === SPECIAL_MATCH || return false
    args = (n::IRSpecial).args
    length(args) == 3 || return false
    pat = args[2]
    pat isa IRExpression || return false               # a bare variable matches ANYTHING, rules too
    h = (pat::IRExpression).head
    h isa IRSymbol || return false                     # a variable head can become `=` at runtime
    nm = (h::IRSymbol).name
    nm !== :(=) && nm !== :(:)
end

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
    # A NESTED head is rendered from the CONSTRAINED PATTERN the clause carries, not rebuilt from
    # `name` + `head_args` — that reconstruction drops the outer application's arguments entirely and
    # leaves the body's references to them unbound (`ANClause.nested_head` records the measured case:
    # `(= ((lambda $var $body) $arg) …)` emitting `(= (lambda $arg) …)`).
    #
    # Minimal MeTTa's `(= <pattern> <body>)` takes an arbitrary pattern, so the TARGET was never the
    # obstacle — the clause struct was. Declining was the safe stopgap; this is the fix.
    if c.nested_head
        c.head_pattern === nothing && return nothing        # nested but no pattern carried ⇒ decline
        hp = _render_il(c.head_pattern)
        occursin("<unrenderable", hp) && return nothing
        return _emit_with_head(c, hp)
    end
    head = "(" * String(c.name) * (isempty(c.head_args) ? "" : " " * _render_args(c.head_args)) * ")"
    _emit_with_head(c, head, variants)
end

"""Emit one clause given an already-rendered HEAD — shared by the plain and nested-head paths so the
unrenderable sweep and the all-or-nothing decline apply identically to both."""
function _emit_with_head(c::ANClause, head::String,
                         variants = _expand_disj(c.goals))::Union{Vector{String}, Nothing}
    variants === nothing && return nothing
    out = String[]
    for gs in variants
        body = _seq(gs, 1, "(return " * render(c.out) * ")", "(return Empty)")
        body === nothing && return nothing            # decline the clause WHOLE, never half of it
        push!(out, "(= " * head * " (function " * body * "))")
    end
    # 🔴 THE UNRENDERABLE SWEEP — ONE CHECK, AT THE END, COVERING EVERY PATH.
    #
    # `render` returns the STRING `"<unrenderable:Foo>"` for a node it has no method for. `Emit.jl`
    # guards that at TWELVE separate call sites (`startswith(s, "<unrenderable")` … `return nothing`);
    # this file guarded it at NONE, and every `_instr` above interpolates `render` directly. It was
    # latent only because the goal types reached here carry node kinds `render` happens to know.
    #
    # It stopped being latent the moment `_instr(::GResidual, …)` began lowering `match` verbatim:
    # the emitted text became `(chain (eval <unrenderable:IRSpecial>) …)`, which PARSES — the sentinel
    # reads as a symbol — and answered `(function (chain (eval <unrenderable:IRSpecial>) NotReducible
    # (return NotReducible)))` instead of `alice`. The coverage ratchet counted all 106 such clauses
    # as emitted. Caught by the compile-lane differential, not by any structural check.
    #
    # Guarding the ONE place every clause passes through is deliberate: twelve per-site guards is a
    # rule a future `_instr` can forget, and this one it cannot. Cheap — a substring scan of text we
    # just built.
    any(s -> occursin("<unrenderable", s), out) && return nothing
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
