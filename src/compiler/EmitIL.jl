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
using ..CompilerEmit: render, _escape_il_string
import ..CompilerEmit   # reuse the renderer AND its escaper — a second
                                                  # of either would drift from the first
using ..StandardMeTTa: Atom, Sym, Var, Expression, Grounded   # typed atom model — same idiom as Frontend.jl:38
import ..Eval                          # TOKEN_REGISTRY, for parse-equivalent predefined ops

export emit_il_clause, emit_il_program, ILResult


"Result of lowering a program to minimal MeTTa. `declined` carries a REASON per clause, never a bare count."
struct ILResult
    # BOTH forms, from ONE emission. `atoms` is what the compile lane consumes — no re-parse, so the
    # round-trip corruption class cannot arise internally. `clauses` is `string.(atoms)`: the WIRE
    # form, which the IL still owes as Fig-2's distributed artifact, plus every existing consumer
    # (ratchet, differentials, `test_eval_one_step`) unchanged. Struct in memory, bytes on the wire.
    atoms::Vector{Atom}
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
# The instruction heads, interned once. `Sym` holds a Julia `Symbol`, so these are pointer-compares
# rather than the string concatenation the text emitter did per node.
const _A_EQ, _A_FUNCTION, _A_RETURN   = Sym("="), Sym("function"), Sym("return")
const _A_CHAIN, _A_UNIFY, _A_METTA    = Sym("chain"), Sym("unify"), Sym("metta")
const _A_EVAL, _A_COLLAPSE            = Sym("eval"), Sym("collapse-bind")
const _A_EMPTY, _A_UNDEF, _A_SELF     = Sym("Empty"), Sym("%Undefined%"), Sym("&self")
_ret(a::Atom)::Atom = Expression(Atom[_A_RETURN, a])

"""Atom → the IL's WIRE TEXT. `string`/`show` is NOT this, and that gap is the session's recurring
defect in a third place.

`Base.show(::Grounded)` prints the underlying value, so a `Grounded{String}` prints WITHOUT quotes —
`string(Grounded("abc")) == "abc"`, which re-parses as a SYMBOL. `render(::IRGrounded)` gets it right
by quoting, and this keeps that. Everything else agrees with `show`: an `Operation` prints its name, a
`Space` prints `&self`, numbers print themselves, and `_name_spaces` has already turned a NAMED space
into a `Sym` before lowering, so no name lookup is needed here.

⇒ `clauses = il_text.(atoms)`: ONE emission, two views, and the wire form is produced by a serializer
that knows the quoting rule rather than by a display method that does not."""
function il_text(a::Atom)::String
    a isa Expression && return "(" * join(String[il_text(c) for c in a.children], " ") * ")"
    a isa Grounded && a.value isa AbstractString && return "\"" * _escape_il_string(a.value) * "\""
    string(a)
end
const _RET_EMPTY = Expression(Atom[_A_RETURN, _A_EMPTY])
# ⚠️ THIS `Empty` IS WRONG AND SWAPPING IT FOR `NotReducible` DOES NOT FIX IT — tried and reverted
# 2026-08-12, with the measurement kept so the next attempt starts past it.
#
# THE DEFECT IS REAL. `metta.txt:78-79` distinguishes "Empty — the function doesn't return any result"
# from "NotReducible — returns the UNCHANGED FUNCTION CALL instead". When a guard cannot decide — its
# condition unifies with neither True nor False — the call must come back as itself. Measured on
# `(= (guarded $x) (if (< $x 0) neg pos))` applied to a symbol:
#     hyperon-experimental  (if (< sym 0) neg pos)
#     Core interpreter      (if (< sym 0) neg pos)      ← ours is right
#     Core COMPILED lane    (no result)                 ← the answer is lost
#
# THE OBVIOUS FIX MAKES IT WORSE. Emitting `(return NotReducible)` at the branch fallthrough leaves the
# sentinel BOUND TO THE CHAIN VARIABLE instead of reaching the evaluator's `metta-noreduce` backstop
# (`Eval.jl:1593-1602`, hyperon `interpreter.rs:145`), so the compiled lane answered with its own IL:
#     (function (chain (metta (< sym 0) %Undefined% &self) … (return NotReducible)))
# — leaking the compiled form into a MeTTa answer, which is worse than losing it. Corpora stayed at
# 70/71 either way, so the corpus differential could NOT have caught this; the five-engine check did.
#
# ⇒ The fix is not a different sentinel at this site. `metta-noreduce` wraps a call and surfaces the
# ORIGINAL atom when its result is the sentinel; the compiled clause never sets that wrapper up. Making
# it work means emitting the backstop around the clause body, with the head as the original — a change
# to `_emit_with_head`, not to this constant.

function _seq(gs::Vector{Goal}, i::Int, tail::Atom, fail::Atom)::Union{Atom, Nothing}
    i > length(gs) && return tail
    cont = _seq(gs, i + 1, tail, fail)
    cont === nothing && return nothing
    _instr(gs[i], cont, fail)
end

"Every argument as an atom, or `nothing` if any is unrenderable (the old `<unrenderable` scan)."
function _atom_args(args::Vector{IRAtom})::Union{Vector{Atom}, Nothing}
    out = Atom[]
    for a in args
        v = _render_atom(a); v === nothing && return nothing; push!(out, v)
    end
    out
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
function _atom_of(a::IRAtom, specials::Bool)::Union{Atom, Nothing}
    if a isa IRSpecial
        # `specials=false` mirrors the SHARED `render`, which has no `IRSpecial` method and returns
        # `<unrenderable:IRSpecial>` ⇒ the caller declines. That is not an oversight to fix here:
        # widening it is what silently widened MM2 (376 → 378) on 2026-08-10.
        specials || return nothing
        kids = Atom[Sym(String((a::IRSpecial).surface))]
        for x in (a::IRSpecial).args
            c = _atom_of(x, specials); c === nothing && return nothing; push!(kids, c)
        end
        return Expression(kids)
    elseif a isa IRExpression
        # The unit atom `()` is an EMPTY Expression, not a one-element one containing the sentinel.
        CompilerEmit._is_unit(a::IRExpression) && return Expression(Atom[])
        kids = Atom[]
        for x in IRAtom[(a::IRExpression).head; (a::IRExpression).args]
            c = _atom_of(x, specials); c === nothing && return nothing; push!(kids, c)
        end
        return Expression(kids)
    elseif a isa IRSymbol       ; return Sym(String((a::IRSymbol).name))
    elseif a isa IRResolvedSymbol; return Sym(String((a::IRResolvedSymbol).name))
    elseif a isa IRVariable     ; return Var(String((a::IRVariable).name))
    elseif a isa IRPredefined
        # PARSE-EQUIVALENT: parsing `+` against a space's token table yields `Grounded{Operation}`,
        # not `Sym("+")`. The IR keeps only the NAME, so the registry supplies the value — the one
        # lookup this direction needs. Falls back to `Sym` for a name that is not registered, which
        # is what parsing would also produce.
        return get(Eval.TOKEN_REGISTRY, String((a::IRPredefined).name),
                   Sym(String((a::IRPredefined).name)))
    elseif a isa IRGrounded
        # PARSE-EQUIVALENT: the IR already HOLDS the value, so this is the real thing — a
        # `Grounded{String}`, `Grounded{Int}`, `Grounded{Space}` — exactly what parsing the rendered
        # text produces, and for a Space it is the SAME OBJECT (`parse("&self") === sp`, measured).
        # The earlier version returned a text-equivalent `Sym`, which is why consuming these atoms in
        # the lane broke five corpus scripts.
        return Grounded((a::IRGrounded).value)
    end
    nothing                                   # ⇒ `<unrenderable:…>` in the text path
end

"""The `_render_il` twin — handles `IRSpecial`. Use ONLY where the text path calls `_render_il`,
i.e. `_instr(::GResidual, …)`."""
_il_atom(a::IRAtom)::Union{Atom, Nothing} = _atom_of(a, true)

"""The SHARED-`render` twin — `IRSpecial` yields `nothing`, matching `<unrenderable:IRSpecial>`.
Use at every OTHER site (`GUnify`/`GCall`/`GBranch`/`GFindall`), which is what the text path does.

Two builders, because there are two renderers — see the trap note on `_atom_of`. Collapsing them into
one is the easy mistake, and the ratchet would score it as a win."""
_render_atom(a::IRAtom)::Union{Atom, Nothing} = _atom_of(a, false)

"`(unify <atom> <pattern> <then> <else>)` — spec §3. A failed unification yields `Empty`, Core's own
`EMPTY` sentinel (`Eval.jl:39`), so a non-matching clause contributes no result rather than erroring."
function _instr(g::GUnify, cont::Atom, fail::Atom)::Union{Atom, Nothing}
    l = _render_atom(g.lhs); l === nothing && return nothing
    r = _render_atom(g.rhs); r === nothing && return nothing
    Expression(Atom[_A_UNIFY, l, r, cont, fail])
end

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
function _instr(g::GCall, cont::Atom, ::Atom)::Union{Atom, Nothing}
    args = _atom_args(g.args); args === nothing && return nothing
    o = _render_atom(g.out);   o === nothing && return nothing
    call = Expression(Atom[Sym(String(g.head)); args])
    Expression(Atom[_A_CHAIN, Expression(Atom[_A_METTA, call, _A_UNDEF, _A_SELF]), o, cont])
end

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
function _instr(g::GBranch, cont::Atom, ::Atom)::Union{Atom, Nothing}
    o = _render_atom(g.out); o === nothing && return nothing
    ret = _ret(o)
    thn = _seq(g.then, 1, ret, _RET_EMPTY); thn === nothing && return nothing
    # An EMPTY `els` means "no further arm" — failing there yields Empty, it does not fall out of the
    # clause. A non-empty `els` is the NEXT ARM and is itself a GBranch.
    els = isempty(g.els) ? _RET_EMPTY : _seq(g.els, 1, ret, _RET_EMPTY)
    els === nothing && return nothing
    # `cond` carries the REAL test (a GUnify). Its success continuation is the then-arm and its
    # FAILURE continuation is the else-arm — that threading is the whole fix.
    body = _seq(g.cond, 1, thn, els); body === nothing && return nothing
    Expression(Atom[_A_CHAIN, Expression(Atom[_A_FUNCTION, body]), o, cont])
end

"""🔴 DEFECT — `collapse` IS LOWERED TO `collapse-bind`, WHICH RETURNS BINDINGS TOO.

MEASURED 2026-08-12. `(= (allfoo) (collapse (match &self (foo \$x) \$x)))` over facts `(foo bar)` and
`(foo baz)`:

    interpreter  ["(bar baz)"]
    compiled     ["((baz Bindings(Binding(\$x#4115, baz), …)) (bar Bindings(…)))"]

`collapse_bind_op` (`Eval.jl:944-950`) is faithful to hyperon `interpreter.rs:746` and returns an
expression of `(atom bindings)` PAIRS — that is its contract, and it is why `superpose-bind` can
"continue the process of the interpretation from the moment where collapse-bind stopped"
(`metta.txt:96`). Plain `collapse` must yield the VALUES. This lowering never strips the pairs, so
internal Julia `Grounded{Bindings}` atoms reach MeTTa answers.

ISOLATED, NOT GUESSED: a five-case probe showed `add-atom`+`match`, a fact + `match`, a definition
reading the space via `match &self`, and pure arithmetic ALL agree between the lanes. Only the
`collapse` case diverges — so this is not a space-connectivity problem, which was the leading
hypothesis when the disagreements first appeared as empty results.

It is the mechanism behind the `Core/lib` differential's findings.

🔧 THE FIX, EXACTLY — upstream defines `collapse` in MINIMAL MeTTa, our own target language
(`hyperon-experimental/lib/src/metta/runner/stdlib/stdlib.metta:1203-1209`):

    (: collapse (-> Atom Atom))
    (= (collapse \$atom)
      (function
        (chain (context-space) \$space
          (chain (collapse-bind (metta \$atom %Undefined% \$space)) \$eval
            (chain (eval (foldl-atom \$eval () \$res \$item
                           (_collapse-add-next-atom-from-collapse-bind-result \$res \$item))) \$result
              (return \$result))))))

and documents the distinction we missed, in its own `@doc` entries:
  * `collapse-bind` — "returns an expression which contains all alternative evaluations IN A FORM
    (Atom Bindings). Bindings are represented in a form of a grounded atom."  `(-> Atom Expression)`
  * `collapse`      — "Converts a nondeterministic result into A TUPLE."                `(-> Atom Atom)`

We emit ONLY the middle line. The missing parts are `(context-space)` and the FOLD that strips each
pair to its atom. `_collapse-add-next-atom-from-collapse-bind-result` is a GROUNDED function upstream
(`stdlib/core.rs:347-351`, typed `(-> Expression Expression Atom)`), so porting the shape needs that
one grounded op on our side — `context-space` we already have (`Eval.jl:2292`).

⚠️ TWO ROUTES, AND THE CHEAP ONE HAS A COST: emitting our own grounded `collapse` verbatim (it is
correct — `Eval.jl:2326`) would fix the answer in one line, but `collapse` is NOT one of the thirteen
minimal-MeTTa instructions, so the emitted IL would stop being minimal MeTTa — and Fig-2 makes that IL
the DISTRIBUTED artifact, consumed by backends that have no `collapse`. Upstream's shape stays minimal;
that is why it is written the way it is.

Not applied here — it needs its own before/after on the
corpora, and the differential that would show it working landed only today.

Original note follows.

`collapse` — `(chain (collapse-bind (function ⟨body … (return tmpl)⟩)) \$out ⟨cont⟩)`.

Spec §3: `collapse-bind` interprets an atom and returns a tuple of ALL its results. The body is a goal
sequence, so it is wrapped in `function`/`return` to become one interpretable atom."""
function _instr(g::GFindall, cont::Atom, ::Atom)::Union{Atom, Nothing}
    tm = _render_atom(g.template); tm === nothing && return nothing
    o  = _render_atom(g.out);      o  === nothing && return nothing
    body = _seq(g.body, 1, _ret(tm), _RET_EMPTY); body === nothing && return nothing
    # STRIP THE BINDINGS. `collapse-bind` returns `(Atom Bindings)` PAIRS by contract (hyperon
    # `@doc collapse-bind`: "…in a form (Atom Bindings)"), while `collapse` must yield a TUPLE
    # (`@doc collapse`: "Converts a nondeterministic result into a tuple"). Emitting the capture
    # primitive alone leaked `Grounded{Bindings}` atoms into answers — measured against four engines,
    # which all returned `(bar baz)` where this returned `((baz Bindings(…)) (bar Bindings(…)))`.
    #
    # This mirrors upstream's own minimal-MeTTa definition (`stdlib.metta:1203-1209`): fold the pairs
    # with `_collapse-add-next-atom-from-collapse-bind-result`, which is grounded there
    # (`stdlib/core.rs:347-351`) and grounded here for the same reason — minimal MeTTa has no append.
    # Upstream wraps `(metta \$atom %Undefined% \$space)`; our body is already a `function`, so the
    # `(context-space)` step it needs to build that call is not required here.
    pairs = fresh_ilvar("c")
    acc   = fresh_ilvar("res")
    item  = fresh_ilvar("item")
    fold  = Expression(Atom[_A_EVAL,
                Expression(Atom[Sym("foldl-atom"), pairs, Expression(Atom[]), acc, item,
                                Expression(Atom[Sym("_collapse-add-next-atom-from-collapse-bind-result"),
                                                acc, item])])])
    Expression(Atom[_A_CHAIN,
                    Expression(Atom[_A_COLLAPSE, Expression(Atom[_A_FUNCTION, body])]), pairs,
                    Expression(Atom[_A_CHAIN, fold, o, cont])])
end

# Fresh IL-level variable names. Distinct prefix from the A-normalizer's `\$__t` so a collision is
# impossible by construction rather than by hoping the counters never meet.
const _IL_VAR_N = Ref(0)
fresh_ilvar(tag::AbstractString)::Atom = (_IL_VAR_N[] += 1; Var("__il_" * tag * string(_IL_VAR_N[])))

# GDisj never reaches here — `_expand_disj` removes it before the fold. If one survives, that is a bug
# in the expansion, not a shape to improvise around, so decline loudly rather than guess.
_instr(::GDisj, ::Atom, ::Atom)::Nothing = nothing

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
function _instr(g::GResidual, cont::Atom, ::Atom)::Union{Atom, Nothing}
    n = g.node
    # `_il_atom` (NOT `_render_atom`) — this is the one site the text path renders with `_render_il`,
    # which handles `IRSpecial`. Using the same builder as the other sites here would DECLINE clauses
    # that emit today; using this builder at the other sites would WIDEN them. See `_atom_of`.
    nd = _il_atom(n)
    inner = nd === nothing              ? nothing :
            _lowerable_match(n)         ? Expression(Atom[_A_EVAL, nd]) :
            _is_minimal_instruction(n)  ? nd :
            _var_headed_call(n)         ? Expression(Atom[_A_METTA, nd, _A_UNDEF, _A_SELF]) :
                                          nothing
    inner === nothing && return nothing
    # THE RENDER GUARD, and it closes a CLASS rather than the instance that produced it. Lowering a
    # node VERBATIM is only sound if it renders; `_render_il` is total and marks what it cannot render
    # instead of throwing. MEASURED 2026-08-10: the first `match` lowering had no `IRSpecial` renderer,
    # emitted the marker AS A SYMBOL, and produced
    #   `(function (chain (eval <unrenderable:IRSpecial>) NotReducible (return NotReducible)))`
    # — well-formed, executable, and wrong. The coverage ratchet scored it identically to the working
    # version. Any future verbatim lowering gets this check for free by going through here.
    # The old `<unrenderable` SUBSTRING SCAN is gone: an unrenderable node is now `nothing` from the
    # builder and propagates by construction, so the guard cannot be forgotten by a future `_instr`.
    o = _render_atom(g.out); o === nothing && return nothing
    Expression(Atom[_A_CHAIN, inner, o, cont])
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
    # RECURSIVE. This scan used to look only at TOP-LEVEL goals, so a residual inside a `GBranch` or
    # `GFindall` was invisible to it — the clause fell through to the catch-all and was reported as
    # "structural", i.e. as a different problem. MEASURED 2026-08-12: 25 of the 28 clauses that
    # reported "structural" carry a NESTED residual, and it is the same two node kinds as the
    # top-level ones. The decline taxonomy looked like six classes and is really two.
    nested = _first_residual(gs)
    nested === nothing || return "GResidual (unflattened node: " * nested * ")"
    for g in gs
        g isa GDisj && isempty((g::GDisj).branches) && return "GDisj with zero branches (emits nothing)"
    end
    any(g -> g isa GDisj, gs) && return "GDisj expansion exceeded the 64-clause limit"

    # 🔴 WAS A CATCH-ALL. Everything that did not match a case above returned the same string, "a
    # nested goal could not be lowered" — which named a SYMPTOM (the clause has goals and one failed)
    # and not a cause, and which 34 corpus clauses landed in. There are ~18 `return nothing` sites in
    # this file and they were indistinguishable from the outside.
    #
    # So instead of guessing, ASK THE BUILDERS. Every one of those sites bottoms out in `_atom_of`
    # returning `nothing` for a node it cannot build, so walking the goals' atoms and reporting the
    # FIRST such node names the actual blocker. Pure — it rebuilds nothing and mutates nothing, it
    # just re-runs the predicate that already failed and reports what it tripped on.
    blocker = _first_unbuildable(gs)
    blocker === nothing ||
        return "unbuildable node in a goal: " * blocker
    "a nested goal could not be lowered (no unbuildable node found — the failure is structural)"
end

"Name the node kind of the first `GResidual` in `gs`, descending into branch and findall bodies."
function _first_residual(gs::Vector{Goal})::Union{Nothing, String}
    for g in gs
        if g isa GResidual
            return string(nameof(typeof((g::GResidual).node)))
        elseif g isa GBranch
            for sub in ((g::GBranch).cond, (g::GBranch).then, (g::GBranch).els)
                r = _first_residual(sub); r === nothing || return r
            end
        elseif g isa GFindall
            r = _first_residual((g::GFindall).body); r === nothing || return r
        end
    end
    nothing
end

"""Name the first IR node in `gs` that the atom builders cannot produce, or `nothing` if every node
builds (in which case the decline came from a structural path — arity, `nested_head` without a
pattern, a `_seq` continuation — rather than from an unrenderable node)."""
function _first_unbuildable(gs::Vector{Goal})::Union{Nothing, String}
    found = Ref{Union{Nothing, String}}(nothing)
    # 🔴 THE MODE MUST MATCH THE SITE. `GResidual` is emitted with `_il_atom` (specials=TRUE); every
    # other site uses `_render_atom` (specials=FALSE). A first version of this function tested every
    # node with `false`, so every residual holding an `IRSpecial` was reported as "builds only in
    # GResidual position" — a node the emitter builds without difficulty. That mislabelled 11 clauses
    # and would have sent the next reader to widen a restriction that was not the blocker.
    # A diagnostic that does not reproduce the caller's conditions invents its own findings.
    note(a::IRAtom, specials::Bool) = begin
        found[] === nothing || return nothing
        if _atom_of(a, specials) === nothing
            found[] = specials ?
                      string(nameof(typeof(a))) * " (unbuildable even in GResidual position)" :
                      (_atom_of(a, true) === nothing ?
                       string(nameof(typeof(a))) :
                       string(nameof(typeof(a))) * " (builds only in GResidual position)")
        end
        nothing
    end
    walk(a::IRAtom, specials::Bool = false) = begin
        note(a, specials)
        if a isa IRExpression
            walk((a::IRExpression).head, specials)
            for x in (a::IRExpression).args; walk(x, specials); end
        elseif a isa IRSpecial
            for x in (a::IRSpecial).args; walk(x, specials); end
        end
        nothing
    end
    for g in gs
        if g isa GUnify
            walk((g::GUnify).lhs); walk((g::GUnify).rhs)
        elseif g isa GCall
            for x in (g::GCall).args; walk(x); end
            walk((g::GCall).out)
        elseif g isa GResidual
            walk((g::GResidual).node, true)      # emitted via `_il_atom` — specials ARE buildable here
        elseif g isa GBranch
            walk((g::GBranch).out)
            for sub in ((g::GBranch).cond, (g::GBranch).then, (g::GBranch).els)
                r = _first_unbuildable(sub)
                r === nothing || (found[] === nothing && (found[] = r))
            end
        elseif g isa GFindall
            walk((g::GFindall).template); walk((g::GFindall).out)
            r = _first_unbuildable((g::GFindall).body)
            r === nothing || (found[] === nothing && (found[] = r))
        end
    end
    found[]
end

"""
    emit_il_clause(c::ANClause) -> Union{Vector{String}, Nothing}

Lower one A-normal clause to minimal-MeTTa `(= head body)` clauses. Returns several when the clause
contains a `GDisj` (one per branch), or `nothing` if it cannot be lowered at all.
"""
function emit_il_clause(c::ANClause)::Union{Vector{Atom}, Nothing}
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
        hp = _il_atom(c.head_pattern); hp === nothing && return nothing
        return _emit_with_head(c, hp)
    end
    hargs = _atom_args(c.head_args); hargs === nothing && return nothing
    head = Expression(Atom[Sym(String(c.name)); hargs])
    _emit_with_head(c, head, variants)
end

"""Emit one clause given an already-rendered HEAD — shared by the plain and nested-head paths so the
unrenderable sweep and the all-or-nothing decline apply identically to both."""
function _emit_with_head(c::ANClause, head::Atom,
                         variants = _expand_disj(c.goals))::Union{Vector{Atom}, Nothing}
    variants === nothing && return nothing
    o = _render_atom(c.out); o === nothing && return nothing
    out = Atom[]
    for gs in variants
        body = _seq(gs, 1, _ret(o), _RET_EMPTY)
        body === nothing && return nothing            # decline the clause WHOLE, never half of it
        push!(out, Expression(Atom[_A_EQ, head, Expression(Atom[_A_FUNCTION, body])]))
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
    # (The old `<unrenderable` substring sweep lived here. It is now STRUCTURAL: an unrenderable node
    # is `nothing` from `_render_atom`/`_il_atom` and propagates out of `_seq`, so a clause cannot be
    # built half-formed at all. That sweep's own comment warned twelve per-site guards is "a rule a
    # future `_instr` can forget" — there is nothing left to forget.)
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
    out = Atom[]
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
    # `clauses` is DERIVED, never separately built — one emission, two views, so the wire form cannot
    # drift from what the lane actually loads.
    ILResult(out, String[il_text(a) for a in out], nemit, nexpanded, declined)
end

end # module CompilerEmitIL
