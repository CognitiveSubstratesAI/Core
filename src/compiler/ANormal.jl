# ANormal.jl — the Core MeTTa compiler, stage 3: A-normalization of rule bodies to GOAL LISTS.
#
# ─── PORTED FROM PeTTa (Prolog), NOT INVENTED ────────────────────────────────────────────────────
# Reference: `dev-zone/PeTTa/src/translator.pl` (441 LOC), `translate_clause/3` + `translate_expr/3`.
# PeTTa is the clean existence proof that MeTTa `(= H B)` compiles to host clauses, and it is the
# lineage Core already took SLG from. Function names are kept — `translate_clause`, `translate_expr`,
# `constrain_args`, `letstar_to_rec_let`, `goals_list_to_conj` — so a future session can diff us
# against `translator.pl` by grepping the same identifier.
#
# ─── THE ONE IDEA ────────────────────────────────────────────────────────────────────────────────
# `translate_expr(Expr) -> (Goals, Out)`: a nested FUNCTIONAL expression becomes a FLAT LIST OF GOALS
# plus an output variable. Nesting turns into sequencing. Everything else follows:
#
#   PeTTa translator.pl:184-187
#     (HV == let ; HV == chain), T = [Pat,Val,In] -> translate_expr(Pat,Gp,Pv),
#                                                    translate_expr(Val,Gv,V),
#                                                    translate_expr(In, Gi,Out),
#                                                    append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
#
# `let` IS ONE UNIFICATION GOAL. Not a construct to lower — a goal spliced into the list. And
# translator.pl:188-189, `let*` is `letstar_to_rec_let` then recurse: it is not a primitive at all,
# only sugar for nested `let`.
#
# WHY THAT MATTERS HERE. `MM2Router` hard-rejects `let`/`let*`/`if` by head string
# (`_MM2_SPECIAL_FORMS`), and MEASURED over Core/lib those three account for 399 of the 579 rules
# (69%) that cannot reach the compiled lane. There was no lowering to write because a String→String
# rewriter has no way to express a binding. In A-normal form the question dissolves: a binding is a
# goal. Measured by the frontend over all 73 lib files: 505 `let` nodes and 441 branch nodes.
#
# ─── WHAT A GOAL BECOMES ON OUR SUBSTRATE ────────────────────────────────────────────────────────
# PeTTa emits Prolog goals because SWI executes them and supplies clause indexing, WAM and tabling.
# We have no WAM — but a goal CONJUNCTION is exactly MM2's conjunctive source `(, P1 P2 …)`, and a
# DISJUNCTION is several rules. So the goal list is the right shared waypoint for both, which is why
# this stage stops at goals and does not emit: emission belongs to the MeTTa-IL bridge, a later file.
#
# ─── STATUS ──────────────────────────────────────────────────────────────────────────────────────
# Stage 3. Stages 1-2 are `compiler/IR.jl` and `compiler/Frontend.jl`. This file is PURE — it builds
# goal structures and executes nothing. Not wired into any evaluation path.

module CompilerANormal

using ..CompilerIR
import ..CompilerIR: NodeId, NO_ID

# ── goals (PeTTa's goal terms, typed) ────────────────────────────────────────────────────────────
# In Prolog a goal is just a term and the distinctions are implicit in the functor. Julia has no
# `=..`, and implicit-by-functor is exactly the string-dispatch failure mode this compiler exists to
# remove, so each goal shape is its own type.

abstract type Goal end

"""
PeTTa `(Pv = V)` — unification. THE representation of `let`.

`translate_expr` for `let` emits exactly this one goal, plus the goals of the pattern, the value and
the body. There is no `let` node past this stage.
"""
struct GUnify <: Goal
    lhs::IRAtom
    rhs::IRAtom
end

"""
PeTTa `Goal =.. [F|CallArgs]` with `append(Args,[Out],CallArgs)` (translator.pl:55-56, the runtime
dispatcher — the previously cited :33-34 is `goals_list_to_conj`, a different `append`).

RESULT-AS-LAST-ARGUMENT — the functional→relational lowering. A MeTTa function returns; a relation
binds. `(f a b)` with result `R` becomes the goal `f(a, b, R)`. This is what lets a nested functional
body flatten into a conjunction at all.
"""
struct GCall <: Goal
    head::Base.Symbol
    args::Vector{IRAtom}
    out::IRAtom
end

"""
PeTTa `(Cv == true -> BT ; BE)` (translator.pl:155-162).

BOTH ARMS UNIFY TO THE SAME `out` — that is `build_branch`'s job upstream, and it is what makes a
branch usable as a single goal in a conjunction. Each arm carries its own goals, so the arms are
independently A-normalized.
"""
struct GBranch <: Goal
    cond::Vector{Goal}
    condval::IRAtom
    then::Vector{Goal}
    els::Vector{Goal}
    out::IRAtom
end

"""
PeTTa `build_superpose_branches` + `disj_list` (translator.pl:110-112) — nondeterminism as a
DISJUNCTION of goal lists, all producing `out`.

Kept as one goal rather than split into rules here: whether a disjunction becomes several MM2 exec
rules or one is an EMISSION decision, and this stage must not pre-empt it.
"""
struct GDisj <: Goal
    branches::Vector{Vector{Goal}}
    out::IRAtom
end

"""
PeTTa `findall(EV, Conj, Out)` (translator.pl:116) — `collapse`.

The inverse of `GDisj`: gather every solution of a nondeterministic body into one list value. On our
substrate this is saturation-then-collect rather than SWI's `findall`, which is precisely why it stays
a typed goal instead of a host call.
"""
struct GFindall <: Goal
    template::IRAtom
    body::Vector{Goal}
    out::IRAtom
end

"""
A goal this stage could not flatten, carried verbatim.

FAILS OPEN DELIBERATELY, AND VISIBLY. Every other lane in this tree that met an unknown form either
dropped it silently (the MeTTa-IL lane, which returned `String[]` and an empty space) or rejected the
whole rule (`MM2Router`'s four gates). Neither is right for a compiler stage: dropping loses answers,
rejecting loses the 69%. Keeping the node means a later pass — or the interpreter fallback — can still
handle it, and `residuals` below makes it countable rather than invisible.
"""
struct GResidual <: Goal
    node::IRAtom
    out::IRAtom
end

# ── context ──────────────────────────────────────────────────────────────────────────────────────

"""
    ANCtx

Fresh-variable source, plus `funs` — the set of heads that are DEFINED FUNCTIONS in this module.

`funs` is PeTTa's `fun/1` predicate, resolved STATICALLY. It decides the single most consequential
question in this stage: is `(f a b)` a CALL (⇒ result-as-last-argument, `f(a,b,Out)`) or DATA (⇒ a
plain pattern, `f(a,b)`)? Getting it wrong is not subtle — MEASURED 2026-08-06, without this the
relation `(= (ancestor \$x \$y) (parent \$x \$y))` emitted

    (exec 0 (, (parent \$x \$y \$__t1)) (, (ancestor \$x \$y \$__t1)))

whose 3-ary source can never match the 2-ary facts `(parent alice bob)`. Silently derives nothing.

WHY STATIC, not a runtime check. PeTTa asks at runtime — `reduce/2` does `fun(F)` then
`current_predicate(F/Arity)` (`translator.pl:48-56`, still present at HEAD `d9a437c`). A compiler
need not pay that at all: the defined heads are exactly `IRProgram.definitions`, known for the whole
module before a single goal is emitted. That is the whole argument, and it stands on its own.

🔴 …AND ITS PREMISE IS VIOLATED BY THE ONLY PRODUCTION CALLER. `CompileLane.compile_definition`
compiles ONE FORM AT A TIME (deliberately — Invariant 6: a definition contributes its IL form or its
source form, never both). So `IRProgram.definitions` holds exactly ONE head, every callee looks like
data, and its call is never hoisted out of argument position. MEASURED 2026-08-11: that is why
`(= (frog \$x) (and (croaks \$x) (eat_flies \$x)))` emits
`(chain (eval (and (croaks \$x) (eat_flies \$x))) …)` and returns UNREDUCED, while the same source
compiled WITH its callees visible emits the hoisted chain and answers `["True","True"]`.

⚠️ AND THE OBVIOUS FIX MAKES IT WORSE — MEASURED, REVERTED, THIRD ATTEMPT. Passing the Space's
defined heads through as `extra_funs` (`keys(Eval._rules_of(Eval.all_atoms(sp)))`) was tried on
2026-08-11 and the corpus differential rejected it:

    b1_equal_chain.metta      0 → 4 extra errors
    b2_backchain.metta        0 → 1 extra error
    c1_grounded_basic.metta   0 → 1 exhausted
    e1_kb_write.metta         2 → 2   (UNCHANGED — it does not even fix its target)

Three clean scripts regressed and the intended beneficiary did not move. An earlier attempt at the
same idea was reverted for ANSWER DOUBLING. So "give `is_fun` the whole program" is NOT sufficient and
is actively harmful on its own: more heads known ⇒ more expressions become `GCall` ⇒ more clauses are
emitted, and those clauses are wrong in a different way.

WHAT PeTTa ACTUALLY HAS, and we have only half of. It runs BOTH mechanisms: a global `fun/1`
(`assertz`, `metta.pl:326`) AND the runtime dispatcher `reduce/2`, which keeps the term when `fun(F)`
fails (`Out = partial(F,Args)`). We took the static half and have no deferral, so an unresolved head
is frozen as data forever instead of being decided at run time.

THE MeTTa-NATIVE DEFERRAL IS `metta`, NOT `eval` — measured, because the obvious choice is wrong:

    (chain (eval  (Cons 1 Nil)) \$t \$t)                     ⟶ NotReducible        ✗ data destroyed
    (chain (metta (Cons 1 Nil) %Undefined% &self) \$t \$t)   ⟶ (Cons 1 Nil)        ✓ term kept
    (chain (metta (f a) %Undefined% &self) \$t \$t)          ⟶ reduced             ✓ call made

`metta.txt:79` defines `NotReducible` as "returns the unchanged function call instead", and
`interpret_args` (`metta.txt:352`) evaluates each argument with `metta` — guarding on `\$h != \$atom` —
precisely because `metta` returns the atom unchanged when nothing reduces. Lowering the conjunction
above with `metta`-deferred arguments answers `["True","True"]`, matching the source.

So the shape of a real fix is BOTH halves together — Space-wide `is_fun` for what is statically known,
plus a `metta` chain for what is not. Neither alone is safe. Do not retry the static half by itself.

⚠️ CORRECTED 2026-08-08. This previously claimed "PeTTa PR #165 had its `current_predicate/1` calls
REMOVED at maintainer request as too expensive, refactored to multifile declarations." EVERY CLAUSE
WAS FALSE, and it was written without opening the PR. #165 is "Memoization Library"
(`lib/lib_memo.pl`, 799 LOC, since removed from HEAD); it touches `current_predicate` zero times;
`translator.pl:54` still calls it; PeTTa has no `multifile` declaration anywhere in `src/`. The
grain of truth belonged to a LATER commit, `4a469c6`, which swapped `current_predicate` for
`multifile` in **`lib_memo`'s own availability check** — a different subject entirely. A citation
invented to corroborate a decision already made is worse than no citation: it survives review
BECAUSE it is plausible and BECAUSE it flatters the choice. Verify upstream refs when writing them.
"""
mutable struct ANCtx
    gen::UniqueAtomIdGenerator
    tmp::Int
    funs::Set{Tuple{Base.Symbol, Int}}      # (head, ARITY) — see `is_fun`
end
ANCtx(gen::UniqueAtomIdGenerator) = ANCtx(gen, 0, Set{Tuple{Base.Symbol, Int}}())
ANCtx(gen::UniqueAtomIdGenerator, funs::Set{Tuple{Base.Symbol, Int}}) = ANCtx(gen, 0, funs)

"""PeTTa `fun/1` + `current_predicate(F/Arity)` — is this head a defined function AT THIS ARITY?

🔴 NAME ALONE IS NOT ENOUGH, and the counterexample is in the conformance corpus.
`b1_equal_chain.metta` defines and uses `S` as two different things:

    line 15   (= (S \$x \$y \$z) (\$x \$z (\$y \$z)))       the SKI combinator — arity 3, a FUNCTION
    line 42   (= (Add \$x (S \$y)) (Add (S \$x) \$y))     Peano successor    — arity 1, a CONSTRUCTOR

With a name-keyed set, `S` reads as "a function" and the PATTERN `(S \$y)` is hoisted out of the rule
head, which becomes `(Add \$x \$__t1)` and matches nothing. MEASURED 2026-08-11: that one clause
produced ALL FOUR of b1's extra errors, and removing `S` alone from the known set took the diff to
zero. `S` is not even defined at two arities — it is defined at 3 and USED at 1, which name-keying
cannot express.

PeTTa carries the arity: `assertz(arity(F, Arity))` at `translator.pl:258`, and `reduce/2` gates the
call on `current_predicate(F/Arity)` (`translator.pl:53`), not on `fun(F)` alone. This is that pair.

⚠️ THE OLD NAME-ONLY BEHAVIOUR WAS ONLY SAFE BY ACCIDENT. It never bit because
`CompileLane.compile_definition` compiles ONE FORM AT A TIME, so `funs` held a single head and almost
nothing was classified as a call. Any whole-module compile — which the coverage ratchet already does —
was exposed to this the whole time."""
is_fun(c::ANCtx, name::Base.Symbol, arity::Int)::Bool = (name, arity) in c.funs

"Mint a fresh temporary — PeTTa's anonymous intermediate variables, named for debuggability."
function fresh_var(c::ANCtx)::IRVariable
    c.tmp += 1
    u = next_id!(c.gen)
    IRVariable(Base.Symbol("__t", c.tmp), u, next_id!(c.gen), NO_SOURCE)
end

# ── translate_expr — the heart (PeTTa translator.pl:96+) ─────────────────────────────────────────

"""
    translate_expr(ctx, node) -> (Vector{Goal}, IRAtom)

Flatten `node` into a goal list plus the value it produces.

PeTTa's base case is `translate_expr(X, [], X) :- (var(X) ; atomic(X)), !.` — a variable or atom
produces NO goals and is its own value. Everything else recurses and appends.

RETURN TYPE IS ANNOTATED ON EVERY METHOD, and that is load-bearing rather than decorative.
`translate_expr` recurses on the ABSTRACT `IRAtom`, so without an annotation Julia infers `Any` at
each recursive call and the whole walk becomes runtime dispatch. JET `@report_opt` reported 14 such
dispatches through `translate_expr`/`constrain_args` before these were added (2026-08-07).
"""
function translate_expr end

# base cases — a leaf is its own value, no goals (translator.pl:96)
translate_expr(::ANCtx, a::IRVariable)::Tuple{Vector{Goal},IRAtom} = (Goal[], a)
translate_expr(::ANCtx, a::IRSymbol)::Tuple{Vector{Goal},IRAtom} = (Goal[], a)
translate_expr(::ANCtx, a::IRGrounded)::Tuple{Vector{Goal},IRAtom} = (Goal[], a)
translate_expr(::ANCtx, a::IRResolvedSymbol)::Tuple{Vector{Goal},IRAtom} = (Goal[], a)
translate_expr(::ANCtx, a::IRPredefined)::Tuple{Vector{Goal},IRAtom} = (Goal[], a)

"""
An application. Arguments are flattened FIRST (their goals precede the call), then the call itself
produces a fresh output — PeTTa's `translate_args` followed by `Goal =.. [F|CallArgs]`.

A non-symbol head (`((curry +) 2)`) has no `F` to build a goal from, so it becomes a residual rather
than a wrong guess. PeTTa handles that case with `partial/2` closures at RUNTIME; we have no closure
representation yet, and inventing one here would be exactly the kind of unreferenced improvisation
this file avoids.
"""
function translate_expr(c::ANCtx, a::IRExpression)::Tuple{Vector{Goal},IRAtom}
    goals = Goal[]
    args = IRAtom[]
    for x in a.args
        g, v = translate_expr(c, x)
        append!(goals, g); push!(args, v)
    end
    # A SYMBOL head is a user function; a PREDEFINED head is a primitive. Both are calls, and both
    # get result-as-last-argument. Distinguishing them is the emitter's job, not this stage's.
    #
    # `IRPredefined` matters here disproportionately: MEASURED, 2192 of 2765 residuals were primitive
    # heads the compiler did not recognise, because `parse_from` resolves tokens at parse time
    # (Eval.jl:2525) so `match`/`+`/`car-atom` never arrive as symbols. Handling them is what
    # lets a rule that merely MENTIONS a primitive be compiled at all — `MM2Router`'s gate 2 rejects
    # exactly those rules, and that gate is a large part of its 65% miss rate.
    # CALL vs DATA — PeTTa's `fun/1`, resolved statically (see ANCtx). A defined function gets
    # result-as-last-argument and becomes a goal; anything else is DATA and stays a term, producing
    # NO goal and being its own value. Emitting a call for data yields a pattern one arity too wide,
    # which matches nothing and derives nothing silently.
    if a.head isa IRSymbol
        h = (a.head::IRSymbol).name
        if is_fun(c, h, length(args))
            out = fresh_var(c)
            push!(goals, GCall(h, args, out))
            return (goals, out)
        end
        return (goals, IRExpression(a.head, args, a.id, a.src))      # data term
    elseif a.head isa IRPredefined
        # A primitive is always a call — it computes, it is never a stored fact.
        out = fresh_var(c)
        push!(goals, GCall((a.head::IRPredefined).name, args, out))
        return (goals, out)
    end
    hg, _ = translate_expr(c, a.head)
    append!(goals, hg)
    out = fresh_var(c)
    push!(goals, GResidual(a, out))
    (goals, out)
end

"""
    translate_pattern(a) -> IRAtom

A PATTERN is DATA. It is matched against a value; nothing in it is called, so it lowers to ITSELF and
emits NO goals.

🔴 WHY THIS FUNCTION EXISTS — MEASURED 2026-08-10. Both pattern sites used `translate_expr`, the
EXPRESSION translator, whose whole job is to name intermediate computations. Run over a pattern it
does the wrong thing twice over: an all-variable tuple like `(\$h \$t)` has no symbol head and no
predefined head, so it falls to the catch-all and becomes a `GResidual` — and a residual declines the
CLAUSE. That is the single largest blocker in the MeTTa-IL stage: 111 of 313 declined clauses have a
variable-headed expression as their ONLY residual, and they are `let`-destructuring patterns —
`(let (\$h \$t) (decons-atom \$type) …)` in `stdlib.metta`'s own `car-atom`, `is-function`,
`get-doc-params`.

⚠️ AND IT IS NOT "TREAT VARIABLE-HEADED EXPRESSIONS AS DATA", which was the tempting one-line fix and
is WRONG. `for-each-in-atom` contains `(let \$_ (\$func \$head) …)` — the same shape, in VALUE position,
and it IS a dynamic call. POSITION decides, not node type. Keeping the split at the call site means
patterns lower as data and values keep going through `translate_expr`, where a variable head stays a
counted residual because we cannot resolve the callee. Neither reading is guessed at.

This is PeTTa's own distinction — `translator.pl:184-189` threads "the pattern's goals, the value's
goals, ONE unification", and a pattern's goals are empty because a pattern computes nothing.
"""
translate_pattern(a::IRAtom)::IRAtom = a

"""
`let` / `let*` — PeTTa translator.pl:184-189.

`let`  → `append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)`: the pattern's goals, the value's goals, ONE
         unification, then the body's goals. The body's value is the whole form's value.
`let*` → `letstar_to_rec_let` then recurse. Sequential binding is nested `let`, so the scoping is
         handled by the nesting itself and never by this function.
"""
function translate_expr(c::ANCtx, a::IRDestructiveBinding)::Tuple{Vector{Goal},IRAtom}
    goals = Goal[]
    # `let*` and `let` differ ONLY in nesting, and the frontend already recorded which this is.
    # Emitting the bindings in order gives `let*`; for plain `let` the values were lowered in the
    # outer scope by the frontend, so order is immaterial and the same walk is correct for both.
    for b in a.bindings
        gv, v = translate_expr(c, b.value)
        append!(goals, gv)
        push!(goals, GUnify(translate_pattern(b.pattern), v))   # ← `let` IS this goal
    end
    gb, out = translate_expr(c, a.body)
    append!(goals, gb)
    (goals, out)
end

"""
`if` / `case` / `match` — PeTTa translator.pl:150-176.

An `IRMatch` with the frontend's True/False arms is an `if`; anything else is a `case`. Both become a
`GBranch` chain whose arms share one `out`, which is what `build_branch` guarantees upstream.

A `case` with more than two arms folds right into nested branches — PeTTa's `translate_case` builds
the same if-then-else chain.
"""
function translate_expr(c::ANCtx, a::IRMatch)::Tuple{Vector{Goal},IRAtom}
    gs, scrutval = translate_expr(c, a.scrutinee)
    out = fresh_var(c)
    isempty(a.branches) && (push!(gs, GResidual(a, out)); return (gs, out))
    push!(gs, _branch_chain(c, a.branches, 1, scrutval, out))
    (gs, out)
end

"Fold arms right into nested `GBranch`es, all sharing `out` (PeTTa `translate_case`)."
function _branch_chain(c::ANCtx, brs::Vector{IRMatchBranch}, i::Int,
                       scrutval::IRAtom, out::IRAtom)::Goal
    b = brs[i]
    pv = translate_pattern(b.pattern)
    gt, tv = translate_expr(c, b.body)
    push!(gt, GUnify(out, tv))                  # arm's value IS the form's value
    # THE ARM TEST — the scrutinee must unify with THIS arm's pattern.
    #
    # ⚠️ This line was missing and the omission was silent. `scrutval` was threaded through the whole
    # recursion and then DISCARDED: the `GBranch` recorded `condval = pv` (the arm's pattern) with no
    # reference to the scrutinee anywhere in the goal. MEASURED 2026-08-07:
    #
    #   (= (col $c) (case $c ((red warm) (blue cool))))
    #     ⟹ GBranch(condval = red, cond = 0 goals)      -- `$c` is ABSENT
    #
    # A branch whose test has one operand cannot be lowered at all, which is why `GBranch` had no
    # `render_goal` and every clause carrying one was declined as `:control_flow`. Recording the test
    # as a GUnify — rather than as a new struct field — is what PeTTa does (`Cv == true`), and it
    # makes the arm directly emittable: `_unify_subst` discharges it into the substitution, so the
    # arm's rule is the redex SPECIALIZED to that pattern, which is the upstream Selection idiom
    # (`MM2_Structuring_Code/structuring_code_04_Control.md:106-119`, one exec per arm).
    cond = Goal[GUnify(scrutval, pv)]
    if i == length(brs)
        return GBranch(cond, pv, gt, Goal[], out)
    end
    GBranch(cond, pv, gt, Goal[_branch_chain(c, brs, i + 1, scrutval, out)], out)
end

"`superpose` — PeTTa `build_superpose_branches` + `disj_list` (translator.pl:110)."
function translate_expr(c::ANCtx, a::IRSuperpose)::Tuple{Vector{Goal},IRAtom}
    out = fresh_var(c)
    branches = Vector{Goal}[]
    for alt in a.alternatives
        g, v = translate_expr(c, alt)
        push!(g, GUnify(out, v))                # every branch produces the SAME out
        push!(branches, g)
    end
    (Goal[GDisj(branches, out)], out)
end

"Special forms kept WHOLE because a BINDER makes it mandatory — see the note in `translate_expr`."
const _KEEP_WHOLE = (SPECIAL_CHAIN,)

"""
Remaining special forms. `collapse` is PeTTa's `findall` (translator.pl:116); anything without a
reference lowering becomes a residual rather than a guess.
"""
function translate_expr(c::ANCtx, a::IRSpecial)::Tuple{Vector{Goal},IRAtom}
    if a.kind === SPECIAL_COLLAPSE && length(a.args) == 1
        g, v = translate_expr(c, a.args[1])
        out = fresh_var(c)
        return (Goal[GFindall(v, g, out)], out)
    end
    # `match` — RESIDUAL WITH ITS ARGUMENTS UNTOUCHED, which is the point of the special case.
    #
    # `(match <space> <pattern> <template>)` takes a space reference, a PATTERN and a TEMPLATE. None
    # of the three is a computation this stage should name: the pattern is matched structurally (the
    # same reason `translate_pattern` exists), and the template is evaluated by `match` itself AFTER
    # binding, not before. Running `translate_expr` over them — which the generic path below does —
    # hoists goals that a target then DOUBLE-EVALUATES if it lowers the node verbatim, and
    # `EmitIL.jl` does exactly that. Keeping the node whole is what makes verbatim lowering sound.
    #
    # `chain` JOINS IT, AND ONLY `chain` — `_KEEP_WHOLE` is a one-element tuple for a measured reason.
    # `Core/lib` and `stdlib.metta` contain hand-written minimal MeTTa (`car-atom` is
    # `(chain (decons-atom $atom) $ht (unify ($head $_) $ht …))`), and `EmitIL.jl` emits all four of
    # `chain`/`eval`/`function`/`return` VERBATIM because they ARE its target language. But only
    # `chain` must be kept whole HERE: its third argument is a TEMPLATE with a variable BOUND in it,
    # so hoisting a computation out of the binder's scope changes what the template means. That is a
    # wrong answer, not an inefficiency.
    #
    # ⚠️ WIDENING THIS SET TO ALL FOUR COST MM2 FOUR CLAUSES — 358 → 354 in `lib`, caught by the
    # coverage ratchet, not by the suite. This stage is SHARED, and `eval`/`function`/`return` have no
    # binder, so A-normalizing their arguments is sound and MM2 makes use of the resulting goals.
    # Narrowing back: MM2 377 (≥ the 376 floor), IL 847 instead of 848. One IL clause is the whole
    # price of not regressing the other lane.
    #
    # ⚠️ THE RESIDUAL COST, STATED RATHER THAN HIDDEN: for the other three, the argument is BOTH
    # hoisted into goals AND re-rendered inside the verbatim node, so it is evaluated more than once.
    # MEASURED — `(= (w) (function (return (nd))))` emits
    #   `(chain (eval (nd)) $t1 (chain (return (nd)) $t2 (chain (function (return (nd))) $t3 …)))`
    # — three evaluations of `(nd)`. It is WASTE, not a wrong answer: verified against the interpreter
    # with a NONDETERMINISTIC `(nd)` (two clauses), where duplicated branches would have shown up as
    # duplicated answers, and both lanes returned exactly `["a","b"]`. Removing the waste means
    # teaching `EmitIL` which goals were hoisted for a node it renders whole — a real change, not a
    # tidy-up, and out of scope here.
    #
    # This stays a `GResidual` rather than becoming a new goal type because MM2 has none of these
    # instructions and must keep declining them. The node is preserved; the target decides.
    if a.kind === SPECIAL_MATCH || a.kind in _KEEP_WHOLE
        out = fresh_var(c)
        return (Goal[GResidual(a, out)], out)
    end
    goals = Goal[]
    for x in a.args
        g, _ = translate_expr(c, x)
        append!(goals, g)
    end
    out = fresh_var(c)
    push!(goals, GResidual(a, out))
    (goals, out)
end

# catch-all so the function is TOTAL over IRAtom — an unmatched node becomes a counted residual, not
# a MethodError at compile time and not a silent drop.
function translate_expr(c::ANCtx, a::IRAtom)::Tuple{Vector{Goal},IRAtom}
    out = fresh_var(c)
    (Goal[GResidual(a, out)], out)
end

# ── clauses (PeTTa translator.pl:18-35) ──────────────────────────────────────────────────────────

"""
    ANClause

One A-normalized clause: head arguments, the body's goals, and the output variable.

`out` is the result-as-last-argument: PeTTa's `append(HeadArgs,[Out],FinalArgs)`. The head of the
compiled relation is `name(head_args..., out)`.
"""
struct ANClause
    name::Base.Symbol
    head_args::Vector{IRAtom}
    goals::Vector{Goal}
    out::IRAtom
    # 🔴 THE CLAUSE'S HEAD WAS NESTED and this shape CANNOT be reconstructed from `name` + `head_args`.
    # `(= (((curry $f) $x) $y) …)` has `lhs.args == [$y]`; `((curry $f) $x)` is the HEAD, not an
    # argument, so `$f` and `$x` are nowhere in this struct. `EmitIL` builds its head as
    # `(name head_args…)`, which for that clause is `(curry $y)` — matching `(curry ANYTHING)` with a
    # body referencing UNBOUND `$f`/`$x`.
    #
    # MEASURED 2026-08-11, and it is LIVE, not hypothetical:
    #     (= ((lambda $var $body) $arg) (let $var $arg $body))
    #   emits
    #     (= (lambda $arg) (function (unify $var $arg (return $body) (return Empty))))
    #   with `$var`/`$body` unbound. `curry`/`curry-a` escape only because their variable-headed BODY
    #   is declined — the wrong head is masked by an unrelated decline, not prevented.
    #
    # Emission DECLINES on this flag rather than guessing. The real fix is to carry the original
    # pattern through to emission (minimal MeTTa's `(= <pattern> <body>)` accepts a nested pattern
    # perfectly well, so the target is not the obstacle — this struct is), and that is a larger change
    # than removing a wrong answer, which is what this does.
    nested_head::Bool
end
ANClause(n::Base.Symbol, ha::Vector{IRAtom}, gs::Vector{Goal}, o::IRAtom) =
    ANClause(n, ha, gs, o, false)

"""
    constrain_args(ctx, arg) -> (Vector{Goal}, IRAtom)

PeTTa `constrain_args/3` (translator.pl:2-13).

A head argument that is a FUNCTION CALL is hoisted out into body goals and replaced by a variable, so
head patterns stay first-order and indexable. A variable or atom passes through untouched; a
structure recurses.

This is what keeps the head matchable. It is also the piece that makes first-argument indexing
possible at all — the mechanism by which Prolog decides a call is deterministic, which is the same
question §3c of the JeTTa spec says we have no answer to.
"""
function constrain_args(c::ANCtx, a::IRAtom)::Tuple{Vector{Goal},IRAtom}
    (a isa IRVariable || a isa IRSymbol || a isa IRGrounded) && return (Goal[], a)
    if a isa IRExpression
        # A CALL in head position: hoist it. A CONSTRUCTOR PATTERN: keep it, and recurse into its
        # arguments. PeTTa gates this on `fun(F)` — `constrain_args([F|Args], Var, Goals) :- atom(F),
        # fun(F), !, translate_expr(...)` (translator.pl:9-12) — and ours did not, hoisting anything
        # with a symbol head. That was invisible only because `funs` was near-empty per form; with
        # real knowledge it destroys `(= (Add $x (S $y)) …)` by hoisting the Peano pattern.
        if a.head isa IRSymbol && is_fun(c, (a.head::IRSymbol).name, length(a.args))
            g, v = translate_expr(c, a)
            return (g, v)
        end
        goals = Goal[]; kids = IRAtom[]
        for x in a.args
            g, v = constrain_args(c, x)
            append!(goals, g); push!(kids, v)
        end
        return (goals, IRExpression(a.head, kids, a.id, a.src))
    end
    (Goal[], a)
end

"""
    translate_clause(ctx, name, clause) -> ANClause

PeTTa `translate_clause/3` (translator.pl:18).

  1. `constrain_args` over the head arguments, collecting a goal PREFIX,
  2. `translate_expr` over the body → goals + output,
  3. result-as-last-argument.

`GoalsPrefix` comes first, exactly as upstream's `append(GoalsPrefix, FinalGoals, Goals)`.
"""
function translate_clause(c::ANCtx, name::Base.Symbol, clause::IRBoundAtom)::ANClause
    head_args = IRAtom[]
    prefix = Goal[]
    lhs = clause.pattern
    if lhs isa IRExpression
        for x in lhs.args
            g, v = constrain_args(c, x)
            append!(prefix, g); push!(head_args, v)
        end
    end
    body, out = translate_expr(c, clause.value)
    # A head whose own head is another EXPRESSION is nested — see `ANClause.nested_head`.
    nested = lhs isa IRExpression && (lhs::IRExpression).head isa IRExpression
    ANClause(name, head_args, vcat(prefix, body), out, nested)
end

"""Every `(head, arity)` this program DEFINES — keyed per CLAUSE, not per definition.

Clauses of one name may differ in arity (`(= (K \$x \$y) \$x)` alongside `(= ((K \$x) \$y) \$x)` in
`b1_equal_chain.metta`), so the pair comes off each clause's own pattern. A definition whose pattern
is not an expression — a nullary head written bare — contributes arity 0."""
function defined_arities(program::IRProgram)::Set{Tuple{Base.Symbol, Int}}
    out = Set{Tuple{Base.Symbol, Int}}()
    for d in program.definitions, cl in d.clauses
        p = cl.pattern
        push!(out, (d.name, p isa IRExpression ? length((p::IRExpression).args) : 0))
    end
    out
end

"""
A-normalize every clause of every definition in `program`.

Collects the module's DEFINED HEADS first, so `translate_expr` can distinguish a call from data
without a runtime existence check. This is the whole-module knowledge a compiler has and an
interpreter does not.
"""
function translate_program(program::IRProgram)::Vector{ANClause}
    funs = defined_arities(program)
    c = ANCtx(program.gen, funs)
    out = ANClause[]
    for d in program.definitions, cl in d.clauses
        push!(out, translate_clause(c, d.name, cl))
    end
    out
end

# ── inspection ───────────────────────────────────────────────────────────────────────────────────

"Every goal in `gs`, including those nested inside branches, disjunctions and findalls."
function all_goals(gs::Vector{Goal})::Vector{Goal}
    acc = Goal[]
    for g in gs
        push!(acc, g)
        if g isa GBranch
            append!(acc, all_goals(g.cond)); append!(acc, all_goals(g.then)); append!(acc, all_goals(g.els))
        elseif g isa GDisj
            for b in g.branches; append!(acc, all_goals(b)); end
        elseif g isa GFindall
            append!(acc, all_goals(g.body))
        end
    end
    acc
end

"""
    residuals(clause) -> Int

How many goals this stage could NOT flatten.

The number that matters: a clause with zero residuals is fully A-normalized and can be emitted; one
with residuals still needs the interpreter. Reporting it is the difference between knowing our
coverage and assuming it — `MM2Router` reported coverage as a pass/fail gate and nobody knew the 65%
figure until it was measured.
"""
residuals(cl::ANClause)::Int = count(g -> g isa GResidual, all_goals(cl.goals))

"Is this clause fully A-normalized (no residual goals)?"
is_flat(cl::ANClause)::Bool = residuals(cl) == 0


# ── CONTROL-FLOW EXPANSION ───────────────────────────────────────────────────────────────────────
#
# `GBranch`/`GDisj` have no `render_goal`, so every clause carrying one was declined `:control_flow`
# (146 of 725 at 366/1000 coverage). Rather than teach the emitter a branching template, expand each
# clause into one control-free clause PER EXECUTION PATH and let the existing — now staged — emitter
# handle each unchanged. That is upstream's Selection idiom verbatim: one exec per arm
# (`MM2_Structuring_Code/structuring_code_04_Control.md:106-119`, VERIFIED on our kernel 2026-08-07).
#
# WHY ONE-EXEC-PER-ARM IS SOUND HERE, AND WHEN IT IS NOT. Running every arm is equivalent to
# first-match ONLY when the arms are mutually exclusive. MM2 has no negation — `(I (not X))` panics
# upstream at `sources.rs:233` — so an `else` cannot be expressed as "the condition failed". We
# therefore require every arm pattern to be a GROUND CONSTANT and decline otherwise. That covers `if`
# (arms are exactly `True`/`False`) and a constant `case` (`red`/`blue`), and it declines a
# variable-headed arm, which matches everything and would make the arms overlap.
#
# PARTIAL EXPANSION IS NEVER EMITTED. If any path of a clause fails to emit, the WHOLE clause is
# declined. Emitting three of four arms silently drops an answer, and this compiler's standing rule is
# that a rule which cannot fire is worse than an absent one.

"A ground constant — the only arm pattern for which running all arms equals first-match."
_ground_arm(a::IRAtom)::Bool = a isa IRSymbol || a isa IRGrounded

"""
    expand_control(clause; max_paths=32) -> Vector{ANClause} | nothing

One control-free clause per execution path, or `nothing` if the clause falls outside the expandable
fragment (a non-ground arm pattern, a `GFindall`, or a path count over `max_paths`).

`max_paths` is a real bound, not a formality: nested branches multiply, and three 2-armed branches in
one body is already 8 paths. Declining past the cap keeps a pathological clause from generating
hundreds of exec rules that would each have to fire.
"""
function expand_control(clause::ANClause; max_paths::Int = 32)::Union{Vector{ANClause},Nothing}
    paths = _expand_goals(clause.goals, max_paths)
    paths === nothing && return nothing
    ANClause[ANClause(clause.name, clause.head_args, gs, clause.out) for gs in paths]
end

"Cartesian product over the goal list — each goal contributes its own alternatives."
function _expand_goals(gs::Vector{Goal}, cap::Int)::Union{Vector{Vector{Goal}},Nothing}
    acc = Vector{Goal}[Goal[]]
    for g in gs
        alts = _expand_goal(g, cap)
        alts === nothing && return nothing
        nxt = Vector{Goal}[]
        for a in acc, b in alts
            length(nxt) >= cap && return nothing
            push!(nxt, Goal[a..., b...])
        end
        acc = nxt
    end
    acc
end

"""
Static value of the arm test when both sides are ground: `:yes`, `:no`, or `:dynamic`.

`(if True yes no)` lowers to an arm test `GUnify(True, True)` — GROUND ON BOTH SIDES. `_unify_subst`
discharges only VARIABLE-headed unifications, so such a goal declined the whole clause even though its
value is known at compile time. Deciding it here removes the dead arm entirely, which is both the
correct lowering and the one place this compiler does any real specialisation.
"""
function _static_test(lhs::IRAtom, rhs::IRAtom)::Base.Symbol
    (_ground_arm(lhs) && _ground_arm(rhs)) || return :dynamic
    if lhs isa IRSymbol && rhs isa IRSymbol
        return lhs.name === rhs.name ? :yes : :no
    elseif lhs isa IRGrounded && rhs isa IRGrounded
        return lhs.value == rhs.value ? :yes : :no
    end
    :no                                             # a symbol and a grounded literal never unify
end

function _expand_goal(g::GBranch, cap::Int)::Union{Vector{Vector{Goal}},Nothing}
    # The arm test is the GUnify `_branch_chain` puts first in `cond`.
    test = isempty(g.cond) ? nothing : g.cond[1]
    static = test isa GUnify ? _static_test(test.lhs, test.rhs) : :dynamic

    # A DYNAMIC test needs a ground arm pattern, or the arms overlap and run-all ≠ first-match.
    static === :dynamic && !_ground_arm(g.condval) && return nothing

    out = Vector{Goal}[]
    if static !== :no                               # :no ⇒ this arm is unreachable, drop it entirely
        # A statically-true test carries no information; emitting it would decline on ground-vs-ground.
        rest = static === :yes ? Goal[g.cond[2:end]..., g.then...] : Goal[g.cond..., g.then...]
        thens = _expand_goals(rest, cap)
        thens === nothing && return nothing
        append!(out, thens)
    end
    # A statically-TRUE arm makes every later arm unreachable — that is what `else` means.
    static === :yes && return out
    if !isempty(g.els)                               # the else arm is the NEXT arm's GBranch
        elses = _expand_goals(g.els, cap)
        elses === nothing && return nothing
        append!(out, elses)
    end
    length(out) > cap ? nothing : out
end

function _expand_goal(g::GDisj, cap::Int)::Union{Vector{Vector{Goal}},Nothing}
    out = Vector{Goal}[]
    for b in g.branches
        e = _expand_goals(b, cap)
        e === nothing && return nothing
        append!(out, e)
    end
    length(out) > cap ? nothing : out
end

# `collapse` gathers EVERY solution into one list value — saturation-then-collect, not a path split.
# Expansion cannot express it, so it stays declined and stays counted.
_expand_goal(::GFindall, ::Int)::Union{Vector{Vector{Goal}},Nothing} = nothing
_expand_goal(g::Goal, ::Int)::Union{Vector{Vector{Goal}},Nothing} = Vector{Goal}[Goal[g]]

export Goal, GUnify, GCall, GBranch, GDisj, GFindall, GResidual, expand_control,
       ANCtx, fresh_var, translate_expr, constrain_args, translate_clause, translate_program,
       ANClause, all_goals, residuals, is_flat

end # module CompilerANormal
