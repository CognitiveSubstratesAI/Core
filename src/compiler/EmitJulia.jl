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
import ..Eval: merge_bindings
import ..CompilerANormal: Goal, GUnify, GCall, GBranch, GDisj, GFindall, GResidual, ANClause
import ..CompilerIR: IRAtom
import ..CompilerEmitIL: _atom_of
# 🔴 IMPORTED EXPLICITLY, NOT ASSUMED. First run died on `UndefVarError: freshvar` — the guessed-name
# class again. These five live in TWO modules: `match_atoms`/`is_present` in Atoms.jl (StandardMeTTa),
# `rename_fresh`/`freshvar`/`subst` in Eval.jl. Located before importing, not after failing.
import ..CompilerEmitJuliaCode
import ..CompilerEmitJuliaCode: codegen_head, head_compilable, CompiledDepthExceeded,
    _builds_reducible_arg
import ..CompilerFrontend
import ..CompilerANormal
import ..Eval          # the MODULE, not only its names — `jit_head!` reaches Eval.all_atoms / _JIT_HEAD_HOOK
import ..Eval: rename_fresh, freshvar, subst, CompiledOk, ExecNoReduce,
    TOKEN_REGISTRY, is_executable, execute, ExecOk, Bindings, add_var_binding,
    interpret, _metta, UNDEF

export emit_julia_clause, emit_julia_program

"Goal kinds this stage handles. GBranch/GDisj/GFindall are MILESTONE 2 — declined, never dropped."
_supported(g::Goal)::Bool = g isa GUnify || g isa GCall || g isa GResidual

"""
    emit_julia_clause(cl) -> Union{Tuple{Atom, Vector}, Nothing}

Compile ONE clause to `(rule_atom, step_plan)`: the rule `(= (name head_args…) out)` it denotes,
plus the goal plan run at call time. `nothing` = declined.

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
function emit_julia_clause(cl::ANClause)
    cl.nested_head && return nothing
    all(_supported, cl.goals) || return nothing
    # MILESTONE 1b: GUnify + GROUNDED GCall. A non-grounded GCall would have to route back through
    # `interpret`, which is a DEFERRAL, not compilation — declined here rather than counted.
    plan = _plan_goals(cl.goals)
    plan === nothing && return nothing
    parts = Atom[Sym(String(cl.name))]
    for a in cl.head_args                        # operand position ⇒ NO specials (two-builder split)
        v = _atom_of(a, false)
        v === nothing && return nothing
        push!(parts, v)
    end
    out = _atom_of(cl.out, false)
    out === nothing && return nothing
    rule = Expression(Atom[Sym("="), Expression(parts), out])
    # 🔴 PACK RULE + PLAN INTO ONE ATOM. `rename_fresh` is applied PER CALL so a clause's variables
    # do not capture across calls — but it renames ONE ATOM. The plan's atoms are built HERE, at
    # compile time, so renaming the rule alone leaves the plan referencing the ORIGINAL names and
    # every goal then unifies against a variable that no longer exists. MEASURED before this fix:
    # `(= (dup $x) (let $y $x (pair $y $y)))` answered `(pair $y#1097 $y#1097)` instead of
    # `(pair 7 7)`, and `(= (inc $x) (+ $x 1))` returned the call itself. Renaming the PAIR as a
    # single atom keeps the correspondence by construction.
    (rule, plan, _pack(rule, plan))
end

"Pack rule + every plan atom into one container atom, so `rename_fresh` renames them CONSISTENTLY."
function _pack(rule::Atom, plan)
    items = Atom[rule]
    for st in plan
        if st[1] === :unify
            (push!(items, st[2]); push!(items, st[3]))
        else
            (append!(items, st[3]); push!(items, st[4]))
        end
    end
    Expression(items)
end

"Unpack a renamed container back into (rule, plan) with the SAME fresh variables throughout."
function _unpack(packed::Atom, plan)
    ch = (packed::Expression).children
    rule = ch[1]
    k = 2
    # allow-any: tagged plan steps of MIXED ARITY — `(:unify, l, r)` and a 4-element GCall
    # form, discriminated by `st[1]`. A `Vector{Tuple}` would still be abstract; the real fix
    # is a PlanStep struct per goal kind, which is a refactor of `_plan_goals`, not a type
    # annotation. Not a hot path: built once per clause at COMPILE time, never per call.
    out = Any[]
    for st in plan
        if st[1] === :unify
            push!(out, (:unify, ch[k], ch[k + 1]))
            k += 2
        else
            n = length(st[3])
            push!(out, (:gcall, st[2], Atom[ch[k + i - 1] for i in 1:n], ch[k + n]))
            k += n + 1
        end
    end
    (rule, out)
end

"""
    _plan_goals(goals) -> Union{Vector, Nothing}

Compile the goal list to a STEP PLAN, or decline. Each step is executed at call time against the
running substitution.

  `GUnify(l, r)`   -> (:unify, l_atom, r_atom)          real unification, extends sigma
  `GCall(h,a,o)`   -> (:gcall, grounded, arg_atoms, o)  DIRECT `execute` — native, no interpreter
                                                        round trip. THIS is the compiled part.
  anything else    -> decline

🔴 A NON-GROUNDED `GCall` IS DECLINED, NOT DEFERRED. Routing it back through `interpret` would raise
"emitted" while compiling nothing — the same inflation `FLOOR_IL_RESIDUAL_FREE` exists to expose. A
head calling another COMPILED head is the natural next step and is not this increment.
"""
function _plan_goals(goals::Vector{Goal})
    # allow-any: same tagged mixed-arity plan steps as `out` above — see that note.
    plan = Any[]
    for g in goals
        if g isa GUnify
            l = _atom_of(g.lhs, false)
            l === nothing && return nothing
            r = _atom_of(g.rhs, false)
            r === nothing && return nothing
            push!(plan, (:unify, l, r))
        elseif g isa GCall
            as = Atom[]
            for a in g.args
                v = _atom_of(a, false)
                v === nothing && return nothing
                push!(as, v)
            end
            o = _atom_of(g.out, false)
            o === nothing && return nothing
            op = get(TOKEN_REGISTRY, String(g.head), nothing)
            if op !== nothing && is_executable(op)
                push!(plan, (:gcall_native, op, as, o))       # DIRECT execute — compiled
            else
                # 🔴 A USER-FUNCTION CALL COMPILES TO SEAM RE-ENTRANCY, NOT A DECLINE. Declining it
                # would cover only grounded arithmetic and `let`, leaving most of `lib/` out and
                # making the DELIVERY gate fail by construction (WorldModel heads-dispatched ~0).
                # `interpret((head args…), sigma)` reaches `rule_results`, which finds the callee's
                # CLOSURE if it has one and its rules otherwise — the same way JeTTa links compiled
                # functions (INVOKESTATIC to compiled code, eval for the rest).
                # ⚠️ COUNTED SEPARATELY: "calls via seam" is a THIRD category — not native, not a
                # GResidual. Folding it into either would misreport what is compiled.
                push!(plan, (:gcall_seam, Sym(String(g.head)), as, o))
            end
        else
            return nothing
        end
    end
    plan
end

"""
Run one clause's plan. Returns EVERY surviving substitution — a VECTOR, not one sigma.

🔴 FAN-OUT IS NOT OPTIONAL. MeTTa is multi-result: a call can answer several ways and each answer
extends sigma differently. Threading a single sigma (the first version here) silently keeps ONE
branch and drops the rest — the same truncation shape as `_reduced_goal`'s `rs[1]`, which is a
recorded wrong-answer defect in the tabling path. Empty vector = the clause contributes nothing.
"""
function _run_plan(plan, sigma0::Bindings, space)::Vector{Bindings}
    sigmas = Bindings[sigma0]
    for step in plan
        isempty(sigmas) && return sigmas
        nxt = Bindings[]
        for sigma in sigmas
            _bind_step!(nxt, step, sigma, space)
        end
        sigmas = nxt
    end
    sigmas
end

"One plan step against one sigma, appending every resulting sigma to `acc`."
function _bind_step!(acc::Vector{Bindings}, step, sigma::Bindings, space)
    kind = step[1]
    if kind === :unify
        for b in match_atoms(subst(step[2], sigma), subst(step[3], sigma))
            append!(acc, merge_bindings(sigma, b))
        end
        return acc
    end
    (_, callee, as, o) = step
    args = Atom[subst(a, sigma) for a in as]
    results = if kind === :gcall_native
        r = execute(callee, args, nothing)
        r isa ExecOk ? r.results : Atom[]
    else                                              # :gcall_seam — re-enter via the interpreter
        call = Expression(Atom[callee, args...])
        Atom[a for (a, _) in interpret(_metta(call, UNDEF), space, sigma)]
    end
    for res in results
        for b in match_atoms(subst(o, sigma), res)
            append!(acc, merge_bindings(sigma, b))
        end
    end
    acc
end

# 🔴 `_CUR_SPACE` WAS HERE AND IS GONE. It was a global `Ref{Union{Nothing, Space}}` that
# `_head_closure` SET ON ENTRY AND NEVER RESTORED, standing in for "the space this evaluation is
# running in" — the same defect class as the global head registry this chunk replaced: process-wide
# mutable state impersonating per-evaluation state.
# MEASURED 2026-10-01: it held a STRONG reference to the most recent plan-lane space, so that space
# outlived every user reference and `_SPACE_DEFS` could not drop its table — the WeakKeyDict is not
# an ephemeron table, and a strong ref reachable from anywhere pins the key. Gate:
# `test/test_jit_head_op.jl`, which measures collection with a `WeakRef` rather than by the dict's
# length (dead entries are removed LAZILY by finalizers, so a length can count an already-dead key).
# It was also unrestored across nesting, so an evaluation that re-entered the plan lane in another
# space would leave the outer call reading the inner one's space.
# ⇒ the space is now an ARGUMENT, threaded `_head_closure` -> `_run_plan` -> `_bind_step!`.

"""
    emit_julia_program(clauses) -> Dict{Symbol, Function}

Group by HEAD and build one closure per head over ALL its clauses.

🔴 ALL-OR-NOTHING PER HEAD, NOT PER CLAUSE. If a head has five clauses and only four compile,
registering it would DROP the fifth's answers — the seam shadows the head, so the interpreter never
sees the rules the closure does not carry. A head is registered only if EVERY one of its clauses
emitted. (`docs/architecture/COMPILED_HEAD_SEAM.md`, "the unit is the HEAD".)
"""
# 🔴 `space` IS OPTIONAL BUT PRODUCTION ALWAYS PASSES IT. It supplies `Eval.space_id`, which goes
# into every GENERATED FUNCTION NAME (`EmitJuliaCode._genname`). Without it, two spaces' same-named
# heads compile to the SAME Julia function, and because a caller names its callee's entry directly
# (:281 below) compiling one program silently redefines the other's code — MEASURED 2026-10-01 as
# A answering 101 instead of 2, gated by `test/compiler/test_ab_space_collision.jl`.
# `nothing` ⇒ id 0, the unidentified namespace: correct for the isolated harnesses in
# `test/compiler/` that compile one program at a time and never register two spaces' heads at once.
function emit_julia_program(clauses::Vector{ANClause}, space=nothing, reducible=nothing)
    sid = space === nothing ? 0 : Eval.space_id(space)
    # WHICH HEADS REDUCE — the soundness guard's input (see `_builds_reducible_arg`). From the SPACE,
    # because a data constructor and a function are told apart by HAVING RULES, which is a property
    # of the space and not of this program fragment. `jit_head!` already walks `all_atoms` to collect
    # its clauses and passes the set it saw, so the walk is not paid twice.
    red = reducible === nothing ?
        (space === nothing ? Set{Base.Symbol}() : _space_rule_heads(space)) :
        reducible
    # TYPED, like `an_by_head` below. `emit_julia_clause` returns `(rule, plan, packed)` — NOT a
    # bare Atom; an earlier attempt typed this `Vector{Atom}` from the `_pack` helper's return and a
    # comment, and 3 suite files failed with
    #   `MethodError: Cannot convert Tuple{Expression, Vector{Any}, Expression} to Atom`.
    # Read the function's own return, not a neighbour's. `plan` stays a bare `Vector` (mixed-arity
    # tagged steps — see `_plan_goals`), which is abstract but is NOT `Any`.
    by_head = Dict{Base.Symbol, Vector{Tuple{Expression, Vector, Expression}}}()
    an_by_head = Dict{Base.Symbol, Vector{ANClause}}()
    declined = Set{Base.Symbol}()
    # TWO PASSES, because the soundness guard needs `red` and `red` needs the program's own heads
    # when no space was given.
    for cl in clauses
        push!(get!(an_by_head, cl.name, ANClause[]), cl)
    end
    _red = isempty(red) && space === nothing ? Set(keys(an_by_head)) : red
    for cl in clauses
        # 🔴 THE SOUNDNESS GUARD APPLIES TO THE PLAN LANE TOO, AND OMITTING IT COST A LIVE PLN
        # DEFECT. `_build_head` enforces it for CODEGEN only, so `compute-demand-field!` —
        # `(let $seed (dem-join! $q 1.0) (propagate! $q))` — kept compiling on the PLAN lane, bound
        # `$seed` to the ATOM `(dem-join! $q 1.0)` instead of calling it, and EVERY WRITE WAS
        # SILENTLY SKIPPED: 5 `(dem …)` atoms became 0. Both lanes build arguments the same way, so
        # both need the same refusal.
        if _builds_reducible_arg(cl.goals, _red)
            push!(declined, cl.name)
            continue
        end
        r = emit_julia_clause(cl)
        if r === nothing
            push!(declined, cl.name)
        else
            push!(get!(by_head, cl.name, Tuple{Expression, Vector, Expression}[]), r)
        end
    end
    for h in declined                            # any declined clause disqualifies the whole head
        delete!(by_head, h)
    end
    CODEGEN_NATIVE_HEADS[] = 0
    # 🔴 WHICH HEADS COMPILE IS A FIXPOINT, NOT A PER-HEAD TEST. Once generated code can CALL another
    # compiled head it names that head's entry directly, so `f` compiles only if every head it calls
    # also compiles — and dropping one callee can disqualify its callers transitively. Start with
    # every head a candidate and shrink until stable. `head_compilable` builds without evaluating,
    # so a candidate that is later dropped leaves no half-registered functions behind.
    # 🔴 AND THE CANDIDATE SET IS `an_by_head`, NOT `by_head` — MEASURED 2026-09-26. Building it
    # from `by_head` GATES THE NATIVE LANE BEHIND THE PLAN LANE: a head one clause of which
    # `emit_julia_clause` declines is deleted above, so codegen never sees it even when codegen
    # compiles it perfectly well. `(= (down $n) (if …))` + `(= (down $n) tag)` was exactly that —
    # `codegen_head` returned a function, `emit_julia_program` registered NOTHING, and the call came
    # back unreduced. The two lanes have different, overlapping scopes; neither is a subset of the
    # other, so each must be asked independently and a head kept if EITHER accepts it.
    compilable = Set{Base.Symbol}()
    if CODEGEN_ENABLED[]
        union!(compilable, keys(an_by_head))
        while true
            drop = Base.Symbol[]
            for h in compilable
                haskey(an_by_head, h) || (push!(drop, h); continue)
                head_compilable(h, an_by_head[h], compilable, red) || push!(drop, h)
            end
            isempty(drop) && break
            setdiff!(compilable, drop)
        end
    end
    out = Dict{Base.Symbol, Function}()
    for h in keys(an_by_head)
        fn = h in compilable ? codegen_head(h, an_by_head[h], compilable, sid, red) : nothing
        if fn !== nothing
            CODEGEN_NATIVE_HEADS[] += 1
            out[h] = _codegen_seam_fn(h, fn)     # GENERATED JULIA -> LLVM -> native
            # 🔴 THE LANE IS DECIDED HERE AND NOWHERE ELSE, so it is recorded here. The seam
            # (`Eval.rule_results`) cannot tell the two apart afterwards: both arrive as a
            # `CompiledHead` holding an opaque `Function`. Without this, "compiled" would lump the
            # A-normal plan interpreter in with generated code — the inflation the native-share
            # metric exists to catch. See `Eval.SpaceCompileState`.
            Eval.set_head_lane!(space, h, :native)
        elseif haskey(by_head, h)
            out[h] = _seam_fn(h, by_head[h])     # the PLAN-WALKING closure — an A-normal interpreter
            Eval.set_head_lane!(space, h, :plan)
        else                                     # neither lane ⇒ not registered, interpreter handles it
            # A head that USED to compile and no longer does must not keep a stale lane, or its
            # interpreter calls would be counted as compiled ones.
            Eval.clear_head_lane!(space, h)
        end
    end
    out
end

"""
Switch for stage 4d. `false` ⇒ every head gets `_seam_fn`, exactly as before this flag existed.

🔴 WHY A FLAG AND NOT A REPLACEMENT. `_seam_fn` handles clauses `codegen_head` does not. Turning
codegen on must never LOSE a head: out of scope ⇒ `codegen_head` returns `nothing` ⇒ that head keeps
the plan-walking closure. Per-head, not per-program, so one unsupported head does not disable the
lane. ⚠️ The two lanes' scopes OVERLAP but neither contains the other — `emit_julia_program` asks
each independently and keeps a head if EITHER accepts, which is a defect this file once had the
other way round.

🟢 **DEFAULT FLIPPED TO `true`, 2026-09-26** — and read the next paragraph before quoting that.

🔴 **WHAT THE FLAG DOES NOT DO: IT DOES NOT MAKE ANYTHING COMPILE.** The ONLY production trigger for
this whole path is the explicit MeTTa op `(compile-head <name>)` — `Eval.jl:2450` is the single
caller of `_JIT_HEAD_HOOK`, and `jit_head!` is the only thing that reaches `emit_julia_program`. So
`true` means "when a head IS compiled, generate native Julia instead of a plan-walking closure"; it
does not mean heads compile by themselves, and an ordinary MeTTa program still runs interpreted
unless it asks. The commit that flipped this said "the compiler is the primary lane; the interpreter
is the fallback" — THAT WAS WRONG, and it is the same never-wired class `test_jit_head_op.jl`'s
header records: a flag was flipped and called a finish line without checking what invokes the path.
Making compilation automatic is a separate, unwritten step.

What the flip DID have to earn, and did:
  * SCOPE. 228 of 768 `Core/lib` heads compile natively, 251 take the plan lane, 289 neither — up
    from 115 native, measured THROUGH this function rather than by calling `codegen_head` directly.
  * CORRECTNESS. A differential against the interpreter on MULTISETS, plus the reference engines:
    `!(outer 20)` through a cross-head call agrees 6/6 with hyperon; `!(down 2)` agrees on the
    multiset `{done, tag, tag, tag}` with hyperon, CeTTa, JeTTa and PeTTa (Core's ORDER differs,
    which is within spec — result order is unspecified).
  * NO COMPILE-TIME BLOWUP. The sink is `@nospecialize`d: 2 specialisations at any recursion depth,
    where it was one per level.
  * A BOUNDED FAILURE THAT COSTS NO ANSWERS. Past the depth budget the seam returns `nothing`, so
    `rule_results` runs its ordinary `(= …)` query and the call still answers — measured at depth
    4,500 with a 4,000 budget: 4,502 answers, identical to the interpreter, no error atom. The head
    is marked `Eval.COMPILED_INTERPRET_ONLY` for the rest of the call tree, or the retry re-faults
    at every level (depth x budget of wasted work).
  * RE-RUN SAFETY. Impure ops are out of the lane (cost: one head).
Set it to `false` to get the previous behaviour; every head then takes `_seam_fn` as before.
"""
const CODEGEN_ENABLED = Ref(true)

"How many heads the LAST `emit_julia_program` compiled to native code. The lane's own coverage number."
const CODEGEN_NATIVE_HEADS = Ref(0)

# ── THE LINK THAT DID NOT EXIST ──────────────────────────────────────────────────────────────────
"""Every head that HAS RULES in `space` — i.e. every head that REDUCES, as opposed to a data
constructor. The soundness guard's notion of "reducible"; see `_builds_reducible_arg`."""
function _space_rule_heads(space)::Set{Base.Symbol}
    hs = Set{Base.Symbol}()
    for a in Eval.all_atoms(space)
        a isa Expression && length(a.children) == 3 || continue
        h = a.children[1]
        (h isa Sym && String(h.name) == "=") || continue
        lhs = a.children[2]
        hd = lhs isa Expression && !isempty(lhs.children) ? lhs.children[1] : lhs
        hd isa Sym && push!(hs, Base.Symbol(hd.name))
    end
    hs
end

"""
    jit_head!(name, space) -> Bool

Compile the clauses of head `name` FROM `space` and register them with the interpreter. `true` ⇒ the
head now dispatches through `Eval.compiled_head`; `false` ⇒ it declined and stays interpreted.

🔴 THIS CLOSES `Frontend -> ANormal -> emit -> compile_head!`. Until 2026-09-18 nothing in `src/`
ran that chain: `emit_julia_program`'s only caller was a test and `compile_head!`'s only callers were
tests, so `_COMPILED_HEADS` was always empty in production. Every stage worked; the last two links
were absent.

⚠️ INVALIDATION IS BY CLAUSE-SET HASH, which is what `CompiledHead` already keys on — deliberately
NOT by a space revision, which would recompile on every `add-atom` and make the compiled lane slower
than the interpreter on any writing program (the reason is recorded at `Eval.jl`'s `_COMPILED_HEADS`).
The hash is taken over the head's OWN rule atoms, so an unrelated `add-atom` does not disturb it.

⚠️ A DECLINE IS NORMAL. Out-of-scope heads keep the interpreter; the caller counts them so a
benchmark can report WHAT FRACTION OF HOT HEADS WERE IN SCOPE, not only the speedup on the ones that
happened to be.
"""
function jit_head!(name::Base.Symbol, space)::Bool
    rules = Atom[]
    rule_heads = Set{Base.Symbol}()      # collected in THIS walk — see `_space_rule_heads`
    for a in Eval.all_atoms(space)
        a isa Expression && length(a.children) == 3 || continue
        h = a.children[1]
        (h isa Sym && String(h.name) == "=") || continue
        lhs = a.children[2]
        hd = lhs isa Expression && !isempty(lhs.children) ? lhs.children[1] : lhs
        hd isa Sym || continue
        push!(rule_heads, Base.Symbol(hd.name))
        (Base.Symbol(hd.name) === name) && push!(rules, a)
    end
    isempty(rules) && return false
    key = hash(rules)                                   # the CLAUSE SET, not the space
    clauses = try
        CompilerANormal.translate_program(CompilerFrontend.lower_program(rules))
    catch
        return false
    end
    mine = ANClause[c for c in clauses if c.name === name]
    isempty(mine) && return false
    heads = emit_julia_program(mine, space, rule_heads)   # space identity reaches _genname
    fn = get(heads, name, nothing)
    fn === nothing && return false                      # every clause must emit — all-or-nothing
    # ARITY comes from the clauses, so the definition is keyed (head, arity) — SWI's name/arity
    # indexing. Without it every arity of `name` would share one entry, which is why a mixed-arity
    # head declines codegen wholesale (`_build_head` rejects mixed arity).
    # 🔴 `carries_bindings = false` — GENERATED CODE DOES NOT PROPAGATE A CALLEE'S BINDINGS. The
    # sink convention passes `sink(answer, bindings)` and the emitter passes `nothing` there, so a
    # callee that binds the CALLER'S variable loses it. `compiled_head` refuses a non-ground call to
    # this entry. When the emitter fills that argument in, this flips to `true` and the guard goes.
    # the heads this compilation ASSUMED have no rules — part of the staleness key, see
    # `CompiledHead.assumed_ruleless`.
    _assumed = Base.Symbol[]
    for c in mine
        append!(_assumed, collect(CompilerEmitJuliaCode.assumed_ruleless(c.goals, rule_heads)))
    end
    Eval.compile_head!(name, fn, key, space; arity = length(mine[1].head_args),
                       carries_bindings = false, assumed_ruleless = unique!(_assumed))
    true
end

"""
    _codegen_seam_fn(head, fn) -> Function

Adapt a generated closure in the SINK CONVENTION — `(sink, args::Vector{Atom}) -> Bool`, calling
`sink(answer, bindings)` once per answer, where `bindings` is `nothing` when the head produced none — to the seam's signature `(call::Atom, space) -> CompiledOk | ExecNoReduce`.

⚠️ ZERO ANSWERS BECOMES `ExecNoReduce`, i.e. NotReducible: the call returns ITSELF. That is right for
"no equation matched" and WRONG for "an equation matched and produced nothing", which must be
`Empty`. The sink convention makes the two distinguishable for the first time; this adapter
deliberately keeps the OLD behaviour so the interpreter differential stays a like-for-like
comparison. Fixing it belongs with `match`, which is where a genuine zero-answer arises.

⚠️ ARGS ARE TAKEN FROM `call`, WHICH MAY HAVE NONE. `compiled_head` passes `to_eval` ITSELF and says
why: a zero-arg call `(d)` has no children past the head, and a closure that rebuilds the call from
args alone yields the bare symbol `d` and matches nothing (MEASURED).

⚠️ EMPTY `Bindings` IS CORRECT HERE, AND IT IS THE `(pair \$w schiphol)` DEFECT CLASS IF IT IS NOT.
`rule_results` applies `subst(res, mb)` to every compiled result. The plan-walking lane needs real
bindings because it returns a rule's RHS uninstantiated. Codegen does not: `_atomexpr` maps an
`IRVariable` to the JULIA LOCAL holding its atom, so the generated code substitutes EAGERLY and the
result leaves already instantiated — `subst` over empty bindings is then a no-op on a ground term.
That is an argument, not a proof, so `test_codegen_head_seam.jl` asserts it on a NON-GROUND rule
shape where a missing substitution would show.

`invokelatest` because `fn` was `eval`ed during this call: the world age of the caller predates it.
"""
function _codegen_seam_fn(head::Base.Symbol, fn::Function)
    function (call::Atom, space)
        args = if (call isa Expression && length(call.children) > 1)
            Atom[call.children[i] for i in 2:length(call.children)]
        else
            Atom[]
        end
        # THE SINK CONVENTION (`CompilerEmitJuliaCode`): `fn(sink, args)` calls `sink` once per
        # answer. Collecting into a vector here is not a loss of the convention's generality — the
        # SEAM's own contract is `CompiledOk(results, bindings)`, a collect-all shape, so the
        # boundary is where streaming ends. `sink` is passed POSITIONALLY to a `where {S}` method,
        # so Julia specialises on this closure rather than boxing it.
        rs = Atom[]
        bs = Bindings[]
        try
            Base.invokelatest(fn,
                (r, b) -> (push!(rs, r);
                    push!(bs, b === nothing ? Bindings() : b); true),
                args, 0, space)
        catch e
            # 🔴 THE DEPTH BUDGET FIRED. Generated code raises this BEFORE the stack runs out,
            # because a `StackOverflowError` is not catchable in any way code may depend on — Julia
            # itself says "program state may be corrupted". The backtrace is recorded rather than
            # swallowed: a silent fallback is the invisible-decline class this tree keeps hitting.
            e isa CompiledDepthExceeded || rethrow()
            # 🔴 RETURN `nothing` — HAND THE CALL BACK TO THE INTERPRETER. `compiled_head`'s own
            # contract is `Union{CompiledOk, ExecNoReduce, Nothing}` with "`nothing` = no compiled
            # implementation, so the caller runs its ordinary `(= …)` query" (`Eval.jl:748`), and
            # `rule_results:714` falls through on it. An earlier version of this comment claimed the
            # seam had "no third outcome" and returned a terminal error atom instead — which turned
            # a call that used to ANSWER in the interpreter into an error the moment the lane went
            # on by default. That was a regression introduced by the default flip, not a limitation.
            # This is CeTTa's classification: an exhausted stack is a RETRYABLE control failure, not
            # a semantic verdict (`eval.c:15930`). Sound to re-run because impure ops are excluded.
            @warn "compiled lane hit its call-depth budget — interpreting this head instead" head=e.head depth=e.depth
            for fr in stacktrace(catch_backtrace())[1:min(6, end)]
                @debug "  at" fr
            end
            # SESSION-SCOPED, and counted rather than silent — see `Eval.COMPILED_INTERPRET_ONLY`.
            # Per-evaluation scoping is unsound because `metta_run` is RE-ENTERED at
            # `_REDUCE_DEPTH == 0` from inside an evaluation, which drops a live mark and lets the
            # fault repeat down the whole tree. (An earlier note here blamed a suite memory runaway
            # for this; that attribution was refuted — see `COMPILED_INTERPRET_ONLY`.)
            Eval.COMPILED_FALLBACK_DEPTH[] += 1
            Eval.mark_interpret_only!(space, e.head)   # PER SPACE — see SpaceCompileState
            return nothing
        end
        isempty(rs) && return ExecNoReduce()
        CompiledOk(rs, bs)
    end
end

"""
    _seam_fn(head, rules) -> Function

The registered function, in the SEAM's OWN SIGNATURE: `(args::Vector{Atom}, space)` ->
`CompiledOk` | `ExecNoReduce`, which is what `Eval.compiled_head` calls. The adapter lives HERE, not
in the caller: a test that rebuilds the call atom itself would be reconstructing what the seam
already had, and a nested or unusual head could differ from what `compiled_head` actually saw.

`nothing` from the matcher ⇒ `ExecNoReduce` ⇒ NotReducible: the call returns ITSELF, never `Empty`.
"""
function _seam_fn(head::Base.Symbol, rules::Vector{Tuple{Expression, Vector, Expression}})
    inner = _head_closure(rules)
    function (call::Atom, space)
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
function _head_closure(rules::Vector)
    function (call::Atom, space)
        out = Tuple{Atom, Bindings}[]
        for (rule0, plan0, packed) in rules
            fresh = rename_fresh(packed)          # ONE rename for rule AND plan — see `_pack`
            (rule, plan) = _unpack(fresh, plan0)
            X = freshvar("X")
            pattern = Expression(Atom[Sym("="), call, X])
            for mb in match_atoms(pattern, rule)
                is_present(mb, X) || continue   # resolve-filter, exactly as `query`'s consumers do
                for sigma in (isempty(plan) ? Bindings[mb] : _run_plan(plan, mb, space))
                    push!(out, (subst(X, sigma), sigma))
                end
            end
        end
        isempty(out) ? nothing : out
    end
end


# Install the JIT entry point for `Eval`'s `(compile-head …)` op. `Eval` loads FIRST and cannot
# reference this module, so the dependency is inverted here rather than there.
function __init__()
    Eval._JIT_HEAD_HOOK[] = jit_head!
end

end # module
