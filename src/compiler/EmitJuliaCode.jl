# EmitJuliaCode.jl — stage 4d: A-normal clauses → GENERATED JULIA CODE.
#
# ─── WHY THIS EXISTS AND `EmitJulia` DOES NOT REPLACE IT ─────────────────────────────────────────
# `EmitJulia`'s `_run_plan` WALKS A PLAN OF TUPLES calling `match_atoms`/`subst`/`merge_bindings` at
# runtime — an INTERPRETER FOR A-NORMAL FORM, the same dynamic work in the same order one level up.
# `[[reference_jetta_aot_jvm_compiler]]` names the standard it fails: "compiled bodies do NOT bounce
# back through an interpreter" (the metta-wam trap).
#
# THIS stage builds a Julia `Expr` per clause, `eval`s it ONCE per head at compile time, and calls it
# through `invokelatest`. `$x` becomes a JULIA LOCAL; `(+ $x 1)` becomes `Grounded(x.value + 1)` —
# raw machine arithmetic, no `execute` dispatch, no Atom walk, no binding merge.
# ⚠️ World-age: paid ONCE per head at registration, which is why the unit must be a CLOSURE and not a
# method. "Julia cannot add code to a running program" is FALSE at closure granularity.
#
# ─── SCOPE, DELIBERATELY NARROW ──────────────────────────────────────────────────────────────────
# Clauses whose head args are ALL DISTINCT VARIABLES (so the head match is positional binding, not
# unification), whose goals are GCall to a mapped arithmetic/comparison op, GUnify of a variable, or
# GBranch. That is exactly the shape of `fib` — the workload the >=10x decision bar is measured on.
# Everything else DECLINES and falls back to `EmitJulia`/the interpreter.
module CompilerEmitJuliaCode

using ..StandardMeTTa
import ..CompilerANormal: Goal, GUnify, GCall, GBranch, GDisj, GFindall, GResidual, ANClause
import ..CompilerIR: IRAtom, IRVariable, IRSymbol, IRGrounded, IRExpression
# Imported EXPLICITLY and located first — `Operation`/`ExecOk` are used inside the GENERATED code,
# so a missing import fails at codegen time, not at load. (First run: UndefVarError.)
import ..Eval: TOKEN_REGISTRY, Operation, ExecOk, ExecNoReduce

export codegen_clause, codegen_head, head_compilable

# 🔴 NO OP TABLE HERE, DELIBERATELY. A first draft of this file defined
# `_J_ARITH = Dict(:+ => :+, …)` and generated `Grounded(x.value + 1)` — reinventing arithmetic the
# tree already grounds, AND GETTING IT WRONG. `Eval._num_binop(name, f)` wraps the raw Julia `f` in a
# closure that ALSO:
#   * propagates WFS bottom  — `propagated_undefined(...)` — "⊥ is absorbed by strict ops"; skipping
#     it is a recorded defect class that "truncated rule bodies and framed the SLG engine";
#   * returns `ExecNoReduce()` when an operand is not a grounded Number, so `(+ foo 1)` is
#     NotReducible rather than a Julia MethodError.
# Regenerating `x.value + 1` drops both. ⇒ CODEGEN SPLICES THE EXISTING OPERATION'S FUNCTION AND
# CALLS IT DIRECTLY.
#
# The speedup was never in reimplementing `+`. It is in removing the INTERPRETIVE MACHINERY AROUND
# the call — `metta_instr` dispatch, the frame stack machine, binding merges, and an equation lookup
# per call. A direct `op_fn(args)` keeps every semantic the grounded op carries and skips all of that.

_local(v::IRVariable) = Base.Symbol("v_", v.name)

"""
IR operand -> a Julia expression producing an ATOM (for results that leave the clause).

🔴 A STRUCTURED OPERAND WAS THE SINGLE LARGEST DECLINE CAUSE, AND IT WAS INVISIBLE. Returning
`nothing` for `IRExpression` meant any clause whose OUTPUT or whose goal ARGUMENTS were a built term
— `(= (f \$x) (Cons \$x nil))`, the ordinary shape of anything constructing data — declined the
head. MEASURED across `Core/lib` 2026-09-25: it blocked 435 of 768 heads, more than any other cause,
and a first-match classifier had filed all of them under "other" so it never appeared in a priority
list. Building the `Expression` is recursive and the head is its FIRST CHILD, which is why
`IRExpression` carries `head` as its own field rather than as `args[1]` (see the struct's docstring).
"""
function _atomexpr(a::IRAtom, vars::Set{Base.Symbol})
    a isa IRVariable && return _local(a)
    a isa IRGrounded && return :(Grounded($(a.value)))
    a isa IRSymbol   && return :(Sym($(String(a.name))))
    if a isa IRExpression
        h = _atomexpr(a.head, vars); h === nothing && return nothing
        kids = Any[]
        for x in a.args
            v = _atomexpr(x, vars); v === nothing && return nothing
            push!(kids, v)
        end
        return :(Expression(Atom[$h, $(kids...)]))
    end
    nothing
end

# ─── THE CALLING CONVENTION FOR COMPILED HEADS ───────────────────────────────────────────────────
# 🔴 THE OLD SHAPE COULD NOT EXPRESS MeTTa. `codegen_head` used to emit `Atom[body₁, …, body_N]` — a
# Julia vector literal, one element per clause, LENGTH FIXED AT CODEGEN TIME. A clause could not
# answer zero times and could not answer twice, so `superpose` and EVERY MULTI-EQUATION FUNCTION
# declined, and the interpreter stayed the only lane that runs.
#
# THE CONVENTION. A compiled head is `f(sink, args::Vector{Atom})::Bool`. It calls
# `sink(answer, bindings)` ONCE PER ANSWER: zero calls = no answer, N calls = N answers, so
# MULTIPLICITY IS PRESERVED BY CONSTRUCTION and order is left unspecified. `sink` returns `false` to
# ask the producer to stop, and `f` returns `false` iff it stopped early — that is what `once` needs.
# NO CHOICE POINTS, NO TRAIL: the decision against Prolog backtracking machinery holds.
#
# 🔴 WHY `sink` TAKES BINDINGS, THOUGH NOTHING PRODUCES THEM YET. An argument may hold an UNBOUND
# VARIABLE, and a binding the callee makes MUST REACH THE CALLER. ORACLE, 2026-09-25, on
# `(= (p (S $x)) (got $x))` then `!(let $r (p $y) ($y $r))`:
#     hyperon  [((S $x#38) (got $x#38))]      CeTTa  [((S $x#1) (got $x#1))]
#     PeTTa    ((S $_0) (got $_0))            Core   ((S $x#19872) (got $x#19872))
# `$y` took the value `(S $x)` and the SAME variable appears in both positions. Today every compiled
# head binds its arguments POSITIONALLY (head args must be distinct variables), so no binding is ever
# produced and the generators pass `nothing`. The parameter is here NOW because head-argument
# PATTERNS — the next increment — is exactly what starts producing them, and widening the signature
# afterwards would mean rewriting every generator and every call site built on it. `nothing` means
# "no bindings" and costs no allocation on the deterministic path.
#
# ⚠️ `sink` IS A TYPE PARAMETER, NOT A `Function` FIELD. `f(sink::S, …) where {S}` makes Julia
# specialise and inline the call. Boxing it as `::Function` costs an allocation and a dynamic
# dispatch PER ANSWER — `[[reference_rust_closures_are_free_julia_closures_allocate]]`.
#
# ─── NONDETERMINISM IS NESTED `for` LOOPS, NOT CONTINUATIONS ────────────────────────────────────
# A goal that can answer N times becomes a loop over its answers, with the REST OF THE CLAUSE
# generated inside it. Zero answers = the body never runs; N answers = N passes; early stop = a
# `return false` out of every enclosing loop. Julia's own loops supply the iteration, so there are no
# closures per choice point and STACK DEPTH DOES NOT GROW WITH THE ANSWER COUNT — it grows only with
# CHAINED nondeterminism, which is the cost the design note predicted and a far smaller one.
#
# ─── WHAT A GROUNDED CALL CAN ANSWER, MEASURED RATHER THAN ASSUMED ──────────────────────────────
# Every one of the 80 in-scope `Operation`s in `TOKEN_REGISTRY` was CALLED over 10 argument shapes
# and its result count recorded (2026-09-25). EXACTLY ONE can answer with ≠1 result:
#
#     superpose   [3]
#
# `match`, `collapse`, `case`, `get-atoms`, `get-type` are `SpaceOp`s, which `_gen_goal` has always
# excluded, so they never reach here. `_NONDET_OPS` below records that measurement, and
# `test_codegen_multi_result.jl` RE-RUNS THE CENSUS and fails naming any op outside the set that
# answers ≠1 — `[[feedback_enforcement_works_prose_memory_does_not]]`, the classification is a GATE
# rather than a comment that rots. It is NOT an op table in the sense this file forbids above: it
# says nothing about what an op COMPUTES, only whether it is deterministic.
const _NONDET_OPS = Set(["superpose"])

# ─── `NotReducible` IS AN ANSWER, AND GETTING THAT WRONG LOSES ONE ──────────────────────────────
# 🔴 MEASURED by this file's own differential, on its first run. `(= (g $x) (+ $x 1))` applied to a
# SYMBOL: `+` answers `ExecNoReduce`, and in MeTTa a term that cannot reduce IS the answer — the
# interpreter returns `(+ foo 1)`. Treating `ExecNoReduce` as "this clause has no answer" silently
# dropped it:
#     interpreter ["(+ foo 1)", "tagged"]        compiled ["tagged"]
# So a declining grounded call yields the RESIDUAL TERM `(op args…)`, rebuilt from the argument
# atoms the call was made with. (The shape this replaced was worse still: it executed `return
# nothing` from a function the seam annotated `::Vector{Atom}`, i.e. a `TypeError` instead of an
# answer.)

"Every goal reachable in this clause, flattened — `GBranch` arms included."
function _all_goals(gs::Vector{Goal})
    out = Goal[]
    for g in gs
        push!(out, g)
        if g isa GBranch
            append!(out, _all_goals(g.cond)); append!(out, _all_goals(g.then))
            append!(out, _all_goals(g.els))
        elseif g isa GDisj
            for br in g.branches; append!(out, _all_goals(br)); end
        elseif g isa GFindall
            append!(out, _all_goals(g.body))
        end
    end
    out
end

"The generated entry name for a head. DETERMINISTIC, so a caller can name a callee not yet built."
_genname(sym::Base.Symbol) = Base.Symbol("_gen_", sym, "_", string(hash(sym), base=16)[1:6])

"A call to another MeTTa head rather than to a grounded op or to this clause's own head."
function _is_user_call(g::Goal, selfname::Base.Symbol)
    g isa GCall || return false
    g.head === selfname && return false
    op = get(TOKEN_REGISTRY, String(g.head), nothing)
    !(op isa Grounded && op.value isa Operation)
end

"""
Can this clause answer other than exactly once? Then it has no deterministic entry and must take the
loop path. Three sources, and MISSING THE FIRST IS WHAT MADE `superpose` DECLINE: a `GDisj` or
`GFindall` NODE is nondeterministic IN ITSELF, and `superpose`'s branches contain no call to
`superpose` — A-normal has already turned it into a disjunction of plain bindings. Checking only for
a nondeterministic OP therefore answered `false`, routed the head down the DETERMINISTIC path, whose
generator has no `GDisj` case, and the head declined with the loop path never consulted.

A CALL TO ANOTHER HEAD is the third: the callee may answer zero times or many, so the caller cannot
be deterministic. A call to THIS head is excluded — a one-clause head that only recurses into itself
is deterministic by induction, which is what keeps `fib` on the fast path.
"""
_is_nondet(gs::Vector{Goal}, selfname::Base.Symbol) =
    any(g -> g isa GDisj || g isa GFindall ||
             (g isa GCall && String(g.head) in _NONDET_OPS) ||
             _is_user_call(g, selfname),
        _all_goals(gs))

# ⚠️ THE REST OF THE CLAUSE IS GENERATED INSIDE EACH ARM OR BRANCH, so it is DUPLICATED per arm and
# nesting MULTIPLIES. The budget is therefore the duplication FACTOR, not a node count: a `GBranch`
# doubles it, a `GDisj` multiplies by its branch count, and a clause that would exceed the cap
# declines rather than blowing up at `eval` time. `fib`, the workload this file is measured on, has
# a factor of 2.
const _MAX_DUP = 32

"""
Compile `cond`-position goals to a Julia BOOLEAN. A `GUnify` here is a TEST — `\$__t1 = True` asks
whether `\$__t1` IS `True`, it does not bind. Only variable-vs-constant tests are in scope; anything
else declines rather than guessing.
"""
function _gen_test(cond::Vector{Goal}, vars::Set{Base.Symbol})
    isempty(cond) && return :(true)
    ex = nothing
    for c in cond
        c isa GUnify || return nothing
        l = _atomexpr(c.lhs, vars); r = _atomexpr(c.rhs, vars)
        (l === nothing || r === nothing) && return nothing
        t = :($l == $r)
        ex = ex === nothing ? t : :($ex && $t)
    end
    ex
end

"""
The grounded `Operation` behind a `GCall`, its argument expressions, and a fresh symbol pair — or
`nothing` if the call is out of scope. Shared by both generators so the RESIDUAL TERM and the
argument vector are built identically in each.
"""
function _gcall_parts(g::GCall, vars::Set{Base.Symbol})
    (g.out isa IRVariable) || return nothing
    op = get(TOKEN_REGISTRY, String(g.head), nothing)
    (op isa Grounded && op.value isa Operation) || return nothing   # not grounded ⇒ decline
    as = Any[]
    for a in g.args
        v = _atomexpr(a, vars); v === nothing && return nothing
        push!(as, v)
    end
    n = string(g.head, "_", length(vars))
    (op.value.fn, as, Base.Symbol("_ar_", n), Base.Symbol("_rs_", n), String(g.head))
end

# ═══ GENERATOR 1: THE NONDETERMINISTIC FORM ══════════════════════════════════════════════════════
# Goals become nested loops; `out` is handed to `_sink` at the innermost point of every path.

"""
    _gen_seq(goals, k, vars, out_ir, nbranch) -> Union{Expr, Nothing}

Generate goals `k..end` with the clause's answer delivered to `_sink` inside every innermost scope.
Returns `nothing` if anything is out of scope. `vars` is MUTATED along a path and COPIED into each
`GBranch` arm, because the arms bind different names.
"""
function _gen_seq(goals::Vector{Goal}, k::Int, vars::Set{Base.Symbol}, out_ir::IRAtom, dup::Int,
                  selfname::Base.Symbol, fname::Base.Symbol, compilable::Set{Base.Symbol})
    if k > length(goals)
        ox = _atomexpr(out_ir, vars); ox === nothing && return nothing
        # `||` and not `&&`: a sink answering `false` means STOP, and it must propagate out of every
        # enclosing loop rather than merely ending this iteration.
        return Expr(:(||), Expr(:(::), Expr(:call, :_sink, ox, :nothing), :Bool), Expr(:return, false))
    end
    g = goals[k]
    if g isa GUnify
        (g.lhs isa IRVariable) || return nothing
        r = _atomexpr(g.rhs, vars); r === nothing && return nothing
        push!(vars, (g.lhs::IRVariable).name)
        rest = _gen_seq(goals, k + 1, vars, out_ir, dup, selfname, fname, compilable); rest === nothing && return nothing
        return Expr(:block, Expr(:(=), _local(g.lhs), r), rest)
    elseif g isa GCall
        p = _gcall_parts(g, vars)
        if p === nothing
            # 🔴 A CALL TO ANOTHER COMPILED HEAD. This is what the sink convention was FOR: the
            # callee answers zero-to-N times, and "the rest of this clause" is handed to it AS the
            # sink, so each of its answers continues the caller. No collect, no intermediate vector.
            # `return false` inside the closure returns from the CLOSURE, which is exactly the stop
            # signal the callee reads; the callee then returns `false` and the `||` propagates it out
            # of the caller too, so an early stop crosses call boundaries intact.
            # A SELF-CALL LANDS HERE TOO in the loop path, targeting the head's own ENTRY (`fname`)
            # rather than a per-clause function — which is why a multi-clause head may now recurse.
            (g.out isa IRVariable) || return nothing
            callee = g.head === selfname ? fname :
                     (g.head in compilable ? _genname(g.head) : return nothing)
            as = Any[]
            for a in g.args
                v = _atomexpr(a, vars); v === nothing && return nothing
                push!(as, v)
            end
            push!(vars, (g.out::IRVariable).name)
            rest = _gen_seq(goals, k + 1, vars, out_ir, dup, selfname, fname, compilable)
            rest === nothing && return nothing
            lv = _local(g.out)
            # ⚠️ `_b` is the callee's bindings and is DISCARDED here. Sound only while head args are
            # bound POSITIONALLY, so no callee can produce one. Head-argument patterns must merge it.
            closure = Expr(:->, Expr(:tuple, :_r, :_b),
                           Expr(:block, Expr(:(=), lv, :_r), rest, true))
            return Expr(:(||), Expr(:call, callee, closure, Expr(:ref, :Atom, as...)),
                        Expr(:return, false))
        end
        (fn, as, arv, rsv, opname) = p
        push!(vars, (g.out::IRVariable).name)
        rest = _gen_seq(goals, k + 1, vars, out_ir, dup, selfname, fname, compilable); rest === nothing && return nothing
        lv = _local(g.out)
        return quote
            $arv = Atom[$(as...)]
            local $rsv::Vector{Atom}
            let _r = $(fn)($arv)
                $rsv = _r isa ExecOk        ? _r.results :
                       _r isa ExecNoReduce  ? Atom[Expression(Atom[Sym($opname), $arv...])] :
                                              Atom[]
            end
            for $lv in $rsv
                $rest
            end
        end
    elseif g isa GBranch
        (g.out isa IRVariable) || return nothing
        dup * 2 > _MAX_DUP && return nothing
        # 🔴 THE SEMANTICS, read from `EmitIL._instr(::GBranch)` after guessing them wrong:
        #   "`cond` carries the REAL test (a GUnify). Its success continuation is the then-arm and
        #    its FAILURE continuation is the else-arm."
        # So a `GUnify` means TWO DIFFERENT THINGS BY POSITION: a TEST inside `cond`, an ASSIGNMENT
        # inside an arm. Treating both as assignments made the then-arm always win — `fib(16)`
        # returned 16, instantly, which timing alone would have reported as a 4,000,000x speedup.
        test = _gen_test(g.cond, vars); test === nothing && return nothing
        rest = goals[k+1:end]
        tb = _gen_seq(vcat(g.then, rest), 1, copy(vars), out_ir, dup * 2, selfname, fname, compilable)
        tb === nothing && return nothing
        # An EMPTY `els` means "no further arm": this PATH yields nothing, which in the sink
        # convention is simply not calling `_sink` — no early return, the other clauses still run.
        eb = isempty(g.els) ? :(nothing) :
             _gen_seq(vcat(g.els, rest), 1, copy(vars), out_ir, dup * 2, selfname, fname, compilable)
        eb === nothing && return nothing
        return Expr(:if, test, tb, eb)
    elseif g isa GDisj
        # 🔴 `superpose` LOWERS TO THIS, NOT TO A GROUNDED CALL. A census of the registry found
        # `superpose` to be the one in-scope `Operation` answering with !=1 result, but A-normal
        # never routes it through `GCall`: `build_superpose_branches` turns it into a DISJUNCTION of
        # goal lists all producing `out` (PeTTa translator.pl:110-112). `EmitJulia.jl` declines this
        # node as "milestone 2" and `_gen_goal` never matched it, which is why every `superpose`
        # declined. In the sink convention it is simply each branch in turn, with the rest of the
        # clause inside: a branch that answers nothing calls no sink, and a `false` from one
        # propagates out of the whole disjunction.
        (g.out isa IRVariable) || return nothing
        isempty(g.branches) && return :(nothing)          # no branches ⇒ no answers, not an error
        dup * length(g.branches) > _MAX_DUP && return nothing
        rest = goals[k+1:end]
        blk = Expr(:block)
        for br in g.branches
            bb = _gen_seq(vcat(br, rest), 1, copy(vars), out_ir, dup * length(g.branches),
                          selfname, fname, compilable)
            bb === nothing && return nothing
            push!(blk.args, bb)
        end
        return blk
    end
    nothing
end

# ═══ GENERATOR 2: THE DETERMINISTIC FAST PATH ════════════════════════════════════════════════════
# A head with ONE clause that calls no `_NONDET_OPS` op answers at most once, so it also gets
# `f_det(args)::Union{Nothing,Atom}` — straight-line code, no sink, no loop. SELF-RECURSION CALLS
# `f_det` DIRECTLY, which is why `fib` never allocates a sink in its hot loop and the >=10x
# measurement is not at risk. (It is cheaper than the old shape, which allocated a `Vector{Atom}`
# per recursive return and then checked its length.)

function _gen_det(g::Goal, vars::Set{Base.Symbol}, selfname::Base.Symbol, dname::Base.Symbol)
    if g isa GUnify
        (g.lhs isa IRVariable) || return nothing
        r = _atomexpr(g.rhs, vars); r === nothing && return nothing
        push!(vars, (g.lhs::IRVariable).name)
        return :($(_local(g.lhs)) = $r)             # a `let` binding becomes a Julia assignment
    elseif g isa GCall
        (g.out isa IRVariable) || return nothing
        if g.head === selfname
            as = Any[]
            for a in g.args
                v = _atomexpr(a, vars); v === nothing && return nothing
                push!(as, v)
            end
            push!(vars, (g.out::IRVariable).name)
            r = Base.Symbol("r_", (g.out::IRVariable).name)
            # 🔴 ONE JULIA CALL. No seam, no interpreter, no equation lookup, no sink.
            return quote
                $r = $dname(Atom[$(as...)])
                $r === nothing && return nothing
                $(_local(g.out)) = $r::Atom
            end
        end
        p = _gcall_parts(g, vars); p === nothing && return nothing
        (fn, as, arv, rsv, opname) = p
        push!(vars, (g.out::IRVariable).name)
        lv = _local(g.out)
        # 🔴 THE COMPILED CALL: the EXISTING grounded Operation's own function, spliced as a constant
        # and invoked directly. Every semantic the op carries (⊥ propagation, NotReducible on
        # non-numbers) is preserved because it IS the op — see the NO-OP-TABLE note above.
        return quote
            $arv = Atom[$(as...)]
            $rsv = $(fn)($arv)
            if $rsv isa ExecOk
                length($rsv.results) == 1 || return nothing   # excluded statically by _NONDET_OPS
                $lv = $rsv.results[1]
            elseif $rsv isa ExecNoReduce
                $lv = Expression(Atom[Sym($opname), $arv...])  # NotReducible IS the answer
            else
                return nothing
            end
        end
    elseif g isa GBranch
        (g.out isa IRVariable) || return nothing
        test = _gen_test(g.cond, vars); test === nothing && return nothing
        tv = copy(vars); ev = copy(vars)
        ts = Expr[]
        for t in g.then
            x = _gen_det(t, tv, selfname, dname); x === nothing && return nothing
            push!(ts, x)
        end
        es = Expr[]
        for e in g.els
            x = _gen_det(e, ev, selfname, dname); x === nothing && return nothing
            push!(es, x)
        end
        push!(vars, (g.out::IRVariable).name)
        o = _local(g.out)
        elsblk = isempty(g.els) ? Expr(:return, :nothing) : Expr(:block, es..., o)
        return Expr(:(=), o, Expr(:if, test, Expr(:block, ts..., o), elsblk))
    end
    nothing
end

"""
    codegen_clause(cl, selfname, dname) -> Union{Expr, Nothing}

The DETERMINISTIC body for one clause, or `nothing` if it is outside scope. The block's last element
is the clause's single answer; a runtime decline is `return nothing`. Retained under its original
name because it is the unit the deterministic path is built from and tested through.
"""
function codegen_clause(cl::ANClause, selfname::Base.Symbol=Base.Symbol(""),
                        dname::Base.Symbol=Base.Symbol(""))
    cl.nested_head && return nothing
    _is_nondet(cl.goals, selfname) && return nothing
    vars = Set{Base.Symbol}()
    for a in cl.head_args
        a isa IRVariable || return nothing          # positional binding only — no unification here
        push!(vars, a.name)
    end
    stmts = Expr[]
    for g in cl.goals
        st = _gen_det(g, vars, selfname, dname); st === nothing && return nothing
        push!(stmts, st)
    end
    outx = _atomexpr(cl.out, vars); outx === nothing && return nothing
    Expr(:block, stmts..., outx)
end

"The NONDETERMINISTIC body for one clause: `_sink` is called once per answer, then `true`."
function _codegen_clause_sink(cl::ANClause, selfname::Base.Symbol, fname::Base.Symbol,
                              compilable::Set{Base.Symbol})
    cl.nested_head && return nothing
    vars = Set{Base.Symbol}()
    for a in cl.head_args
        a isa IRVariable || return nothing
        push!(vars, a.name)
    end
    seq = _gen_seq(cl.goals, 1, vars, cl.out, 1, selfname, fname, compilable)
    seq === nothing && return nothing
    Expr(:block, seq, true)
end

# `f(sink::S, _a::Vector{Atom}) where {S}` as an `Expr`, with `body` spliced in.
_sinkfn(name::Base.Symbol, body::Expr) =
    Expr(:function,
         Expr(:where, Expr(:call, name, Expr(:(::), :_sink, :S), :(_a::Vector{Atom})), :S),
         body)

_bindargs(head_args) = [Expr(:(=), _local(a::IRVariable), :(_a[$i])) for (i, a) in enumerate(head_args)]

"""
    _build_head(name, clauses, compilable) -> Union{Vector{Expr}, Nothing}

Build the functions for a head WITHOUT evaluating them, or `nothing` if it is out of scope. The last
element is the entry.

🔴 BUILDING IS SEPARATE FROM `eval` BECAUSE CALLS BETWEEN HEADS NEED A FIXPOINT. A head compiles only
if every head it calls also compiles, and that is not knowable one head at a time: `emit_julia_program`
starts with all heads as candidates and drops them until the set is stable. A build that evaluated as
it went would leave half-registered functions behind on every dropped candidate.
"""
function _build_head(name::Base.Symbol, clauses::Vector{ANClause}, compilable::Set{Base.Symbol})
    isempty(clauses) && return nothing
    fname = _genname(name)
    arity = length(clauses[1].head_args)
    for cl in clauses
        length(cl.head_args) == arity || return nothing     # mixed arity ⇒ out of scope
    end

    if length(clauses) == 1 && !_is_nondet(clauses[1].goals, name)
        dname = Base.Symbol(fname, "_det")
        b = codegen_clause(clauses[1], name, dname)
        b === nothing && return nothing
        det = Expr(:function, Expr(:call, dname, :(_a::Vector{Atom})),
                   Expr(:block, _bindargs(clauses[1].head_args)..., b))
        wrap = Expr(:block,
            Expr(:(=), :_r, Expr(:call, dname, :_a)),
            Expr(:if, Expr(:call, :(===), :_r, :nothing),
                 true,
                 Expr(:(::), Expr(:call, :_sink, :_r, :nothing), :Bool)))
        return Expr[det, _sinkfn(fname, wrap)]
    end

    out = Expr[]
    parts = Base.Symbol[]
    for (i, cl) in enumerate(clauses)
        b = _codegen_clause_sink(cl, name, fname, compilable)
        b === nothing && return nothing
        cn = Base.Symbol(fname, "_c", i)
        push!(out, _sinkfn(cn, Expr(:block, _bindargs(cl.head_args)..., b)))
        push!(parts, cn)
    end
    comb = Expr(:block)
    for cn in parts
        push!(comb.args, Expr(:(||), Expr(:call, cn, :_sink, :_a), Expr(:return, false)))
    end
    push!(comb.args, true)
    push!(out, _sinkfn(fname, comb))
    out
end

"True if this head would compile given `compilable` as the set of heads that do. No `eval`."
head_compilable(name::Base.Symbol, clauses::Vector{ANClause}, compilable::Set{Base.Symbol}) =
    _build_head(name, clauses, compilable) !== nothing

"""
    codegen_head(name, clauses, compilable) -> Union{Function, Nothing}

`eval` the compiled entry for a head, in the SINK CONVENTION: `f(sink, args::Vector{Atom})::Bool`,
calling `sink(answer, bindings)` once per answer and returning `false` iff a sink asked it to stop.
`bindings` is `nothing` while head arguments are bound positionally — see the header for the oracle
that says the parameter must exist before head patterns do.

`compilable` is the set of OTHER heads that will also be registered; a call to a head outside it
declines, because the generated code names the callee's entry directly. Callers that compile a head
in isolation may pass the default and get no cross-head calls.

All-or-nothing per head: any clause outside scope disqualifies the head, because the seam SHADOWS it
and a partial registration loses answers.

A head with ONE clause that is deterministic throughout additionally gets `f_det(args)` — the
deterministic fast path, which self-recursion calls directly, and which is why `fib` allocates no
sink in its hot loop. A MULTI-CLAUSE head may now recurse: in the loop path a self-call is an
ordinary call to the head's own ENTRY, which answers zero-to-N times through the sink, so the answer
that the old guard was protecting can no longer be dropped.
"""
function codegen_head(name::Base.Symbol, clauses::Vector{ANClause},
                      compilable::Set{Base.Symbol}=Set{Base.Symbol}())
    fns = _build_head(name, clauses, compilable)
    fns === nothing && return nothing
    local last
    for f in fns
        last = Base.eval(@__MODULE__, f)     # world-age paid ONCE per head, at registration
    end
    last
end

end # module
