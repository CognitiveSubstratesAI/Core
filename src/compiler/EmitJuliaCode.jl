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

export codegen_clause, codegen_head

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

"IR operand -> a Julia expression producing an ATOM (for results that leave the clause)."
function _atomexpr(a::IRAtom, vars::Set{Base.Symbol})
    a isa IRVariable && return _local(a)
    a isa IRGrounded && return :(Grounded($(a.value)))
    a isa IRSymbol   && return :(Sym($(String(a.name))))
    nothing
end

"""
    codegen_clause(cl) -> Union{Expr, Nothing}

Build the Julia body for ONE clause, or `nothing` if it is outside scope. The generated body assumes
head args are already bound to locals `v_<name>`; `codegen_head` emits that binding.
"""
function codegen_clause(cl::ANClause, selfname::Base.Symbol=Base.Symbol(""), fname::Base.Symbol=Base.Symbol(""))
    cl.nested_head && return nothing
    vars = Set{Base.Symbol}()
    for a in cl.head_args
        a isa IRVariable || return nothing          # positional binding only — no unification here
        push!(vars, a.name)
    end
    stmts = Expr[]
    for g in cl.goals
        st = _gen_goal(g, vars, selfname, fname)
        st === nothing && return nothing
        push!(stmts, st)
    end
    outx = _atomexpr(cl.out, vars)
    outx === nothing && return nothing
    Expr(:block, stmts..., outx)
end

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

function _gen_goal(g::Goal, vars::Set{Base.Symbol}, selfname::Base.Symbol, fname::Base.Symbol)
    if g isa GUnify
        (g.lhs isa IRVariable) || return nothing
        r = _atomexpr(g.rhs, vars); r === nothing && return nothing
        push!(vars, (g.lhs::IRVariable).name)
        return :($(_local(g.lhs)) = $r)             # a `let` binding becomes a Julia assignment
    elseif g isa GCall
        (g.out isa IRVariable) || return nothing
        if g.head === selfname
            # 🔴 SELF-RECURSION IS A DIRECT JULIA CALL — the whole point. `fib` calling `fib` does
            # NOT re-enter the seam, the interpreter, or an equation lookup; it is one Julia call
            # into the same generated function. This is what a >=10x result would come from.
            as = Any[]
            for a in g.args
                v = _atomexpr(a, vars); v === nothing && return nothing
                push!(as, v)
            end
            push!(vars, (g.out::IRVariable).name)
            r = Base.Symbol("r_", (g.out::IRVariable).name)
            return quote
                $r = $fname(Atom[$(as...)])
                length($r) == 1 || return Atom[]
                $(_local(g.out)) = $r[1]
            end
        end
        op = get(TOKEN_REGISTRY, String(g.head), nothing)
        (op isa Grounded && op.value isa Operation) || return nothing   # not grounded ⇒ decline
        as = Any[]
        for a in g.args
            v = _atomexpr(a, vars); v === nothing && return nothing
            push!(as, v)
        end
        push!(vars, (g.out::IRVariable).name)
        r = Base.Symbol("r_", (g.out::IRVariable).name)
        # 🔴 THE COMPILED CALL: the EXISTING grounded Operation's own function, spliced as a constant
        # and invoked directly. No `metta_instr`, no frame machine, no equation lookup, no binding
        # merge — and every semantic the op carries (⊥ propagation, NotReducible on non-numbers) is
        # preserved because it IS the op.
        return quote
            $r = $(op.value.fn)(Atom[$(as...)])
            $r isa ExecOk && length($r.results) == 1 || return nothing
            $(_local(g.out)) = $r.results[1]
        end
    elseif g isa GBranch
        (g.out isa IRVariable) || return nothing
        # 🔴 THE SEMANTICS, read from `EmitIL._instr(::GBranch)` after guessing them wrong:
        #   "`cond` carries the REAL test (a GUnify). Its success continuation is the then-arm and
        #    its FAILURE continuation is the else-arm."
        # So `condval` is the PATTERN matched against (`True`, then `False`), NOT the scrutinee, and
        # a `GUnify` means TWO DIFFERENT THINGS BY POSITION: a TEST inside `cond`, an ASSIGNMENT
        # inside an arm. Treating both as assignments made the then-arm always win — `fib(16)`
        # returned 16, instantly, which timing alone would have reported as a 4,000,000x speedup.
        test = _gen_test(g.cond, vars)
        test === nothing && return nothing
        tv = copy(vars); ev = copy(vars)
        ts = Expr[]
        for t in g.then
            x = _gen_goal(t, tv, selfname, fname); x === nothing && return nothing
            push!(ts, x)
        end
        es = Expr[]
        for e in g.els
            x = _gen_goal(e, ev, selfname, fname); x === nothing && return nothing
            push!(es, x)
        end
        push!(vars, (g.out::IRVariable).name)
        o = _local(g.out)
        # An EMPTY `els` means "no further arm" -> Empty, per EmitIL's note. Represent that as an
        # early return of no answers rather than a bound value.
        elsblk = isempty(g.els) ? :(return Atom[]) : Expr(:block, es..., o)
        return Expr(:(=), o, Expr(:if, test, Expr(:block, ts..., o), elsblk))
    end
    nothing
end

"""
    codegen_head(name, clauses) -> Union{Function, Nothing}

`eval` ONE closure for a head over all its clauses. All-or-nothing: any clause outside scope
disqualifies the head, because the seam SHADOWS it and a partial registration loses answers.
"""
function codegen_head(name::Base.Symbol, clauses::Vector{ANClause})
    fname = Base.Symbol("_gen_", name, "_", string(hash(name), base=16)[1:6])
    bodies = Expr[]
    arity = -1
    for cl in clauses
        b = codegen_clause(cl, name, fname); b === nothing && return nothing
        arity < 0 && (arity = length(cl.head_args))
        length(cl.head_args) == arity || return nothing     # mixed arity ⇒ out of scope
        args = [_local(a::IRVariable) for a in cl.head_args]
        push!(bodies, Expr(:block, [:($(args[i]) = _a[$i]) for i in 1:arity]..., b))
    end
    isempty(bodies) && return nothing
    fn = Expr(:function, Expr(:call, fname, :(_a::Vector{Atom})),
              Expr(:block, :(Atom[$(bodies...)])))
    Base.eval(@__MODULE__, fn)                              # world-age paid ONCE, at registration
end

end # module
