# Frontend.jl — the Core MeTTa compiler, stage 2: surface Atom → CompilerIR, with resolution.
#
# ─── WHAT MAKES THIS A COMPILER STAGE AND NOT A TRANSLATION ──────────────────────────────────────
# It does three things a string rewriter cannot:
#   1. RESOLUTION. Every `$x` gets a unique id, minted per CLAUSE, with LHS and RHS sharing one scope.
#      That is not cosmetic — MORK variables are POSITIONAL, and `MeTTaIL.jl` carries a standing CRUX
#      note that parsing head and body separately silently reorders indices, `(q $y $x)` over
#      `(p a b)` yielding `(q a b)`. Resolution makes the sharing explicit instead of accidental.
#   2. SPECIAL FORMS BECOME NODES. `let`/`let*`/`if`/`case` stop being head strings to reject and
#      become `IRDestructiveBinding` / `IRMatch`. MEASURED over Core/lib: 399 of the 579 rules that
#      cannot reach the compiled lane (69%) are rejected on exactly these heads.
#   3. HEAD IS STRUCTURAL. A compound in operator position is an `IRExpression` whose `head` is itself
#      an `IRExpression` — representable, not a `"\0compound-operator"` sentinel string.
#
# ─── SLG / TABLING IS REUSED, NOT REBUILT ────────────────────────────────────────────────────────
# Core already adopted SWI-Prolog-style SLG variant tabling in the interpreter (`Eval.jl:929`,
# opt-in) together with the Van Gelder alternating-fixpoint WFS (`:952`). The registry is
# `_TABLED_HEADS`, a set of HEAD NAME symbols, consulted by `is_tabled` (`:982`). The compiler reads
# THAT SET. It does not declare a second tabling registry, does not re-derive which predicates are
# tabled, and does not reimplement the engine — `tabled_definitions` below is a lookup against the
# interpreter's own state, so `table!` / `auto_table!` / `untable_all!` remain the single control
# surface for both lanes.
#
# ─── STATUS ──────────────────────────────────────────────────────────────────────────────────────
# Stage 2 of a compiler. Stage 1 is `compiler/IR.jl`. Passes (control-flow lowering) and the emitter
# into the MeTTa-IL bridge are NOT written. This file does not execute anything and is not wired into
# any evaluation path yet — nothing here changes existing behaviour.

module CompilerFrontend

using ..CompilerIR
import ..CompilerIR: NodeId, NO_ID

# The SURFACE grammar — `module StandardMeTTa` in standard/Atoms.jl, a SIBLING submodule of this one
# (both live directly under MeTTaCore), hence `..StandardMeTTa`. Distinct layer from the IR: these
# four constructors are `metta_grammar.ebnf`'s ATOM, what the parser produces; CompilerIR is what the
# compiler reasons over afterwards.
using ..StandardMeTTa: Atom, Sym, Var, Expression, Grounded

# The interpreter — imported for ONE reason: its existing SLG tabling registry. See
# `tabled_definitions` at the bottom. Nothing else in this file touches the evaluator.
import ..Eval

# ── special-form table ───────────────────────────────────────────────────────────────────────────
# ⚠️ THIS LINE USED TO CITE "CeTTa's surface⇄IR symbol pairing, mm2_lower.c" AS PRECEDENT. IT IS NOT.
# Verified 2026-08-07 against the source: `mm2_lower.c` takes atoms ALREADY PARSED FROM MM2 SURFACE
# TEXT and renames their heads into inert IR symbols so CeTTa's HE evaluator will NOT reduce them —
# `mm2_exec`, `mm2_pattern_and`, `mm2_pattern_btm`, `mm2_guard_eq`, `mm2_sink_add`, `mm2_sink_remove`,
# `mm2_sink_z3` (:47-57) — and `mm2_raise_atom_impl` (:107-151) is the exact inverse. The direction is
# MM2 → inert → MM2, a round trip; it is never MeTTa → IR.
#
# The symbol sets have ZERO overlap with ours: theirs is MM2 CALCULUS vocabulary (exec/pattern/guard/
# sink), ours is MeTTa LANGUAGE vocabulary (let/if/case/match/…). Same shape, opposite purpose — theirs
# PROTECTS atoms from an evaluator, ours CLASSIFIES forms for a compiler. A borrowed citation that does
# not survive reading the cited file is worse than none.
# Surface spelling on the left, IR kind on the right. A pass dispatches on the KIND; only this table
# ever compares a surface string, so adding a spelling is one line and cannot drift across sites the
# way `_MM2_SPECIAL_FORMS` + `_MM2_ARITH_I64` + the four exec templates did.
const SPECIAL_FORMS = Dict{Base.Symbol, SpecialKind}(
    :let        => SPECIAL_LET,
    Base.Symbol("let*") => SPECIAL_LET_SEQ,
    :if         => SPECIAL_IF,
    :case       => SPECIAL_CASE,
    :match      => SPECIAL_MATCH,
    :superpose  => SPECIAL_SUPERPOSE,
    :collapse   => SPECIAL_COLLAPSE,
    :quote      => SPECIAL_QUOTE,
    :eval       => SPECIAL_EVAL,
    :chain      => SPECIAL_CHAIN,
    :function   => SPECIAL_FUNCTION,
    :return     => SPECIAL_RETURN,
    :Error      => SPECIAL_ERROR,
    :catch      => SPECIAL_CATCH,
)

# ── resolution scope ─────────────────────────────────────────────────────────────────────────────

"""
    Scope

Variable name → unique id, for ONE clause.

Chained, not flat: `let` introduces a child scope so an inner `\$x` shadows an outer one instead of
being unified with it. A flat map would silently merge them — the same silent-narrowing shape that
has cost us wrong answers three times in this tree.
"""
struct Scope
    names::Dict{Base.Symbol, NodeId}
    parent::Union{Scope, Nothing}
end
Scope() = Scope(Dict{Base.Symbol, NodeId}(), nothing)
child(s::Scope) = Scope(Dict{Base.Symbol, NodeId}(), s)

function lookup(s::Scope, name::Base.Symbol)::NodeId
    cur = s
    while cur !== nothing
        v = get(cur.names, name, NO_ID)
        v == NO_ID || return v
        cur = cur.parent
    end
    NO_ID
end

"""
    Ctx

Frontend state: the id generator, the current scope, and the program being built.

`gen` is shared across the whole program so ids are globally unique, while `scope` is per-clause so
variable IDENTITY is per-clause. Those are different things and conflating them is the bug class
this file exists to prevent.
"""
mutable struct Ctx
    gen::UniqueAtomIdGenerator
    scope::Scope
    program::IRProgram
end
Ctx(p::IRProgram) = Ctx(p.gen, Scope(), p)

fresh(c::Ctx)::NodeId = next_id!(c.gen)

"Bind `name` in the CURRENT scope (declaring, not looking up) and return its unique id."
bind!(c::Ctx, name::Base.Symbol)::NodeId = (c.scope.names[name] = fresh(c))

"Resolve `name`, binding it in the current scope on first sight — MeTTa variables are implicitly
introduced by use, so first occurrence within a clause declares."
resolve!(c::Ctx, name::Base.Symbol)::NodeId =
    (u = lookup(c.scope, name); u == NO_ID ? bind!(c, name) : u)

# ── grounded typing ──────────────────────────────────────────────────────────────────────────────
# The §3.4 TYPE CONVERSION decision, made ONCE here rather than per lane. `NumericSeam` owns the
# arithmetic semantics; this only tags what the value IS.
ground_type(::Integer)         = GROUNDED_INT
ground_type(::AbstractFloat)   = GROUNDED_FLOAT
ground_type(::Bool)            = GROUNDED_BOOL
ground_type(::AbstractString)  = GROUNDED_STRING
ground_type(_)                 = GROUNDED_OPAQUE

# ── the lowering ─────────────────────────────────────────────────────────────────────────────────

"""
    lower(ctx, atom) -> IRAtom

Surface `Atom` → IR node. Total over the four-constructor grammar
(`ATOM = SYMBOL | VARIABLE | GROUNDED | EXPRESSION`, `metta_grammar.ebnf`), so there is no
fall-through case that can silently drop a form.
"""
function lower end

lower(c::Ctx, a::Sym)::IRAtom = IRSymbol(a.name, fresh(c), NO_SOURCE)

lower(c::Ctx, a::Var)::IRAtom =
    (n = Base.Symbol(a.name); IRVariable(n, resolve!(c, n), fresh(c), NO_SOURCE))

# Bool BEFORE Integer — Julia's `Bool <: Integer`, so the generic method would tag `true` as an INT.
lower(c::Ctx, a::Grounded{Bool})::IRAtom = IRGrounded(a.value, GROUNDED_BOOL, fresh(c), NO_SOURCE)

# ── A GROUNDED OPERATION IS A PRIMITIVE, NOT A VALUE ─────────────────────────────────────────────
# MEASURED 2026-08-06: without these two methods, 2192 of 2765 residual goals in the A-normalizer
# were expressions whose HEAD was `Grounded{Operation}` / `Grounded{SpaceOp}` — i.e. 79% of everything
# the compiler could not flatten was in fact an ordinary primitive call it simply did not recognise.
#
# The cause is upstream of us: `parse_from` SUBSTITUTES BOUND TOKENS AT PARSE TIME
# (`Eval.jl:2525`), so `match`, `+`, `car-atom` … never reach the compiler as `Sym`; they
# arrive already resolved to the interpreter's own callable struct. Treating that as an opaque
# grounded VALUE is what forced the compiled lane to bail to the interpreter on any rule mentioning a
# primitive — the same reason `MM2Router`'s gate 2 rejects every head found in `TOKEN_REGISTRY`.
#
# `IRPredefined` is the node for this (JeTTa's `Predefined`, its largest IR file at 61 LOC). Emitting
# it here is the concrete step of moving primitive attachment off the interpreter: the compiler now
# holds the primitive's NAME and ARITY itself, instead of holding an interpreter closure it cannot
# reason about.
lower(c::Ctx, a::Grounded{Eval.Operation})::IRAtom =
    IRPredefined(Base.Symbol(a.value.name), Int32(-1), nothing, fresh(c), NO_SOURCE)
lower(c::Ctx, a::Grounded{Eval.SpaceOp})::IRAtom =
    IRPredefined(Base.Symbol(a.value.name), Int32(-1), nothing, fresh(c), NO_SOURCE)

# Long form: `f(x::Grounded{T})::IRAtom where {T} = …` does not parse — the return annotation binds
# before `where`, so `T` is not yet in scope. This was the ONE unannotated `lower` method, and JET
# traced `lower_program`'s runtime dispatch to it.
function lower(c::Ctx, a::Grounded{T})::IRAtom where {T}
    IRGrounded(a.value, ground_type(a.value), fresh(c), NO_SOURCE)
end

function lower(c::Ctx, a::Expression)::IRAtom
    isempty(a.children) && return IRExpression(IRSymbol(:Nil, fresh(c), NO_SOURCE),
                                               IRAtom[], fresh(c), NO_SOURCE)
    h = a.children[1]
    rest = @view a.children[2:end]
    # A SYMBOL head may be a special form; a compound head never is, and stays structural.
    #
    # ⚠️ A GROUNDED head must be checked TOO. `parse_from` substitutes bound tokens at parse time
    # (Eval.jl:2525), so a registered name — `case`, `if`, `match` … — arrives as
    # `Grounded{Operation}`/`Grounded{SpaceOp}`, NEVER as `Sym`. Checking only `Sym` meant those
    # forms silently became ordinary applications and no `IRMatch` was ever built. MEASURED
    # 2026-08-06: `specialize_matches` reported `clauses split: 0` on
    # `(= (colour \$c) (case \$c ((red warm) (blue cool))))` for exactly this reason.
    #
    # This is the SECOND site with this bug — `definition_name` had it and was fixed; this one was
    # not swept at the same time. Per the standing rule, a recurring defect gets the RULE applied to
    # every candidate site, not a fix at the instance that happened to be noticed.
    hname = h isa Sym                              ? (h::Sym).name :
            h isa Grounded{Eval.Operation}  ? Base.Symbol(h.value.name) :
            h isa Grounded{Eval.SpaceOp}    ? Base.Symbol(h.value.name) : nothing
    if hname !== nothing
        kind = get(SPECIAL_FORMS, hname, nothing)
        kind === nothing || return lower_special(c, kind, hname, rest)
    end
    IRExpression(lower(c, h), IRAtom[lower(c, x) for x in rest], fresh(c), NO_SOURCE)
end

"""
    lower_special(ctx, kind, surface, args) -> IRAtom

Special forms that have a DEDICATED node become one; the rest keep their arguments and are carried as
`IRSpecial` so a later pass can lower them. Nothing is dropped — that is the contract, and the reason
this returns `IRSpecial` rather than falling back to `IRExpression`: an unlowered special form must
stay visibly special, not disguise itself as an application.
"""
function lower_special(c::Ctx, kind::SpecialKind, surface::Base.Symbol,
                       args::AbstractVector{Atom})::IRAtom
    if kind === SPECIAL_LET || kind === SPECIAL_LET_SEQ
        b = lower_let(c, kind, surface, args)
        b === nothing || return b
    elseif kind === SPECIAL_IF && length(args) == 3
        return lower_if(c, args)
    elseif kind === SPECIAL_CASE && length(args) == 2
        # ⚠️ `SPECIAL_MATCH` USED TO BE ACCEPTED HERE TOO, AND IT SILENTLY DISCARDED THE PATTERN.
        # `lower_case` takes `scrut = args[1]` and `arms = args[end]`. Those are the right slots for
        # `(case SCRUT ARMS)` — but `(match SPACE PATTERN TEMPLATE)` is a THREE-argument space query,
        # so the same read makes the SPACE the scrutinee, the TEMPLATE the arm list, and never looks
        # at `args[2]` at all. MEASURED 2026-08-07:
        #
        #   (match &self ($a $b) ((p 1) (q 2)))  ⟹  IRMatch(scrutinee = &self, 2 branches)
        #                                            the pattern ($a $b) is ABSENT FROM THE IR
        #
        # It only reached that shape when the TEMPLATE happened to parse as a list of 2-element
        # pairs; otherwise `lower_case` returned `nothing` and the form fell through to `IRSpecial`
        # anyway. So the common outcome was already the honest decline and the rare one was a WRONG
        # ANSWER — the worst possible split, because coverage never showed it.
        #
        # `match` now always falls to `IRSpecial`, which preserves all three arguments for the pass
        # that will lower it. Arity is pinned to exactly 2 for the same reason: a `case` of another
        # arity is not a shape this function can read correctly either.
        m = lower_case(c, kind, args)
        m === nothing || return m
    elseif kind === SPECIAL_SUPERPOSE
        # `(superpose (a b c))` takes ONE tuple argument whose CHILDREN are the alternatives — it is
        # not variadic. Taking `args` directly gave a single alternative holding the whole tuple, so
        # the disjunction had one branch and `superpose` reduced to the tuple itself.
        # ORACLE, 2026-08-07: `!(superpose (a b c))` → `[c, b, a]` — THREE answers, not one.
        alts = (length(args) == 1 && args[1] isa Expression) ?
               (args[1]::Expression).children : args
        return IRSuperpose(IRAtom[lower(c, x) for x in alts], fresh(c), NO_SOURCE)
    end
    IRSpecial(kind, surface, IRAtom[lower(c, x) for x in args], fresh(c), NO_SOURCE)
end

"""
`(let PAT VAL BODY)` and `(let* ((P1 V1) (P2 V2) …) BODY)`.

SCOPE RULE — the whole reason `let` needs a node. In `let*`, each value is lowered in the scope
BEFORE its own pattern is bound, and the pattern is then bound so the NEXT value can see it. In
`let`, all values are lowered in the outer scope and only then are the patterns bound. Getting this
backwards makes `(let* ((\$x 1) (\$x (+ \$x 1))) \$x)` collapse to one variable.

Returns `nothing` on a shape it does not recognise, so the caller can fall back to `IRSpecial` rather
than this function guessing.
"""
function lower_let(c::Ctx, kind::SpecialKind, ::Base.Symbol, args::AbstractVector{Atom})
    outer = c.scope
    binds = IRBoundAtom[]
    body_atom::Union{Atom, Nothing} = nothing

    if kind === SPECIAL_LET && length(args) == 3
        val = lower(c, args[2])                     # value in the OUTER scope
        c.scope = child(outer)
        pat = lower(c, args[1])                     # pattern binds in the INNER scope
        push!(binds, IRBoundAtom(pat, val, fresh(c), NO_SOURCE))
        body_atom = args[3]
    elseif kind === SPECIAL_LET_SEQ && length(args) == 2 && args[1] isa Expression
        c.scope = child(outer)
        for pv in (args[1]::Expression).children
            (pv isa Expression && length(pv.children) == 2) || (c.scope = outer; return nothing)
            val = lower(c, pv.children[2])          # sequential: value sees all PRIOR bindings
            pat = lower(c, pv.children[1])          # then this pattern becomes visible
            push!(binds, IRBoundAtom(pat, val, fresh(c), NO_SOURCE))
        end
        body_atom = args[2]
    else
        return nothing
    end

    body = lower(c, body_atom::Atom)
    c.scope = outer                                  # bindings do NOT escape
    IRDestructiveBinding(binds, kind === SPECIAL_LET_SEQ, body, fresh(c), NO_SOURCE)
end

"""
`(if COND THEN ELSE)` → `IRMatch` on the condition against True/False.

`if` is not a distinct primitive — JeTTa has `Match`/`MatchBranch` and no `If`, and MeTTa's own
stdlib defines `if` by equations. Lowering it here means one node type carries all branching, so a
later pass handles `if` and `case` once.
"""
lower_if(c::Ctx, args::AbstractVector{Atom})::IRAtom =
    IRMatch(lower(c, args[1]),
            IRMatchBranch[IRMatchBranch(IRSymbol(:True,  fresh(c), NO_SOURCE), lower(c, args[2])),
                          IRMatchBranch(IRSymbol(:False, fresh(c), NO_SOURCE), lower(c, args[3]))],
            fresh(c), NO_SOURCE)

"""
`(case SCRUT ((P1 B1) (P2 B2) …))` → `IRMatch`.

Each arm gets its OWN child scope: arm patterns bind independently, and a variable in one arm is not
the variable of the same name in the next.
"""
function lower_case(c::Ctx, ::SpecialKind, args::AbstractVector{Atom})
    arms_atom = args[end]
    arms_atom isa Expression || return nothing
    scrut = lower(c, args[1])
    outer = c.scope
    branches = IRMatchBranch[]
    for arm in (arms_atom::Expression).children
        (arm isa Expression && length(arm.children) == 2) || (c.scope = outer; return nothing)
        c.scope = child(outer)
        push!(branches, IRMatchBranch(lower(c, arm.children[1]), lower(c, arm.children[2])))
    end
    c.scope = outer
    IRMatch(scrut, branches, fresh(c), NO_SOURCE)
end

# ── definitions and programs ─────────────────────────────────────────────────────────────────────

"Is `a` a `(= LHS RHS)` definition?"
is_definition(a::Atom)::Bool =
    a isa Expression && length(a.children) == 3 &&
    a.children[1] isa Sym && (a.children[1]::Sym).name === :(=)

"""
Head name of a definition's LHS — `(= (f \$x) …)` → `:f`. Empty symbol if there is no name to take.

MUST handle a GROUNDED head, not only `Sym`. `parse_from` substitutes bound tokens at parse time
(`Eval.jl:2525`), so any head that is a registered op — `id`, `match`, `+` … — arrives as
`Grounded{Operation}`/`Grounded{SpaceOp}`, never as `Sym`. MEASURED 2026-08-06: without this,
`(= (id \$x) \$x)` compiled to `(exec 0 (, ( \$x)) …)` — an EMPTY head, a pattern that matches
nothing, and a rule that silently never fires.

MUST ALSO DESCEND A COMPOUND HEAD — the THIRD instance of the same rule, after `Sym` and then
`Grounded` (`:199` records that sweep). A curried definition puts an EXPRESSION where the head symbol
goes:

    (= (((curry \$f) \$x) \$y) (\$f \$x \$y))     ⟶ head is ((curry \$f) \$x)
    (= ((lambda \$var \$body) \$arg) …)         ⟶ head is (lambda \$var \$body)

None of the three cases fired, so this returned `Symbol("")` — and `lower_program` groups clauses BY
NAME, so every compound-head definition in one call landed in the SAME group. MEASURED 2026-08-11:
three distinct functions (`curry`, `curry-a`, `lambda`) collapsed into ONE `IRFunctionDefinition` with
3 clauses, which then PARTIALLY emitted (1 of 3; the other two declined). All of
`d2_higherfunc.metta` is this shape.

The name to take is the INNERMOST symbol head, reached by descending: `curry`, `curry-a`, `lambda`.
That is the function the definition is about, and it keeps the three apart. Grouping two clauses of
ONE curried function together stays correct — their PATTERNS still differ, and that is what
multi-clause dispatch matches on; the name is only a grouping key.

⚠️ A VARIABLE HEAD — `(= (\$f \$x) …)` — is genuinely un-nameable and still yields `NO_NAME`. Descending
cannot help: there is no symbol. `lower_program` handles it by NOT grouping, because a name that
cannot identify a function must not be used to claim two definitions are the same one.
"""
function definition_name(a::Expression)::Base.Symbol
    lhs = a.children[2]
    while lhs isa Expression && !isempty(lhs.children)
        h = (lhs::Expression).children[1]
        h isa Sym && return (h::Sym).name
        h isa Grounded{Eval.Operation} && return Base.Symbol(h.value.name)
        h isa Grounded{Eval.SpaceOp}   && return Base.Symbol(h.value.name)
        h isa Expression || break          # a Var head: un-nameable, and descending cannot help
        lhs = h                            # compound head — the name is one level further in
    end
    lhs isa Sym ? (lhs::Sym).name : NO_NAME
end

"""What `definition_name` returns when a definition's head cannot identify a function.

Only a VARIABLE head reaches this now — `(= (\$f \$x) …)`. It is a sentinel, NOT a name, and
`lower_program` must not group by it: two such definitions are not known to be the same function,
and merging them silently built one multi-clause definition out of unrelated code."""
const NO_NAME = Base.Symbol("")

"""
    lower_program(atoms) -> IRProgram

Compile a parsed MeTTa module.

Clauses of the same function are GROUPED into one `IRFunctionDefinition`, in source order — MeTTa
functions are multi-clause and every matching clause contributes a result, so collapsing them would
change the semantics.

EACH CLAUSE GETS A FRESH SCOPE, and LHS and RHS are lowered in that ONE scope. This is the whole
point of resolution: within a clause `\$x` is one variable, across clauses it is not.
"""
function lower_program(atoms::Vector{Atom})::IRProgram
    prog = IRProgram()
    c = Ctx(prog)
    order = Base.Symbol[]
    byname = Dict{Base.Symbol, Vector{IRBoundAtom}}()
    unnamed = IRBoundAtom[]                          # variable-headed clauses — one group each

    for a in atoms
        if is_definition(a)
            e = a::Expression
            name = definition_name(e)
            c.scope = Scope()                        # fresh scope PER CLAUSE
            lhs = lower(c, e.children[2])
            rhs = lower(c, e.children[3])            # same scope — shared variables
            # GROUPING IS BY NAME, so an un-nameable head must NOT be grouped. `NO_NAME` is a
            # sentinel meaning "this head identifies no function"; treating it as a name merged
            # unrelated definitions into one multi-clause group. Each gets its own group instead —
            # the clauses are still emitted, they are just no longer claimed to be one function.
            if name === NO_NAME
                push!(unnamed, IRBoundAtom(lhs, rhs, fresh(c), NO_SOURCE))
            else
                haskey(byname, name) || (byname[name] = IRBoundAtom[]; push!(order, name))
                push!(byname[name], IRBoundAtom(lhs, rhs, fresh(c), NO_SOURCE))
            end
        else
            c.scope = Scope()
            push!(prog.runs, IRRun(lower(c, a), fresh(c), NO_SOURCE))
        end
    end

    for name in order
        push!(prog.definitions,
              IRFunctionDefinition(name, byname[name], nothing, fresh(c), NO_SOURCE))
    end
    # Un-nameable clauses last, one definition each. Order among themselves is source order; they
    # cannot collide with a named group because `NO_NAME` is never a key in `byname`.
    for cl in unnamed
        push!(prog.definitions,
              IRFunctionDefinition(NO_NAME, IRBoundAtom[cl], nothing, fresh(c), NO_SOURCE))
    end
    prog
end

# ── SLG: consult the interpreter's registry, do not duplicate it ─────────────────────────────────

"""
    tabled_definitions(program) -> Vector{Base.Symbol}

Which of `program`'s definitions are TABLED, according to the interpreter's own SLG registry.

Core already adopted SWI-style SLG variant tabling (`Eval.jl:929`) plus the Van Gelder
alternating-fixpoint WFS (`:952`), controlled by `table!` / `auto_table!` / `untable_all!` over the
`_TABLED_HEADS` set. This reads that set. There is deliberately NO compiler-side tabling registry:
two registries for one concept is exactly how `TOKEN_REGISTRY` and MORK's `GROUNDED_REGISTRY` came to
hold 44 shared names that measurably disagree on arity.
"""
tabled_definitions(program::IRProgram)::Vector{Base.Symbol} =
    Base.Symbol[d.name for d in program.definitions if d.name in Eval._TABLED_HEADS]

export Scope, Ctx, SPECIAL_FORMS, lower, lower_program, is_definition, definition_name,
       tabled_definitions, ground_type

end # module CompilerFrontend
