# IR.jl — the Core MeTTa compiler's intermediate representation.
#
# ─── WHY THIS FILE EXISTS ────────────────────────────────────────────────────────────────────────
# Core had NO IR. Every "compiled" path was String→String: `MM2Router.jl` is 931 LOC of hand-written
# `(exec …)` templates re-parsed at each level by a hand-rolled paren splitter (`mm2_expr_args`), and
# `MeTTaIL.jl` translates one s-expression string into another. That is a rewriter, not a compiler,
# and it has the failure mode a rewriter always has: on 2026-08-06 the exec SOURCE FUNCTOR was typed
# by hand at FOUR independent sites, three of them wrong, and upstream MORK panicked on all three.
# With an IR and one emitter that decision is made once.
#
# ─── PORTED FROM, NOT INVENTED ───────────────────────────────────────────────────────────────────
# The node set is JeTTa's (`dev-zone/jetta`, "A compiler from MeTTa to JVM bytecode", 26,327 LOC
# Kotlin), whose IR package is 22 files / 387 LOC at
#   frontend-api/src/main/kotlin/net/singularity/jetta/compiler/frontend/ir/
# JeTTa is the only MeTTa-specific compiler IR among our references, so it is the one to follow.
# NAMES ARE KEPT VERBATIM so a future session can diff us against upstream by grepping the same
# identifier — the same discipline that made the MORK port auditable. They live in `module CompilerIR`
# precisely so `Symbol`/`Variable`/`Expression`/`Grounded` can match JeTTa without colliding with
# Core's ATOM grammar in `standard/Atoms.jl` (`Sym`/`Var`/`Expression`/`Grounded`) — two different
# layers that genuinely have the same concepts, and conflating them is what trapped the grammar's
# Atom type inside the evaluator in the first place.
#
# Corroborating structure from the other three references we read:
#   * rholang-rs — typed AST (`Proc`, 32 variants) + a SemanticDb of PID-keyed ANNOTATION SIDE-TABLES,
#     with nothing rewritten into a new tree, then an explicit pass pipeline
#     (ResolverPass → ForCompElaborationPass → EnclosureAnalysisPass). Hence `NodeId` + side-tables
#     below rather than repeatedly rebuilding trees.
#   * CeTTa — `mm2_lower.c` pairs a SURFACE symbol with an IR symbol (`surf_exec` ⇄ `ir_exec`) and
#     lowers on every parse, with an inverse raise. Hence `Special.surface`/`Special.kind` below.
#   * MeTTaTron — `EvalResult = (Vec<MettaValue>, Environment)`: nondeterminism lives in the RETURN
#     TYPE, so every form threads a vector and the Cartesian product falls out. The IR therefore
#     models `Superpose` as a first-class node instead of leaving multiplicity implicit.
#
# ─── WHAT THIS IS AND IS NOT ─────────────────────────────────────────────────────────────────────
# THIS IS the data type + node set only — stage 1. It is NOT a compiler by itself, and must not be
# described as one. A frontend (Atom → IR, with resolution) and passes (control-flow lowering) are
# separate files. Calling a surface translation "the compiler" is a mistake already made in this
# tree today; do not repeat it.
#
# NO `Any` ANYWHERE — a standing project rule, tests included. `Grounded` is parametric; every
# container is concretely typed; `Vector{IRAtom}` mirrors `Atoms.jl`'s own `Vector{Atom}`.

module CompilerIR

# ── identity ─────────────────────────────────────────────────────────────────────────────────────
# rholang-rs keys its SemanticDb annotations by node PID rather than threading analysis results
# through the tree. Same here: a NodeId is stable, so a pass records its results in a side-table and
# the tree is never rebuilt to carry them.
const NodeId = UInt32
const NO_ID = NodeId(0)

"JeTTa `UniqueAtomIdGenerator` — mints the unique ids that make alpha-renaming decidable."
mutable struct UniqueAtomIdGenerator
    counter::NodeId
end
UniqueAtomIdGenerator() = UniqueAtomIdGenerator(NO_ID)
next_id!(g::UniqueAtomIdGenerator)::NodeId = (g.counter += NodeId(1); g.counter)

# ── source positions (JeTTa Position.kt / SourcePosition.kt) ─────────────────────────────────────
# Kept from the first line rather than retrofitted: a compiler that cannot say WHERE a rule came from
# cannot produce a usable diagnostic, and Core's existing lanes silently drop forms (the MeTTa-IL
# lane dropped every non-`~>` form without a word until a guard was added).

"JeTTa `Position` — a point in a source file."
struct Position
    line::Int32
    column::Int32
end
const NO_POSITION = Position(Int32(0), Int32(0))

"JeTTa `SourcePosition` — a span, with the originating file."
struct SourcePosition
    file::String
    start::Position
    stop::Position
end
const NO_SOURCE = SourcePosition("", NO_POSITION, NO_POSITION)

# ── the node hierarchy (JeTTa Atom.kt is the root interface) ─────────────────────────────────────

"""
    IRAtom

Root of the IR node hierarchy — JeTTa's `Atom` interface.

Named `IRAtom`, not `Atom`, for one reason: Core already has an `Atom` grammar type in
`standard/Atoms.jl`, and these are DIFFERENT LAYERS. `Atoms.Atom` is the surface grammar
(`ATOM = SYMBOL | VARIABLE | GROUNDED | EXPRESSION`, per `metta_grammar.ebnf`); `IRAtom` is what the
compiler reasons over after resolution, and it carries things the grammar has no word for — binding
structure, resolved references, arrow types, branch arms.
"""
abstract type IRAtom end

"Every node carries an id and a source span."
id(a::IRAtom)::NodeId = a.id
source(a::IRAtom)::SourcePosition = a.src

# ── leaves ───────────────────────────────────────────────────────────────────────────────────────

"JeTTa `Symbol` — a bare name, before resolution."
struct IRSymbol <: IRAtom
    name::Base.Symbol
    id::NodeId
    src::SourcePosition
end
IRSymbol(name::Base.Symbol) = IRSymbol(name, NO_ID, NO_SOURCE)
IRSymbol(name::AbstractString) = IRSymbol(Base.Symbol(name))

"""
JeTTa `Variable` — a MeTTa `\$x`.

`unique` is the alpha-renamed identity assigned by the resolver, distinct from the written `name`.
Two `\$x` in different rules are different variables and must not unify; two `\$x` in the SAME rule
are one variable and must. A string lowering cannot express that distinction at all, which is why
`MeTTaIL.jl` has a standing CRUX note that head and body must be parsed together or MORK's POSITIONAL
variables silently reorder — `(q \$y \$x)` over `(p a b)` yielding `(q a b)`.
"""
struct IRVariable <: IRAtom
    name::Base.Symbol
    unique::NodeId          # NO_ID until the resolver runs
    id::NodeId
    src::SourcePosition
end
IRVariable(name::Base.Symbol) = IRVariable(name, NO_ID, NO_ID, NO_SOURCE)
IRVariable(name::AbstractString) = IRVariable(Base.Symbol(name))
is_resolved(v::IRVariable)::Bool = v.unique != NO_ID

"""Head symbol marking the UNIT atom `()` — an `IRExpression` with this head and no args IS `()`.

`Symbol("()")` is unwritable in source (the tokenizer treats parens as delimiters, so no symbol token
can contain them), so it cannot collide with a user symbol. The previous sentinel `:Nil` COULD and did:
`()` and `(Nil)` lowered to the same node and `()` was silently rewritten to `(Nil)`."""
const UNIT_HEAD = Symbol("()")

"JeTTa `GroundedType` — the type tag of a grounded value."

@enum GroundedType GROUNDED_INT GROUNDED_FLOAT GROUNDED_BOOL GROUNDED_STRING GROUNDED_OPAQUE

"""
JeTTa `Grounded` — a host value embedded in the IR.

Parametric on the host type, so no `Any` enters the IR. `ty` is the MeTTa-visible tag; the two are
kept separate because the §3.4 TYPE CONVERSION ambiguity is a real defect source here — `(/ 7 2)`
returned `3.5` against a reference that returns `3`, on all three lanes at once, because no single
place owned the decision. `NumericSeam` owns the arithmetic half; this field is how the compiler
carries the type it decided on rather than re-deriving it per lane.
"""
struct IRGrounded{T} <: IRAtom
    value::T
    ty::GroundedType
    id::NodeId
    src::SourcePosition
end
IRGrounded(v::T, ty::GroundedType) where {T} = IRGrounded{T}(v, ty, NO_ID, NO_SOURCE)

"JeTTa `ResolvedSymbol` — a `Symbol` the resolver has bound to a definition."
struct IRResolvedSymbol <: IRAtom
    name::Base.Symbol
    target::NodeId          # the FunctionDefinition / BoundAtom it resolves to
    id::NodeId
    src::SourcePosition
end

# ── composites ───────────────────────────────────────────────────────────────────────────────────

"""
JeTTa `Expression` — an application.

HEAD IS A SEPARATE FIELD, not `children[1]`. That is deliberate and is a measured bug class here:
`MM2Router` needed a sentinel constant `_MM2_COMPOUND_HEAD = "\\0compound-operator"` — an
unrepresentable NUL string — purely to detect a compound in operator position, because in a flat
s-expression string the head is just the first substring. With the head as its own field the case is
structural and cannot be missed.
"""
struct IRExpression <: IRAtom
    head::IRAtom
    args::Vector{IRAtom}
    id::NodeId
    src::SourcePosition
end
IRExpression(head::IRAtom, args::Vector{IRAtom}) = IRExpression(head, args, NO_ID, NO_SOURCE)

"""
JeTTa `Special` — a special form, carrying BOTH its surface spelling and its IR kind.

The pair is CeTTa's design (`mm2_lower.c` interns `surf_exec = "exec"` alongside `ir_exec =
"mm2_exec"` and lowers on every parse, with an inverse raise). Keeping `surface` means a diagnostic
can quote what the user wrote, and the IR can be raised back to source form for debugging — while
`kind` is what passes dispatch on, so a pass never string-compares a head.
"""
@enum SpecialKind begin
    SPECIAL_LET; SPECIAL_LET_SEQ; SPECIAL_IF; SPECIAL_CASE; SPECIAL_MATCH
    SPECIAL_SUPERPOSE; SPECIAL_COLLAPSE; SPECIAL_QUOTE; SPECIAL_EVAL; SPECIAL_CHAIN
    SPECIAL_FUNCTION; SPECIAL_RETURN; SPECIAL_ERROR; SPECIAL_CATCH
end

struct IRSpecial <: IRAtom
    kind::SpecialKind
    surface::Base.Symbol
    args::Vector{IRAtom}
    id::NodeId
    src::SourcePosition
end

"""
JeTTa `BoundAtom` — one binding: a PATTERN bound to a VALUE.

A pattern, not a name: MeTTa's `let` destructures, so `(let (\$a \$b) (pair 1 2) …)` binds two
variables through one binding. JeTTa has a separate `DestructiveBinding` node for the destructuring
case; here the pattern field subsumes it, and `is_destructuring` reports which it is.
"""
struct IRBoundAtom <: IRAtom
    pattern::IRAtom
    value::IRAtom
    id::NodeId
    src::SourcePosition
end
IRBoundAtom(pattern::IRAtom, value::IRAtom) = IRBoundAtom(pattern, value, NO_ID, NO_SOURCE)
is_destructuring(b::IRBoundAtom)::Bool = !(b.pattern isa IRVariable)

"""
JeTTa `DestructiveBinding` (38 LOC upstream, the largest IR node) — a `let` / `let*`.

`sequential` distinguishes them: `let*` binds left-to-right with each binding visible to the next,
`let` does not. Modelling this EXPLICITLY is the point of the whole file. Measured over `Core/lib`:
of 888 top-level `(=)` rules, 579 cannot reach the compiled lane, and `let*` (159) + `if` (150) +
`let` (90) = 399 of those 579 — **69% of all rejections are these two nodes and `IRIf`**. They are
excluded today because `MM2Router` hard-rejects them by head string (`_MM2_SPECIAL_FORMS`); there is
no lowering to write in a String→String world, because a binding has no representation there.
"""
struct IRDestructiveBinding <: IRAtom
    bindings::Vector{IRBoundAtom}
    sequential::Bool
    body::IRAtom
    id::NodeId
    src::SourcePosition
end

"JeTTa `MatchBranch` — one arm of a `case`/`match`."
struct IRMatchBranch
    pattern::IRAtom
    body::IRAtom
    src::SourcePosition
end
IRMatchBranch(pattern::IRAtom, body::IRAtom) = IRMatchBranch(pattern, body, NO_SOURCE)

"JeTTa `Match` — scrutinee plus ordered arms. `if` lowers to this; it is not a distinct primitive."
struct IRMatch <: IRAtom
    scrutinee::IRAtom
    branches::Vector{IRMatchBranch}
    id::NodeId
    src::SourcePosition
end

"""
Nondeterminism as a first-class node.

MeTTaTron carries this in the return type — `EvalResult = (Vec<MettaValue>, Environment)`, every form
iterating the vector — so the Cartesian product is structural rather than implemented per form. An IR
cannot borrow a return type, so multiplicity becomes a node instead; passes that must preserve
branching then cannot silently drop it.
"""
struct IRSuperpose <: IRAtom
    alternatives::Vector{IRAtom}
    id::NodeId
    src::SourcePosition
end

# ── types (JeTTa ArrowType.kt / SeqType.kt) ──────────────────────────────────────────────────────

"JeTTa `ArrowType` — `(-> A B C)`, a function type."
struct IRArrowType <: IRAtom
    params::Vector{IRAtom}
    result::IRAtom
    id::NodeId
    src::SourcePosition
end

"JeTTa `SeqType` — a sequence/tuple type."
struct IRSeqType <: IRAtom
    elements::Vector{IRAtom}
    id::NodeId
    src::SourcePosition
end

# ── definitions (JeTTa FunctionLike / FunctionDefinition / Lambda) ───────────────────────────────

"JeTTa `FunctionLike` — the common interface of anything with parameters and a body."
abstract type IRFunctionLike <: IRAtom end

"JeTTa `Lambda` — an anonymous function."
struct IRLambda <: IRFunctionLike
    params::Vector{IRVariable}
    body::IRAtom
    id::NodeId
    src::SourcePosition
end

"""
JeTTa `FunctionDefinition` — a compiled MeTTa `(= (f …) body)`.

`clauses` is a VECTOR because MeTTa functions are multi-clause and the clauses are ordered and
nondeterministic — every matching clause contributes a result. Collapsing them to one would be the
same silent-narrowing defect class the MeTTa-IL lane already shipped once.
"""
struct IRFunctionDefinition <: IRFunctionLike
    name::Base.Symbol
    clauses::Vector{IRBoundAtom}     # pattern = LHS, value = RHS
    ty::Union{IRArrowType, Nothing}  # from a `(: f (-> …))` declaration, if present
    id::NodeId
    src::SourcePosition
end

"JeTTa `Run` — a top-level `!` directive."
struct IRRun <: IRAtom
    body::IRAtom
    id::NodeId
    src::SourcePosition
end

"""
JeTTa `Predefined` (61 LOC upstream, the largest IR file) — a primitive the compiler knows natively.

This node is what "move the primitives off the interpreter" needs. Today a grounded op is reachable
only through the interpreter's `TOKEN_REGISTRY`/`MINIMAL_OPS`, and `MM2Router` must REJECT any rule
whose head appears there (gate 2) because the compiled lane cannot call it — 44 op names exist in
both that registry and MORK's `GROUNDED_REGISTRY`, and the two measurably disagree on arity. A
`Predefined` node lets the compiler resolve a primitive itself instead of bailing to the fallback.
"""
struct IRPredefined <: IRAtom
    name::Base.Symbol
    arity::Int32                     # -1 = variadic
    ty::Union{IRArrowType, Nothing}
    id::NodeId
    src::SourcePosition
end

# ── the program ──────────────────────────────────────────────────────────────────────────────────

"""
    IRProgram

A compiled module: definitions, top-level `!` runs, and the annotation side-tables.

`annotations` is rholang-rs's SemanticDb shape — analysis results keyed by `NodeId` rather than
rewritten into the tree, so a pass adds information without rebuilding and without invalidating the
ids other passes recorded against.
"""
struct IRProgram
    definitions::Vector{IRFunctionDefinition}
    runs::Vector{IRRun}
    predefined::Dict{Base.Symbol, IRPredefined}
    annotations::Dict{Base.Symbol, Dict{NodeId, NodeId}}
    # DECLARED TYPES, from `(: name type)` forms. A VECTOR per name because an atom may carry SEVERAL
    # types — hyperon's `get_atom_types` returns a list and `types.rs` documents `get_atom_types((a b))`
    # as `[(A B), (B B)]` when `a:{A,B}`. Collapsing to one would silently pick a winner.
    #
    # WHY THE COMPILER NEEDS THIS AT ALL: every upstream that resolves "is this expression a CALL or a
    # DATA TUPLE" consults types to do it — hyperon forks on whether the head has a function type,
    # MeTTaScript's predicate is `defined-head OR arrow-typed head`, CeTTa infers a product type. We had
    # no type information in the compiler at all, so none of those was available to us and expression
    # heads were simply declined (41 of 66 declines, measured 2026-08-12). See
    # `docs/specs/expression_head_call_vs_data_four_upstreams.md`.
    types::Dict{Base.Symbol, Vector{IRAtom}}
    gen::UniqueAtomIdGenerator
end
IRProgram() = IRProgram(IRFunctionDefinition[], IRRun[], Dict{Base.Symbol, IRPredefined}(),
                        Dict{Base.Symbol, Dict{NodeId, NodeId}}(),
                        Dict{Base.Symbol, Vector{IRAtom}}(), UniqueAtomIdGenerator())

"The declared types of `name`, in declaration order; empty if it has none."
declared_types(p::IRProgram, name::Base.Symbol)::Vector{IRAtom} =
    get(p.types, name, IRAtom[])

"""Does `name` carry a declared ARROW type — i.e. an `(-> …)` expression?

This is the half of MeTTaScript's call-vs-data predicate that we could not compute before
(`eval.ts::getTypesForQuery`: *defined-head symbol OR arrow-typed head* → function, else tuple). The
other half — is the head a defined symbol — `ANormal` already has as PeTTa's `fun/1`.

⚠️ NOT YET WIRED into any lowering decision. Capturing the information and USING it are separate
changes on purpose: the last attempt to widen expression-head lowering committed to one static reading
and broke `test_stdlib.metta` on `(() () \$l2)`.

🔴 AND A LOOKUP LIKE THIS ONE CANNOT, BY ITSELF, RECOVER ANY OF THE DECLINED CLAUSES. Measured
2026-08-12 over the 74 lib + stdlib files, before building the rule that would have used it:

    type declarations across the corpus : 56
    IRExpression residuals in declines  : 121
      head is itself an EXPRESSION      : 121      <- ALL of them
      symbol head WITH an arrow type    : 0

Every declined residual has an EXPRESSION head, and this function needs a NAME. The recoverable set for
a name-keyed lookup is exactly zero.

What those clauses need is what `Eval.jl`'s `_arg_actual_types_uncached` does: INFER the head
expression's type by applying its own head's function type to its arguments, recursively —
`head_types = head isa Expression ? arg_actual_types(head, space) : atom_types(head, space)`. That is a
type-inference pass over the IR, not a table lookup, and this table is its input rather than its
substitute."""
function has_arrow_type(p::IRProgram, name::Base.Symbol)::Bool
    for t in declared_types(p, name)
        t isa IRExpression || continue
        h = (t::IRExpression).head
        h isa IRSymbol && (h::IRSymbol).name === :(->) && return true
    end
    false
end

"Record an analysis result for `node` under `pass`, without touching the tree."
function annotate!(p::IRProgram, pass::Base.Symbol, node::NodeId, value::NodeId)
    get!(() -> Dict{NodeId, NodeId}(), p.annotations, pass)[node] = value
    p
end

"Read back a pass's annotation for `node`, or `nothing`."
function annotation(p::IRProgram, pass::Base.Symbol, node::NodeId)
    tbl = get(p.annotations, pass, nothing)
    tbl === nothing ? nothing : get(tbl, node, nothing)
end

# ── traversal ────────────────────────────────────────────────────────────────────────────────────

"Direct children of a node, in evaluation order. One definition, so no pass hand-rolls a walk."
children(a::IRSymbol)::Vector{IRAtom} = IRAtom[]
children(a::IRVariable)::Vector{IRAtom} = IRAtom[]
children(a::IRGrounded)::Vector{IRAtom} = IRAtom[]
children(a::IRResolvedSymbol)::Vector{IRAtom} = IRAtom[]
children(a::IRPredefined)::Vector{IRAtom} = IRAtom[]
children(a::IRExpression)::Vector{IRAtom} = IRAtom[a.head, a.args...]
children(a::IRSpecial)::Vector{IRAtom} = a.args
children(a::IRBoundAtom)::Vector{IRAtom} = IRAtom[a.pattern, a.value]
children(a::IRSuperpose)::Vector{IRAtom} = a.alternatives
children(a::IRSeqType)::Vector{IRAtom} = a.elements
children(a::IRArrowType)::Vector{IRAtom} = IRAtom[a.params..., a.result]
children(a::IRRun)::Vector{IRAtom} = IRAtom[a.body]
children(a::IRLambda)::Vector{IRAtom} = IRAtom[a.params..., a.body]
children(a::IRDestructiveBinding)::Vector{IRAtom} = IRAtom[a.bindings..., a.body]
children(a::IRMatch)::Vector{IRAtom} =
    IRAtom[a.scrutinee, (x for b in a.branches for x in (b.pattern, b.body))...]
children(a::IRFunctionDefinition)::Vector{IRAtom} = IRAtom[a.clauses...]

"Pre-order walk, applying `f` to every node."
function walk(f, a::IRAtom)
    f(a)
    for c in children(a)
        walk(f, c)
    end
    nothing
end

export NodeId, NO_ID, UniqueAtomIdGenerator, next_id!,
       Position, SourcePosition, NO_POSITION, NO_SOURCE,
       IRAtom, IRSymbol, IRVariable, IRGrounded, GroundedType,
       GROUNDED_INT, GROUNDED_FLOAT, GROUNDED_BOOL, GROUNDED_STRING, GROUNDED_OPAQUE,
       UNIT_HEAD,
       IRResolvedSymbol, IRExpression, IRSpecial, SpecialKind,
       declared_types, has_arrow_type,
       SPECIAL_LET, SPECIAL_LET_SEQ, SPECIAL_IF, SPECIAL_CASE, SPECIAL_MATCH,
       SPECIAL_SUPERPOSE, SPECIAL_COLLAPSE, SPECIAL_QUOTE, SPECIAL_EVAL, SPECIAL_CHAIN,
       SPECIAL_FUNCTION, SPECIAL_RETURN, SPECIAL_ERROR, SPECIAL_CATCH,
       IRBoundAtom, IRDestructiveBinding, IRMatchBranch, IRMatch, IRSuperpose,
       IRArrowType, IRSeqType, IRFunctionLike, IRLambda, IRFunctionDefinition,
       IRRun, IRPredefined, IRProgram,
       id, source, is_resolved, is_destructuring, annotate!, annotation, children, walk

end # module CompilerIR
