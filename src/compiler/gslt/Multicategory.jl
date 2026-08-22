# Multicategory.jl — the CONTEXT MULTICATEGORY that a GSLT morphism is a pseudofunctor of.
#
# LAYER: the GSLT presentation layer (whitepaper §3.4.1). NO Figure-2 arrow.
#
# ─── WHY THIS FILE EXISTS AND THE ONE ABOVE IT DOES NOT ──────────────────────────────────────────
# The task was "the coarse-grained surface GSLT + morphism". Read against the sources, that is two
# halves with two different problems, and only one of them can be built honestly.
#
# 🔴 THE COARSE-GRAINED GSLT IS NOT BUILT, AND MUST NOT BE. The two-GSLT design is asserted by the
# whitepaper and ABSENT FROM THE DEFINITION AUTHORITY. Verified at the source, not taken from a note:
#
#   `gslt_mettail_summary_spec.md:819`  "Two-GSLT design (fine-grained + coarse-grained) — NOT FOUND
#                                        in this document at all"
#   `gslt_mettail_summary_spec.md:392`  "This deck never uses the terms 'fine-grained' or
#                                        'coarse-grained' anywhere in its 20 pages … Do not assume
#                                        the GSLT/continued-interactive split is the same thing"
#   `SPECMAP_METTAIL.md` C2             "OPEN — do not build to the two-GSLT design on the
#                                        whitepaper's word alone."
#
# And the whitepaper itself does not claim the correspondence: §3.4.1 says any claimed correspondence
# "requires the typed maps, assumptions, theorem statement, proof artifact, and replayable
# environment" or remains "an explicit formalization obligation — i.e., not asserted as proven in
# this paper." Building it would mean inventing BOTH the developer-facing theory AND the
# correspondence the source declines to assert. That is not a gap to fill; it is a gap on purpose.
#
# ─── WHAT A MORPHISM ACTUALLY IS, AND WHY IT IS NOT A MAP OF TERMS ───────────────────────────────
# The deck's §7 (page 12) kills the obvious definition with three counterexamples before giving its
# own, and the counterexamples are the reason this file models CONTEXTS rather than terms:
#
#   the constant map      "Send every term to 0. Preserves signatures and bisimulation trivially — a
#                          morphism from anything to anything. The category orders nothing."
#   Milner's encoding     "⟦M⟧u sends a λ-term to a π-term PARAMETERISED BY A NAME. Signature
#                          preservation does not typecheck — the motivating example is excluded."
#   ambient contexts      "A rho context may quote and compare quotations. Bisimulation over all rho
#                          contexts separates images of π-terms no π context can separate."
#
# DEFINITION 5.1, verbatim: "A morphism of GSLTs is a pseudofunctor of context multicategories,
# bisimulation-preserving for context-labelled transitions, where the bisimulation on the target is
# computed ONLY OVER THE IMAGE OF THE SOURCE'S CONTEXTS. Objects of the context multicategory are
# INTERFACES — the sort of a hole, its binding stage, its interaction surface; multimorphisms are
# CONTEXTS; composition is PLUGGING."
#
# ─── SO THIS FILE IS THE MULTICATEGORY, NOT THE MORPHISM ─────────────────────────────────────────
# It builds exactly the three things that sentence names — interfaces, contexts, plugging — and
# checks the multicategory laws. It does NOT build the pseudofunctor, because the other half of
# Definition 5.1 is bisimulation over context-labelled transitions, and this tree has no labelled
# transition system for a presentation to be bisimilar in. Claiming a morphism without that would be
# claiming exactly the naive term-map the deck spends a page refuting.
#
# ⚠️ ONE COMPONENT OF AN INTERFACE IS NOT MODELLED, AND IT IS NAMED RATHER THAN QUIETLY DROPPED.
# "The sort of a hole" and "its binding stage" are both computable from Σ — the sort from the
# enclosing constructor's signature, the stage by counting the binders a hole sits under. "Its
# INTERACTION SURFACE" is not: the deck grounds it in Rholang's interaction (comm, quoting) and our
# presentations carry no interaction relation. `GInterface` therefore has two of the three fields and
# says so. A third field filled with a guess would make every downstream comparison meaningless.
module CompilerGSLTMulticategory

using ..StandardMeTTa: Atom, Sym, Var, Expression, Grounded
using ..CompilerGSLTPresentation: GPresentation, GRule, GCat, GItem,
    ItemNonTerminal, ItemAbs, ItemBind, LabelId,
    cat_name, binders_of

export GHole, GContext, GInterface, hole, is_hole, arity, holes_of, plug, plug_term,
    identity_context, context_of, interface_at, binding_stage

"""The reserved head marking a hole: `(Hole i)`, `i` a 1-based index.

A SYMBOL rather than a new `Atom` subtype, deliberately — a context must be an ordinary term so that
`Reduce`/`Context` can be pointed at one without special-casing. The cost is that a presentation
which declares a constructor named `Hole` would collide; `context_of` rejects that rather than
producing a context whose holes are somebody's data."""
const HOLE = :Hole

"A hole, identified by position. Multicategory multimorphisms have MANY inputs; these index them."
struct GHole
    index::Int
end

is_hole(a::Atom)::Bool =
    a isa Expression && length((a::Expression).children) == 2 &&
    (a::Expression).children[1] isa Sym && ((a::Expression).children[1]::Sym).name === HOLE

"""`(Hole i)` as a term.

⚠️ THE INDEX IS `Grounded{Int}`, BECAUSE THAT IS WHAT THE READER PRODUCES. `_xt("(Hole 1)")` parses
`1` as a grounded integer, so a constructor that built `Sym("1")` would make `hole(1)` and the parsed
`(Hole 1)` UNEQUAL — every `.term ==` comparison against parsed text would fail, and `holes_of` would
not see a parsed hole at all. Measured on the first run of the test file."""
hole(i::Int)::Atom = Expression(Atom[Sym(HOLE), Grounded(i)])

"The index of a hole, accepting either the reader's `Grounded{Int}` or a symbolic digit."
function _hole_index(a::Atom)::Int
    h = (a::Expression).children[2]
    h isa Grounded && (h::Grounded).value isa Integer && return Int((h::Grounded).value)
    h isa Sym && return something(tryparse(Int, String((h::Sym).name)),
        error("GSLT context: hole index is not an integer in $(a)"))
    error("GSLT context: malformed hole $(a)")
end

"""A CONTEXT — a term with numbered holes. The multimorphisms of Definition 5.1.

`arity` is the number of holes, so a context is a multimorphism `I₁ … Iₙ → I`, where the `Iᵢ` are the
interfaces of its holes and `I` the interface of the whole. A 1-ary context is an ordinary unary
morphism; the 0-ary case is a closed term."""
struct GContext
    term::Atom
end

"Every hole index occurring in the context, ascending."
function holes_of(c::GContext)::Vector{Int}
    out = Int[]
    walk(a::Atom) = begin
        if is_hole(a)
            push!(out, _hole_index(a))
        elseif a isa Expression
            for x in (a::Expression).children
                walk(x)
            end
        end
        nothing
    end
    walk(c.term)
    sort!(unique!(out))
end

"""The number of holes — the context's arity as a multimorphism.

⚠️ COUNTS DISTINCT INDICES, NOT OCCURRENCES. `(f (Hole 1) (Hole 1))` is a UNARY context that uses its
input twice, not a binary one. That is the multicategory reading and it is also the one that makes
plugging well-defined: filling input 1 fills both positions."""
arity(c::GContext)::Int = length(holes_of(c))

"The identity context `(Hole 1)` — plugging into it, or it into a hole, changes nothing."
identity_context()::GContext = GContext(hole(1))

"""
    plug_term(c, i, t) -> GContext

Fill hole `i` with the TERM `t`. Every occurrence of `(Hole i)` is replaced.
"""
function plug_term(c::GContext, i::Int, t::Atom)::GContext
    subst(a::Atom)::Atom =
        if is_hole(a)
            (_hole_index(a) == i ? t : a)
        elseif a isa Expression
            Expression(Atom[subst(x) for x in (a::Expression).children])
        else
            a
        end
    GContext(subst(c.term))
end

"""
    plug(outer, i, inner) -> GContext

COMPOSITION — plug `inner` into hole `i` of `outer`.

⚠️ THE RESULT'S INPUTS ARE RENUMBERED, and the scheme is forced by the UNIT LAWS, not chosen. `inner`'s
inputs take the POSITION the consumed hole occupied, and `outer`'s later inputs shift up by
`arity(inner) - 1`:

    outer input at position p < pos  →  p
    inner input at position q        →  pos - 1 + q
    outer input at position p > pos  →  p - 1 + arity(inner)

MEASURED: the first version simply shifted `inner`'s holes above `outer`'s maximum, which is
collision-free and WRONG — `plug(c, 1, identity)` returned `(App (Hole 2) a)` for `(App (Hole 1) a)`,
so the right unit law failed. Collision-freedom is necessary and not sufficient; the numbering has to
be the one the laws demand.

Renumbering happens in a SINGLE pass that builds the result term, so `outer`'s holes and `inner`'s can
never transiently collide the way a two-step renumber-then-substitute would allow.

Arity: `arity(outer) - 1 + arity(inner)`.
"""
function plug(outer::GContext, i::Int, inner::GContext)::GContext
    oh = holes_of(outer)
    pos = findfirst(==(i), oh)
    pos === nothing && error("GSLT context: no hole $i to plug (holes: $oh)")
    ih = holes_of(inner)
    n = length(ih)

    inmap = Dict{Int, Int}(k => pos - 1 + q for (q, k) in enumerate(ih))
    outmap = Dict{Int, Int}()
    for (p, k) in enumerate(oh)
        k == i && continue
        outmap[k] = p < pos ? p : p - 1 + n
    end

    renum_inner(a::Atom)::Atom =
        if is_hole(a)
            hole(inmap[_hole_index(a)])
        elseif a isa Expression
            Expression(Atom[renum_inner(x) for x in (a::Expression).children])
        else
            a
        end
    filled = renum_inner(inner.term)

    build(a::Atom)::Atom =
        if is_hole(a)
            (_hole_index(a) == i ? filled : hole(outmap[_hole_index(a)]))
        elseif a isa Expression
            Expression(Atom[build(x) for x in (a::Expression).children])
        else
            a
        end

    GContext(build(outer.term))
end

"""An INTERFACE — an object of the context multicategory (Definition 5.1).

Two of the three components the deck names. See the file header for why the third is absent rather
than guessed:

    sort           the sort of the hole, read off the ENCLOSING CONSTRUCTOR's signature in Σ
    binding_stage  how many binders the hole sits under — `ItemAbs` positions on the way down
    ⟨interaction surface⟩  NOT MODELLED — our presentations carry no interaction relation

`sort === nothing` means the hole sits somewhere Σ does not assign a sort (under an undeclared head,
or at the root), which is information, not a failure."""
struct GInterface
    sort::Union{Base.Symbol, Nothing}
    binding_stage::Int
end

"""Turn a term into a context, checking that its holes are well-formed and that `Hole` is not also a
declared constructor of `p` — a presentation that builds `(Hole …)` as data would otherwise get
contexts whose holes are its own terms."""
function context_of(p::GPresentation, t::Atom)::GContext
    for r in p.terms
        (r.label::LabelId).name === HOLE &&
            error(
                "GSLT context: presentation `$(p.name)` declares a constructor named `$HOLE`, " *
                "which is the reserved hole marker"
            )
    end
    GContext(t)
end

"""
    interface_at(p, c, i) -> GInterface

The interface of hole `i`: the sort Σ gives that position, and the number of binders above it.

⚠️ USES THE FIRST OCCURRENCE. A context may use one input in several positions with DIFFERENT
binding stages — `(Lam x (Hole 1))` and `(App (Hole 1) a)` in the same term. The multicategory says an
input has ONE interface, so a context whose occurrences disagree is not well-formed; `disagrees` below
reports it rather than silently taking one."""
function interface_at(p::GPresentation, c::GContext, i::Int)::GInterface
    found = GInterface[]
    binders = Set(Base.Symbol[(r.label::LabelId).name for r in binders_of(p)])
    rules = Dict{Base.Symbol, GRule}((r.label::LabelId).name => r for r in p.terms)

    function walk(a::Atom, stage::Int, sort::Union{Base.Symbol, Nothing})
        if is_hole(a)
            _hole_index(a) == i && push!(found, GInterface(sort, stage))
            return nothing
        end
        a isa Expression || return nothing
        ch = (a::Expression).children
        isempty(ch) && return nothing
        h = ch[1]
        hname = h isa Sym ? (h::Sym).name : nothing
        r = hname === nothing ? nothing : get(rules, hname, nothing)
        under = hname !== nothing && hname in binders
        for (k, x) in enumerate(ch)
            k == 1 && continue
            # the sort of argument k-1, when Σ declares this constructor
            s = nothing
            if r !== nothing && k - 1 <= length(r.items)
                it = r.items[k - 1]
                cat = if it isa ItemNonTerminal
                    (it::ItemNonTerminal).cat
                elseif it isa ItemBind
                    (it::ItemBind).cat
                elseif it isa ItemAbs && (it::ItemAbs).item isa ItemNonTerminal
                    ((it::ItemAbs).item::ItemNonTerminal).cat
                else
                    nothing
                end
                s = cat === nothing ? nothing : cat_name(cat)
            end
            # a hole under an `ItemAbs` position of a binding constructor is one stage deeper
            deeper =
                under && r !== nothing && k - 1 <= length(r.items) &&
                r.items[k - 1] isa ItemAbs
            walk(x, stage + (deeper ? 1 : 0), s)
        end
        nothing
    end
    walk(c.term, 0, nothing)

    isempty(found) && error("GSLT context: no hole $i in $(c.term)")
    all(==(found[1]), found) ||
        error(
            "GSLT context: hole $i occurs with DISAGREEING interfaces $(unique(found)) — a " *
            "multicategory input has one interface, so this context is not well-formed"
        )
    found[1]
end

"How many binders hole `i` sits under — the `binding_stage` component, on its own."
binding_stage(p::GPresentation, c::GContext, i::Int)::Int =
    interface_at(p, c, i).binding_stage

end # module CompilerGSLTMulticategory
