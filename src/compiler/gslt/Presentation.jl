# Presentation.jl — a GSLT presentation as TYPED DATA: G = (Σ, E, R).
#
# ─── WHAT THIS IS AND WHY IT IS NEW ──────────────────────────────────────────────────────────────
# Definition 2.1 (`docs/specs/MeTTaIL/gslt_mettail_summary_spec.md` §1, verbatim from page 5):
#
#     "A triple G = (Σ, E, R): a signature Σ which is IN GENERAL A LAMBDA THEORY, so that terms may
#      contain variables; a set E of equations imposing a structural congruence ≡; and a set R of
#      rewrite rules."
#
# `standard/GSLT.jl` already implements the theory ALGEBRA — extends / union / replacements — ported
# from the upstream `.module` files, and that part is good. What it cannot express is the part that
# makes Σ a LAMBDA theory:
#
#   1. BINDERS.            Its terms are first-order type-sigs, `(: Mult (-> Elem Elem Elem))`.
#                          There is no way to say "this argument binds a variable in that one".
#   2. FRESHNESS.          No `x # Q` side conditions, so alpha-laws cannot be stated.
#   3. PREMISED REWRITES.  Rewrites are flat `(~> LHS RHS)`. A congruence rule is an INFERENCE rule
#                          with a premise, and there was nowhere to put the premise.
#
# Those three are why there is no GSLT presentation of MeTTa anywhere in this tree: MeTTa has `let`
# and lambda (binders) and its reduction relation is defined by congruence rules (premises). Without
# them the triple cannot be written down, and with no presentation there is nothing for the hypercube
# construction to consume — which is why 4 of the 5 generated constructions (type system, cost,
# history, logic) are absent while only the runtime exists.
#
# ─── ADOPTED FROM UPSTREAM, BOTH REPOS, DELIBERATELY ─────────────────────────────────────────────
# The two dev-zone repos are DIFFERENT LAYERS, not versions — mettail-rust is newer by commit date
# (2026-04-06 vs 2026-03-02) but has NO GSLT tree at all, while the Scala `MeTTaIL` repo carries the
# GSLT model, the 8 `.module` presentations, `hypercube.md` and the normative BNFC grammar
# `GSLT/src/main/bnfc/metta_venus.cf` ("MeTTa IL: Language Syntax Definition", 446 lines, whose
# `SpaceInst` algebra is what `mettail_1_0_spec.md` §6 quotes as "MORKL's algebra").
#
#   * MODEL, from `MeTTaIL/GSLT/src/test/module/{UnivAlg,Rholang}.module` — sorts, the theory algebra,
#     freshness side conditions (`if x # Q then …`), congruence rules with premises
#     (`RPar1 : let Src ~> Tgt in (PPar Src Q) ~> (PPar Tgt Q)`).
#   * NOTATION, from `mettail-rust/languages/src/lambda.rs` — strictly clearer for the same content:
#         Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
#         AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
#     `^x.body` is the binder; `| premise |- conclusion` is the inference rule.
#
# ADOPTED, NOT TRANSLITERATED (standing project rule). The upstream surface is BNFC/Rust-macro; ours
# is s-expressions, because in MeTTa the s-expr IS the syntax. Concretely, a binder extends the
# type-sig convention `standard/GSLT.jl` already uses rather than replacing it:
#
#     upstream   Lam . ^x.body:[Term -> Term] |- … : Term
#     ours       (: Lam (-> (bind Term Term) Term))
#
# so `(bind A B)` is the sort of "an A-binder scoping a B" — the higher-order sort `[A -> B]`. A
# first-order signature stays exactly as it is today; nothing existing has to change.
#
# ─── SCOPE OF THIS FILE ──────────────────────────────────────────────────────────────────────────
# The DATA MODEL only: hold a presentation and answer structural questions about it. No hypercube, no
# generation, no lowering — those CONSUME a presentation and cannot be built before one can be
# written down. Terms are the grammar's own `StandardMeTTa.Atom`, not strings: a presentation is
# surface-level data, and SPECMAP C7's standing criticism of this tree is that its "IL" is
# `AbstractString` → `String` throughout.
module CompilerGSLTPresentation

using ..StandardMeTTa: Atom

export GSort, GBind, GArg, GCtor, GFresh, GEquation, GRewrite, GPresentation
export binders_of, is_lambda_theory, ctor_arity, declared_sorts_used

# ── Σ: sorts and the arguments a constructor takes ───────────────────────────────────────────────

"A plain (first-order) sort occurrence, e.g. `Term` in `(: App (-> Term Term Term))`."
struct GSort
    name::Base.Symbol
end

"""A BINDING argument — upstream `^x.body:[A -> B]`, ours `(bind A B)`.

`var_sort` is the sort of the bound variable, `body_sort` the sort it scopes over. This is the single
construct that makes Σ a LAMBDA theory rather than a first-order signature, and its absence is why
`standard/GSLT.jl` cannot present any language with `let`, lambda, `new` or `for`."""
struct GBind
    var_sort::Base.Symbol
    body_sort::Base.Symbol
end

"An argument position: either a plain sort or a binder. A closed two-case union — union-splits, so no `Any`."
const GArg = Union{GSort, GBind}

"""A term constructor: label, argument sorts (plain or binding), result sort.

Upstream `Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term` also carries CONCRETE SYNTAX
(`"lam " x "." body`). We deliberately drop it: in MeTTa the s-expr IS the syntax, so a separate
concrete grammar would be a second source of truth for the same information."""
struct GCtor
    label::Base.Symbol
    args::Vector{GArg}
    result::Base.Symbol
end

ctor_arity(c::GCtor)::Int = length(c.args)

# ── E: equations, with the freshness side conditions alpha-laws need ─────────────────────────────

"""A freshness condition — upstream `if x # Q then …`, ours `(fresh x Q)`.

Read "`var` does not occur free in `term`". Scope-extrusion laws are unstateable without it: the
Rholang presentation's `if x # Q then (PPar (PNew x P) Q) == (PNew x (PPar P Q))` is exactly this
shape, and it is one of the four equations giving the rho calculus its structural congruence."""
struct GFresh
    var::Base.Symbol
    term::Base.Symbol
end

"An equation of the structural congruence ≡, guarded by zero or more freshness conditions."
struct GEquation
    lhs::Atom
    rhs::Atom
    conditions::Vector{GFresh}
end

# ── R: rewrites AS INFERENCE RULES ───────────────────────────────────────────────────────────────

"""A rewrite rule with PREMISES — upstream `AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N)`.

`premises` is a list of `(src, tgt)` rewrites that must hold for the conclusion to fire. An empty
list is an ordinary axiom (`Beta`), which is all `standard/GSLT.jl` can currently represent.

THE POINT: congruence — "reduction happens inside any context" — IS a premised rule. A flat
`(~> LHS RHS)` cannot say it, so a flat rewrite set can only ever describe TOP-LEVEL reduction. That
is the difference between presenting a calculus and listing some rewrites."""
struct GRewrite
    label::Base.Symbol
    premises::Vector{Tuple{Atom, Atom}}
    src::Atom
    tgt::Atom
end

"""A GSLT presentation: G = (Σ, E, R), where Σ is `sorts` + `ctors`.

⚠️ KNOWN GAP — `literals`. The upstream macro parses SIX sections, not five
(`mettail-rust/macros/src/ast/language.rs:421-491`): `name · types · literals · terms · equations ·
rewrites`. `literals` declares GROUNDED carrier types with their lexical syntax —
`![i64] as Int`, `![Vec<Proc>] as List ["[", "]", ","]` — each with a regex `pattern` and an `eval`
block. There is no slot for them here.

That is fine for `Lambda` and `Monoid`, which are pure term algebras. It is NOT fine for MeTTa,
whose presentation must account for grounded atoms (`GROUNDED_INT`/`FLOAT`/`STRING`/`BOOL` in
`Eval.jl`) — so this has to exist before `MeTTa.module` can be written, and it is recorded here
rather than discovered again later. Deliberately not stubbed: an empty field would read as "handled"."""
struct GPresentation
    name::Base.Symbol
    sorts::Vector{Base.Symbol}
    ctors::Vector{GCtor}
    equations::Vector{GEquation}
    rewrites::Vector{GRewrite}
end

"Every constructor that binds — i.e. the part of Σ that makes it a lambda theory."
binders_of(p::GPresentation)::Vector{GCtor} =
    GCtor[c for c in p.ctors if any(a -> a isa GBind, c.args)]

"""Is Σ a LAMBDA theory (Definition 2.1's "in general"), or merely first-order?

A presentation with no binding constructor is a first-order signature. That is legal — `Monoid` and
`Rig` are — but it cannot present MeTTa, and it is what every theory currently in this tree is."""
is_lambda_theory(p::GPresentation)::Bool = !isempty(binders_of(p))

"""Every sort NAME mentioned by Σ's constructors, whether or not it was declared.

Used to catch the upstream's own negative-test class: `GSLT/src/test/module/bad/` ships
`ReplacementShadows.module` and `RepeatLabel.module` precisely because a presentation can be
malformed, and a presentation that silently accepts nonsense generates nonsense apparatus."""
function declared_sorts_used(p::GPresentation)::Set{Base.Symbol}
    used = Set{Base.Symbol}()
    for c in p.ctors
        push!(used, c.result)
        for a in c.args
            if a isa GSort
                push!(used, a.name)
            else
                push!(used, (a::GBind).var_sort); push!(used, (a::GBind).body_sort)
            end
        end
    end
    used
end

end # module CompilerGSLTPresentation
