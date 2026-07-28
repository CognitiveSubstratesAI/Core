# GSLT.jl — the GSLT theory front-end of MeTTa-IL (F1R3FLY layered track).
#
# Grounded in the ACTUAL upstream (F1R3FLY/MeTTaIL `GSLT/src/test/module/*.module`): MeTTa-IL is a
# MODULAR theory algebra — theories are built compositionally from parts:
#   * EXTENSION:   Theory Monoid(s: EmptySet) { s  Terms{…} Equations{…} }   (extend a parent)
#   * UNION:       {add \/ mult}   (Rig = CommutativeMonoid ∪ Monoid;  Ring = Rig ∪ AbelianGroup)
#   * REPLACEMENT: [pos] One . Elem => Zero . Elem   (rename/derive a constructor across the theory)
#
# PRIMUS-native (s-expr, NOT BNFC — GSLT `Mult . Elem ::= "(" Elem "*" Elem ")"` becomes the type-sig
# `(: Mult (-> Elem Elem Elem))`; the s-expr IS the syntax). A theory bundles `terms`/`equations`/
# `rewrites` with `extends`/`union`/`replacements`; `flatten` resolves the algebra → the complete
# rewrite set → the MeTTa-IL rewrite lane (MeTTaIL.jl) → MM2 → MORK, bisimulation-gated.
#
# Surface:
#   (theory NAME ()                 (terms …) (equations …) (rewrites …))   ; base
#   (theory NAME (extends P)        … )                                     ; extension
#   (theory NAME (union A B)        … )                                     ; composition
#   (theory NAME (extends P) (replacements (=> Old New) …) … )              ; replacement
#
# Follow-ons: theory parameterization (`Theory T(p: P)` — work over any P-instance), the BNF grammar /
# Terms front-end, Equations-as-rewrite orientation, replacement argument-position permutation `[0,1]`.

struct Theory
    name::String
    base::Tuple{Symbol, Vector{String}}            # (:none,[]) | (:extends,[P]) | (:union,[A,B,…])
    params::Vector{Tuple{String, String}}          # (param-name, default-theory) — GSLT `Theory T(p: P)`
    terms::Vector{String}
    equations::Vector{String}
    rewrites::Vector{String}
    replacements::Vector{Tuple{String, String}}    # (old-ctor, new-ctor)
end

_theory_section(args, key) =
    (i = findfirst(s -> mm2_head(s) == key, args)) === nothing ? String[] : mm2_expr_args(args[i])[2:end]

"Parse one `(theory NAME BASE SECTIONS…)` definition."
function parse_theory(def::AbstractString)::Theory
    a = mm2_expr_args(def)
    (length(a) >= 3 && a[1] == "theory") || error("parse_theory: expected (theory NAME BASE …), got: $def")
    name = a[2]
    bspec = mm2_expr_args(a[3])
    base = isempty(bspec) ? (:none, String[]) :
           bspec[1] == "extends" ? (:extends, String[bspec[2]]) :
           bspec[1] == "union" ? (:union, String[bspec[2:end]...]) :
           error("parse_theory: base must be (), (extends P), or (union A B…); got '$(a[3])'")
    sections = a[4:end]
    reps = Tuple{String, String}[]
    for r in _theory_section(sections, "replacements")
        ra = mm2_expr_args(r)
        (ra[1] == "=>" && length(ra) == 3) || error("replacement must be (=> Old New), got: $r")
        push!(reps, (ra[2], ra[3]))
    end
    params = Tuple{String, String}[]
    for p in _theory_section(sections, "params")
        pa = mm2_expr_args(p)
        length(pa) == 2 || error("param must be (name Theory), got: $p")
        push!(params, (pa[1], pa[2]))
    end
    Theory(name, base, params,
           _theory_section(sections, "terms"),
           _theory_section(sections, "equations"),
           _theory_section(sections, "rewrites"),
           reps)
end

"Parse all `(theory …)` definitions in a program → name→Theory env."
function load_theories(program::AbstractString)::Dict{String, Theory}
    env = Dict{String, Theory}()
    for (bang, f) in mm2_split_forms(program)
        (bang || mm2_head(f) != "theory") && continue
        t = parse_theory(strip(f)); env[t.name] = t
    end
    env
end

# rename constructor `old`→`new` as a whole token (not substring) across an s-expr string
_rename_ctor(s::AbstractString, old::AbstractString, new::AbstractString) =
    replace(s, Regex("(?<![\\w\\-])" * Base.escape_string(old) * "(?![\\w\\-])") => new)

"""
    theory_flatten(name, env; bindings=Dict()) -> (; terms, equations, rewrites)

Resolve the theory algebra: collect the base's content (extension chain / union), append this theory's
own content, then apply this theory's replacements (constructor renames) across the whole result.
Base references that name a PARAMETER (`Theory T(p: P)`) resolve through `bindings` (an instantiation
override), else the param's default theory, else the reference is taken as a direct theory name.
"""
function theory_flatten(name::AbstractString, env::Dict{String, Theory};
                        bindings::Dict{String, String} = Dict{String, String}())
    haskey(env, name) || error("theory_flatten: unknown theory '$name'")
    t = env[name]
    function resolve(ref)                                   # param override > param default > direct name
        haskey(bindings, ref) && return bindings[ref]
        i = findfirst(p -> p[1] == ref, t.params)
        i === nothing ? ref : t.params[i][2]
    end
    terms = String[]; eqs = String[]; rws = String[]
    if t.base[1] == :extends
        b = theory_flatten(resolve(t.base[2][1]), env); append!(terms, b.terms); append!(eqs, b.equations); append!(rws, b.rewrites)
    elseif t.base[1] == :union
        for p in t.base[2]
            b = theory_flatten(resolve(p), env); append!(terms, b.terms); append!(eqs, b.equations); append!(rws, b.rewrites)
        end
    end
    append!(terms, t.terms); append!(eqs, t.equations); append!(rws, t.rewrites)
    for (old, new) in t.replacements
        terms = String[_rename_ctor(s, old, new) for s in terms]
        eqs   = String[_rename_ctor(s, old, new) for s in eqs]
        rws   = String[_rename_ctor(s, old, new) for s in rws]
    end
    (terms = unique(terms), equations = unique(eqs), rewrites = unique(rws))
end

"The flattened rewrites of a theory (the executable reduction relation)."
theory_rewrites(name::AbstractString, env::Dict{String, Theory})::Vector{String} =
    theory_flatten(name, env).rewrites

"""
    theory_instantiate(name, env, overrides) -> (; terms, equations, rewrites)

Flatten a parameterized theory with its parameters bound to concrete theories (`overrides`, a
param-name→theory map). Unbound params fall back to their declared default theory.
"""
theory_instantiate(name::AbstractString, env::Dict{String, Theory}, overrides::Dict{String, String}) =
    theory_flatten(name, env; bindings = overrides)

# --- Equation orientation (a-tail) -------------------------------------------------------------------
# Knuth-Bendix orientation is undecidable in general; this is a SOUND, INCOMPLETE fragment: orient
# `(= L R)` as `(~> L R)` only when the RHS has strictly fewer function symbols AND no variable occurs
# more often in the RHS than in the LHS (NON-DUPLICATION). Both halves are load-bearing — the symbol
# count alone is a measure on the RULE, and substitution multiplies each variable's instance, so a
# duplicating rule can grow the term even while the rule shrinks. This orients
# unit/simplification laws and FLAGS the rest (commutativity, associativity, distributivity — equal-or-
# larger RHS) as non-orientable; those need AC-matching or an explicit reduction order (LPO/KBO), the
# deeper follow-on. Oriented rewrites are usable directly by `metta_il_normalize`.
_eq_tokens(s::AbstractString) = filter(!isempty, split(replace(String(s), '(' => ' ', ')' => ' ')))
_eq_vars(s::AbstractString) = Set(t for t in _eq_tokens(s) if startswith(t, "\$"))

"""
    _eq_var_counts(s) -> Dict{String,Int}

Per-variable OCCURRENCE COUNTS, not the variable SET.

The orientation test used `issubset(_eq_vars(rhs), _eq_vars(lhs))` — "the RHS introduces no new
variables" — and claimed that plus a shrinking symbol count "guarantees termination". It does not:
`issubset` is a SET test, so it cannot see DUPLICATION. Measured before this fix,
`(= (f (h \$x)) (g \$x \$x))` was ORIENTED:

    symbols 1 < 2 ✓      vars {\$x} ⊆ {\$x} ✓      ⇒ accepted as terminating

but it duplicates `\$x`, and counting symbols in the RULE is only a termination measure when
variables are not duplicated — substitution multiplies each variable's instance. With σ = {\$x ↦ t}:

    |Lσ| = 2 + |t|        |Rσ| = 1 + 2·|t|        ⇒ the RHS is BIGGER once |t| > 1

so the rewrite can grow the term without bound. The required side condition is the standard
non-duplication one: **for every variable, occurrences in the RHS ≤ occurrences in the LHS.**
That subsumes the old "no new variables" test (a fresh variable has 0 occurrences on the left and
≥1 on the right, so it fails the count test too).
"""
function _eq_var_counts(s::AbstractString)::Dict{String, Int}
    counts = Dict{String, Int}()
    for t in _eq_tokens(s)
        startswith(t, "\$") || continue
        counts[String(t)] = get(counts, String(t), 0) + 1
    end
    counts
end

"True iff no variable occurs more often in `rhs` than in `lhs` (non-duplication)."
function _eq_non_duplicating(lhs::AbstractString, rhs::AbstractString)::Bool
    lc = _eq_var_counts(lhs)
    all(kv -> kv.second <= get(lc, kv.first, 0), _eq_var_counts(rhs))
end
_eq_symbols(s::AbstractString) = count(t -> !startswith(t, "\$"), _eq_tokens(s))

"""
    theory_orient_equations(name, env) -> (; oriented, flagged)

Orient a flattened theory's equations into terminating rewrites where provable. `oriented` are
`(~> L R)` rewrites (RHS strictly fewer symbols, no new vars); `flagged` are equations left
un-oriented (commutativity/associativity/…), reported honestly rather than silently dropped.
"""
function theory_orient_equations(name::AbstractString, env::Dict{String, Theory})
    oriented = String[]; flagged = String[]
    for eq in theory_flatten(name, env).equations
        a = mm2_expr_args(eq)
        if length(a) == 3 && a[1] == "=" &&
           _eq_symbols(a[3]) < _eq_symbols(a[2]) && _eq_non_duplicating(a[2], a[3])
            push!(oriented, "(~> $(a[2]) $(a[3]))")
        else
            push!(flagged, eq)
        end
    end
    (oriented = oriented, flagged = flagged)
end

"""
    theory_run!(cs, data, program, name; steps=1_000_000, saturate=false) -> Vector{String}

Flatten theory `name` from `program`, lower its rewrites, run over `data` on native MORK. `saturate=true`
runs the rewrites to fixpoint (recursive closure) via KBSaturation; default does one exec generation.
"""
function theory_run!(cs::CoreSpace, data::AbstractString, program::AbstractString, name::AbstractString;
                     steps::Int = 1_000_000, saturate::Bool = false,
                     use_magic_sets::Bool = false, magic_query::AbstractString = "", magic_bound::Int = 0)
    env = load_theories(program)
    metta_il_run!(cs, data, join(theory_rewrites(name, env), "\n"); steps = steps, saturate = saturate,
        use_magic_sets = use_magic_sets, magic_query = magic_query, magic_bound = magic_bound)
end
