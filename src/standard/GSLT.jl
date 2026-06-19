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
    Theory(name, base,
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
    theory_flatten(name, env) -> (; terms, equations, rewrites)

Resolve the theory algebra: collect the base's content (extension chain / union), append this theory's
own content, then apply this theory's replacements (constructor renames) across the whole result.
"""
function theory_flatten(name::AbstractString, env::Dict{String, Theory})
    haskey(env, name) || error("theory_flatten: unknown theory '$name'")
    t = env[name]
    terms = String[]; eqs = String[]; rws = String[]
    if t.base[1] == :extends
        b = theory_flatten(t.base[2][1], env); append!(terms, b.terms); append!(eqs, b.equations); append!(rws, b.rewrites)
    elseif t.base[1] == :union
        for p in t.base[2]
            b = theory_flatten(p, env); append!(terms, b.terms); append!(eqs, b.equations); append!(rws, b.rewrites)
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
    theory_run!(cs, data, program, name; steps=1_000_000) -> Vector{String}

Flatten theory `name` from `program`, lower its rewrites to MM2, run over `data` on native MORK.
"""
function theory_run!(cs::CoreSpace, data::AbstractString, program::AbstractString, name::AbstractString;
                     steps::Int = 1_000_000)
    env = load_theories(program)
    metta_il_run!(cs, data, join(theory_rewrites(name, env), "\n"); steps = steps)
end
