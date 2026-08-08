# AtomExprBridge.jl — typed `Atom` ⇄ `MORK.Expr`, the LANE-NEUTRAL conversion pair.
#
# ─── WHY THESE ARE NOT ROUTER CODE ───────────────────────────────────────────────────────────────
# `typed_atom_to_expr` / `expr_to_atom` convert between the GRAMMAR's `Atom` (standard/Atoms.jl) and
# MORK's byte `Expr`. That is a substrate boundary, not an MM2 lowering decision, and the consumers
# say so — they are LIVE outside the router:
#
#     space/CoreSpace.jl        typed_atom_to_expr
#     primitives/Primitives.jl  expr_to_atom   (:172)
#     test_grounded_registry_differential.jl · test_mm2_router.jl
#
# MEASURED by the 2026-08-07 audit: without `expr_to_atom`'s de-Bruijn CO-REFERENCE rebuild,
# `!(get-metatype (A B))` regresses to `Symbol`. Deleting or breaking this pair is a live wrong answer
# in the interpreter, nothing to do with MM2 — which is exactly why it must not sit inside a file
# slated for obsolescence.
#
# `const _MM2_ATOM = StandardMeTTa` moves WITH them and stays under its original name: `MM2Router`'s
# `_mm2_is_eq_rule` still reads it, and this file is `include`d BEFORE the router, so that keeps
# working untouched. Renaming the alias is a later cosmetic change, deliberately not bundled here.
#
# ⚠️ THE CO-REFERENCE IS THE POINT. A `VarRef(idx)` returns the SAME `Var` object as the idx-th
# `NewVar`, so `(= (f $x) $x)` round-trips with both `$x` identical — which the lossy `$`/`_N` sexpr
# TEXT dump cannot do. Any future IL/backend that round-trips atoms through MORK needs this, not a
# string path.

# ── typed Atom → MM2 sexpr (the LIVE-eval handoff: load_metta!/eval hold typed Atoms, not strings) ──
const _MM2_ATOM = StandardMeTTa
function _typed_atom_to_expr!(io::IO, a)
    if a isa _MM2_ATOM.Sym
        print(io, a.name)
    elseif a isa _MM2_ATOM.Var
        print(io, "\$", a.name, a.id == 0 ? "" : "#$(a.id)")  # keep #id (mirrors Var's show): DISTINCT Vars with the same base name (post rename_fresh) must NOT collapse into one on MORK's name-based de Bruijn
    elseif a isa _MM2_ATOM.Expression
        print(io, "(")
        for (k, c) in enumerate(a.children); k > 1 && print(io, " "); _typed_atom_to_expr!(io, c); end
        print(io, ")")
    elseif a isa _MM2_ATOM.Grounded
        print(io, a.value)
    else
        print(io, a)
    end
end

"""
    typed_atom_to_expr(atom) -> String

Serialize a typed `StandardMeTTa` `Atom` to the MeTTa sexpr string MORK's parser ingests — the inverse
of parse, for the live-eval handoff (eval holds typed `Atom` objects, not source strings). Variables
emit as `\$name` with the internal `#id` dropped; MORK assigns the byte-level De Bruijn (NewVar/VarRef)
on `space_add_all_sexpr!`, and interned/repeated vars print consistently in first-occurrence order.
Round-trip gated: `mm2_lower_equals(typed_atom_to_expr(parse(rule))) == mm2_lower_equals(rule_string)`.
"""
typed_atom_to_expr(a)::String = (io = IOBuffer(); _typed_atom_to_expr!(io, a); String(take!(io)))

# ── MM2 Expr bytes → typed Atom (the READ-BACK: byte-level, reconstructs de Bruijn CO-REFERENCE) ──
# Inverse of typed_atom_to_expr's write. A NewVar byte mints a fresh Var; a VarRef(idx) reuses the idx-th
# (0-based) introduced Var — so co-referential variables survive the MORK round-trip. The `$`/`_N` SEXPR
# TEXT dump CANNOT express this (it is lossy — faithfully so vs upstream: `_N` re-parses as a symbol),
# which is why Core reached for the `__var_x` workaround. Reading the round-trip-safe BYTES is the fix.
# Symbols route through parse_atom so numeric/bool literals rebuild as Grounded, matching parse.
function _expr_to_atom!(e::MORK.Expr, pos::Base.RefValue{Int}, vars::Vector{_MM2_ATOM.Var})::_MM2_ATOM.Atom
    tag = MORK.byte_item(e.buf[pos[]])
    if tag isa MORK.ExprSymbol
        n = Int(tag.size); b = @view e.buf[(pos[] + 1):(pos[] + n)]; pos[] += 1 + n
        return Eval.parse_atom(String(b))
    elseif tag isa MORK.ExprArity
        k = Int(tag.arity); pos[] += 1
        return _MM2_ATOM.Expression(_MM2_ATOM.Atom[_expr_to_atom!(e, pos, vars) for _ in 1:k])
    elseif tag isa MORK.ExprNewVar
        # id≠0 (source vars are always id 0) ⇒ a synthetic var can NEVER capture a source var spelled
        # `$_0`: distinctness comes from the `id` FIELD, not the name string (the day's whole lesson).
        pos[] += 1; v = _MM2_ATOM.Var("_$(length(vars))", UInt64(length(vars) + 1)); push!(vars, v); return v
    else  # ExprVarRef(idx) — 0-based back-reference to the idx-th introduced var
        pos[] += 1
        return vars[Int(tag.idx) + 1]
    end
end

"""
    expr_to_atom(e::MORK.Expr) -> Atom

Byte-level READER: reconstruct a typed `StandardMeTTa` `Atom` from a MORK `Expr` — the inverse of
`typed_atom_to_expr`, and the piece Core never ported. Rebuilds de-Bruijn CO-REFERENCE: a `VarRef(idx)`
returns the SAME `Var` object as the idx-th `NewVar`, so `(= (f \$x) \$x)` round-trips with both `\$x`
identical — which the lossy `\$`/`_N` sexpr text dump cannot do. Variable names are synthetic (`\$_k`,
introduction order); MeTTa variable identity is positional, not by name.
"""
expr_to_atom(e::MORK.Expr)::_MM2_ATOM.Atom = _expr_to_atom!(e, Ref(1), _MM2_ATOM.Var[])
