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
        for (k, c) in enumerate(a.children)
            k > 1 && print(io, " ")
            _typed_atom_to_expr!(io, c)
        end
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
typed_atom_to_expr(a)::String =
    (io=IOBuffer(); _typed_atom_to_expr!(io, a); String(take!(io)))

# ── MM2 Expr bytes → typed Atom (the READ-BACK: byte-level, reconstructs de Bruijn CO-REFERENCE) ──
# Inverse of typed_atom_to_expr's write. A NewVar byte mints a fresh Var; a VarRef(idx) reuses the idx-th
# (0-based) introduced Var — so co-referential variables survive the MORK round-trip. The `$`/`_N` SEXPR
# TEXT dump CANNOT express this (it is lossy — faithfully so vs upstream: `_N` re-parses as a symbol),
# which is why Core reached for the `__var_x` workaround. Reading the round-trip-safe BYTES is the fix.
# Symbols route through parse_atom so numeric/bool literals rebuild as Grounded, matching parse.
function _expr_to_atom!(
    e::MORK.Expr, pos::Base.RefValue{Int}, vars::Vector{_MM2_ATOM.Var}
)::_MM2_ATOM.Atom
    tag = MORK.byte_item(e.buf[pos[]])
    if tag isa MORK.ExprSymbol
        n = Int(tag.size)
        b = @view e.buf[(pos[] + 1):(pos[] + n)]
        pos[] += 1 + n
        return Eval.parse_atom(String(b))
    elseif tag isa MORK.ExprArity
        k = Int(tag.arity)
        pos[] += 1
        return _MM2_ATOM.Expression(
            _MM2_ATOM.Atom[_expr_to_atom!(e, pos, vars) for _ in 1:k]
        )
    elseif tag isa MORK.ExprNewVar
        # id≠0 (source vars are always id 0) ⇒ a synthetic var can NEVER capture a source var spelled
        # `$_0`: distinctness comes from the `id` FIELD, not the name string (the day's whole lesson).
        pos[] += 1
        v = _MM2_ATOM.Var("_$(length(vars))", UInt64(length(vars) + 1))
        push!(vars, v)
        return v
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

# ══════════════════════════════════════════════════════════════════════════════════════════════════
# atom_to_expr — typed Atom → MORK `Expr` BYTES, with no text hop. The missing half of this pair.
#
# ⚠️ NAME COLLISION, READ THIS FIRST. `typed_atom_to_expr` (above) returns a **String** despite its
# name — it renders sexpr TEXT and lets `space_add_all_sexpr!` do the byte encoding. THIS function
# returns bytes. The pair that is actually symmetric is `atom_to_expr` ⇄ `expr_to_atom`.
#
# WHY IT IS NEEDED. `MorkBridge.jl`'s BLOCKER 2: Core stores `$x` as the ground symbol `__var_x`
# because MORK's de Bruijn encoding drops variable NAMES on serialisation, so `expr_unify` sees a
# CONSTANT and every stored lib rule is inert to the native rewriter. Going Atom → bytes directly
# emits `NewVar`/`VarRef` tags at encode time, so the variable survives storage.
#
# 🔴 WHAT THIS DOES *NOT* CLAIM. Core's `Atom` model still has no MORK-variable type. A `Var` is
# translated into tags HERE, at encode time. "We can now store variables" is true; "Core represents
# MORK variables" is not.
#
# ─── THE ENCODING CONTRACT (spec, not code — it exists nowhere else) ──────────────────────────────
# `MORK.wiki/Data-in-MORK.md` §"Constraints on MORK data types" gives the whole tag space:
#     0b_00_......  Arity      (remaining bits = arity, 0..=63)
#     0b_01_......  reserved for future use
#     0b_10_......  VarRef     (remaining bits = a De Bruijn LEVEL, 0..=63)
#     0b_11_......  Symbol (non-zero length 1..=63) or, at 0b_11_00_00_00 exactly, NewVar
# Four live classes; there is NO grounded tag — MORK grounding is dispatch BY NAME over ordinary
# symbols (`MORK/src/kernel/Sources.jl`: "MORK kernel itself has no grounding"). So a `Grounded`
# encodes as a Symbol, exactly as `Sym` does.
#
# 🔑 LEVELS, NOT INDICES — and the wiki is explicit that these are easy to confuse:
#     "variable references are relative to the total number of introduced bindings TO THE LEFT …
#      De Bruijn LEVELS (not to be confused with De Bruijn INDICES, which are relative to the most
#      recent bindings to the left) … `[2] &0 $` would be a syntax error, the reference precedes
#      the binding."
# VERIFIED by execution against `sexpr_to_expr`, both orders:
#     (f $x $y $x $y) -> [5] <f> $ $ &0 &1        (g $a $b $b $a) -> [5] <g> $ $ &1 &0
# The ordinal tracks the VARIABLE, not the distance; indices would swap both.
#
# ⚠️ CONSEQUENCE: THIS CANNOT BE COMPOSITIONAL. A level is absolute, so a subterm's `VarRef(k)`
# depends on how many bindings appeared to its left in the WHOLE expression. Encoding children
# independently and concatenating is WRONG. Hence one pre-order pass threading `nvars`.
#
# 🔴 VARIABLE IDENTITY IS name+id, NOT name. `typed_atom_to_expr` above emits `$name#id` and says
# why: "DISTINCT Vars with the same base name (post rename_fresh) must NOT collapse into one on
# MORK's name-based de Bruijn". Keying levels on `name` alone is VARIABLE CAPTURE — valid-looking
# bytes that decode to the wrong term, and byte-equality against the text path would NOT catch it
# (that path carries the `#id`).
#
# ─── DECLINES, never throws and never wraps ──────────────────────────────────────────────────────
# Returns a REASON, the `_unroundtrippable` idiom (`Union{Nothing,String}`), because a bare count is
# not actionable. The 64-variable ceiling is a WHOLE-EXPRESSION property that `item_byte` cannot
# catch — it asserts `VarRef.idx < 64` per tag, not the COUNT of distinct bindings. The spec:
# "There is no way to store a singular expression with more than 64 free variables … the limit is on
# a STORABLE EXPRESSION, but not necessarily for a computation, a transaction, or the space of all
# expressions." Masking instead of declining wraps ACROSS a tag boundary (64 & 0x3f == 0 ⇒ NewVar) —
# the CID incident, `Expr.jl:57-63`.
# ══════════════════════════════════════════════════════════════════════════════════════════════════

"Result of encoding an `Atom` to MORK bytes. Exactly one of `expr`/`declined` is non-`nothing`."
struct AtomEncoding
    expr::Union{MORK.Expr, Nothing}
    declined::Union{Nothing, String}      # a REASON, never a bare flag
end

# Variable identity key — name AND id. See the name+id note above; `id == 0` is a source var.
#
# ⚠️ COST, STATED SO NOBODY OPTIMIZES IT BEFORE MEASURING: this builds a `String` per VAR OCCURRENCE
# (and `get`/`setindex!` hash it), so a rule with many variable mentions allocates once per mention.
# That is the obvious inefficiency and it is deliberately left alone — the correct key is a
# `(name, id)` tuple, which allocates nothing and hashes directly, but switching it is a change to
# the identity relation and belongs with a measurement, not with the first version. No caller is on
# a hot path today: `atom_to_expr` runs at INGEST, not per rewrite step.
_var_key(v)::String = v.id == 0 ? v.name : string(v.name, "#", v.id)

# The single pre-order pass. `nvars` is threaded because levels are ABSOLUTE (see above).
# Returns `nothing` on success or the decline reason.
function _atom_bytes!(
    out::Vector{UInt8}, a, seen::Dict{String, UInt8}, nvars::Base.RefValue{UInt8}
)::Union{Nothing, String}
    if a isa _MM2_ATOM.Expression
        ch = (a::_MM2_ATOM.Expression).children
        length(ch) < 64 ||
            return "arity $(length(ch)) exceeds the Rule of 64 (max 63) — nest instead"
        push!(out, MORK.item_byte(MORK.ExprArity(UInt8(length(ch)))))
        for c in ch
            r = _atom_bytes!(out, c, seen, nvars)
            r === nothing || return r
        end
        return nothing
    elseif a isa _MM2_ATOM.Var
        k = get(seen, _var_key(a), nothing)
        if k === nothing
            nvars[] < 64 || return "more than 64 distinct variables — not a STORABLE expression " *
                                   "(Data-in-MORK: the limit is on storage, not on computation)"
            seen[_var_key(a)] = nvars[]
            push!(out, MORK.item_byte(MORK.ExprNewVar()))
            nvars[] += UInt8(1)
        else
            push!(out, MORK.item_byte(MORK.ExprVarRef(k)))
        end
        return nothing
    elseif a isa _MM2_ATOM.Sym
        return _word_bytes!(out, String((a::_MM2_ATOM.Sym).name))
    elseif a isa _MM2_ATOM.Grounded
        # No grounded TAG exists; a grounded atom encodes as its WORD, exactly as `typed_atom_to_expr`
        # prints it (`print(io, a.value)`) so the two paths agree byte for byte.
        return _word_bytes!(out, string((a::_MM2_ATOM.Grounded).value))
    end
    "unsupported atom kind $(typeof(a))"
end

# A SYMBOL, per grammar §1.1 `SYMBOL ::= WORD` / `GROUNDED ::= STRING | WORD`. A value whose textual
# form is not a single token (a StateCell prints `(State …)`, an EXPRESSION) has no symbol encoding —
# decline rather than emit bytes that decode to something else.
function _word_bytes!(out::Vector{UInt8}, w::AbstractString)::Union{Nothing, String}
    tb = Vector{UInt8}(String(w))
    isempty(tb) && return "empty symbol — SymbolSize is 1..63, length 0 is unrepresentable"
    length(tb) < 64 ||
        return "symbol of $(length(tb)) bytes exceeds the Rule of 64 (max 63) — a long opaque " *
               "string is not a symbol; store digests/paths as VALUES"
    (occursin(' ', w) || occursin('(', w) || occursin(')', w)) &&
        return "textual form `$w` is not a single WORD (grammar §1.1) — no symbol encoding"
    push!(out, MORK.item_byte(MORK.ExprSymbol(UInt8(length(tb)))))
    append!(out, tb)
    nothing
end

"""
    atom_to_expr(atom) -> AtomEncoding

Encode a typed `StandardMeTTa` `Atom` to MORK `Expr` bytes **without the sexpr text hop** — the
byte-level inverse of [`expr_to_atom`](@ref), and the half of this pair Core never had.

Variables become native `NewVar`/`VarRef` tags at encode time, so a rule stored through this path is
unifiable by `expr_unify` rather than inert (`MorkBridge.jl` BLOCKER 2). Levels are De Bruijn LEVELS
and identity is name+id — see the block comment above; both are load-bearing.

Declines with a reason (never throws, never wraps) on: arity ≥ 64, a symbol of 0 or ≥ 64 bytes, a
65th distinct variable, or a value with no single-WORD textual form.

⚠️ Not to be confused with `typed_atom_to_expr`, which returns a **String**.
"""
function atom_to_expr(a)::AtomEncoding
    out = UInt8[]
    r = _atom_bytes!(out, a, Dict{String, UInt8}(), Ref(UInt8(0)))
    r === nothing ? AtomEncoding(MORK.Expr(out), nothing) : AtomEncoding(nothing, r)
end

# ══════════════════════════════════════════════════════════════════════════════════════════════════
# WHY `atom_to_expr` HAS NO CALLER YET — the blocker is the READ side, and it is a FORMAT property
#
# The obvious consumer is `core_add!` (space/CoreSpace.jl:532). Its PREFIXED branch already goes
# byte-level (`sexpr_to_expr(to_sexpr(a))` then `set_val_at!`), so swapping in `atom_to_expr` looks
# like removing a serialize-parse hop. It is not, and the reason is worth reading before trying.
#
# WHAT WOULD CHANGE. Today `to_sexpr` maps `$x -> __var_x`, a NAMED GROUND SYMBOL, deliberately —
# `space/CoreSpaceLoad.jl:198-206` explains it and MEASURES the stakes: "on lib/quantale, 25 of 31
# atoms carry a variable". `atom_to_expr` would instead store native `NewVar`/`VarRef` tags. That
# FIXES `MorkBridge.jl` BLOCKER 2 (a `__var_x` is a CONSTANT to `expr_unify`, so every stored lib
# rule is inert to the native rewriter) — and BREAKS every TEXT reader of that space.
#
# 🔴 THE TEXT FORM IS NOT A BIJECTION, AND THAT IS THE FORMAT, NOT A BUG IN EITHER IMPLEMENTATION.
# The byte encoding strips variable NAMES by design (MORK.wiki Data-in-MORK: "note how variables are
# stripped of their names"). The default renderer therefore cannot put them back, and BOTH defaults
# agree on what it prints instead:
#     upstream  expr/src/lib.rs:1387-1388   NewVar => "$"   VarRef(r) => format!("_{}", r + 1)
#     ours      expr/src/Expr.jl:542-543    NewVar => "$"   VarRef   => "_$(idx + 1)"
# identical, `r + 1` included. Ours is a FAITHFUL PORT. And by the MeTTa grammar
# (`docs/specs/metta grammar/metta_language_spec.md` §1.1, `VARIABLE ::= '$', (CHAR|'"'), {...}`) the
# output is not re-parseable as variables at all: bare `$` is ungrammatical and `_1` matches
# `WORD -> SYMBOL`. So `_is_var_symbol` accepting only `$…`/`__var_…` is CORRECT, and a dumped rule
# silently stops being a rule. `__var_x` is the workaround for the FORMAT.
#
# THE CONSUMERS THAT WOULD BREAK: `space_dump_all_sexpr` (and `core_atoms`, which uses it for a root
# space and `expr_serialize`s even on its prefix branch), and anything gated by `_is_var_symbol`.
# `core_rule_exprs` (MorkBridge.jl) is already safe — it reads RAW BYTE PATHS and never serialises,
# which is exactly why it was written that way, and why `MORK/docs/src/guide/zipper_queries.md`
# recommends byte reads for this class of work.
#
# 🟢 THE PLUGGABLE ESCAPE HATCH NOBODY HAS USED. Upstream's `Expr::serialize2`
# (`expr/src/lib.rs:964`) takes `map_variable: G` — variable rendering is a PARAMETER. Supplying a
# name-generating mapper would make dumps re-parseable and dissolve this blocker without touching
# storage. Evidence it is the intended path: our own `test/conformance/**.expected` files, produced
# by the upstream BINARY, render `$a`/`$b` with co-reference preserved (`(cell 2 $a $a)`), so
# upstream's tooling already judges `$` / `_N` insufficient for round-tripping.
# ⚠️ COST, STATED PRECISELY: this is a FIXTURE MIGRATION, not a semantic divergence. The conformance
# gate compares ATOM SETS; the differential corpus compares DUMPS. Changing the rendering changes the
# dumps, so dump-comparison fixtures must be regenerated. It is a formatting choice upstream itself
# made pluggable — not a correctness risk, and not "diverging from upstream".
#
# ⚠️ A RETRACTION, KEPT BECAUSE THE SHAPE RECURS. On 2026-08-27 this was briefly written up as "our
# serializer is defective, upstream renders `$a`" — inferred from the `.expected` fixtures BEFORE
# opening upstream's serializer, which turned out to be character-identical to ours. Third instance
# this week of partial evidence pointing somewhere while the file that settles it stayed unopened
# (cf. the ZAM name-grep, and the dropped §2.3 mass clause). All three were caught by opening the
# file; none was caught by a test.
# ══════════════════════════════════════════════════════════════════════════════════════════════════
