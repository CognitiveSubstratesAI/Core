# src/eval/MorkBridge.jl
#
# Bridge to MORK's native term engine — unification + hygienic substitution over byte-`Expr`s,
# the verified (differential-conformant) replacement for Core's Julia-structural `_unify` and the
# string-`replace` substitution path. This is E1.0: the foundation the rest of E1 builds on.
#
# CRUX (validated 2026-06-11). MORK variables are POSITIONAL — `(source_id, index)`, assigned by
# occurrence order *within an `Expr`*. So parsing a rule's head and body as SEPARATE exprs gives a
# reordered template the wrong indices: `(q $y $x)` applied over `(p $x $y)` vs `(p a b)` wrongly
# yields `(q a b)`. Parsing the WHOLE `(= head body)` as a single `Expr` and splitting it with
# `ee_args!` keeps head and body in one shared variable namespace, so `(q $y $x)` correctly yields
# `(q b a)`. All bridge entry points that span head↔body therefore operate on one parsed rule.

"""
    mork_unify(query, data) -> Union{Dict, Nothing}

Robinson MGU (with occurs-check) of `query` (source 0) against `data` (source 1) via MORK's
`expr_unify`. Accepts `MORK.Expr`s or MORK-syntax s-expression strings (dollar-variable syntax). Returns the
bindings `Dict{ExprVar,ExprEnv}` on success, `nothing` on no match.
"""
function mork_unify(query::MORK.Expr, data::MORK.Expr)
    r = MORK.expr_unify([(MORK.ExprEnv(UInt8(0), UInt8(0), UInt32(0), query),
                          MORK.ExprEnv(UInt8(1), UInt8(0), UInt32(0), data))])
    r isa Dict ? r : nothing
end
mork_unify(q::AbstractString, d::AbstractString) =
    mork_unify(MORK.sexpr_to_expr(String(q)), MORK.sexpr_to_expr(String(d)))

"""
    mork_apply(base::MORK.Expr, offset::Integer, bindings) -> MORK.Expr

Hygienically substitute `bindings` into the source-0 template sub-expression at 0-based byte
`offset` within `base`, via MORK's `expr_apply` (de-Bruijn renaming + cycle handling). Returns the
result as an owned `Expr`.
"""
function mork_apply(base::MORK.Expr, offset::Integer, bindings)
    out = MORK.Expr(Vector{UInt8}(undef, max(length(base.buf) * 4, 64)))
    oz = MORK.ExprZipper(out, 1)
    MORK.expr_apply(MORK.ExprZipper(base, Int(offset) + 1), bindings, oz)
    MORK.Expr(out.buf[1:(oz.loc - 1)])
end

"""
    mork_rule_rewrite(rule, data) -> Union{MORK.Expr, Nothing}  (or stripped String for the string form)

One rewrite step. Split `rule` = `(= head body)` (head and body share the rule's single variable
namespace — see CRUX above), unify `data` against `head`, and apply the bindings to `body`. Returns
the rewritten term, or `nothing` if `rule` isn't a `(= … …)` or `data` doesn't match `head`.
"""
function mork_rule_rewrite(rule::MORK.Expr, data::MORK.Expr)
    args = MORK.ExprEnv[]
    MORK.ee_args!(MORK.ExprEnv(UInt8(0), UInt8(0), UInt32(0), rule), args)
    length(args) >= 3 || return nothing                 # not (= head body)
    head_ee, body_ee = args[2], args[3]                 # both source 0 ⇒ shared var indices
    b = MORK.expr_unify([(head_ee, MORK.ExprEnv(UInt8(1), UInt8(0), UInt32(0), data))])
    b isa Dict || return nothing
    mork_apply(rule, body_ee.offset, b)
end
function mork_rule_rewrite(rule::AbstractString, data::AbstractString)
    r = mork_rule_rewrite(MORK.sexpr_to_expr(String(rule)), MORK.sexpr_to_expr(String(data)))
    r === nothing ? nothing : strip(MORK.expr_serialize(r.buf))
end

# ══════════════════════════════════════════════════════════════════════════════════════════════
# E1.1 — RUNNING TRIE-STORED RULES NATIVELY (the two blockers, measured 2026-07-29)
#
# The trie DOES hold executable rewrite rules: `space_add_all_sexpr!` stores exactly the bytes
# `sexpr_to_expr` produces (verified: `get_val_at(btm, e.buf) !== nothing`), variables land as native
# `Tag(NewVar)`/`Tag(VarRef)`, and `mork_rule_rewrite` rewrites straight from those bytes. Two things
# in CORE — not in MORK — stopped us using that:
#
#   BLOCKER 1 — EVERY read path serializes to TEXT, and the text form is LOSSY for rewriting.
#     `core_atoms` uses `space_dump_all_sexpr` for a root space, and even its prefix branch does
#     `rel_bytes` -> `expr_serialize` -> text. A rule dumped and re-parsed loses its binding
#     structure: `(= (swap $a $b) (pair $b $a))` dumps as `(= (swap $ $) (pair _2 _1))`, and
#     re-parsing that yields NO MATCH (2-var) or `(plus _1 _1)` instead of `(plus N N)` (1-var).
#     MEASURED, same rules, same trie, only the read path differs:
#         via text dump   (dbl N) -> (plus _1 _1) ✗   (swap X Y) -> NO MATCH ✗
#         via byte paths  (dbl N) -> (plus N N)   ✓   (swap X Y) -> (pair Y X) ✓
#
#   BLOCKER 2 — `load_metta!(::CoreSpace)` stores `__var_x` GROUND SYMBOLS, not native vars.
#     That is deliberate (`MeTTaCore.jl:96-100`): MORK's de-Bruijn encoding drops variable NAMES on
#     serialisation, so Core stores `$x` as the named ground symbol `__var_x` to survive the round
#     trip. The cost is that `expr_unify` treats `__var_x` as a CONSTANT, so every stored lib rule is
#     INERT to the native rewriter (`mork_rule_rewrite` returns `nothing` on all of them).
#
# The fix below is ADDITIVE and changes NO storage: keep `__var_x` on disk (names preserved, the
# interpreter's view unchanged) and convert to native vars ON THE REWRITE PATH.
# ══════════════════════════════════════════════════════════════════════════════════════════════

const _CORE_VAR_PREFIX = "__var_"

"""
    mork_native_vars(e::MORK.Expr) -> MORK.Expr

Rewrite Core's `__var_NAME` ground symbols into MORK-native variables, so a rule stored by
`load_metta!(::CoreSpace)` becomes unifiable by `expr_unify`.

First occurrence of a name becomes `Tag(NewVar)` (0xC0); each later occurrence becomes
`Tag(VarRef(k))` (0x80|k) where `k` is that variable's 0-based ordinal among the NewVars — the same
de-Bruijn discipline MORK's own reader produces for `\$x`. Every other byte is copied through.

The scan is a flat pass because the encoding is prefix-free (Expr.jl:5-8):
    Arity      0x00..0x3F  (no payload)
    VarRef     0x80..0xBF  (no payload)
    NewVar     0xC0        (no payload)
    SymbolSize 0xC1..0xFF  (low 6 bits = byte count that FOLLOWS)

⚠️ Pre-existing `Tag(VarRef)` bytes are copied unchanged. A rule may therefore not MIX native
variables with `__var_` symbols — Core's loader never produces such a mix (it writes one or the
other for the whole atom), and mixing would make the back-reference indices inconsistent.
"""
function mork_native_vars(e::MORK.Expr)::MORK.Expr
    src = e.buf
    out = UInt8[]
    sizehint!(out, length(src))
    seen = Dict{String, UInt8}()      # var name -> its 0-based NewVar ordinal
    nvars = UInt8(0)
    i = 1
    @inbounds while i <= length(src)
        b = src[i]
        if b >= 0xC1                                   # SymbolSize(n) + n payload bytes
            n = Int(b & 0x3F)
            name = String(@view src[(i + 1):(i + n)])
            if startswith(name, _CORE_VAR_PREFIX)
                k = get(seen, name, nothing)
                if k === nothing
                    seen[name] = nvars
                    nvars += UInt8(1)
                    push!(out, 0xC0)                   # NewVar — first occurrence
                else
                    push!(out, 0x80 | k)               # VarRef(k) — back-reference
                end
            else
                push!(out, b)
                append!(out, @view src[(i + 1):(i + n)])
            end
            i += 1 + n
        else                                           # Arity / VarRef / NewVar — no payload
            push!(out, b)
            i += 1
        end
    end
    MORK.Expr(out)
end

"""
    core_rule_exprs(cs::CoreSpace) -> Vector{MORK.Expr}

Every `(= head body)` rule in `cs`, as native-variable `MORK.Expr` ready for `mork_rule_rewrite`.

**Reads RAW BYTE PATHS and never calls `expr_serialize`** — that is the whole point (see BLOCKER 1).
Going through the text dump silently mangles variable bindings, which reads as "the rule did not
match" rather than as an error.
"""
function core_rule_exprs(cs::CoreSpace)::Vector{MORK.Expr}
    rules = MORK.Expr[]
    with_read_permit(cs) do
        rz = read_zipper_at_path(cs.inner.btm, cs.prefix)
        while zipper_to_next_val!(rz)
            e = mork_native_vars(MORK.Expr(collect(zipper_path(rz))))
            args = MORK.ExprEnv[]
            try
                MORK.ee_args!(MORK.ExprEnv(UInt8(0), UInt8(0), UInt32(0), e), args)
            catch
                continue                                # not a well-formed expr — skip, don't throw
            end
            length(args) >= 3 || continue               # not a 3-element form
            # keep only `(= _ _)`: the head symbol must be exactly "="
            h = args[1]
            hb = h.base.buf
            o = Int(h.offset) + 1
            (o <= length(hb) && hb[o] >= 0xC1 && Int(hb[o] & 0x3F) == 1 &&
             o + 1 <= length(hb) && hb[o + 1] == UInt8('=')) || continue
            push!(rules, e)
        end
    end
    rules
end

"""
    core_rewrite_step(rules, term) -> Union{MORK.Expr, Nothing}

First rule in `rules` whose head unifies with `term`, applied. `nothing` if none match.

⚠️ TWO MEASURED LIMITS — do not read this as MeTTa's evaluation semantics (an earlier version of
this docstring claimed "committed choice … first match wins, source order"; BOTH halves were false,
measured 2026-07-29):

 1. **"First" is TRIE order, not SOURCE order.** `core_rule_exprs` walks the trie, which is
    byte-lexicographic — the MORK trie does not record insertion order. Loading
    `(= (f \$n) nonzero)` THEN `(= (f 0) zero)` reads back `(= (f 0) zero)` first, and reversing the
    source text changes nothing. So a multi-clause head resolves by byte order, and which clause
    wins is independent of how the program was written.

 2. **One answer, not all.** MeTTa evaluation is nondeterministic. On the same two clauses Core's
    interpreter returns BOTH — `(f 0)` → `Atom[zero, nonzero]`, and their ORDER tracks source order.
    This returns a single rewrite.

Both are pinned by `test_mork_native_rewrite.jl` so they stay visible. Closing #1 needs an insertion
ordinal carried alongside the atom (an encoding decision, not a local fix); closing #2 needs the
step to return all unifying rules.
"""
function core_rewrite_step(rules::Vector{MORK.Expr}, term::MORK.Expr)
    for r in rules
        out = mork_rule_rewrite(r, term)
        out === nothing || return out
    end
    nothing
end

"""
    core_normalize(cs::CoreSpace, term::AbstractString; max_steps=1000) -> String

Rewrite `term` to a fixpoint using the rules stored in `cs`'s trie — the native path, no MM2
translation and no text round-trip between steps.

This is the runtime shape whitepaper Fig-2 draws: MeTTa rules live in the MORK Atomspace and
execution IS metagraph rewriting over them (`docs/specs/Mork/Reflective_Metagraph_Rewriting_spec.md`
§1: *"MeTTa programs ARE metagraph rewrite rules … Execution is metagraph rewriting"*). MM2 stays
what §3.3 says it is — a kernel tier for performance-sensitive algorithms, not the compilation target.

⚠️ TOP-LEVEL ONLY, and PURELY SYNTACTIC. No congruence descent into subterms and no grounded-op
evaluation, so `(+ 1 2)` does not reduce. `metta_il_normalize` has the innermost-subterm driver but
recurses on STRINGS (253 KiB/rewrite measured); merging the two is the next step.

⚠️ Inherits both limits of `core_rewrite_step` — rules are applied in TRIE (byte-lexicographic)
order, not source order, and one rewrite is taken per step rather than all. For a multi-clause head
this is NOT the interpreter's answer set. See that docstring.

Grounded ops, when wired, come from **MORK's own `GROUNDED_REGISTRY`** (`MORK/src/kernel/Sources.jl`),
which Core already populates with ~40 primitives via `register_core_primitives!`
(`Core/src/primitives/Primitives.jl`) — arithmetic included. Not the interpreter's `TOKEN_REGISTRY`:
that is the fallback lane's table and reaching into it from here would invert the standing
compiler-primary directive.
"""
function core_normalize(cs::CoreSpace, term::AbstractString; max_steps::Int = 1000)::String
    rules = core_rule_exprs(cs)
    cur = MORK.sexpr_to_expr(String(term))
    for _ in 1:max_steps
        nxt = core_rewrite_step(rules, cur)
        nxt === nothing && break
        cur = nxt
    end
    strip(MORK.expr_serialize(cur.buf))
end

export mork_native_vars, core_rule_exprs, core_rewrite_step, core_normalize
