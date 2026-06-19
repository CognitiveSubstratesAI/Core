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
