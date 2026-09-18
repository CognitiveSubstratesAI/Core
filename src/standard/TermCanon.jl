# TermCanon.jl — ONE audited variable-renaming walker, with a POLICY per subsystem.
#
# 🔴 THE NEGATIVE EXAMPLE THIS FILE EXISTS TO PREVENT, stated because it had already happened here.
# Core carried TWO independent alpha-canonicalisers, written in different files, months apart, by the
# same hand:
#     `_variant_rename` (Tabling.jl)  Var("_v", 1-based)   the tabling VARIANT KEY
#     `_alpha_canon`    (Eval.jl)     Var("$α", 0-based)   `unique-atom` / `assertAlphaEqualToResult`
# Neither file mentions the other. MEASURED 2026-09-17/18: they produce DIFFERENT representatives for
# every input and induce the SAME partition — i.e. they are the same equivalence relation, implemented
# twice, drifting independently. The whole of this session's root cause is duplication of exactly this
# kind, one level up.
#
# CeTTa reached the same fork and resolved it better than "delete one caller": ONE walker, with a
# POLICY parameter, and its header names the failure it is avoiding — *"two nearly identical VarId map
# implementations drifting apart in separate runtime subsystems"*. That resolution is available TODAY
# and does not wait on BLOCKER 2, which the "both become deletable under positional identity" plan did.
#
# ⚠️ THE MERGE PRESERVES OUTPUT, NOT MERELY THE RELATION. Partition equality proves the two RELATIONS
# agree; it does NOT license changing what either caller returns. `_v` names are live TABLE KEYS, and
# `_v#1` and `$α#1` are deliberately UNEQUAL — measured, and §5o of the BLOCKER 2 note depends on it.
# So each policy reproduces its caller's bytes exactly, and the gate is byte-exact output per caller
# over a corpus, which is STRICTER than the partition equality that motivated the merge.

"""
    CanonPolicy(spelling, first_ordinal)

How one subsystem spells a canonical variable, and where its ordinals start. The ONLY thing the two
canonicalisers ever disagreed about.

⚠️ The spelling is load-bearing, not cosmetic: two canonicalisers using the SAME spelling would make
a variant key and an alpha-canonical form compare EQUAL, which they are not today and must not become
by accident.
"""
struct CanonPolicy
    spelling::String
    first_ordinal::UInt64
end

"Tabling's variant key: `_v`, 1-based. SWI's variant canonicalization (`\$tbl_variant_table`)."
const CANON_VARIANT = CanonPolicy("_v", UInt64(1))

"Alpha-equality for `unique-atom` / `assertAlphaEqualToResult`: `\$α`, 0-based."
const CANON_ALPHA = CanonPolicy("\$α", UInt64(0))

"""
    canon_rename(a, policy, seen=Dict{Var,Var}()) -> Atom

Rename every variable in `a` by FIRST-ENCOUNTER ORDER under `policy`. Alpha-equivalent terms map to
equal terms; non-equivalent ones do not.

`seen` is exposed so a caller can canonicalise several terms in ONE namespace. ⚠️ Both current callers
pass a FRESH map per atom — `_alpha1`'s comment says "each atom canonicalized independently" and
`_variant_rename` allocates internally — and the census confirming that is what made this merge safe.
A future caller that shares the map is doing something different and should say why.
"""
function canon_rename(a::Atom, policy::CanonPolicy, seen::Dict{Var, Var}=Dict{Var, Var}())::Atom
    if a isa Var
        # `get!(f, d, k)` evaluates `f` BEFORE inserting, so `length(seen)` is the pre-insertion count
        # — which is what makes `first_ordinal + length` reproduce both callers' numbering exactly.
        return get!(seen, a) do
            Var(policy.spelling, policy.first_ordinal + UInt64(length(seen)))
        end
    elseif a isa Expression
        return Expression(Atom[canon_rename(c, policy, seen) for c in a.children])
    else
        return a
    end
end
