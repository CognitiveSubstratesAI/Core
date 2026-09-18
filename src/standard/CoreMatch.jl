# CoreMatch.jl — SEAM 1: one matcher, on the MORK term model.
#
# 🔴 THIS EXISTS TO **DELETE** `match_atoms` FROM THE LIVE PATH, NOT TO ADD A SECOND MATCHER.
#
# ⚠️ REVISED 2026-09-18, AND THE REVISION NARROWS THAT GOAL. `core_match` puts the pattern at
# `ExprEnv` source 0 and the data at source 1, so a variable NAME appearing on BOTH sides is TWO
# variables. `match_atoms` has ONE namespace. That is a genuine semantic difference, and a census of
# every `match_atoms` call site found TWO LIVE SITES where both arguments go through the SAME
# bindings, so one namespace is correct BY CONSTRUCTION:
#     Eval.jl:1834      match_types_b   match_atoms(subst(t1, b), subst(t2, b))
#     EmitJulia.jl:200  _bind_step!     match_atoms(subst(step[2], sigma), subst(step[3], sigma))
# `match_types_b`'s own comment states why: "Applying `b` first lets a type variable bound by an
# earlier argument constrain a later one (polymorphism)" — measured live, `(same 1 "x")` against
# `(: same (-> $t $t Bool))` answers `BadArgType 2 Number String`.
# ⇒ `core_match` replaces `match_atoms` where the two sides come from DIFFERENT namespaces (a pattern
# against a freshly renamed stored rule) and NOT where they share one. Closing the gap needs a
# SAME-NAMESPACE MODE — encode both sides into ONE source so a shared name maps to one de Bruijn
# level — or `match_atoms` surviving at those sites. Undecided; it must be settled before the flag
# flips, because it is the difference between one matcher and one-and-a-fraction.
# Say it here because the INTERMEDIATE STATE — two matchers behind a flag — is indistinguishable from
# the duplication this whole effort is removing, and a flag left in place long enough stops reading
# as a migration and starts reading as a permanent option. It is not an option. The end state is
# `core_match` on the live path and `match_atoms` retained only as a DIFFERENTIAL ORACLE and as the
# fallback for inputs MORK declines. If this file still has a flag when the tabling corpus is green,
# that is the bug.
#
# WHAT IT IS. Core keeps its own term model, identity relation, matcher and store alongside MORK's
# (docs/specs/term_model_boundary.md). `match_atoms` (Atoms.jl:309) is the second matcher.
# `expr_unify` is the first. This routes Core's matching through MORK's, so there is one.
#
# ── THE FOUR THINGS THAT MAKE IT SOUND ────────────────────────────────────────────────────────────
#
# 1. 🔴 IT USES `expr_unify_cycle_safe`, NOT `expr_unify`. Upstream: "the unify __function__ does not
#    do full occurs check, this enforces it __after__ apply, making the unify __method__ cycle safe".
#    The two differ by a SAFETY property and the weaker one has the shorter name — which is how it
#    gets picked. MEASURED cost of picking wrong: USink gained 3 conformance probes and REGRESSED
#    `g7_u_occurs` (CODEMAP row 197).
#
# 2. 🔴 BOUND VALUES ARE RECOVERED BY **POSITION**, NEVER BY DECODING BYTES. A binding maps a pattern
#    variable to a subterm OF THE DATA, and we still hold the data `Atom`, so the ORIGINAL object is
#    returned. Decoding would silently downgrade values: of 7 `Grounded` types only Int and Float
#    survive a byte round trip — `true`, `false`, `"hello"`, `:sym` all come back as `Sym` — and the
#    loss is on the ENCODE side ("No grounded TAG exists"), so `Grounded("hello")` and `Sym("hello")`
#    are the SAME BYTES and no decoder can fix it. MEASURED: a dereferenced binding's `ExprEnv.base`
#    IS the data buffer, with `offset` at the bound subterm's first byte.
#
# 3. 🔴 A DECLINE IS PART OF THE CONTRACT, NOT A FALLBACK DETAIL. `atom_to_expr` declines on arity
#    ≥ 64, a symbol of 0 or ≥ 64 bytes, a 65th distinct variable, or a value with no single-WORD form.
#    `core_match` returns `nothing` for those, the caller uses `match_atoms`, and the DIFFERENTIAL
#    COVERS THEM — otherwise the over-limit path is untested exactly where the two engines are
#    guaranteed to differ in mechanism.
#
# 4. 🔴 IT DOES NOT USE MORK's `_deref` REIMPLEMENTED HERE. `MORK.expr_deref` is exported for this.
#    A private deref loop would duplicate AN ASSUMPTION ABOUT THE SOLVED FORM'S SHAPE, which upstream
#    says VARIES (path compression; which end of a var-var equation survived) — invisible until it
#    happens to differ.

"Flag. `false` ⇒ `core_match` is not consulted on any live path. Seam 1 lands OFF and stays OFF until
the differential is green on the tabling corpus. `match_atoms` remains AUTHORITATIVE meanwhile;
disagreements are RECORDED, never acted on — the same shape as the trie-vs-`_ANSWER_TABLE` mirror
the tabling migration used to find its disagreements before they became answers."
# All Atom-layer types live in `StandardMeTTa`; reach them the way AtomExprBridge.jl does.
const _CM_ATOM = StandardMeTTa

const CORE_MATCH_ENABLED = Ref(false)

"""
Recorded disagreements between `core_match` and `match_atoms`. Diagnostic only; never consulted.

Each carries its CLASS, because the two kinds mean opposite things and a corpus run produces too
many to triage by inspection:

* `:namespace` — a variable NAME occurs in BOTH the pattern and the data, so the engines are
  answering different questions (one namespace vs two sources). **Not a defect in either.** The
  count measures HOW MUCH OF `match_atoms` SURVIVES SEAM 1, which is a design quantity.
* `:semantic` — no shared name, so both engines are answering the SAME question and differ.
  **This is the one that must be zero**, and it is the gate on flipping the flag.
"""
const CORE_MATCH_DISAGREEMENTS =
    Vector{NamedTuple{(:pattern, :data, :class, :oracle, :ours),
                      Tuple{Any, Any, Base.Symbol, Any, Any}}}()

"""
    disagreement_class(pattern, data) -> :namespace | :semantic

🔴 COMPUTED FROM THE INPUTS, NOT INFERRED FROM THE OUTPUTS. The discriminator is whether a variable
name is shared across the two sides, by Core's OWN identity relation — which is decidable before
either matcher runs, so a class is never assigned by looking at how the two engines happened to
differ. Classifying from the outputs would make every unexplained disagreement look like the
expected kind.
"""
function disagreement_class(pattern, data)::Base.Symbol
    pv = collect_vars(pattern)
    dv = collect_vars(data)
    any(v -> any(w -> w == v, dv), pv) ? :namespace : :semantic
end

"""
Declines tallied PER CLASS. A decline is a THIRD outcome, not a kind of agreement: `core_match`
never ran, so the pair says nothing about whether the two engines agree.

🔴 REPORTED SEPARATELY BECAUSE AGGREGATING IT HIDES IT. `core_match_differential` returns
`agree = true` for a decline — correct, since a decline is not a disagreement — so a summary that
counts only agreements and disagreements lets "never ran" sit inside "agreed". On the tabling corpus
that matters: goals over the Rule of 64 decline, and they are exactly the ones where the two engines
differ in MECHANISM.
"""
const CORE_MATCH_DECLINES = Dict{Base.Symbol, Int}(:semantic => 0, :namespace => 0)

"""
    core_match_disagreement_counts() -> (; semantic, namespace, declined_semantic, declined_namespace, total)

The corpus gate reads SEVERAL numbers, not one list, and they mean different things:

* `semantic` — **the gate. Must be zero.** Both engines answered the same question and differed.
* `namespace` — a MEASURE, not a failure: how much of `match_atoms` survives seam 1.
* `declined_*` — `core_match` never ran. Neither agreement nor disagreement; evidence about COVERAGE.

⚠️ A corpus summary that reports only `semantic` is not enough: `semantic == 0` with a high decline
count means the gate passed on the pairs that ran, which is a weaker statement than it looks.
"""
core_match_disagreement_counts() = (;
    semantic = count(d -> d.class === :semantic, CORE_MATCH_DISAGREEMENTS),
    namespace = count(d -> d.class === :namespace, CORE_MATCH_DISAGREEMENTS),
    declined_semantic = CORE_MATCH_DECLINES[:semantic],
    declined_namespace = CORE_MATCH_DECLINES[:namespace],
    total = length(CORE_MATCH_DISAGREEMENTS),
)

"Forget every recorded disagreement AND decline, so a corpus run measures ITSELF and not the session
before it. ⚠️ Both, or the decline tally leaks across runs while the disagreements do not."
function reset_core_match_disagreements!()
    empty!(CORE_MATCH_DISAGREEMENTS)
    CORE_MATCH_DECLINES[:semantic] = 0
    CORE_MATCH_DECLINES[:namespace] = 0
    nothing
end

"""
    core_match(pattern::Atom, data::Atom) -> Vector{Bindings} | nothing

Match `pattern` against `data` through MORK's unifier. `nothing` means **DECLINED** — the caller must
fall back to `match_atoms`; it does NOT mean "no match", which is an empty vector.

⚠️ Pattern variables are source 0 and data variables source 1. `expr_unify_cycle_safe` builds that
stack itself so a caller cannot get it wrong: building BOTH at base 0 makes a pattern `\$x` and a data
`\$y` the SAME variable and manufactures a spurious conflict (USink's first defect, which MASKED its
second).
"""
function core_match(pattern, data)
    pe = atom_to_expr(pattern)
    pe.declined === nothing || return nothing
    de = atom_to_expr(data)
    de.declined === nothing || return nothing

    r = MORK.expr_unify_cycle_safe(pe.expr, de.expr)
    r isa MORK.Bindings || return _CM_ATOM.Bindings[]     # no match — includes an occurs rejection

    b = _CM_ATOM.Bindings()
    for level in 0:(length(pe.vars) - 1)
        env = get(r, (UInt8(0), UInt8(level)), nothing)
        env === nothing && continue              # this pattern variable stayed FREE — no entry
        resolved = MORK.expr_deref(r, env)
        val = _recover_subterm(resolved, pe, de)
        val === nothing && return nothing        # could not place it — DECLINE rather than guess
        pv = pe.vars[level + 1]
        val isa _CM_ATOM.Var && val == pv && continue     # a variable bound to itself is not a binding
        push!(b.entries, _CM_ATOM.Binding(pv, val))
    end
    [b]
end

"""
Recover the SOURCE subterm a resolved cursor points at, by POSITION, from whichever encoding owns its
buffer. `nothing` when the cursor's buffer is neither operand — which happens if a future MORK change
starts synthesizing buffers, and is exactly the case that must DECLINE rather than be guessed at.
"""
function _recover_subterm(env, pe::AtomEncoding, de::AtomEncoding)
    buf = env.base.buf
    off = Int(env.offset)
    if buf === de.expr.buf
        return encoding_subterm(de, off)
    elseif buf === pe.expr.buf
        return encoding_subterm(pe, off)
    end
    nothing
end

"""
    core_match_differential(pattern, data) -> NamedTuple

Run BOTH matchers and compare. `match_atoms` is AUTHORITATIVE; this only reports.

🔴 COMPARED AS A MULTISET OF **DEREFERENCED** SUBSTITUTIONS, NOT AS BINDING MAPS. Order is free
(invariant I7) but CARDINALITY IS NOT, so a set comparison would hide a duplicated or dropped
solution. And comparing the maps STRUCTURALLY would be the same mistake upstream warns about one
level up: two engines' solved forms may differ in shape — which end of a var-var equation survived,
whether a chain was compressed — while denoting the same substitution. So each solution is reduced to
what it DOES: the pattern's variables mapped to their resolved values.
"""
function core_match_differential(pattern, data)
    oracle = _CM_ATOM.match_atoms(pattern, data)
    ours = core_match(pattern, data)
    if ours === nothing
        cls = disagreement_class(pattern, data)
        CORE_MATCH_DECLINES[cls] = get(CORE_MATCH_DECLINES, cls, 0) + 1
        return (; declined = true, agree = true, class = cls, oracle, ours)
    end
    o = _subst_multiset(pattern, oracle)
    m = _subst_multiset(pattern, ours)
    agree = o == m
    cls = disagreement_class(pattern, data)
    agree || push!(CORE_MATCH_DISAGREEMENTS, (; pattern, data, class = cls, oracle = o, ours = m))
    (; declined = false, agree, class = cls, oracle = o, ours = m)
end

"""
The observable of a solution set: for each solution, what it DENOTES, as a sorted multiset.

🔴 A VARIABLE-VALUED BINDING IS COMPARED AS AN EQUALITY **CLASS**, NOT AS A REPRESENTATIVE. This is
the rule "compare the PARTITIONS an equivalence induces, never the representatives", and it is here
because ignoring it produced a false disagreement on the first run: `(f \$x \$x)` vs `(f \$y \$y)` gave

    match_atoms : x => \$x        core_match : x => \$y

Both say "x and y are one variable". They differ only in WHICH END OF THE VAR-VAR EQUATION SURVIVED —
precisely the accident upstream warns downstream not to depend on, and a comparator that reports it
as a disagreement is itself depending on it, one level up.

So: pattern variables resolving to a VARIABLE are grouped, and the group (not its representative) is
what gets compared. Variables resolving to a TERM are compared by the term.
⚠️ Order is free (I7) but CARDINALITY IS NOT — `sort!`, never `unique`, or a duplicated or dropped
solution becomes invisible.
"""
function _subst_multiset(pattern, sols)
    vs = collect_vars(pattern)
    out = Vector{String}()
    for s in sols
        resolved = [(v, _resolve_for_compare(s, v)) for v in vs]
        # group the variable-valued ones by the variable they resolve to
        reps = _CM_ATOM.Var[]
        for (_, r) in resolved
            r isa _CM_ATOM.Var && !any(x -> x == r, reps) && push!(reps, r)
        end
        parts = String[]
        for (v, r) in resolved
            key = string(v.name, "#", v.id)
            if r isa _CM_ATOM.Var
                # the CLASS: every pattern variable that resolves to the same variable as this one
                cls = sort!([string(w.name, "#", w.id) for (w, q) in resolved
                             if q isa _CM_ATOM.Var && q == r])
                push!(parts, key * "=>CLASS{" * join(cls, ",") * "}")
            else
                push!(parts, key * "=>" * string(r))
            end
        end
        push!(out, join(sort!(parts), "|"))
    end
    sort!(out)
    out
end

# resolve `v` through a Core `Bindings`, following the equality-class representative the way the
# interpreter's own consumers do, so the comparison observes the substitution and not the storage.
function _resolve_for_compare(b::_CM_ATOM.Bindings, v::_CM_ATOM.Var)
    r = _CM_ATOM.canonical_var(b, v)
    for e in b.entries
        e.var == r && return e.val
    end
    r
end

"Every `Var` occurring in `a`, in pre-order, DEDUPLICATED by Core's own identity relation."
function collect_vars(a, acc = _CM_ATOM.Var[])
    if a isa _CM_ATOM.Var
        any(x -> x == a, acc) || push!(acc, a)
    elseif a isa _CM_ATOM.Expression
        for c in a.children
            collect_vars(c, acc)
        end
    end
    acc
end
