# Passes.jl — IR→IR transformations that run between the frontend and A-normalization.
#
# ─── SPECIALIZE_MATCHES — the control-flow answer ────────────────────────────────────────────────
# MEASURED over Core's 1000-clause corpus: 177 clauses decline for control flow, the second-largest
# bucket. The lowering for them exists and is spec-proved — `_compile_match!` implements §9.3's
# Conditional Equivalence theorem — but the shape it emits DOES NOT FIRE. Verified against the
# upstream MORK binary on `(= (colour $c) (case $c ((red warm) (blue cool))))` with `(colour red)`:
#
#   A  one exec per arm, arm SUBSTITUTED INTO THE REDEX          -> warm      ✅
#        (exec 0 (, (colour red))  (O (+ warm) (- (colour red))))
#        (exec 0 (, (colour blue)) (O (+ cool) (- (colour blue))))
#   B  scrutinee and pattern as two conjuncts (what codegen emits today)  -> did not fire
#        (exec 0 (, (colour $c) red) (O (+ warm)))
#   C  arm pattern alone as the source                            -> did not fire
#
# So the correct lowering is RULE SPECIALIZATION: one clause per arm, with the scrutinee variable
# replaced by that arm's pattern THROUGHOUT THE HEAD. It is the same shape as upstream's own
# `MM2_Structuring_Code/mm2_programs/Control_04_Select_b_c.mm2` — one exec per arm, selection by
# mutual exclusion of patterns, no conditional primitive involved.
#
# ⚠️ WHY THIS IS A PASS AND NOT A CODEGEN FIX. `_compile_match!` receives only the `MatchNode` — the
# rule BODY. Substituting an arm pattern into the redex needs the HEAD, which it cannot see. The
# transformation is therefore only expressible where head and body are both in scope, i.e. on a
# whole clause, before A-normalization. Trying to fix it inside codegen would be fixing it in the one
# place that structurally cannot.
#
# This also leaves the proved codegen untouched: `_compile_match!`, its §9.3 citation and its
# bisimulation obligations are unchanged. After this pass a `case` clause has become N ordinary
# clauses, which the existing reduction path already compiles.

module CompilerPasses

using ..CompilerIR

"""
    subst_var(node, target, replacement) -> IRAtom

Replace every occurrence of the variable `target` (by unique id) with `replacement`.

Matched on the RESOLVED id, not the written name — resolution exists precisely so that two clauses
each writing `\$x` are different variables. Substituting by name would capture across scopes.
"""
function subst_var(node::IRAtom, target::NodeId, replacement::IRAtom)::IRAtom
    if node isa IRVariable
        return (node::IRVariable).unique == target ? replacement : node
    elseif node isa IRExpression
        e = node::IRExpression
        return IRExpression(subst_var(e.head, target, replacement),
                            IRAtom[subst_var(a, target, replacement) for a in e.args],
                            e.id, e.src)
    elseif node isa IRSpecial
        s = node::IRSpecial
        return IRSpecial(s.kind, s.surface,
                         IRAtom[subst_var(a, target, replacement) for a in s.args], s.id, s.src)
    elseif node isa IRSuperpose
        p = node::IRSuperpose
        return IRSuperpose(IRAtom[subst_var(a, target, replacement) for a in p.alternatives],
                           p.id, p.src)
    elseif node isa IRDestructiveBinding
        d = node::IRDestructiveBinding
        binds = IRBoundAtom[IRBoundAtom(subst_var(b.pattern, target, replacement),
                                        subst_var(b.value, target, replacement), b.id, b.src)
                            for b in d.bindings]
        return IRDestructiveBinding(binds, d.sequential,
                                    subst_var(d.body, target, replacement), d.id, d.src)
    elseif node isa IRMatch
        m = node::IRMatch
        brs = IRMatchBranch[IRMatchBranch(subst_var(b.pattern, target, replacement),
                                          subst_var(b.body, target, replacement), b.src)
                            for b in m.branches]
        return IRMatch(subst_var(m.scrutinee, target, replacement), brs, m.id, m.src)
    end
    node                                    # leaves: Sym / Grounded / Predefined / ResolvedSymbol
end

"Does `target` occur anywhere in `node`?"
function occurs(node::IRAtom, target::NodeId)::Bool
    found = false
    walk(node) do n
        n isa IRVariable && (n::IRVariable).unique == target && (found = true)
    end
    found
end

"""
    specialize_clause(lhs, rhs) -> Vector{IRBoundAtom} | nothing

Split one clause whose body is an `IRMatch` on a HEAD VARIABLE into one clause per arm.

    (= (colour \$c) (case \$c ((red warm) (blue cool))))
      ⟹  (= (colour red)  warm)
          (= (colour blue) cool)

Returns `nothing` — leave the clause alone — when the split is not sound:

  * the body is not an `IRMatch`;
  * the scrutinee is not a plain variable (a computed condition needs its value produced FIRST,
    which is a staging problem, not a substitution — `(if (ready) …)` cannot be specialized because
    `(ready)` must reduce before anything can match on it);
  * the scrutinee variable does not occur in the head, so substituting changes nothing and the arms
    are not discriminated by the redex.

Declining is deliberate: an unsound split silently changes which rules fire.
"""
function specialize_clause(lhs::IRAtom, rhs::IRAtom)::Union{Vector{IRBoundAtom},Nothing}
    rhs isa IRMatch || return nothing
    m = rhs::IRMatch
    isempty(m.branches) && return nothing
    m.scrutinee isa IRVariable || return nothing            # computed scrutinee ⇒ staging, not this
    v = (m.scrutinee::IRVariable).unique
    v == NO_ID && return nothing                            # unresolved — refuse to guess
    occurs(lhs, v) || return nothing                        # arms would not be discriminated

    out = IRBoundAtom[]
    for b in m.branches
        push!(out, IRBoundAtom(subst_var(lhs, v, b.pattern), b.body))
    end
    out
end

"""
    specialize_matches(program) -> (IRProgram, n_split)

Apply `specialize_clause` across every definition, returning the rewritten program and how many
clauses were split.

The count is returned rather than logged: this pass changes the clause count, so a coverage number
measured after it is not comparable to one measured before unless the split count is known.
"""
function specialize_matches(program::IRProgram)
    defs = IRFunctionDefinition[]
    n_split = 0
    for d in program.definitions
        clauses = IRBoundAtom[]
        for cl in d.clauses
            sp = specialize_clause(cl.pattern, cl.value)
            if sp === nothing
                push!(clauses, cl)
            else
                append!(clauses, sp); n_split += 1
            end
        end
        push!(defs, IRFunctionDefinition(d.name, clauses, d.ty, d.id, d.src))
    end
    (IRProgram(defs, program.runs, program.predefined, program.annotations, program.gen), n_split)
end

export subst_var, occurs, specialize_clause, specialize_matches

end # module CompilerPasses
