# tabling/Subsumptive.jl — CALL SUBSUMPTION. SWI manual §7.5, `:- table p/1 as subsumptive`.
#
# Mirrors `boot/tabling.pl`'s `start_subsumptive_tabling/3` (`:429`) and `more_general_table/2`
# (`:1073`), plus the CALL SUBSUMPTION INDEXING section of `pl-tabling.c` (`:2618`).
#
# ─── WHAT IT IS ──────────────────────────────────────────────────────────────────────────────────
# Variant tabling gives `p(a)` and `p(X)` SEPARATE tables, because they are not variants. Subsumptive
# tabling lets the more specific call be answered FROM the more general table: if `p(X)` is complete,
# `p(a)` needs no table of its own — filter `p(X)`'s answers by unification with `p(a)`.
#
# It is a second LOOKUP MODE over the tables we already have, not a second table format. That is why
# the roadmap calls it "the first feature after the base".
#
# ─── THE MECHANISM, AND THE TRICK THAT MAKES IT ONE-WAY ──────────────────────────────────────────
# Upstream's `more_general_table/2`:
#
#     more_general_table(G, Trie) :-
#         term_attvars(G, []), !,
#         term_variables(G, Vars),              % the CALL's own variables, BEFORE
#         '$tbl_variant_table'(VariantTrie),
#         trie_gen(VariantTrie, G, Trie),       % stored keys that UNIFY with G
#         is_most_general_term(Vars).           % …and left G's variables UNBOUND
#
# 🔑 `trie_gen` UNIFIES, which is symmetric — a stored `p(a)` would also unify with a call `p(X)`,
# the wrong direction. `is_most_general_term(Vars)` is what makes it one-way: it re-checks that the
# CALL's original variables are still distinct and unbound afterwards. If unifying bound one of
# them, the stored key was MORE SPECIFIC, not more general, and is rejected.
#
# We have the same asymmetry problem — `match_atoms` unifies in both directions — and take the same
# solution rather than writing a separate one-way matcher, because a second matcher is a second
# thing to keep in agreement with the first.
#
# ─── WHAT WE CANNOT DO AS UPSTREAM DOES, AND WHY IT IS ONLY A COST ───────────────────────────────
# Upstream answers a subsumed call with `'$tbl_answer_update_dl'(ATrie, Skeleton)` and says why
# (`:419` note (*)): *"We should not use trie_gen_compiled/2 here as this will enumerate all answers
# while '$tbl_answer_update_dl'/2 uses the available trie indexing to only fetch the relevant
# answer(s)."*
#
# `$tbl_answer_update_dl` is one of the TWO DELAY-LIST primitives we lack (§7.6.1). So we take the
# path upstream avoids: enumerate the general table's answers and filter. That is a PERFORMANCE
# difference, not a semantic one — the answer SET is identical — and it is the honest trade rather
# than a blocked feature. When delay lists land, this is where indexed retrieval replaces the scan.
#
# ⚠️ UPSTREAM CONSTRAINT, RECORDED: subsumptive tabling does NOT combine with `incremental` or
# `shared` (§7.5). Nothing here enforces that yet because we have neither; when §7.7/§7.9 land, the
# declaration must refuse the combination rather than silently pick one.

"""
    subsumes(general, specific) -> Bool

Does `general` subsume `specific` — i.e. is there a substitution making `general` equal to
`specific`, WITHOUT binding any of `specific`'s own variables?

Upstream's `trie_gen` + `is_most_general_term(Vars)` pair (`more_general_table/2`), for the same
reason: our `match_atoms` unifies symmetrically, so the direction has to be re-imposed afterwards.

`p(\$x)` subsumes `p(a)`; `p(a)` does NOT subsume `p(\$x)`; `p(\$x)` subsumes `p(\$y)` (mutual variants
subsume each other, which is why the caller checks for an exact variant FIRST).
"""
function subsumes(general::Atom, specific::Atom)::Bool
    bs = match_atoms(general, specific)
    isempty(bs) && return false
    svars = collect(collect_vars(specific))        # the CALL's own variables — `term_variables(G,Vars)`
    isempty(svars) && return true                  # ground call: nothing of ours could be bound
    any(b -> _is_most_general(b, svars), bs)
end

"""`is_most_general_term(Vars)` — after unification, are `vars` still DISTINCT FREE VARIABLES?

⚠️ "UNBOUND" IS THE WRONG TEST, and the first version of `subsumes` used it. A variable bound to
ANOTHER VARIABLE is still free — it was renamed, not instantiated — so `p(VAR-x)` must subsume
`p(VAR-y)` (they are mutual variants). Measured: the unbound-only test returned FALSE there.

Two conditions, both from upstream's predicate name: every var maps to a VARIABLE, and those
variables are DISTINCT. The second matters — unifying `p(VAR-x, VAR-x)` against `p(VAR-y, VAR-z)` leaves y and z
both free but COLLAPSED onto one variable, so the specific term is not most-general and the stored
key was the more specific of the two."""
function _is_most_general(b::Bindings, vars::Vector{Var})::Bool
    mapped = Atom[subst(v, b) for v in vars]
    all(m -> m isa Var, mapped) || return false    # bound to a NON-variable ⇒ instantiated
    length(unique(mapped)) == length(mapped)       # …and no two collapsed onto one
end

"""
    is_most_general_term(t) -> Bool

`is_most_general_term/1` (`pl-prims.c:3499-3572`) — the TERM-level predicate, as distinct from
`_is_most_general(bindings, vars)` above, which asks the same question of a UNIFICATION.

    isAtom(t)  -> true
    isTerm(t)  -> every argument is a DISTINCT unbound variable
    otherwise  -> false        (a bare variable included — that is upstream's answer, not an omission)

⚠️ DISTINCTNESS IS THE HALF THAT IS EASY TO DROP, and upstream enforces it by a trick worth naming:
it `set_marked`s each argument as it goes, and a marked word no longer satisfies `isVar`, so a
SECOND occurrence of the same variable fails the very test that admitted the first. `p(X, X)` is
therefore NOT most general — it constrains its two arguments to be equal, which is a real constraint.

Used by §7.11.1 to decide whether an abstracted goal is worth treating as abstract at all: an
abstraction that lands on a maximally-general goal is indistinguishable from having asked the general
goal directly, so it takes the plain variant arm (`boot/tabling.pl:481`).
"""
function is_most_general_term(t::Atom)::Bool
    t isa Sym && return true
    t isa Expression || return false
    args = @view (t::Expression).children[2:end]        # children[1] is the functor
    all(x -> x isa Var, args) || return false
    length(unique(args)) == length(args)                # …and DISTINCT
end

"""
    more_general_table(goal) -> Union{Tuple{Atom,AnswerTrie},Nothing}

`more_general_table/2` (`boot/tabling.pl:1073`). The table whose key SUBSUMES `goal`, or `nothing`.

⚠️ AN EXACT VARIANT IS NOT RETURNED. Upstream reaches `more_general_table/2` only after
`'\$tbl_existing_variant_table'` has already failed, so by construction the exact table does not
exist there. Ours is callable directly, so it excludes the variant itself — otherwise a caller
would get "use the general table" for a table that IS the call, and the subsumptive path would
shadow the ordinary one.

When several tables subsume, the MOST SPECIFIC is chosen: it has the smallest answer set to filter,
and any of them is semantically valid. Upstream leaves the choice to `trie_gen`'s enumeration order;
choosing deliberately is the Julia-side decision, and it is stated rather than incidental.
"""
function more_general_table(goal::Atom)
    key = _variant_rename(goal)
    best = nothing
    for k in sort!(collect(keys(_ANSWER_TRIES)); by=string)
        k == key && continue                       # not the exact variant — see the note above
        subsumes(k, goal) || continue
        # MOST SPECIFIC wins: the one that is itself subsumed by every other candidate.
        if best === nothing || subsumes(best, k)
            best = k
        end
    end
    best === nothing ? nothing : (best, answer_trie_for(best))
end

"""
    subsumptive_answers(goal) -> Union{Vector{Atom},Nothing}

Answer `goal` from a more general COMPLETE table, or `nothing` if none applies.

`nothing` means "fall through to ordinary tabling" — upstream's final
`;   start_tabling(Closure, Wrapper, Worker)` clause. An EMPTY VECTOR is a different answer: a
general table exists, is complete, and genuinely has no answer matching this call.

⚠️ ONLY A `:complete` TABLE IS USED. Upstream's first subsumptive clause requires
`'\$tbl_table_status'(ATrie, complete, ...)`; an incomplete general table means the answers are still
arriving, and filtering a partial set would silently under-answer. Upstream's other clauses SUSPEND
on that case (`shift_for_copy`), which needs the consumer path — so for now we fall through to
ordinary tabling instead, which is correct but does more work.
"""
function subsumptive_answers(goal::Atom, space=nothing)
    g = more_general_table(goal)
    g === nothing && return nothing
    (genkey, t) = g
    is_complete(t) || return nothing               # not complete ⇒ fall through, do not under-answer

    # 🔴🔴 THIS RETURNED THE EMPTY SET FOR EVERY VALUE TABLE — MEASURED 2026-08-18, warm probe:
    #     (= (f a) 1)  (= (f b) 2)   table!(:f)   driven by !(f $z)
    #     more_general_table((f a))  = (f $_v#1)      answers ["1", "2"]
    #     subsumptive_answers((f a)) = Atom[]          ← upstream gives 1
    # And `Atom[]` is LOADED here: per this function's own contract an empty vector means "a general
    # table exists, is complete, and genuinely has no answer matching this call". So it was not a
    # slow path, it was a WRONG ANSWER, latent only because §7.5 is unwired.
    #
    # CAUSE — THE THIRD ASSUMPTION, for the third time. The old body did `match_atoms(a, goal)`:
    # unify the ANSWER against the GOAL. Upstream can, because a Prolog answer IS a substitution over
    # the goal skeleton, so `'$tbl_table_status'(ATrie, complete, Wrapper, Skeleton)`
    # (boot/tabling.pl:438-440) binds the caller's wrapper INTO the skeleton and the answer rides
    # along. Ours is a VALUE — `1` never unifies with `(f a)` — so every answer was rejected.
    #
    # FIX: bind the GENERAL VARIANT against the SPECIFIC CALL, then substitute into each answer.
    # That is exactly `Abstract.abstract_answers`, and it is deliberately the same shape: §7.5 and
    # §7.11.1 are upstream's own "merge between variant and subsumptive tabling", so they should not
    # have two different answers to one question. `[[feedback_recurring_defect_derive_the_rule]]`
    bs = match_atoms(genkey, goal)
    answers = trie_answers(t)
    isempty(bs) && return copy(answers)             # cannot specialise ⇒ the general set, unfiltered

    # 🔑 AND THE PRECISION IS RECOVERABLE, SOUNDLY — reusing §7.11.1's gate rather than repeating its
    # mistake. Filtering by recorded INSTANCE was shipped for abstraction, found to DROP ANSWERS, and
    # is sound exactly on heads that cannot reduce into themselves (`_self_reaching_heads`): the
    # recorded instance is the goal AT THE POINT THE RULE MATCHED, which for a reducing head is a
    # different term from the call. `f` above is facts-only, so the filter applies and the answer is
    # EXACT (`1`, not `1` and `2`); a recursive head over-approximates instead, which is sound.
    filterable =
        space !== nothing && (h = head_name(goal)) !== nothing &&
        !(h in _self_reaching_heads(all_atoms(space)))
    out = Atom[]
    for a in answers
        # 🔴 TWO ANSWER SHAPES LIVE IN THE SAME TRIE, AND THEY NEED DIFFERENT TREATMENT.
        # An answer that is an INSTANCE OF THE TABLE'S OWN GOAL PATTERN (Prolog-shaped: the table
        # `(p $x)` holding `(p a)`, which is what `generalise_answer_substitution` and the §7.11.3
        # restraint produce) can be filtered by unifying it against the specific call — that is
        # upstream's test and it is exact. A VALUE answer (`(f a)` holding `1`) cannot: it does not
        # unify with any goal, and rejecting it on that basis is what made this function return the
        # empty set for every value table.
        #
        # `match_atoms(a, genkey)` is the discriminator: it asks "is this answer an instance of the
        # goal pattern this table is keyed on?". Fixing only the value case, as the first cut did,
        # broke the goal-shaped case in the opposite direction — it stopped filtering and returned
        # every answer. Both shapes are real and both are tested.
        if !isempty(match_atoms(a, genkey))                 # goal-shaped ⇒ upstream's exact filter
            isempty(match_atoms(a, goal)) && continue
        elseif filterable                                   # value-shaped ⇒ the §7.11.1 gated filter
            insts = trie_instances(t, a)
            isempty(insts) || any(i -> !isempty(match_atoms(i, goal)), insts) || continue
        end
        for b in bs
            inst = subst(a, b)
            any(x -> variant_eq(x, inst), out) || push!(out, inst)
        end
    end
    out
end

# ── the declaration surface ──────────────────────────────────────────────────────────────────────
const _SUBSUMPTIVE = Set{Symbol}()

"""`:- table p/1 as subsumptive` (`boot/tabling.pl:304`). Mode is per PREDICATE, not per call."""
table_subsumptive!(head::Symbol) = (push!(_SUBSUMPTIVE, head); nothing)
is_subsumptive(head::Symbol)::Bool = head in _SUBSUMPTIVE
untable_subsumptive!(head::Symbol) = (delete!(_SUBSUMPTIVE, head); nothing)
clear_subsumptive!() = (empty!(_SUBSUMPTIVE); nothing)
