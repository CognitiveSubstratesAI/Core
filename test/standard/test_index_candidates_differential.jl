# test_index_candidates_differential.jl — EVERY NARROWING MUST BE INVISIBLE TO THE ANSWER.
#
# `index_candidates` is a FILTER in front of `match_atoms`. Its only licence is to return a SUPERSET
# of what can match; anything else is a WRONG ANSWER, not a slow one. And "wrong" here is quiet: a
# narrowing that drops a candidate returns FEWER answers, which no assertion about the remaining
# answers can see.
#
# 🔴 SO THE ORACLE IS THE UNINDEXED SCAN, not a hand-written expectation. Every assertion below runs
# the SAME pattern twice — once with `Index.INDEX_ENABLED[] = false`, once true — and demands the
# answer lists be IDENTICAL, **order and multiplicity included**. MeTTa answers are a MULTISET and
# `collapse` exposes their ORDER, so `Set` equality would pass a reordering that changes a program's
# meaning. See `[[feedback_compare_partitions_not_representatives]]`.
#
# THE TWO NARROWINGS UNDER TEST, and the correctness condition each one carries:
#   * PER-HEAD LISTS — candidates come from the `(head symbol, arity)` list instead of the whole
#     store. 🔴 An atom whose head is NOT a symbol (a variable head, a compound head) can match
#     ANYTHING, so it lives in a wildcard list that must be UNIONED INTO EVERY LOOKUP. A pattern
#     whose own head is a variable must still see the whole store.
#   * DEEP KEY — a compound argument keys by functor PLUS first argument, `(→, A3)`. 🔴 A lookup on
#     `(→, A3)` must ALSO return atoms with a VARIABLE at that position, and atoms whose compound has
#     a VARIABLE FIRST ARGUMENT, `(→ $x A1)`. This is precisely the union SWI's `nextClauseFromList`
#     does NOT do — it reaches the variable sublist only when the functor lookup FAILS — and
#     `Index.jl` already records that as the reason its control flow cannot be copied here.
using Test
using MeTTaCore
const EV = MeTTaCore.Eval
const V = MeTTaCore.StandardMeTTa

"Answers for `q` against a space built from `defs`, with the index forced on or off."
function _idx_answers(defs::AbstractString, q::AbstractString; indexed::Bool)
    old = EV.INDEX_ENABLED[]
    EV.INDEX_ENABLED[] = indexed
    try
        sp = EV.Space()
        EV.load_core_stdlib!(sp)
        isempty(strip(defs)) || EV.load_metta!(sp, defs)
        # ⚠️ STRIP THE GENSYM SUFFIX. `rename_fresh` numbers fresh variables from a PROCESS-GLOBAL
        # counter, so `$anyx#5788` and `$anyx#7679` are the same answer reached on different runs.
        # Comparing them raw tests the RENAMER'S COUNTER, not the narrowing —
        # [[feedback_assert_the_contract_not_the_representation]].
        [replace(string(x), r"#\d+" => "") for x in EV.load_metta!(sp, q)]
    finally
        EV.INDEX_ENABLED[] = old
    end
end

"""🔴 The gate: indexed and unindexed must agree EXACTLY — same values, same multiplicity, same order.

⚠️ NAME IT UNIQUELY. The suite includes EVERY test file into ONE module, so two files defining a
helper with the same name and signature REBIND each other — silently, with no warning at the call
site. This function was `_agree(defs, q)` and `compiler/test_emit_il.jl:57` has
`_agree(src::AbstractString, query::AbstractString)` returning a 3-field NamedTuple, so
`(unindexed, indexed) = _agree(…)` destructured ITS result instead. The file passed standalone and
failed only in the suite, which cost five wrong hypotheses (step budget, type-check pragma, tabling
leak, `objectid` reuse, the type memos) before a bisect named the file."""
function _idx_agree(defs, q)
    a = _idx_answers(defs, q; indexed = false)
    b = _idx_answers(defs, q; indexed = true)
    (a, b)
end

@testset "index_candidates — every narrowing agrees with the unindexed scan" begin

    # A corpus with all the shapes the two narrowings must respect, deliberately mixed so the
    # per-head and deep keys both have something to get wrong.
    DEFS = join([
        "(≞ A0 (STV 1 0.1))", "(≞ A1 (STV 1 0.2))", "(≞ A2 (STV 1 0.3))",
        "(≞ (→ A0 A1) (STV 1 0.5))", "(≞ (→ A1 A2) (STV 1 0.6))", "(≞ (→ A2 A0) (STV 1 0.7))",
        # 🔴 A VARIABLE FIRST ARGUMENT inside the compound — must be returned by a lookup on (→, A0).
        "(≞ (→ \$anyx A1) (STV 1 0.8))",
        # 🔴 A VARIABLE AT THE KEYED POSITION — matches any compound there.
        "(≞ \$anyp (STV 1 0.9))",
        # a different functor at the same position, which must NOT be returned for a (→, …) lookup
        "(≞ (⊃ A0 A1) (STV 1 0.4))",
        # a different head symbol and a different arity under the same head
        "(other A0 A1)", "(≞ A0)",
        # 🔴 PADDING PAST THE INDEX THRESHOLD, AND IT IS LOAD-BEARING. MEASURED: with only the dozen
        # atoms above, NO index is ever built (`_TRIE_MIN_BUCKET` = 16, and `bestHash` declines on a
        # small bucket), so `index_candidates` returns the WHOLE STORE on both arms and this file
        # compares the UNINDEXED PATH WITH ITSELF. Proved by mutation: deliberately dropping one
        # candidate from the bucket left the file 23/23 GREEN. The scaling curve put the engagement
        # point near 17 atoms, so the corpus must clear it.
        [string("(≞ (→ B", i, " B", i + 1, ") (STV 1 0.5))") for i in 0:29]...,
        [string("(≞ B", i, " (STV 1 0.1))") for i in 0:29]...,
    ], "\n")

    @testset "ground, variable and mixed patterns all agree" begin
        for q in [
            "!(match &self (≞ (→ A0 A1) \$t) \$t)\n",        # fully ground compound ⇒ deep key hits
            "!(match &self (≞ (→ A0 \$y) \$t) (\$y \$t))\n", # bound first arg, free second
            "!(match &self (≞ (→ \$x A1) \$t) (\$x \$t))\n", # free first arg ⇒ key cannot narrow
            "!(match &self (≞ (⊃ A0 A1) \$t) \$t)\n",        # a DIFFERENT functor
            "!(match &self (≞ \$p \$t) (\$p \$t))\n",        # free at the keyed position ⇒ everything
            "!(match &self (≞ A0 \$t) \$t)\n",               # a symbol, not a compound
            "!(match &self (other \$a \$b) (\$a \$b))\n",    # a different head symbol
            "!(match &self (\$h A0 A1) \$h)\n",              # 🔴 VARIABLE HEAD ⇒ must see everything
        ]
            (unindexed, indexed) = _idx_agree(DEFS, q)
            # ⚠️ IF THIS TRIPS, SUSPECT A HELPER-NAME COLLISION BEFORE ANYTHING ELSE. It fired for a
            # whole afternoon because `_agree` was also defined in `compiler/test_emit_il.jl`, and
            # the suite puts every file in ONE module. Five mechanisms were proposed and measured
            # away first (step budget, type-check pragma, tabling leak, `objectid` reuse, the type
            # memos); a bisect over the suite's file list named the file in two runs. Bisect first.
            @test !isempty(unindexed)          # ANTI-VACUITY: the case must actually match something
            @test indexed == unindexed         # value, multiplicity AND order
        end
    end

    @testset "🔴 THE SECOND CALL — answers, not just statistics" begin
        # MEASURED: a mutation dropping one candidate from the EXISTING-INDEX path left this file
        # 31/31 GREEN. Every other assertion issues a query ONCE, which only ever exercises the
        # BUILD path; the lookup path runs from the second call onward and nothing compared ANSWERS
        # there. `ANTI-VACUITY 2` reached it but checked only counters.
        for q in ["!(match &self (≞ (→ B3 \$y) \$t) \$t)\n",
                  "!(match &self (≞ (→ B7 \$y) \$t) \$t)\n",
                  "!(match &self (≞ (⊗ Q) \$t) \$t)\n"]
            both = Dict{Bool, Vector{String}}()
            for on in (false, true)
                old = EV.INDEX_ENABLED[]; EV.INDEX_ENABLED[] = on
                try
                    sp = EV.Space(); EV.load_core_stdlib!(sp); EV.load_metta!(sp, DEFS)
                    EV.load_metta!(sp, q)                       # 1st: builds the index
                    both[on] = [replace(string(x), r"#\d+" => "")
                                for x in EV.load_metta!(sp, q)]  # 2nd: USES it
                finally
                    EV.INDEX_ENABLED[] = old
                end
            end
            @test !isempty(both[false])        # anti-vacuity: the repeat still answers
            @test both[true] == both[false]    # 🔴 the lookup path must agree too
        end
    end

    @testset "🔴 ABSENT KEY must still return the variable-position atoms" begin
        # `get(ix.buckets, key, Atom[])` returns EMPTY for a key no stored atom carries, and the
        # comment there calls that "genuinely no candidates". FALSE whenever a variable-position atom
        # exists: `(≞ $anyp …)` matches ANY argument, including a key nobody else has.
        (u, i) = _idx_agree(DEFS, "!(match &self (≞ (⊗ Q) \$t) \$t)\n")
        @test !isempty(u)                  # the unindexed scan DOES find `(≞ $anyp …)`
        @test i == u                       # 🔴 indexed currently returns nothing
    end

    @testset "🔴 A STORED ATOM WITH A VARIABLE HEAD must stay a candidate" begin
        # `same_head` keeps only atoms whose head is exactly the pattern's symbol, so `($h A0 …)` —
        # which matches an `≞` pattern perfectly well — stops being a candidate the moment an index
        # applies. It is the head that is wild, not the position, so such an atom is still keyed by
        # its argument and keeps its selectivity.
        defs2 = DEFS * "\n(\$anyh A0 (STV 1 0.99))"
        (u, i) = _idx_agree(defs2, "!(match &self (≞ A0 \$t) \$t)\n")
        @test any(x -> occursin("0.99", x), u)    # the unindexed scan sees it
        @test i == u                              # 🔴 indexed currently drops it
    end

    @testset "🔴 ANTI-VACUITY 2 — the INDEXED path must really have run" begin
        # Without this the file silently compares the unindexed scan with itself, which is exactly
        # what it did until a mutation (drop one bucket candidate) left it 23/23 GREEN.
        old = EV.INDEX_ENABLED[]; EV.INDEX_ENABLED[] = true
        try
            EV.reset_index_stats!()
            sp = EV.Space(); EV.load_core_stdlib!(sp); EV.load_metta!(sp, DEFS)
            EV.load_metta!(sp, "!(match &self (≞ (→ B3 \$y) \$t) \$t)\n")
            st = EV.index_stats()
            @test st.lookups > 0
            @test st.served > 0                # 🔴 an index was BUILT and USED, not declined
            @test st.skipped_frac > 0.0        # and it actually narrowed something
            # 🔴 AND THE SECOND CALL TOO, so BOTH the build path and the lookup path are exercised.
            # The build path returned candidates UNCOUNTED, which is why `served` read 0 on exactly
            # the calls that were reordering answers.
            EV.reset_index_stats!()
            EV.load_metta!(sp, "!(match &self (≞ (→ B4 \$y) \$t) \$t)\n")
            st2 = EV.index_stats()
            @test st2.served > 0
        finally
            EV.INDEX_ENABLED[] = old
        end
    end

    @testset "🔴 the union conditions, each on its own" begin
        # a deep-keyed lookup must return the VARIABLE-FIRST-ARGUMENT clause …
        (u1, i1) = _idx_agree(DEFS, "!(match &self (≞ (→ A0 A1) \$t) \$t)\n")
        @test i1 == u1
        @test any(s -> occursin("0.8", s), u1)   # `(→ $anyx A1)` really is among them
        # … and the VARIABLE-AT-POSITION clause
        @test any(s -> occursin("0.9", s), u1)   # `(≞ $anyp …)` too
    end

    @testset "mutation between lookups: nothing stale, nothing missing" begin
        for indexed in (false, true)
            old = EV.INDEX_ENABLED[]; EV.INDEX_ENABLED[] = indexed
            try
                sp = EV.Space(); EV.load_core_stdlib!(sp); EV.load_metta!(sp, DEFS)
                q = "!(match &self (≞ (→ A0 \$y) \$t) \$t)\n"
                before = [string(x) for x in EV.load_metta!(sp, q)]
                EV.load_metta!(sp, "!(add-atom &self (≞ (→ A0 A9) (STV 1 0.11)))\n")
                after = [string(x) for x in EV.load_metta!(sp, q)]
                @test length(after) == length(before) + 1        # the new atom is VISIBLE
                EV.load_metta!(sp, "!(remove-atom &self (≞ (→ A0 A9) (STV 1 0.11)))\n")
                back = [string(x) for x in EV.load_metta!(sp, q)]
                @test back == before                             # and GONE again, order intact
            finally
                EV.INDEX_ENABLED[] = old
            end
        end
    end
end
