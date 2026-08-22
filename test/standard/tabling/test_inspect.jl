# test_inspect.jl — SWI `library(tables)`, the portable half. §7.12.
#
# `library(tables)` is a THIN Prolog layer (381 lines) over seven C primitives, and the answer trie
# (§1.0 step 4) is the substrate the inspection predicates need. Five primitives we had; the sixth
# (`$tbl_table_status`) landed with `AnswerTrie.status`.
#
# ⚠️ THE THREE NOT PORTED ARE NOT AN OVERSIGHT: `get_residual/2`, `get_returns_and_dls/3` and
# `get_returns_and_tvs/3` need `$tbl_answer_dl` / `$tbl_answer_update_dl` — DELAY LISTS, absent
# (§7.6.1). The split falls exactly on those two primitives, which is why it is a boundary rather
# than a judgement call.
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _IN = Eval
_in_g(h::Symbol, a) = Expression(Atom[Sym(h), Grounded(a)])

@testset "library(tables) — the portable inspection half (§7.12)" begin

    @testset "get_call / get_calls / status" begin
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        k1 = _IN._variant_rename(_in_g(:p, 1))
        k2 = _IN._variant_rename(_in_g(:p, 2))
        k3 = _IN._variant_rename(_in_g(:q, 1))
        for (k, vals) in ((k1, (10, 20)), (k2, (30,)), (k3, (99,)))
            t = _IN.answer_trie_for(k)
            for v in vals
                _IN.trie_insert!(t, Grounded(v))
            end
        end
        _IN.set_table_status!(_IN.answer_trie_for(k1), :complete)

        c = _IN.get_call(_in_g(:p, 1))
        @test c !== nothing
        @test c[1] == k1 && c[3] == :complete && length(c[2]) == 2
        @test _IN.get_call(_in_g(:p, 9)) === nothing        # no table ⇒ nothing, not an empty trie

        calls = _IN.get_calls(:p)                            # the nondeterministic form
        @test length(calls) == 2
        @test Set(s for (_, _, s) in calls) == Set([:complete, :fresh])
        @test isempty(_IN.get_calls(:nosuch))
        @test _IN.tabled_heads() == [:p, :q]
        _IN.abolish_all_tables!()
    end

    @testset "get_returns, with nodes, and for a call" begin
        _IN.abolish_all_tables!()
        k = _IN._variant_rename(_in_g(:p, 1))
        t = _IN.answer_trie_for(k)
        for v in (10, 20, 30)
            _IN.trie_insert!(t, Grounded(v))
        end

        @test String[string(a) for a in _IN.get_returns(t)] == ["10", "20", "30"]   # insertion order
        wn = _IN.get_returns_with_nodes(t)                                          # get_returns/3
        @test length(wn) == 3
        @test all(n isa _IN.TrieNode for (_, n) in wn)
        @test String[string(a) for (a, _) in wn] == ["10", "20", "30"]
        # the node IS the handle: upstream's NodeID exists so a caller can act on one answer.
        @test wn[2][2].answer == Grounded(20)

        @test String[string(a) for a in _IN.get_returns_for_call(_in_g(:p, 1))] ==
            ["10", "20", "30"]
        @test isempty(_IN.get_returns_for_call(_in_g(:z, 1)))   # no table ⇒ empty, not an error
        _IN.abolish_all_tables!()
    end

    @testset "status accepts UPSTREAM's set and nothing else" begin
        @test _IN.table_status(_IN.AnswerTrie()) == :fresh      # created, not completed
        @test _IN.TABLE_STATUSES == (:fresh, :active, :complete, :invalid, :dynamic)
        t = _IN.AnswerTrie()
        @test _IN.table_status(_IN.set_table_status!(t, :complete)) == :complete
        @test _IN.is_complete(t)
        # a status we invented would be indistinguishable from one upstream has; refuse it.
        @test_throws ArgumentError _IN.set_table_status!(t, :bogus)
        @test_throws ArgumentError _IN.set_table_status!(t, :done)
    end

    @testset "🔴 abolish_table_pred! drops TABLES; untable! also drops the DECLARATION" begin
        # Upstream keeps these separate and so must we: `abolish_table_pred/1` invalidates the
        # subgoals and the next call RE-TABLES, while `untable/1` retracts `$tabled`/`$table_mode`
        # and clears the attributes so the predicate stops being tabled. Conflating them makes
        # "clear the cache" silently mean "stop memoising".
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        _IN.table!(:p)
        k = _IN._variant_rename(_in_g(:p, 1))
        _IN.trie_insert!(_IN.answer_trie_for(k), Grounded(7))
        @test :p in _IN._TABLED_HEADS
        @test count(x -> _IN.head_name(x) === :p, keys(_IN._ANSWER_TRIES)) == 1

        @test _IN.abolish_table_pred!(:p)                       # had tables ⇒ true
        @test :p in _IN._TABLED_HEADS                           # DECLARATION SURVIVES
        @test count(x -> _IN.head_name(x) === :p, keys(_IN._ANSWER_TRIES)) == 0
        @test !_IN.abolish_table_pred!(:p)                      # nothing left to drop ⇒ false

        @test _IN.untable!(:p)                                  # …and this one drops the declaration
        @test !(:p in _IN._TABLED_HEADS)
        _IN.abolish_all_tables!()
        _IN.untable_all!()
    end

    @testset "abolish_all_tables! clears every table and keeps every declaration" begin
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        _IN.table!(:p)
        _IN.table!(:q)
        for h in (:p, :q)
            _IN.trie_insert!(
                _IN.answer_trie_for(_IN._variant_rename(_in_g(h, 1))), Grounded(1)
            )
        end
        @test length(_IN._ANSWER_TRIES) == 2
        _IN.abolish_all_tables!()
        @test isempty(_IN._ANSWER_TRIES)
        @test :p in _IN._TABLED_HEADS && :q in _IN._TABLED_HEADS   # declarations kept
        _IN.untable_all!()
    end
end

@testset "roadmap 1.0b step 1 — the trie MIRRORS a real completed table" begin
    # Until this, `_ANSWER_TRIES` was populated only by hand in tests: `library(tables)`, §7.5's
    # `more_general_table` and §7.3/§7.11.3's trie-seated inserts were CORRECT AND UNREACHABLE from a
    # real evaluation. `tabled_eval` now mirrors completed answers into the trie.
    #
    # ⚠️ MIRROR, NOT SWITCH. `_ANSWER_TABLE` is still the read path, so this changes no behaviour —
    # it makes the trie OBSERVABLE against the live engine first. Same disable-to-prove order as the
    # resumption flip: agreement before adoption.
    _IN.untable_all!()
    _IN.abolish_all_tables!()
    try
        s = Space()
        load_core_stdlib!(s)
        load_metta!(
            s, raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))" * "\n"
        )
        _IN.table!(:fib)
        @test String[
            string(x) for y in load_metta!(s, "!(fib 8)\n")
            for x in (y isa AbstractVector ? y : [y])
        ] == ["21"]

        # ANTI-VACUITY: a run that tabled nothing would make every assertion below trivially true.
        calls = _IN.get_calls(:fib)
        @test length(calls) > 1                      # fib 8 memoises several subgoals
        @test _IN.tabled_heads() == [:fib]

        # 🔴 THE TWO STORES MUST AGREE — that is the whole point of mirroring before switching.
        for (k, t, st) in calls
            @test st == :complete                    # completion marks status, which §7.5 requires
            @test sort(String[string(a) for a in get(_IN._ANSWER_TABLE, k, Atom[])]) ==
                sort(String[string(a) for a in _IN.get_returns(t)])
        end

        # and the inspection API reaches a REAL table, not a hand-built one
        goal = _IN._reduced_goal(_IN.parse_from(_IN.tokenize("(fib 8)"), Ref(1), s.tokens),
            s, _IN.Bindings())
        c = _IN.get_call(goal)
        @test c !== nothing && c[3] == :complete
        @test String[string(a) for a in _IN.get_returns(c[2])] == ["21"]
    finally
        _IN.abolish_all_tables!()
        _IN.untable_all!()
    end
end

# ═══════════════════════════════════════════════════════════════════════════════════════════════
# THE DELAY-LIST HALF — `get_returns_and_tvs/3`, `get_returns_and_dls/3`, `get_residual/2`.
#
# The header of `Inspect.jl` used to call these unportable, blocked on `'$tbl_answer_dl'` /
# `'$tbl_answer_update_dl'`. Both halves of that were wrong: upstream builds `get_residual/2`
# (`library/tables.pl:269-271`) and `get_returns_and_dls/3` (`:227`) on `'$tbl_answer'/3`, which is
# `trie_gen` + `unify_delay_info` (`pl-tabling.c:5391-5399`) — enumeration we had (`trie_answers`)
# plus a condition we had (`delays_of`). And `'$tbl_answer_update_dl'` is not a gap at all: its
# purpose is the side effect at `pl-tabling.c:5520`, pushing onto the trail-scoped delay register
# that roadmap 7.A deliberately replaced.
# ═══════════════════════════════════════════════════════════════════════════════════════════════

_in_h(h::Symbol) = Expression(Atom[Sym(h)])                    # a zero-arg goal, `(h)`
_in_strs(dls) = [String[string(x) for x in conj] for conj in dls]

@testset "library(tables) — the DELAY-LIST half (`\$tbl_answer`'s Condition)" begin

    @testset "🔴🔴 THE INVERSION: a REASON-LESS bottom is `u`, and `answer_residual` still says True" begin
        # 🔴 THIS TEST IS FIRST BECAUSE IT IS THE ONE THAT FAILS ON THE PLAUSIBLE WRONG
        # IMPLEMENTATION, and the wrong one is the shortest thing anybody would write:
        #
        #     tv = answer_residual(a) == Sym("True") ? :t : :u          # ← SOUNDNESS INVERSION
        #
        # `answer_residual` maps an EMPTY DNF to `Sym("True")` on purpose — empty means "no reason
        # recorded", and `dnf_residual`'s own docstring says a consumer must never read it as
        # "false". So a bottom with no recorded reason has residual `True`, and that implementation
        # reports it as `t`: TRUE for an answer that is UNDEFINED. Upstream is explicit that this
        # case is conditional — `answer_is_conditional` (`pl-tabling.c:764-770`) is
        # `di == DL_UNDEFINED || !isEmptyBuffer(&di->delay_sets)`, and `unify_delay_info` renders it
        # as the ATOM `undefined`, not `true` (`:5371` vs `:5373`).
        #
        # ⚠️ AND THE CASE IS REACHABLE, not hypothetical: `_wfs_bottom_for` yields an EMPTY DNF
        # whenever no optimistic answer carried a delay and no negative dependency was recorded.
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        k = _IN._variant_rename(_in_h(:bare))
        t = _IN.answer_trie_for(k)
        @test _IN.trie_insert!(t, _IN.UNDEFINED)
        @test length(_IN.get_returns(t)) == 1          # ANTI-VACUITY: the trie is not empty

        # the three facts that must hold SIMULTANEOUSLY — this conjunction is the whole test
        @test _IN.answer_residual(_IN.UNDEFINED) == Sym("True")     # …residual says unconditional…
        @test _IN.get_returns_and_tvs(t) == [(_IN.UNDEFINED, :u)]   # …the truth value must NOT.
        @test _in_strs(_IN.delay_lists(_IN.UNDEFINED)) == [["undefined"]]   # …and NOT `[]`

        # the trichotomy itself (`unify_delay_info`, pl-tabling.c:5342-5375)
        @test _IN.answer_condition(_IN.UNDEFINED) === _IN.COND_UNDEFINED
        @test _IN.answer_condition(Grounded(42)) === _IN.COND_TRUE
        @test _IN.answer_condition(
            _IN.undefined_with(
                _IN.DelayDNF([_IN.DelaySet([_IN.delay_negative(Sym(:q))])]))
        ) isa _IN.DelayDNF
        @test _IN.answer_is_conditional(_IN.UNDEFINED)              # `u`, per :764-770
        @test !_IN.answer_is_conditional(Grounded(42))

        # 🔴 `COND_TRUE` IS `Symbol("true")`, NOT `:true` — in Julia `:true` quotes the Bool LITERAL
        # and evaluates to `true::Bool`. Spelling the trichotomy `:true | :undefined | DelayDNF`
        # compiles and then never matches. Measured: it threw
        # `MethodError: Cannot convert Bool to Union{Symbol, Vector{Vector{Delay}}}` on the first
        # unconditional answer, caught only by the return annotation.
        @test _IN.COND_TRUE isa Symbol && _IN.COND_TRUE == Symbol("true")
        @test :true isa Bool && !(:true isa Symbol)

        # get_residual on the same table: ONE row, and its list is the `undefined` conjunction
        rs = _IN.get_residual(_in_h(:bare))
        @test length(rs) == 1
        @test rs[1][1] == _IN.UNDEFINED
        @test String[string(x) for x in rs[1][2]] == ["undefined"]
        _IN.abolish_all_tables!()
        _IN.untable_all!()
    end

    @testset "🔴🔴 A MIXED table from REAL evaluation — exactly one `t` and one `u`" begin
        # ANTI-VACUITY OF THE OTHER KIND. Every assertion above runs on a hand-built trie, so it
        # passes on an implementation nothing ever reaches. This drives the engine: `(r)` has an
        # UNCONDITIONAL clause (`1`) and a clause routed through the canonical paradox, so its ONE
        # table holds one answer of each truth value. An implementation that reports a single tv for
        # the whole table, or that classifies by the table rather than the answer, fails here.
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        try
            s = Space()
            load_core_stdlib!(s)
            load_metta!(
                s,
                raw"(= (p) (tnot (q)))" * "\n" * raw"(= (q) (tnot (p)))" * "\n" *
                raw"(= (r) 1)" * "\n" * raw"(= (r) (p))" * "\n"
            )
            for h in (:p, :q, :r)
                _IN.table!(h)
            end
            vals = Atom[
                x for y in load_metta!(s, "!(r)\n")
                for x in (y isa AbstractVector ? y : [y])
            ]
            @test length(vals) == 2                              # ANTI-VACUITY: both clauses fired
            @test count(_IN.is_undefined, vals) == 1

            c = _IN.get_call(_in_h(:r))
            @test c !== nothing && c[3] == :complete
            tvs = _IN.get_returns_and_tvs(c[2])
            @test length(tvs) == 2
            @test count(x -> x[2] == :t, tvs) == 1               # THE assertion
            @test count(x -> x[2] == :u, tvs) == 1
            # …and the `t` is the ORDINARY value, the `u` is the bottom — not merely one of each
            @test [(string(a), tv) for (a, tv) in tvs] == [("1", :t), ("undefined", :u)]

            # get_returns_and_dls agrees, and the unconditional answer keeps an EMPTY outer list
            # rather than being filtered out (`condition_delay_lists(true, _, [])`, tables.pl:230)
            dls = _IN.get_returns_and_dls(c[2])
            @test length(dls) == 2
            @test isempty(dls[1][2])                             # `1` ⇒ []
            @test !isempty(dls[2][2])                            # the bottom ⇒ a real condition
            @test occursin("q", string(dls[2][2][1]))            # …naming the paradox it delays on

            # get_residual: the unconditional answer is REPORTED (with an empty list), not skipped
            rs = _IN.get_residual(_in_h(:r))
            @test length(rs) == 2
            @test isempty(rs[1][2]) && string(rs[1][1]) == "1"
            @test !isempty(rs[2][2])
        finally
            _IN.abolish_all_tables!()
            _IN.untable_all!()
        end
    end

    @testset "🔴🔴 THE DISJUNCTIVE SPLIT — 1 row from `_dls`, 2 rows from `get_residual`" begin
        # 🔴 THIS IS THE ONLY THING SEPARATING THE TWO PREDICATES, so if an implementation collapses
        # it BOTH are wrong. `condition_delay_list/3` (tables.pl:277-283) puts a `;` between its two
        # recursive calls, so a 2-disjunct condition SUCCEEDS TWICE with one conjunction each;
        # `condition_delay_lists/3` (:232-235) succeeds ONCE with a list of both. Upstream's own doc
        # on `get_returns_and_tvs/3` leans on the same fact — it "will succeed only once" for a
        # multi-delay-list answer, which is why it is cheaper than `get_residual/2`.
        _IN.abolish_all_tables!()
        _IN.untable_all!()
        two = _IN.undefined_with(
            _IN.dnf_or(
                _IN.DelayDNF([_IN.DelaySet([_IN.delay_negative(Sym(:q))])]),
                _IN.DelayDNF([_IN.DelaySet([_IN.delay_negative(Sym(:v))])]))
        )
        @test length(_IN.delays_of(two)) == 2          # ANTI-VACUITY: it really has two disjuncts

        k = _IN._variant_rename(_in_h(:disj))
        t = _IN.answer_trie_for(k)
        @test _IN.trie_insert!(t, two)

        dls = _IN.get_returns_and_dls(t)
        @test length(dls) == 1                                     # ONE row per ANSWER…
        @test _in_strs(dls[1][2]) == [["(not q)"], ["(not v)"]]    # …carrying BOTH disjuncts

        rs = _IN.get_residual(_in_h(:disj))
        @test length(rs) == 2                                      # …but TWO rows per DISJUNCT
        @test all(r -> r[1] == two, rs)                            # both name the SAME answer
        @test [String[string(x) for x in r[2]] for r in rs] == [["(not q)"], ["(not v)"]]

        # and the tv collapses the disjunction to a single `u` — the efficiency upstream documents
        @test _IN.get_returns_and_tvs(t) == [(two, :u)]

        # 🔴 THE ANSWER MUST COME OUT ALONGSIDE THE LIST — `get_residual/2` CANNOT KEEP ITS ARITY.
        # Upstream returns the answer THROUGH the goal term because a Prolog answer IS a substitution
        # over it; ours is an unrelated VALUE. Nothing about `undefined` is recoverable from `(disj)`,
        # so dropping the first tuple slot would report WHICH conditions the table holds while losing
        # which answer each belongs to.
        @test eltype(rs) == Tuple{Atom, Vector{Atom}}
        @test !isempty(String[string(r[1]) for r in rs])

        @test isempty(_IN.get_residual(_in_h(:nosuchtable)))       # no table ⇒ no solutions
        _IN.abolish_all_tables!()
        _IN.untable_all!()
    end
end

@testset "🔴 the MeTTa surface `get-residual` — GOAL-taking, and it FIRES" begin
    # 🔴 THE SHAPE IS FORCED BY A MEASUREMENT, NOT A PREFERENCE. An ANSWER-taking reporting op
    # (`!(answer-residual (p))`) is UNREACHABLE for exactly the inputs it exists to describe: an
    # argument that reduces to a WFS bottom short-circuits the enclosing application through the
    # strict-op contagion guard, so the op is never entered. Measured 2026-08-18: `!(answer-residual 42)`
    # and `!(answer-residual (f))` (tabled, value 7) both CALLED the op; `!(answer-residual (p))`
    # (tabled, ⊥) NEVER called it and returned `undefined`. That guard is correct and must not be
    # punched through — so the surface takes the GOAL, unevaluated, which is also upstream's shape
    # (`get_residual(:CallTerm, -DelayList)`, library/tables.pl:262-274).
    #
    # ⚠️ REGISTRATION LIVES IN `Eval.jl`, WHICH THIS FILE'S AUTHOR DOES NOT OWN. `TOKEN_REGISTRY` and
    # `_GROUNDED_OP_TYPES` are plain mutable Dicts, so the test installs the exact registration and
    # restores it — which makes the test pass BEFORE the patch lands and stay correct AFTER, rather
    # than being a test that cannot run (`[[feedback_verify_the_oracle_runs]]`).
    _had_tok = get(_IN.TOKEN_REGISTRY, "get-residual", nothing)
    _had_typ = get(_IN._GROUNDED_OP_TYPES, _IN.GET_RESIDUAL, nothing)
    _IN.abolish_all_tables!()
    _IN.untable_all!()
    try
        _IN.TOKEN_REGISTRY["get-residual"] = _IN.GET_RESIDUAL
        _IN._GROUNDED_OP_TYPES[_IN.GET_RESIDUAL] = "(-> Atom Atom)"

        s = Space()
        load_core_stdlib!(s)
        load_metta!(
            s,
            raw"(= (p) (tnot (q)))" * "\n" * raw"(= (q) (tnot (p)))" * "\n" *
            raw"(= (r) 1)" * "\n" * raw"(= (r) (p))" * "\n"
        )
        for h in (:p, :q, :r)
            _IN.table!(h)
        end
        _flat(o) = Atom[x for y in o for x in (y isa AbstractVector ? y : [y])]

        @test length(_flat(load_metta!(s, "!(r)\n"))) == 2        # ANTI-VACUITY: the table is real

        rows = String[string(v) for v in _flat(load_metta!(s, "!(get-residual (r))\n"))]
        @test length(rows) == 2                                    # …and the op FIRED, twice
        # order is the engine's LIFO alternative order (see `COLLAPSE`'s comment) — assert content
        @test Set(rows) == Set(["(residual 1 ())", "(residual undefined ((not (q))))"])

        # 🔴 THE CONTROL, and it is the whole reason for the goal-taking shape: the SAME ⊥ passed as
        # an ARGUMENT never reaches the operation — `not` is entered for no value at all.
        @test String[string(v) for v in _flat(load_metta!(s, "!(not (p))\n"))] ==
            ["undefined"]

        # a goal with no table yields nothing — upstream's `trie_gen` fails; `Empty` is MeTTa's form
        @test isempty(
            String[string(v) for v in _flat(load_metta!(s, "!(get-residual (nosuch))\n"))]
        )
    finally
        if _had_tok === nothing
            delete!(_IN.TOKEN_REGISTRY, "get-residual")
        else
            (_IN.TOKEN_REGISTRY["get-residual"] = _had_tok)
        end
        if _had_typ === nothing
            delete!(_IN._GROUNDED_OP_TYPES, _IN.GET_RESIDUAL)
        else
            (_IN._GROUNDED_OP_TYPES[_IN.GET_RESIDUAL] = _had_typ)
        end
        _IN.abolish_all_tables!()
        _IN.untable_all!()
    end
end
