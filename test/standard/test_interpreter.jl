# Validates the `metta` interpreter driver (metta.md §Interpretation, untyped Phase 1a) — full
# reduction, applicative order, nondeterminism — distinct from one-step `eval`.
using MeTTaCore.Eval                  # precompiled submodule (was: include fresh → recompiled per file)
using MeTTaCore.StandardMeTTa
using Test

S(x) = Sym(x); V(x) = Var(x); E(xs...) = Expression(collect(Atom, xs)...)
rule(lhs, rhs) = E(S("="), lhs, rhs)

@testset "metta driver (metta.md §Interpretation, untyped)" begin
    # FULL reduction (vs eval's one step): (foo)→(bar)→a ⇒ metta((foo)) = a
    sp = Space(Atom[rule(E(S("foo")), E(S("bar"))), rule(E(S("bar")), S("a"))])
    @test metta_run(E(S("foo")), sp) == Atom[S("a")]

    # APPLICATIVE order (vs eval NotReducible): (+ 1 (+ 2 3)) → 6
    @test metta_run(E(PLUS, Grounded(1), E(PLUS, Grounded(2), Grounded(3))), Space()) == Atom[Grounded(6)]

    # plain arithmetic + a defined function reducing through grounded
    sp2 = Space(Atom[rule(E(S("inc"), V("n")), E(PLUS, V("n"), Grounded(1)))])
    @test metta_run(E(S("inc"), Grounded(41)), sp2) == Atom[Grounded(42)]

    # NONDETERMINISM: three equalities for (color) ⇒ fan-out to {red, green, blue}
    spc = Space(Atom[rule(E(S("color")), S("red")), rule(E(S("color")), S("green")),
                     rule(E(S("color")), S("blue"))])
    @test Set(metta_run(E(S("color")), spc)) == Set(Atom[S("red"), S("green"), S("blue")])

    # nondeterminism fans through an enclosing expression: (pair (color)) → 3 results
    spp = Space(Atom[rule(E(S("color")), S("red")), rule(E(S("color")), S("green"))])
    res = metta_run(E(S("pair"), E(S("color"))), spp)   # (pair red), (pair green) — pair undefined → as-is
    @test Set(res) == Set(Atom[E(S("pair"), S("red")), E(S("pair"), S("green"))])

    # non-reducible stays as-is: unknown symbol / unknown function
    @test metta_run(S("hello"), Space()) == Atom[S("hello")]
    @test metta_run(E(S("nope"), Grounded(1)), Space()) == Atom[E(S("nope"), Grounded(1))]
end

# Regression: `case` and `foldl-atom` must DISTRIBUTE / FORK over a nondeterministic argument, not
# collapse to one result. Verified against 4 reference engines (hyperon-experimental / CeTTa / MeTTa-TS /
# PeTTa): (case (superpose (a b c)) …) → [a,b,c]; foldl of a superpose op forks the accumulator. Before
# the 2026-07-12 fix Core returned a single result (case: flattened loop break-both; foldl: acc=rs[1]).
@testset "case / foldl distribute over nondeterminism (4-engine verified)" begin
    sp = Space(); load_core_stdlib!(sp)
    q(s) = load_metta!(sp, s)
    # case distributes: N alternatives → N results (catch-all clause)
    @test Set(q(raw"!(case (superpose (a b c)) (($x $x)))")) == Set(Atom[S("a"), S("b"), S("c")])
    @test Set(q(raw"!(case (superpose (1 2)) ((1 one) (2 two)))")) == Set(Atom[S("one"), S("two")])
    # a no-match alternative is dropped (hyperon/CeTTa arbiter — not laundered to Empty)
    @test Set(q(raw"!(case (superpose (1 2 9)) ((1 one) (2 two)))")) == Set(Atom[S("one"), S("two")])
    # deterministic case unchanged
    @test q("!(case foo ((foo matched) (bar other)))") == Atom[S("matched")]
    # foldl forks over a nondeterministic op → multiset {0,2,2,3} (4 paths), not one
    let r = q(raw"!(foldl-atom (1 2) 0 $a $b (superpose ((+ $a $b) (* $a $b))))")
        @test length(r) == 4
        @test Set(r) == Set(Atom[Grounded(0), Grounded(2), Grounded(3)])
    end
    # deterministic foldl unchanged
    @test q(raw"!(foldl-atom (1 2 3) 0 $a $b (+ $a $b))") == Atom[Grounded(6)]
end

@testset "metta driver: gradual types — if / let (lazy args, Phase 1b)" begin
    decl(n, ty) = E(S(":"), S(n), ty)
    arrow(xs...) = E(S("->"), xs...)

    # if: (: if (-> Bool Atom Atom $t)) + the two = rules ; (boom) loops forever
    spif = Space(Atom[
        decl("if", arrow(S("Bool"), S("Atom"), S("Atom"), V("t"))),
        rule(E(S("if"), S("True"),  V("then"), V("else")), V("then")),
        rule(E(S("if"), S("False"), V("then"), V("else")), V("else")),
        rule(E(S("boom")), E(S("boom")))])
    # the DEAD branch (boom) must NOT be evaluated (else: infinite loop → step-limit error)
    @test metta_run(E(S("if"), S("True"),  S("a"), E(S("boom"))), spif) == Atom[S("a")]
    @test metta_run(E(S("if"), S("False"), E(S("boom")), S("b")), spif) == Atom[S("b")]

    # let: (: let (-> Atom %Undefined% Atom %Undefined%)); body via `unify` (a minimal op)
    splet = Space(Atom[
        decl("let", arrow(S("Atom"), S("%Undefined%"), S("Atom"), S("%Undefined%"))),
        rule(E(S("let"), V("p"), V("a"), V("tpl")),
             E(S("unify"), V("a"), V("p"), V("tpl"), S("Empty")))])
    # (let $x (+ 1 2) (g $x)) → (g 3): $a evaluated (%Undefined%), $p/$tpl lazy (Atom), unify binds $x
    @test metta_run(E(S("let"), V("x"), E(PLUS, Grounded(1), Grounded(2)), E(S("g"), V("x"))), splet) ==
          Atom[E(S("g"), Grounded(3))]
end

@testset "metta parser + loader (metta.md §Syntax) — end to end from text" begin
    prog = """
    ; `if` defined as = rules, loaded from TEXT (not constructed)
    (: if (-> Bool Atom Atom \$t))
    (= (if True  \$t \$e) \$t)
    (= (if False \$t \$e) \$e)
    (= (double \$x) (+ \$x \$x))
    !(if True a b)          ; → a
    !(+ 1 (* 2 3))          ; → 7  (applicative: (* 2 3) first)
    !(double 21)            ; → 42
    """
    results = load_metta!(Space(), prog)
    @test results == Atom[S("a"), Grounded(7), Grounded(42)]

    # tokenizer/parse spot checks
    @test tokenize("(a \$x 1)") == ["(", "a", "\$x", "1", ")"]
    let (d, atom) = parse_program("!(+ 1 2)")[1]
        @test d == true && atom == E(PLUS, Grounded(1), Grounded(2))
    end
end

# Control accel #2 — the per-bucket discrimination trie (CeTTa subst_tree borrow) is a CONSERVATIVE candidate
# filter: on a WIDE same-discriminant bucket (> _TRIE_MIN_BUCKET) `query` must return EXACTLY the linear-scan
# result (never drop or duplicate a match) across every pattern shape. Guards the asymptotic fan-out fix.
@testset "query: wide-bucket discrimination trie ≡ linear scan" begin
    G(x) = Grounded(x)
    # a pure linear reference over ALL atoms (== bucket+wildcard match set for a keyed pattern), trie-independent.
    # Compare the resolved output multiset (stable across fresh-renames) so a wrong-atom-but-right-count trie bug fails.
    linref(s, p) = (acc = Bindings[]; for a in Eval.all_atoms(s); append!(acc, match_atoms(p, Eval.rename_fresh(a))); end; acc)
    outs(bs, p) = sort(String[string(Eval.subst(p, b)) for b in bs])       # resolved match instances

    s = Space()
    for k in 1:30; Eval.add_atom!(s, E(S("rel"), S("a"), S("v$k"))); end   # 30 ground facts
    Eval.add_atom!(s, E(S("rel"), S("a"), V("x")))                          # pos-3 wildcard rule
    Eval.add_atom!(s, E(S("rel"), S("a"), E(S("g"), S("b"))))              # nested
    Eval.add_atom!(s, E(S("rel"), S("a"), G(5)))                            # grounded
    @test length(s.store.index[(:rel, :a)]) > Eval._TRIE_MIN_BUCKET              # trie actually fires

    pats = [E(S("rel"), S("a"), S("v5")), E(S("rel"), S("a"), V("o")), E(S("rel"), S("a"), S("v99")),
            E(S("rel"), S("a"), E(S("g"), S("b"))), E(S("rel"), S("a"), E(S("g"), V("z"))),
            E(S("rel"), S("a"), G(5))]
    for p in pats
        q = Eval.query(s, p); r = linref(s, p)
        @test length(q) == length(r)
        @test outs(q, p) == outs(r, p)            # resolved instances identical ⇒ no dropped/wrong/dup match
    end
    # invalidation: adding to the bucket rebuilds the trie ⇒ new atom is found
    Eval.add_atom!(s, E(S("rel"), S("a"), S("vNEW")))
    @test length(Eval.query(s, E(S("rel"), S("a"), S("vNEW")))) ==
          length(linref(s, E(S("rel"), S("a"), S("vNEW"))))
end

# Borrow 2 — revision-stamped SLG table invalidation (CeTTa table_store.c:153). A tabled goal's cached answer set
# is stamped with the space (objectid, revision); a mutation bumps `revision` so the stale entry auto-evicts on the
# next lookup and recomputes — closing the "table goes silently stale on space mutation" hole (§7.7).
@testset "🔴 TABLING COLLAPSES MULTIPLICITY — MeTTa is multiset, the answer table is a SET" begin
    # PINS A REAL SOUNDNESS DEFECT, found 2026-08-16 while trying to auto-table the compiled lane
    # (roadmap 2.2). This is NOT auto-tabling's bug — `_leader_pass` has always merged answers with
    # `unique(vcat(…))`, so **explicit `table!(h)` has always had it**; auto-tabling merely made it
    # reachable on five corpus scripts at once (b1_equal_chain +1, b2_backchain +2, d3_deptypes +1,
    # d4_type_prop +1, e1_kb_write +1 — the LeaTTa PROVED corpus caught every one).
    #
    # THE TENSION IS FUNDAMENTAL, not a patch-in-waiting: tabling REQUIRES set semantics to reach a
    # fixpoint. Dropping `unique` would make the answer set grow forever and never converge. So this
    # is a constraint on WHICH HEADS MAY BE TABLED, not a merge to fix.
    #
    # ⚠️ UPSTREAM ALREADY GUARDS IT AND WE DISMISSED THE GUARD. JeTTa's gate requires
    # `!f.isMultivalued()` (`jetta/backend/.../Generator.kt:166` — "Pure ⇔ **not multivalued**,
    # primitive args + result"). On 2026-08-15 that was called "a downgrade — our SLG handles
    # multi-answer". Handling multi-answer as a SET is not preserving MULTIPLICITY. See roadmap 2.1.
    #
    # 🟢 UPDATED 2026-08-16 — THE MULTIVALUED GUARD LANDED (roadmap 2.0). This no longer asserts only
    # the defect. It now pins BOTH entry points, which behave differently ON PURPOSE:
    #
    #   auto_table!  — AUTOMATIC, so it must be conservative: it refuses any head whose multiplicity
    #                  would be observable, and `!(k)` keeps [1,1].
    #   table!       — the EXPLICIT user directive, the analogue of `:- table h/0`. Upstream does not
    #                  second-guess a declaration, and neither do we, so this STILL collapses. That is
    #                  the user's call, not a silent automatic decision.
    #
    # The distinction matters: the original defect was that the AUTOMATIC path made the collapse
    # reachable on five corpus scripts at once. Making `table!` refuse would instead make a documented
    # Prolog directive fail, and tabling IS set-semantics by design everywhere.
    Eval.untable_all!()
    try
        prog = "(= (h) 1)\n(= (h) 1)\n(= (k) (h))\n"          # two IDENTICAL rules ⇒ two answers
        s = Space(); load_core_stdlib!(s); load_metta!(s, prog)
        @test length(load_metta!(s, "!(k)\n")) == 2            # UNTABLED: multiset preserved, [1, 1]

        # ── AUTOMATIC: the guard refuses, and multiplicity SURVIVES. `k` is caught by PROPAGATION —
        # its single rule cannot overlap anything, but it CALLS `h`, so it inherits multivaluedness.
        # The head-local overlap test alone left `k` tabled and `!(k)` still collapsed; measured.
        Eval.untable_all!()
        s2 = Space(); load_core_stdlib!(s2); load_metta!(s2, prog)
        r = Eval.auto_table!(s2)
        @test :h in r.multivalued
        @test :k in r.multivalued                              # inherited through the call graph
        @test isempty(intersect(Symbol[:h, :k], r.tabled))
        @test length(load_metta!(s2, "!(k)\n")) == 2           # TABLED-BY-AUTO: [1, 1] preserved

        # ── EXPLICIT: still collapses, by design. Kept so the semantic mismatch stays visible.
        Eval.untable_all!()
        s3 = Space(); load_core_stdlib!(s3); load_metta!(s3, prog)
        Eval.table!(:k); Eval.table!(:h)
        @test length(load_metta!(s3, "!(k)\n")) == 1           # the user asked for set semantics

        # ── a DISJOINT-pattern head is NOT refused: `length(rules) > 1` would have excluded it, which
        # is why the guard tests UNIFIABILITY instead. This is the case that signal got wrong.
        Eval.untable_all!()
        s4 = Space(); load_core_stdlib!(s4)
        load_metta!(s4, "(= (f a) 1)\n(= (f b) 2)\n")
        @test !(:f in Eval.auto_table!(s4).multivalued)
    finally
        Eval.untable_all!()
    end
end

@testset "tabling: revision-stamped answer invalidation" begin
    Eval.untable_all!()
    Eval.table!(Symbol("mem"))
    try
        s = Space()
        for p in ["(= (mem) (collapse (match &self (item \$x) \$x)))", "(item a)", "(item b)"]
            for (_, atom) in parse_program(p); Eval.add_atom!(s, atom); end
        end
        q = parse_program("(mem)")[1][2]
        r1 = string(metta_run(q, s))                          # cached at the current revision
        rev1 = s.revision
        for (_, atom) in parse_program("(item c)"); Eval.add_atom!(s, atom); end
        @test s.revision > rev1                               # mutation bumped the revision
        r2 = string(metta_run(q, s))                          # stale entry must be evicted + recomputed
        @test !occursin("c", r1)                              # baseline: c not yet present
        @test occursin("c", r2)                               # fresh: recomputed answer includes the new fact
    finally
        Eval.untable_all!()
    end
end

# Auto-tabler — the purity-analysis FRONT-END to table! (MeTTa-TS `automatic tabling of pure functions`):
# analyze &self, table PURE user function heads, skip impure ones (add-atom / state / match / …). Result-
# preserving (tabling only memoises a pure answer set); the impure fn still runs, just untabled.
@testset "auto-tabler: purity classification + result-identity + impure-skip + surface" begin
    Eval.untable_all!()
    try
        fib = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))"
        # classification: pure fib/dbl tabled; impure remember (add-atom) skipped
        s = Space(); load_core_stdlib!(s); load_metta!(s, fib)
        load_metta!(s, raw"(= (dbl $x) (* $x 2))")
        load_metta!(s, raw"(= (remember $x) (add-atom &self (seen $x)))")
        r = Eval.auto_table!(s)
        @test :fib in r.tabled && :dbl in r.tabled
        @test :remember in r.skipped && !(:remember in r.tabled)
        @test Eval.is_tabled(parse_program("(fib 5)")[1][2])       # fib really registered
        @test !Eval.is_tabled(parse_program("(remember z)")[1][2]) # impure not registered

        # result-identity: auto-tabled fib(10) == untabled fib(10) (order matters — tabling is global)
        Eval.untable_all!()
        u = Space(); load_core_stdlib!(u); load_metta!(u, fib)
        got_untabled = string(load_metta!(u, "!(fib 10)"))                # _TABLED_HEADS empty here
        t = Space(); load_core_stdlib!(t); load_metta!(t, fib); Eval.auto_table!(t)
        got_tabled = string(load_metta!(t, "!(fib 10)"))                  # fib now tabled
        @test got_untabled == got_tabled && occursin("55", got_tabled)    # fib(10)=55, identical

        # impure fn still WORKS (mutates) despite being skipped
        Eval.untable_all!()
        s3 = Space(); load_core_stdlib!(s3)
        load_metta!(s3, raw"(= (remember $x) (add-atom &self (seen $x)))")
        Eval.auto_table!(s3)
        load_metta!(s3, "!(remember foo)")
        @test occursin("foo", string(load_metta!(s3, raw"!(match &self (seen $x) $x)")))

        # surface: the !(auto-table!) directive tables + reports; the auto_table=true load flag tables
        Eval.untable_all!()
        s4 = Space(); load_core_stdlib!(s4); load_metta!(s4, fib)
        @test occursin("fib", string(load_metta!(s4, "!(auto-table!)")))
        @test Eval.is_tabled(parse_program("(fib 1)")[1][2])
        Eval.untable_all!()
        s5 = Space(); load_core_stdlib!(s5); load_metta!(s5, fib; auto_table = true)
        @test Eval.is_tabled(parse_program("(fib 1)")[1][2])

        # ── PURITY MUST SURVIVE COMPILATION (roadmap 0.1, fixed 2026-08-16) ──────────────────────
        # `EmitIL` lowers a definition to `(= (fib $n) (function (chain (metta …) …)))`. Until the
        # minimal-MeTTa control instructions were whitelisted in `_PURE_PRIMS`, `_pure_heads` — a
        # WHITELIST fixpoint, so an unknown op means impure — classified EVERY COMPILED HEAD impure.
        # MEASURED before the fix: `:fib` pure in SOURCE form = true, in IL form = FALSE.
        # ⇒ every purity-gated consumer was SILENTLY INERT on the compiled lane; `auto_table!` on
        # `compile_run`'s output did literally nothing, with no error and no observable difference.
        # That is why this is pinned: a silent no-op leaves nothing to notice if it comes back.
        Eval.untable_all!()
        sIL = Space(); load_core_stdlib!(sIL)
        il = MeTTaCore.compile_definition(sIL, fib)
        @test il !== nothing                                    # guard: the corpus must still compile fib
        for a in il.atoms; Eval.add_atom!(sIL, a); end
        @test :fib in Eval._pure_heads(Eval._rules_of(Eval.all_atoms(sIL)))   # ← the fix
        @test Eval.auto_table!(sIL).tabled == [:fib]            # and it now actually TABLES

        # 🔴 NEGATIVE CONTROL — the whitelist must not have opened a hole. `_callees!` recurses into
        # every child, so a mutator nested INSIDE `(metta …)` must still surface and fail the head.
        # Without this, whitelisting `metta` would silently make every compiled body look pure.
        Eval.untable_all!()
        sIM = Space(); load_core_stdlib!(sIM)
        ilm = MeTTaCore.compile_definition(sIM, raw"(= (bump $x) (add-atom &self (seen $x)))")
        if ilm !== nothing                                       # (if the compiler declines it, nothing to check)
            for a in ilm.atoms; Eval.add_atom!(sIM, a); end
            @test !(:bump in Eval._pure_heads(Eval._rules_of(Eval.all_atoms(sIM))))
        end
    finally
        Eval.untable_all!()
    end
end

# FAST-MATCH — opt-in skip of rename_fresh when it is provably a no-op on the result (goal ground + rule
# closed ⇒ ground result). Correctness gate: results must be BYTE-IDENTICAL to the rename path (alpha-
# normalized for the fresh-var counter, which advances globally between the two runs). Default OFF.
@testset "fast-match: byte-identical to rename path (flag-gated) + closed-rule predicate" begin
    Eval.fast_match!(false)
    try
        norm(rs) = sort([replace(string(x), r"#\d+" => "#N") for x in rs])   # alpha-normalize gensym ids
        run1(prog, q) = (s = Space(); load_core_stdlib!(s); load_metta!(s, prog); load_metta!(s, q))
        for (prog, q) in [
                (raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))", "!(fib 10)"),  # closed+ground → fast fires
                (raw"(= (g $x) (h $x $y))", "!(g a)"),                     # unbound RHS var → NOT closed → falls back
                (raw"(= (pick) (superpose (a b c)))", "!(pick)"),          # nondeterministic closed
                (raw"(= (poly $x) (+ (* $x $x) (* 2 $x)))", "!(poly 5)"),  # nested pure
                (raw"(= (idx (pair $a $b)) $a)", raw"!(idx (pair x y))")]  # var in goal → NOT ground → falls back
            Eval.fast_match!(false); off = norm(run1(prog, q))
            Eval.fast_match!(true);  on  = norm(run1(prog, q))
            Eval.fast_match!(false)
            @test off == on
        end
        # closed-rule predicate: vars(RHS) ⊆ vars(LHS)
        @test Eval._is_closed_rule(parse_program(raw"(= (fib $n) (fib (- $n 1)))")[1][2])
        @test !Eval._is_closed_rule(parse_program(raw"(= (g $x) (h $x $y))")[1][2])   # $y RHS-only
        @test !Eval._is_closed_rule(parse_program("(foo bar)")[1][2])                 # not a (= …) rule
    finally
        Eval.fast_match!(false)
    end
end

@testset "case: empty subject matches the `Empty` clause (hyperon; LeaTTa proved-oracle)" begin
    # LeaTTa (Lean-4 machine-proved MeTTa) differential, 2026-07-08: Core's `case` collapsed an
    # EMPTY result set to `()` and so missed the literal `Empty` clause — hyperon's rule
    # (stdlib.metta §case) is: empty subject ⇒ the `Empty` pattern fires. Fixed in Eval.jl.
    s = Space(); load_core_stdlib!(s)
    # subject with NO results (unify miss) ⇒ the `Empty` clause, NOT the `()`/wildcard clause
    @test load_metta!(s, "!(case (unify (A B) (C D) ok Empty) ((ok yes) (Empty nok)))") == Atom[S("nok")]
    @test load_metta!(s, "!(case Empty ((ok yes) (Empty nok)))")                          == Atom[S("nok")]
    # regression — non-empty subjects are unaffected (first matching clause still wins)
    @test load_metta!(s, "!(case (unify (A B) (A B) ok Empty) ((ok yes) (Empty nok)))") == Atom[S("yes")]
    @test load_metta!(s, "!(case foo ((foo yes) (Empty nok)))")                          == Atom[S("yes")]
end

@testset "get-atoms enumeration is INERT — never re-fires a stored (=) body (regression, omission 638bc7f)" begin
    # Fixed by the `(-> %Undefined% Atom)` intrinsic type on GET_ATOMS. Untyped, get-atoms re-mettad each
    # enumerated result under the caller's %Undefined% type, so a stored side-effecting rule
    # `(= (r) (add-atom &d …))` had its BODY re-reduced and the `add-atom` RE-FIRED (get-atoms returned
    # `(= (r) ())` — body reduced to unit). Oracle: hyperon/PeTTa/CeTTa are all INERT here — get-atoms is
    # pure data retrieval (hyperon GetAtomsOp::type_ = `(-> Space Atom)`; the `Atom` return routes results
    # through interpreter.rs:1005 `typ==Atom ⇒ return verbatim`). The bug was invisible to LeaTTa/234-
    # conformance because no corpus test enumerates a rule-holding space (5-engine differential in scratchpad).
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, raw"!(bind! &d (new-space))")
    load_metta!(s, raw"!(add-atom &d (item x))")
    load_metta!(s, raw"!(bind! &prog (new-space))")
    load_metta!(s, raw"!(add-atom &prog (= (r) (add-atom &d (SIDE))))")
    @test isempty(load_metta!(s, raw"!(match &d (SIDE) fired)"))           # (SIDE) absent before enumeration
    load_metta!(s, raw"!(get-atoms &prog)")                               # enumerate the rule-holding space
    @test isempty(load_metta!(s, raw"!(match &d (SIDE) fired)"))           # STILL absent ⇒ INERT (was [fired] = bug)
    @test occursin("add-atom", string(load_metta!(s, raw"!(collapse (get-atoms &prog))")))  # body intact, not ()
    # the fix must NOT break normal enumeration of inert data:
    s2 = Space(); load_core_stdlib!(s2)
    load_metta!(s2, raw"!(bind! &x (new-space))")
    load_metta!(s2, raw"!(add-atom &x (fact a))"); load_metta!(s2, raw"!(add-atom &x (fact b))")
    @test load_metta!(s2, raw"!(size-atom (collapse (get-atoms &x)))") == Atom[Grounded(2)]
end

# ── SLG ANSWER-TABLE STALENESS — a CHARACTERISATION test for an invariant, not a regression test ──
#
# ⚠️ READ BEFORE DELETING. This test reaches into `sp.store.atoms` directly, which NO production code
# does and which looks like a deliberate violation of the store API. That is the point: it is the
# only way to express the invariant, because the invariant is currently upheld by there being
# nowhere else to write.
#
# WHAT IT PINS. `revision` stamps SLG answer tables (`Eval.jl:1394` compares
# `(objectid(space), space.revision)` against a stored stamp; `:1441` writes it). The comparison is a
# pure EQUALITY test — SLG never counts revisions or diffs them, it only asks "same revision as when
# I cached this?". So any value that CHANGES on mutation satisfies it, and batching many writes into
# one bump is sound. What is NOT sound is a mutation that does not bump at all.
#
# MEASURED 2026-08-15:
#     below-API push into store.atoms   revision 124 -> 124   query -> [1]      STALE
#     the same atom via add_atom!       revision 124 -> 125   query -> [1, 2]   correct
# Same space, same tabled head, same atom. The stale answer arrives with no error and is
# indistinguishable from a correct one.
#
# 🔴 THIS IS LATENT, NOT LIVE — and the distinction is why the test exists. Every `Eval` write
# funnels through `add_atom!`/`remove_atom!`, both of which bump; `space_metta_calculus!` writes a
# MORK PathMap, which a `VectorStore` does not have. So no current path reaches this. The invariant
# "all mutations go through the API" is holding by ACCIDENT OF THERE BEING ONE STORE.
#
# WHAT MAKES IT LIVE: a trie-backed store (`Space{S<:AbstractStore}` + a MORK store). The calculus
# writes underneath via `set_val_at!`/`remove_val_at!`, bypassing the API entirely. The seam does not
# INTRODUCE this bug — it removes the only thing preventing it.
#
# THE FIX THIS ARGUES FOR: bump where the WRITES LAND rather than where the API is called, so a
# trie-backed store is correct by construction rather than by discipline. When that lands, this test
# flips from characterisation to guarded and the direct push should stop producing a stale answer.
@testset "SLG staleness — a mutation that does not bump `revision` serves a stale answer" begin
    Eval.untable_all!()
    try
        # BELOW THE API — the shape of a trie written from underneath.
        s1 = Space()
        for (_, a) in parse_program("(= (p) 1)"); Eval.add_atom!(s1, a); end
        Eval.table!(Symbol("p"))
        q = parse_program("(p)")[1][2]
        string(metta_run(q, s1))                       # populate the answer table
        rev0 = s1.revision
        for (_, a) in parse_program("(= (p) 2)")
            push!(s1.store.atoms, a)                   # ← DELIBERATE API BYPASS; see the note above
        end
        @test s1.revision == rev0                      # the mutation did NOT bump
        @test !occursin("2", string(metta_run(q, s1))) # ← the defect: the new clause is invisible

        # THROUGH THE API — POSITIVE CONTROL. Without it the assertion above would also pass for an
        # engine where tabling simply never returned a second answer.
        s2 = Space()
        for (_, a) in parse_program("(= (r) 1)"); Eval.add_atom!(s2, a); end
        Eval.table!(Symbol("r"))
        q2 = parse_program("(r)")[1][2]
        string(metta_run(q2, s2))
        rev1 = s2.revision
        for (_, a) in parse_program("(= (r) 2)"); Eval.add_atom!(s2, a); end
        @test s2.revision > rev1                       # the API DID bump
        @test occursin("2", string(metta_run(q2, s2))) # so the table invalidated and recomputed
        # ⚠️ DO NOT DECLARE THIS FIXED ON THE STRENGTH OF THIS TEST. A hand `push!` into
        # store.atoms bypasses EVERY layer, so it keeps failing to bump no matter where the bump is
        # relocated — this assertion can pass for the wrong reason forever. The measurement that
        # matters is a CALCULUS write (space_metta_calculus! mutating the trie underneath), and it
        # cannot be written until a trie-backed store exists.
        # ⚠️ THE RELOCATION IS ALSO NOT A LAYER-DOWN MOVE: set_val_at!/remove_val_at! belong to
        # PathMap (WriteZipper.jl:595-639), and the calculus calls them DIRECTLY on s.btm
        # (MORK Space.jl:232-234, 1771) — so a Core-side wrapper is bypassed by the very writer that
        # motivates it. Either MORK.Space carries the bump, or the store DERIVES a stamp from a cheap
        # trie identity; the latter works only because SLG tests EQUALITY and never counts.
        # ⚠️ BUT DO NOT PRICE THE DERIVED STAMP AS THE CLEANER OPTION UNTIL THIS IS CHECKED: it
        # needs an identity that is CHEAP *and* CURRENT AFTER EVERY CALCULUS WRITE, and those may
        # pull against each other. `map_hash` (PathMap Morphisms.jl:420) hashes ON DEMAND — it does
        # not maintain a root — so deriving from it means either hashing per query (not cheap) or
        # caching the hash, and a cache needs to know when to invalidate, which is THIS PROBLEM
        # RESTATED. If no maintained identity exists, the option is circular and MORK.Space carrying
        # the bump is the only shape left. OPEN Morphisms.jl AND CHECK before deciding the struct —
        # this determines whether the store owns a COUNTER or observes a HASH, and they are
        # different structs, so discovering it during the seam means discovering it by rewriting.
        # ✅ CHECKED 2026-08-15: `map_hash` (Morphisms.jl:420) is an ON-DEMAND `cata_cached` fold —
        # no maintained root, no cached-hash field, no dirty flag in PathMapCore.jl or Morphisms.jl.
        # So the derived stamp IS circular and MORK.Space carrying the bump is the only shape left.
        # ⚠️ NOT EXHAUSTIVE — two files, four synonyms. Run `capability_search.sh` over PathMap with
        # a few more before building on it; an incremental digest under another name flips this.
        #
        # TWO THINGS TO SETTLE WHEN THE WORK STARTS, both cheap and both easy to get wrong late:
        #  1. HOW MANY SITES? `space_metta_calculus!` may already funnel writes through the SINKS
        #     (AddSink/RemoveSink, Sinks.jl) rather than calling set_val_at! scattered through the
        #     calculus. If it does, the bump is one or two sites in MORK.Space, not a sweep — and
        #     the "a Core concern living in MORK" objection shrinks to one counter field plus a
        #     comment naming who reads it.
        #  2. WHO OWNS THE COUNTER? If MORK.Space bumps, does Core's add_atom! STOP bumping, or do
        #     both and the counter merely moves faster? Double-bumping is HARMLESS under
        #     equality-only semantics — but two writers to one counter with unclear ownership is
        #     what reads as a bug six months later. Decide it explicitly, in a comment, either way.
    finally
        Eval.untable_all!()                            # _TABLED_HEADS is PROCESS-GLOBAL — never leak it
    end
end
