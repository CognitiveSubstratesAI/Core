# Validates the `metta` interpreter driver (metta.md §Interpretation, untyped Phase 1a) — full
# reduction, applicative order, nondeterminism — distinct from one-step `eval`.
using MeTTaCore.Interpreter                  # precompiled submodule (was: include fresh → recompiled per file)
using MeTTaCore.Interpreter.StandardMeTTa
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
    linref(s, p) = (acc = Bindings[]; for a in s.atoms; append!(acc, match_atoms(p, Interpreter.rename_fresh(a))); end; acc)
    outs(bs, p) = sort(String[string(Interpreter.subst(p, b)) for b in bs])       # resolved match instances

    s = Space()
    for k in 1:30; Interpreter.add_atom!(s, E(S("rel"), S("a"), S("v$k"))); end   # 30 ground facts
    Interpreter.add_atom!(s, E(S("rel"), S("a"), V("x")))                          # pos-3 wildcard rule
    Interpreter.add_atom!(s, E(S("rel"), S("a"), E(S("g"), S("b"))))              # nested
    Interpreter.add_atom!(s, E(S("rel"), S("a"), G(5)))                            # grounded
    @test length(s.index[(:rel, :a)]) > Interpreter._TRIE_MIN_BUCKET              # trie actually fires

    pats = [E(S("rel"), S("a"), S("v5")), E(S("rel"), S("a"), V("o")), E(S("rel"), S("a"), S("v99")),
            E(S("rel"), S("a"), E(S("g"), S("b"))), E(S("rel"), S("a"), E(S("g"), V("z"))),
            E(S("rel"), S("a"), G(5))]
    for p in pats
        q = Interpreter.query(s, p); r = linref(s, p)
        @test length(q) == length(r)
        @test outs(q, p) == outs(r, p)            # resolved instances identical ⇒ no dropped/wrong/dup match
    end
    # invalidation: adding to the bucket rebuilds the trie ⇒ new atom is found
    Interpreter.add_atom!(s, E(S("rel"), S("a"), S("vNEW")))
    @test length(Interpreter.query(s, E(S("rel"), S("a"), S("vNEW")))) ==
          length(linref(s, E(S("rel"), S("a"), S("vNEW"))))
end

# Borrow 2 — revision-stamped SLG table invalidation (CeTTa table_store.c:153). A tabled goal's cached answer set
# is stamped with the space (objectid, revision); a mutation bumps `revision` so the stale entry auto-evicts on the
# next lookup and recomputes — closing the "table goes silently stale on space mutation" hole (§7.7).
@testset "tabling: revision-stamped answer invalidation" begin
    Interpreter.untable_all!()
    Interpreter.table!(Symbol("mem"))
    try
        s = Space()
        for p in ["(= (mem) (collapse (match &self (item \$x) \$x)))", "(item a)", "(item b)"]
            for (_, atom) in parse_program(p); Interpreter.add_atom!(s, atom); end
        end
        q = parse_program("(mem)")[1][2]
        r1 = string(metta_run(q, s))                          # cached at the current revision
        rev1 = s.revision
        for (_, atom) in parse_program("(item c)"); Interpreter.add_atom!(s, atom); end
        @test s.revision > rev1                               # mutation bumped the revision
        r2 = string(metta_run(q, s))                          # stale entry must be evicted + recomputed
        @test !occursin("c", r1)                              # baseline: c not yet present
        @test occursin("c", r2)                               # fresh: recomputed answer includes the new fact
    finally
        Interpreter.untable_all!()
    end
end

# Auto-tabler — the purity-analysis FRONT-END to table! (MeTTa-TS `automatic tabling of pure functions`):
# analyze &self, table PURE user function heads, skip impure ones (add-atom / state / match / …). Result-
# preserving (tabling only memoises a pure answer set); the impure fn still runs, just untabled.
@testset "auto-tabler: purity classification + result-identity + impure-skip + surface" begin
    Interpreter.untable_all!()
    try
        fib = raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))"
        # classification: pure fib/dbl tabled; impure remember (add-atom) skipped
        s = Space(); load_core_stdlib!(s); load_metta!(s, fib)
        load_metta!(s, raw"(= (dbl $x) (* $x 2))")
        load_metta!(s, raw"(= (remember $x) (add-atom &self (seen $x)))")
        r = Interpreter.auto_table!(s)
        @test :fib in r.tabled && :dbl in r.tabled
        @test :remember in r.skipped && !(:remember in r.tabled)
        @test Interpreter.is_tabled(parse_program("(fib 5)")[1][2])       # fib really registered
        @test !Interpreter.is_tabled(parse_program("(remember z)")[1][2]) # impure not registered

        # result-identity: auto-tabled fib(10) == untabled fib(10) (order matters — tabling is global)
        Interpreter.untable_all!()
        u = Space(); load_core_stdlib!(u); load_metta!(u, fib)
        got_untabled = string(load_metta!(u, "!(fib 10)"))                # _TABLED_HEADS empty here
        t = Space(); load_core_stdlib!(t); load_metta!(t, fib); Interpreter.auto_table!(t)
        got_tabled = string(load_metta!(t, "!(fib 10)"))                  # fib now tabled
        @test got_untabled == got_tabled && occursin("55", got_tabled)    # fib(10)=55, identical

        # impure fn still WORKS (mutates) despite being skipped
        Interpreter.untable_all!()
        s3 = Space(); load_core_stdlib!(s3)
        load_metta!(s3, raw"(= (remember $x) (add-atom &self (seen $x)))")
        Interpreter.auto_table!(s3)
        load_metta!(s3, "!(remember foo)")
        @test occursin("foo", string(load_metta!(s3, raw"!(match &self (seen $x) $x)")))

        # surface: the !(auto-table!) directive tables + reports; the auto_table=true load flag tables
        Interpreter.untable_all!()
        s4 = Space(); load_core_stdlib!(s4); load_metta!(s4, fib)
        @test occursin("fib", string(load_metta!(s4, "!(auto-table!)")))
        @test Interpreter.is_tabled(parse_program("(fib 1)")[1][2])
        Interpreter.untable_all!()
        s5 = Space(); load_core_stdlib!(s5); load_metta!(s5, fib; auto_table = true)
        @test Interpreter.is_tabled(parse_program("(fib 1)")[1][2])
    finally
        Interpreter.untable_all!()
    end
end

# FAST-MATCH — opt-in skip of rename_fresh when it is provably a no-op on the result (goal ground + rule
# closed ⇒ ground result). Correctness gate: results must be BYTE-IDENTICAL to the rename path (alpha-
# normalized for the fresh-var counter, which advances globally between the two runs). Default OFF.
@testset "fast-match: byte-identical to rename path (flag-gated) + closed-rule predicate" begin
    Interpreter.fast_match!(false)
    try
        norm(rs) = sort([replace(string(x), r"#\d+" => "#N") for x in rs])   # alpha-normalize gensym ids
        run1(prog, q) = (s = Space(); load_core_stdlib!(s); load_metta!(s, prog); load_metta!(s, q))
        for (prog, q) in [
                (raw"(= (fib $n) (if (< $n 2) $n (+ (fib (- $n 1)) (fib (- $n 2)))))", "!(fib 10)"),  # closed+ground → fast fires
                (raw"(= (g $x) (h $x $y))", "!(g a)"),                     # unbound RHS var → NOT closed → falls back
                (raw"(= (pick) (superpose (a b c)))", "!(pick)"),          # nondeterministic closed
                (raw"(= (poly $x) (+ (* $x $x) (* 2 $x)))", "!(poly 5)"),  # nested pure
                (raw"(= (idx (pair $a $b)) $a)", raw"!(idx (pair x y))")]  # var in goal → NOT ground → falls back
            Interpreter.fast_match!(false); off = norm(run1(prog, q))
            Interpreter.fast_match!(true);  on  = norm(run1(prog, q))
            Interpreter.fast_match!(false)
            @test off == on
        end
        # closed-rule predicate: vars(RHS) ⊆ vars(LHS)
        @test Interpreter._is_closed_rule(parse_program(raw"(= (fib $n) (fib (- $n 1)))")[1][2])
        @test !Interpreter._is_closed_rule(parse_program(raw"(= (g $x) (h $x $y))")[1][2])   # $y RHS-only
        @test !Interpreter._is_closed_rule(parse_program("(foo bar)")[1][2])                 # not a (= …) rule
    finally
        Interpreter.fast_match!(false)
    end
end

@testset "case: empty subject matches the `Empty` clause (hyperon; LeaTTa proved-oracle)" begin
    # LeaTTa (Lean-4 machine-proved MeTTa) differential, 2026-07-08: Core's `case` collapsed an
    # EMPTY result set to `()` and so missed the literal `Empty` clause — hyperon's rule
    # (stdlib.metta §case) is: empty subject ⇒ the `Empty` pattern fires. Fixed in Interpreter.jl.
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
