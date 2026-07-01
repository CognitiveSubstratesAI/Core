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
