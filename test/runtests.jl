using Test
using MeTTaCore

# Boot: register all primitives and load stdlib once for all tests
register_all_primitives!()
const TEST_SPACE = new_core_space()
load_stdlib!(TEST_SPACE)

# Helper: fresh space with stdlib loaded (for isolated tests)
fresh() = load_stdlib!(new_core_space())

# Helper: eval in shared space
em(expr) = eval_metta(expr, TEST_SPACE)

# Bool result helpers (MeTTa returns True/False as various forms)
is_true(r) = r ∈ [true, "True", :True]
is_false(r) = r ∈ [false, "False", :False]
is_num(r, n) = r == n || r == string(n) || r == Float64(n) || r == string(Float64(n))

@testset "Core MeTTa Compatibility Suite" begin

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "1. Atom construction and deconstruction" begin
        s = fresh()
        @test em([Symbol("cons-atom"), 0, [1, 2, 3]]) isa Vector ||
            occursin("0", string(em([Symbol("cons-atom"), 0, [1, 2, 3]])))
        @test em([Symbol("car-atom"), [1, 2, 3]]) == 1
        @test occursin("2", string(em([Symbol("cdr-atom"), [1, 2, 3]])))
        @test em([Symbol("size-atom"), [:a, :b, :c]]) == 3 || em([Symbol("size-atom"), [:a, :b, :c]]) == "3"
        @test em([Symbol("index-atom"), [1, 2, 3], 1]) == 2 || em([Symbol("index-atom"), [1, 2, 3], 1]) == "2"
        @test em([Symbol("index-atom"), [1, 2, 3], 0]) == 1 || em([Symbol("index-atom"), [1, 2, 3], 0]) == "1"
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "2. Arithmetic" begin
        s = fresh()
        @test em([:+, 3, 4]) == 7
        @test em([:-, 10, 3]) == 7
        @test em([:*, 6, 7]) == 42
        @test em([:/, 10, 2]) == 5 || em([:/, 10, 2]) == 5.0
        @test em([:%, 10, 3]) == 1
        @test eval_metta([Symbol("pow-math"), 2, 3], s) |> r -> is_num(r, 8)
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "3. Comparison" begin
        s = fresh()
        @test is_true(em([Symbol("<"), 3, 5]))
        @test is_false(em([Symbol(">"), 3, 5]))
        @test is_true(em([Symbol(">="), 5, 5]))
        @test is_true(em([Symbol("<="), 3, 5]))
        @test is_true(em([Symbol("=="), 3, 3]))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "4. Math (-math suffix)" begin
        s = fresh()
        @test eval_metta([Symbol("sqrt-math"), 9], s) |> r -> is_num(r, 3)
        @test eval_metta([Symbol("abs-math"), -5], s) |> r -> is_num(r, 5)
        @test eval_metta([Symbol("ceil-math"), 5.2], s) |> r -> is_num(r, 6)
        @test eval_metta([Symbol("floor-math"), 5.8], s) |> r -> is_num(r, 5)
        @test eval_metta([Symbol("round-math"), 5.4], s) |> r -> is_num(r, 5)
        @test eval_metta([Symbol("sin-math"), 0], s) |> r -> is_num(r, 0)
        @test eval_metta([Symbol("cos-math"), 0], s) |> r -> is_num(r, 1)
        @test is_false(eval_metta([Symbol("isnan-math"), 0.0], s))
        @test is_false(eval_metta([Symbol("isinf-math"), 0.0], s))
        @test eval_metta([Symbol("min-atom"), (2, 6, 7, 4, 9, 3)], s) |> r -> is_num(r, 2)
        @test eval_metta([Symbol("max-atom"), (2, 6, 7, 4, 9, 3)], s) |> r -> is_num(r, 9)
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "5. Set operations (-atom suffix)" begin
        s = fresh()
        @test begin
            r = eval_metta([Symbol("union-atom"), [:a, :b], [:c, :d]], s)
            occursin("a", string(r)) && occursin("c", string(r))
        end
        @test begin
            r = eval_metta([Symbol("intersection-atom"), [1, 2], [2, 3]], s)
            occursin("2", string(r))
        end
        @test begin
            r = eval_metta([Symbol("unique-atom"), [:a, :b, :c, :d, :d]], s)
            !occursin("d d", string(r))
        end
        @test begin
            r = eval_metta([Symbol("subtraction-atom"), [:a, :b, :b, :c], [:b, :c]], s)
            occursin("a", string(r)) && !occursin("b", string(r))
        end
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "6. Higher-order list ops" begin
        s = fresh()
        @test eval_metta(
            [
                Symbol("foldl-atom"),
                [1, 2, 3, 4],
                0,
                Symbol("\$acc"),
                Symbol("\$x"),
                [:+, Symbol("\$acc"), Symbol("\$x")],
            ],
            s,
        ) == 10
        @test occursin(
            "2", string(eval_metta([Symbol("map-atom"), [1, 2, 3], Symbol("\$x"), [:+, Symbol("\$x"), 1]], s))
        )
        @test begin
            r = eval_metta([Symbol("filter-atom"), [1, 2, 3, 4, 5], Symbol("\$x"), [Symbol(">"), Symbol("\$x"), 3]], s)
            occursin("4", string(r)) && !occursin("3", string(r))
        end
        @test begin
            r = eval_metta([Symbol("union-atom"), [:a, :b, :b, :c], [:b, :c, :c, :d]], s)
            occursin("a", string(r)) && occursin("d", string(r))
        end
        @test begin
            r = eval_metta([Symbol("intersection-atom"), [:a, :b, :c], [:b, :c, :d]], s)
            occursin("b", string(r)) && !occursin("a", string(r))
        end
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "7. Special forms — chain / function / return" begin
        s = fresh()
        @test eval_metta([:chain, [:+, 2, 3], Symbol("\$x"), [:*, Symbol("\$x"), 2]], s) == 10
        @test eval_metta([:function, [:return, 99]], s) == 99
        @test eval_metta([:eval, [:+, 2, 3]], s) == 5
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "8. Special forms — let / let* / case" begin
        s = fresh()
        @test eval_metta([:let, Symbol("\$x"), 5, [:+, Symbol("\$x"), 1]], s) == 6
        @test eval_metta(
            [
                Symbol("let*"),
                [[Symbol("\$x"), 3], [Symbol("\$y"), [:+, Symbol("\$x"), 1]]],
                [:+, Symbol("\$x"), Symbol("\$y")],
            ],
            s,
        ) == 7
        @test begin
            r = eval_metta([:case, :foo, Any[Any[:foo, :matched], Any[:bar, :other]]], s)
            r === :matched || r == "matched"
        end
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "9. Special forms — unify / match" begin
        s = fresh()
        @test eval_metta([:unify, :foo, :foo, :yes, :no], s) === :yes
        @test eval_metta([:unify, :foo, :bar, :yes, :no], s) === :no
        core_add!(s, [:isa, :dog, :animal])
        core_add!(s, [:isa, :cat, :animal])
        r = eval_metta([:match, Symbol("&self"), [:isa, Symbol("\$x"), :animal], Symbol("\$x")], s)
        @test r !== nothing
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "10. Quote / noreduce-eq" begin
        s = fresh()
        @test begin
            r = eval_metta([:quote, [:+, 1, 2]], s)
            r isa Vector && r[1] === :+
        end
        @test eval_metta([:unquote, [:quote, [:+, 1, 2]]], s) == 3
        @test is_true(eval_metta([Symbol("noreduce-eq"), [:+, 1, 2], [:+, 1, 2]], s))
        @test is_false(eval_metta([Symbol("noreduce-eq"), [:+, 1, 2], 3], s))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "11. Alpha-equivalence (=alpha)" begin
        s = fresh()
        @test is_true(eval_metta([Symbol("=alpha"), [:Father, Symbol("\$X")], [:Father, Symbol("\$Y")]], s))
        @test is_false(eval_metta([Symbol("=alpha"), [:Father, Symbol("\$X")], [:Son, Symbol("\$X")]], s))
        @test is_true(
            eval_metta([Symbol("=alpha"), [:f, Symbol("\$a"), Symbol("\$b")], [:f, Symbol("\$x"), Symbol("\$y")]], s)
        )
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "12. Type system" begin
        s = fresh()
        @test occursin("Number", string(eval_metta([Symbol("get-type"), 1], s)))
        # Undeclared symbol → %Undefined% (gradual typing), per MeTTa spec. (Was
        # asserting "Symbol", the old structural-fallback behavior, before get-type
        # was unified with the function-application-aware _infer_type.)
        @test occursin("%Undefined%", string(eval_metta([Symbol("get-type"), :foo], s)))
        @test begin
            r = eval_metta([Symbol("match-types"), :Number, :Number, :yes, :no], s)
            r === :yes || r == "yes"
        end
        @test begin
            r = eval_metta([Symbol("match-types"), :Number, :Bool, :yes, :no], s)
            r === :no || r == "no"
        end
        @test begin
            r = eval_metta([Symbol("match-types"), Symbol("%Undefined%"), :Number, :yes, :no], s)
            r === :yes || r == "yes"
        end
        @test begin
            r = eval_metta([Symbol("get-metatype"), :True], s)
            string(r) ∈ ["Symbol", "Grounded"]
        end
        @test occursin("Expression", string(eval_metta([Symbol("get-metatype"), [:a, :b]], s)))
        @test begin
            r = eval_metta([Symbol("first-from-pair"), [:A, :B]], s)
            r === :A || r == "A"
        end
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "13. if / if-equal from stdlib" begin
        s = fresh()
        @test eval_metta([:if, :True, :yes, :no], s) === :yes
        @test eval_metta([:if, :False, :yes, :no], s) === :no
        @test begin
            r = eval_metta([Symbol("if-equal"), 1, 1, :Equal, :NotEqual], s)
            r === :Equal || r == "Equal"
        end
        @test begin
            r = eval_metta([Symbol("if-equal"), :a, :b, :Equal, :NotEqual], s)
            r === :NotEqual || r == "NotEqual"
        end
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "14. is-function from stdlib" begin
        s = fresh()
        @test is_true(eval_metta([Symbol("is-function"), [Symbol("->"), :Atom, :Atom]], s))
        @test is_false(eval_metta([Symbol("is-function"), :Atom], s))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "15. State atoms (new-state / get-state)" begin
        s = fresh()
        st = eval_metta([Symbol("new-state"), :idle], s)
        @test occursin("State", string(st))
        val = eval_metta([Symbol("get-state"), st], s)
        @test val === :idle || val == "idle"
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "16. bind! and custom rules" begin
        s = fresh()
        eval_metta([Symbol("bind!"), :myconst, 42], s)
        core_add!(s, [:(=), [:double, Symbol("\$x")], [:*, Symbol("\$x"), 2]])
        @test eval_metta([:double, 5], s) == 10
        # Single guarded clause — same single-clause+`if` discipline as the stdlib
        # hygiene fix (`4b2033f`). The old two-clause form `(factorial 0) → 1` +
        # `(factorial $n) → recurse` is the divergent overlap class flagged in the
        # audit: under streaming `=`, both clauses fire on `(factorial 0)` and
        # the recursive branch descends into negatives. Single-clause-with-guard
        # works under both rewriters and aligns test code with stdlib discipline.
        core_add!(
            s,
            [
                :(=),
                [:factorial, Symbol("\$n")],
                [:if, [:>, Symbol("\$n"), 0], [:*, Symbol("\$n"), [:factorial, [:-, Symbol("\$n"), 1]]], 1],
            ],
        )
        @test eval_metta([:factorial, 5], s) == 120
        @test eval_metta([:factorial, 0], s) == 1   # base via guard, not via clause overlap
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "17. Parser (parse_metta)" begin
        exprs = parse_metta("(fact a)\n(fact b)\n!(+ 2 3)")
        @test length(exprs) == 3
        @test exprs[3] isa Vector && exprs[3][1] === :!
        @test exprs[1] == [:fact, :a]
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "18. run_metta / run_file" begin
        s = fresh()
        results = run_metta("(= (sq \$x) (* \$x \$x))\n!(sq 7)", s)
        @test any(r -> r == 49 || r == "49", results)
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "19. Superpose / collapse" begin
        s = fresh()
        r = eval_metta([:superpose, [:a, :b, :c]], s)
        @test r !== nothing
        r2 = eval_metta([:collapse, [:superpose, [:A, :B, :C]]], s)
        @test occursin("A", string(r2))

        # Regression: collapse of a SINGLE match result that is itself an expression
        # (a tuple) must stay a 1-element list, not be flattened into its fields.
        # (Caught by the FAFB connectome info-flow model: a node with one in-edge
        #  had `reached-in` = 0 because (collapse (match … ($r $c))) → (r c) was read
        #  as two results instead of one pair.)
        s2 = fresh()
        core_add!(s2, [:edge, :p, :q, 7])
        one = eval_metta(
            [
                :collapse,
                [
                    :match,
                    Symbol("&self"),
                    [:edge, Symbol("\$a"), Symbol("\$b"), Symbol("\$w")],
                    [Symbol("\$a"), Symbol("\$w")],
                ],
            ],
            s2,
        )
        @test one isa Vector && length(one) == 1          # one result, not two
        @test eval_metta([Symbol("size-atom"), one], s2) ∈ [1, "1"]
        # the lone result is the intact pair (p 7)
        @test eval_metta([Symbol("car-atom"), one], s2) == [:p, 7] ||
            occursin("p", string(eval_metta([Symbol("car-atom"), one], s2)))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "20. CoreSpace — space operations" begin
        s = fresh()
        core_add!(s, [:fact, :x])
        @test !isempty(core_match(s, [:fact, Symbol("\$v")]))
        core_remove!(s, [:fact, :x])
        @test isempty(core_match(s, [:fact, :x]))
        @test !isempty(core_atoms(s))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "21. MORK exec-atom calculus" begin
        s = new_core_space()
        core_add!(s, [:fact, :a])
        core_add!(s, [:fact, :b])
        core_add!(s, "(exec (t 0) (, (fact \$x)) (, (derived \$x)))")
        n = core_calculus!(s, 100)
        @test n >= 1
        @test any(a -> a isa Vector && length(a) >= 2 && a[1] === :derived, core_atoms(s))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "22. Custom grounded functions" begin
        register_grounded!("triple", args -> string(parse(Int, args[1]) * 3))
        s = fresh()
        @test eval_metta([Symbol("triple"), 7], s) ∈ [21, "21"]
        delete!(GROUNDED_REGISTRY, "triple")
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "23. format-args" begin
        s = fresh()
        r = eval_metta([Symbol("format-args"), "(Hello {}!)", [:World]], s)
        @test occursin("World", string(r))
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "24. do / begin sequencing" begin
        s = fresh()
        r = eval_metta([:do, [:+, 1, 1], [:+, 2, 2], [:+, 3, 3]], s)
        @test r == 6 || r == "6"
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "25. stdlib list functions" begin
        s = fresh()
        # id from stdlib
        @test eval_metta([:id, :hello], s) === :hello
        # noeval
        @test eval_metta([Symbol("noeval"), [:+, 1, 2]], s) == [:+, 1, 2]
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "26. metta\"...\" string macro" begin
        # The macro must not interpolate — MeTTa $x variables survive verbatim,
        # equivalent to raw"..." but self-documenting at the call site.
        @test metta"(foo $x $y)" == raw"(foo $x $y)"
        @test metta"(foo $x $y)" == "(foo \$x \$y)"
        # Empty string round-trips.
        @test metta"" == ""
        # Triple-quoted form (the shape tests will use for multi-line programs)
        # must also preserve $ verbatim.
        prog = metta"""
        (exec 0 (, (A $x $y)) (, (Result $x)))
        """
        @test occursin("\$x", prog)
        @test occursin("\$y", prog)
        @test !occursin("__var_", prog)   # never the storage form
        # Sanity: result is a plain Julia String (not a wrapper).
        @test metta"(a $x)" isa String
    end

    # ─────────────────────────────────────────────────────────────────────────────
    # Stage 1 (multi-space-on-shared-trie): tests below exercise the
    # (shared::Space, prefix::Vector{UInt8}) construction path directly rather
    # than going through (bind! &name (new-space)).  Rationale: `bind!` ships
    # dormant in C-mode (per-space-own-trie) — the prefix machinery is recorded
    # as metadata only.  The architecture itself is exercised here so the bytes
    # under different prefixes really are isolated.
    @testset "27. Stage 1 — disjoint-prefix isolation" begin
        using MeTTaCore: get_node_shared, new_core_space
        shared = get_node_shared()
        sa = new_core_space(shared, Vector{UInt8}("ns_a/"))
        sb = new_core_space(shared, Vector{UInt8}("ns_b/"))
        core_add!(sa, [:alpha, 1])
        core_add!(sb, [:beta, 2])
        # Each space sees ONLY its own atoms via core_atoms.
        @test [:alpha, 1] ∈ core_atoms(sa)
        @test [:beta, 2] ∉ core_atoms(sa)
        @test [:beta, 2] ∈ core_atoms(sb)
        @test [:alpha, 1] ∉ core_atoms(sb)
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "28. Stage 1 — cross-prefix match does not bleed" begin
        using MeTTaCore: get_node_shared, new_core_space
        shared = get_node_shared()
        sa = new_core_space(shared, Vector{UInt8}("scope_a/"))
        sb = new_core_space(shared, Vector{UInt8}("scope_b/"))
        core_add!(sa, [:item, :x])
        core_add!(sa, [:item, :y])
        core_add!(sb, [:item, :z])
        # core_match in sa returns only sa's items; sb's atoms are byte-disjoint.
        sa_results = core_match(sa, [:item, Symbol("\$v")])
        sb_results = core_match(sb, [:item, Symbol("\$v")])
        @test length(sa_results) == 2
        @test length(sb_results) == 1
        @test [:item, :z] ∉ sa_results
        @test [:item, :x] ∉ sb_results
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "29. Stage 1 — with-space saves and restores prior binding" begin
        parent = fresh()
        inner1 = new_core_space()
        inner2 = new_core_space()
        parent.named_spaces[Symbol("&scratch")] = inner1
        # `(with-space &scratch inner2 ...)` should rebind to inner2 inside the
        # body and restore inner1 on exit.
        eval_metta(
            [Symbol("with-space"), Symbol("&scratch"), inner2, [Symbol("add-atom"), Symbol("&scratch"), [:probe]]],
            parent,
        )
        # After exit, &scratch is back to inner1 — probe lives in inner2, not inner1.
        @test parent.named_spaces[Symbol("&scratch")] === inner1
        @test [:probe] ∈ core_atoms(inner2)
        @test [:probe] ∉ core_atoms(inner1)
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "30. Stage 1 — .act snapshot / load round-trip" begin
        using MeTTaCore:
            get_node_shared, new_core_space, set_act_dir!, snapshot_space_to_act!, act_exists, load_act_source
        tmpdir = mktempdir()
        set_act_dir!(tmpdir)
        shared = get_node_shared()
        src = new_core_space(shared, Vector{UInt8}("snap_test/"))
        core_add!(src, [:persisted, 1])
        core_add!(src, [:persisted, 2])
        @test snapshot_space_to_act!(src, "smoke_round_trip") === true
        @test act_exists("smoke_round_trip")
        # load_act_source returns (ACTSource, mmaps) — just confirm it constructs
        # without erroring (queryability under multi-source factor is exercised
        # at the MORK layer's own test suite).
        handle, mmaps = load_act_source("smoke_round_trip")
        @test handle !== nothing
        @test mmaps isa Dict
        # Empty prefix snapshot is rejected (returns false, no file written).
        empty_src = new_core_space(shared, Vector{UInt8}("never_used/"))
        @test snapshot_space_to_act!(empty_src, "empty_smoke") === false
        @test !act_exists("empty_smoke")
    end

    # ─────────────────────────────────────────────────────────────────────────────
    @testset "31. Stage 1 — read-your-writes within a prefix" begin
        using MeTTaCore: get_node_shared, new_core_space
        shared = get_node_shared()
        s = new_core_space(shared, Vector{UInt8}("ryw/"))
        @test isempty(core_atoms(s))
        core_add!(s, [:fact, 1])
        @test [:fact, 1] ∈ core_atoms(s)
        core_add!(s, [:fact, 2])
        @test length(core_atoms(s)) == 2
        core_remove!(s, [:fact, 1])
        @test [:fact, 1] ∉ core_atoms(s)
        @test [:fact, 2] ∈ core_atoms(s)
    end

    @testset "32. Prefix-narrowed core_match (== full-walk, but O(subtrie))" begin
        using MeTTaCore: core_match
        s = new_core_space()
        core_add!(s, [:in, :p, :a, 5])
        core_add!(s, [:in, :p, :b, 3])
        core_add!(s, [:in, :q, :c, 7])
        core_add!(s, [:other, :p, :z, 1])
        # functor + bound 2nd arg pinned → only the two (in p ..) atoms
        got = core_match(s, [:in, :p, Symbol("\$r"), Symbol("\$w")])
        @test length(got) == 2
        @test all(a -> a isa Vector && a[1] === :in && a[2] === :p, got)
        # functor-only (2nd arg is a var) → full-walk fallback → all three (in ..)
        @test length(core_match(s, [:in, Symbol("\$x"), Symbol("\$r"), Symbol("\$w")])) == 3
        # integer-id bound arg (the real-connectome case) narrows correctly
        s2 = new_core_space()
        core_add!(s2, [:in, 720575940612305506, :a, 7])
        core_add!(s2, [:in, 720575940612305507, :b, 9])
        one = core_match(s2, [:in, 720575940612305506, Symbol("\$r"), Symbol("\$w")])
        @test length(one) == 1 && one[1][2] == 720575940612305506
        # narrowed result is exactly the full-walk result (correctness, not just count)
        @test Set(string.(got)) == Set(string.(filter(a -> a isa Vector && a[1] === :in && a[2] === :p, core_atoms(s))))
    end
end # testset "Core MeTTa Compatibility Suite"

println("\n✓ Core MeTTa Compatibility Suite tests passed.")

# WILLIAM algorithm tests — pulled in from the adaptive-compression submodule
# at lib/william/.  Top-level @testset inside; failures throw at its close.
# Two known pre-existing failures as of submodule pin 53a8622:
#   - W8 Validate (1 of 2 assertions)
#   - WP§7.2 i-surprisingness > 0
# Fix these by editing the .metta in the submodule (sivaji1012/adaptive-compression),
# pushing, then bumping the submodule pin in Core.
include("test_william.jl")

# MetaMo algorithm tests — lib/metamo/ (icoglabs MetaMo adoption, PLN-style multi-file).
include("test_metamo.jl")

# ECAN acceptance suite — executes examples/ecan/*.metta (attention economy:
# AV, funds, wages, two-tier rent, AF, spreading + Hebbian, governance, fluid,
# adaptive). The slow Stability convergence probe is gated behind ECAN_SLOW_TESTS=1.
include("test_ecan.jl")

# ActPC-Chem algorithm tests — lib/ActPC-Chem/ (migrated from PRIMUS_Core,
# dialect-adapted). AC1–AC7,AC10 core; cross-algo bridges + AG/AC8 are separate.
include("test_actpc_chem.jl")

# MOSES algorithm tests — lib/MOSES/ (1:1 port of iCog metta-moses, Core-dialect-
# adapted: Cons/Nil-ADT → Core-native ()-expr lists). Incremental: M0 scaffold + utils.
include("test_moses.jl")

# Structural lint — no lib/ definition shadows a Core-provided name (closes the
# duplication class from the 2026-06-10 primitive audit; clamp/xor/is-member consolidation).
include("test_no_stdlib_shadow.jl")

# Type-system conformance — Core vs the metta-lang.dev types_basics tutorials,
# grounded in hyperon-experimental's b5_types_prelim/d4_type_prop scripts: gradual
# typing, function-application return-type inference, BadArgType checking, parametric
# types, get-metatype, types-as-propositions, let-destructure, Atom-typed match.
include("test_types.jl")

@testset "MorkBridge (E1.0) — native unify + shared-var rule rewrite" begin
    # E1.0 foundation: rewrite via MORK's verified engine (expr_unify + expr_apply), not Core's
    # Julia-structural _unify / string-replace. The crossed-variable case is the one that breaks
    # naive separate-parse — see the CRUX note in src/eval/MorkBridge.jl.
    @test mork_rule_rewrite("(= (f \$x) (g \$x))", "(f bar)") == "(g bar)"
    @test mork_rule_rewrite("(= (p \$x \$y) (q \$y \$x))", "(p a b)") == "(q b a)"   # crossed vars
    @test mork_rule_rewrite("(= (dup \$x) (\$x \$x))", "(dup k)") == "(k k)"          # template duplication
    @test mork_rule_rewrite("(= (p \$x \$y) (q \$y \$x))", "(z a b)") === nothing     # head mismatch
    @test mork_rule_rewrite("(foo bar)", "(foo bar)") === nothing                     # not a (= ..) rule
    @test mork_unify("(f \$x)", "(f bar)") isa Dict                                   # match → bindings
    @test mork_unify("(f \$x)", "(h bar)") === nothing                                # no match
end

@testset "OutcomeSet evaluator (nondeterministic) — conformance fixtures" begin
    # The cases legacy eval_metta gets wrong (single-value, no fan-out / no binding propagation).
    # eval_nd returns a SET; compare order-insensitively. See docs/CONFORMANCE_AUDIT.md.
    s = new_core_space(); load_stdlib!(s)
    for f in parse_metta("(= (croaks Fritz) True)\n(= (eats_flies Fritz) True)\n" *
                         "(= (croaks Sam) True)\n(= (eats_flies Sam) False)\n" *
                         "(= (frog \$x) (and (croaks \$x) (eats_flies \$x)))\n(= (f \$x) (g \$x))\n" *
                         "(= (green \$x) (frog \$x))\n" *
                         "(= (color) red)\n(= (color) green)\n(= (color) yellow)\n" *
                         "(= (bin) A)\n(= (bin) B)\n(= (croaks2 Fritz) T)\n(= (eat_flies Fritz) T)\n")
        core_add!(s, f)
    end
    ndset(src) = Set(to_sexpr.(eval_nd_results(parse_metta(src)[1], s)))
    @test ndset("(croaks \$x)") == Set(["True"])                               # fan-out over facts → {True}
    @test ndset("(f (superpose (1 2)))") == Set(["(g 1)", "(g 2)"])            # fan-out through application
    @test ndset("(if (frog \$x) (\$x is Frog) (\$x is-not Frog))") ==
          Set(["(Fritz is Frog)", "(Sam is-not Frog)"])                        # the frog tutorial — fan-out + binding
    @test ndset("(color)") == Set(["red", "green", "yellow"])                  # fan-out over multiple rules
    @test ndset("(collapse (color))") == Set(["(red green yellow)"])           # collapse: stream → tuple
    @test ndset("(pair (bin) (bin))") ==
          Set(["(pair A A)", "(pair A B)", "(pair B A)", "(pair B B)"])        # nondeterministic product
    @test ndset("(let \$r (color) (got \$r))") ==
          Set(["(got red)", "(got green)", "(got yellow)"])                    # let over a nondeterministic value
    @test ndset("(match &self (= (\$p Fritz) T) \$p)") == Set(["croaks2", "eat_flies"])  # multi-result match
    @test ndset("(chain (+ 2 3) \$x (* \$x 2))") == Set(["10"])                # chain: bind then use
    @test ndset("(let* ((\$r1 (+ 1 2)) (\$r2 (+ \$r1 1))) (foo \$r2))") == Set(["(foo 4)"])  # sequential let*
    @test ndset("(unify (f \$x) (f 7) (got \$x) nope)") == Set(["(got 7)"])    # unify then-branch + binding
    @test ndset("(unify (f 1) (g 1) yes no)") == Set(["no"])                   # unify else-branch
    @test ndset("(quote (+ 1 2))") == Set(["(+ 1 2)"])                         # quote: unevaluated
    @test ndset("(case (color) ((red R) (green G) (\$_ other)))") == Set(["R", "G", "other"])  # case + wildcard over nondeterminism
    @test ndset("(\$x (green \$x))") == Set(["(Fritz True)", "(Sam False)"])    # var-head expr: binding from one element reaches another (b3_direct)
    # legacy-form delegation: forms eval_nd doesn't implement delegate to eval_metta (one outcome)
    @test ndset("(map-atom (1 2 3) \$x (g \$x))") ==
          Set([to_sexpr(eval_metta(parse_metta("(map-atom (1 2 3) \$x (g \$x))")[1], s))])
end
