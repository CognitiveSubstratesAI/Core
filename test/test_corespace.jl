# CoreSpace + MORK-substrate regression tests.
#
# Extracted from the former "Core MeTTa Compatibility Suite" in runtests.jl when the legacy Vector{Any}
# tree-walker (Eval_obsolete.jl) was retired. The builtin-compatibility testsets that drove `eval_metta`
# were dropped — the modern engine's builtins are validated by StandardMeTTaTests / test_conformance /
# the LeaTTa oracle. Only the tests that exercise the LIVE CoreSpace storage layer + the MORK exec-atom
# calculus (via the surviving `core_*` / `new_core_space` API) are kept here.
using Test
using MeTTaCore

# Fresh CoreSpace with stdlib loaded.
fresh() = load_stdlib!(new_core_space())

@testset "CoreSpace + MORK substrate" begin

    @testset "CoreSpace — space operations" begin
        s = fresh()
        core_add!(s, [:fact, :x])
        @test !isempty(core_match(s, [:fact, Symbol("\$v")]))
        core_remove!(s, [:fact, :x])
        @test isempty(core_match(s, [:fact, :x]))
        @test !isempty(core_atoms(s))
    end

    @testset "MORK exec-atom calculus" begin
        s = new_core_space()
        core_add!(s, [:fact, :a])
        core_add!(s, [:fact, :b])
        core_add!(s, "(exec (t 0) (, (fact \$x)) (, (derived \$x)))")
        n = core_calculus!(s, 100)
        @test n >= 1
        @test any(a -> a isa Vector && length(a) >= 2 && a[1] === :derived, core_atoms(s))
    end

    @testset "Stage 1 — disjoint-prefix isolation" begin
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

    @testset "Stage 1 — cross-prefix match does not bleed" begin
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

    @testset "Stage 1 — .act snapshot / load round-trip" begin
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

    @testset "Stage 1 — read-your-writes within a prefix" begin
        using MeTTaCore: get_node_shared, new_core_space
        shared = get_node_shared()
        # 🔴 UNIQUE PREFIX PER INVOCATION. `Shared` regions co-reside in ONE process-global trie that
        # nothing resets, so a fixed `ryw/` still holds the `[:fact, 2]` this testset wrote the last
        # time it ran IN THIS PROCESS — and then `isempty` is false for reasons that have nothing to
        # do with read-your-writes. Measured 2026-08-18 by running the whole suite twice in one
        # daemon: this and `test_spaces_registry.jl`'s persist probe were the only two data leaks in
        # 92 files, and between them they are why every gate pays a fresh process.
        # `gensym` gives a per-call unique name without introducing a counter that is itself state.
        s = new_core_space(shared, Vector{UInt8}("ryw_" * string(gensym()) * "/"))
        @test isempty(core_atoms(s))
        core_add!(s, [:fact, 1])
        @test [:fact, 1] ∈ core_atoms(s)
        core_add!(s, [:fact, 2])
        @test length(core_atoms(s)) == 2
        core_remove!(s, [:fact, 1])
        @test [:fact, 1] ∉ core_atoms(s)
        @test [:fact, 2] ∈ core_atoms(s)
    end

    @testset "Prefix-narrowed core_match (== full-walk, but O(subtrie))" begin
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
end

println("\n✓ CoreSpace + MORK substrate tests passed.")
