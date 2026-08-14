# ── Space constructor REGISTRY + the capability ledger, verified BY EXECUTION ────────────────────────
#
# 🔴 THE POINT OF THIS FILE. A capability table is worthless if it is only asserted against itself —
# `@test space_caps(:mork).evaluate == false` proves nothing except that someone typed `false`. Every
# declared capability that can be exercised is exercised here, and the test asserts that the BEHAVIOUR
# and the DECLARATION agree. A ledger that drifts from the code it describes then fails, which is the
# only way a ledger stays true (`[[feedback_parses_is_not_fires]]`,
# `[[feedback_run_the_check_before_making_the_claim]]`).
#
# The declines are tested as hard as the grants, deliberately. `:mork` declining `evaluate` IS
# compile-arrow 6; if that ever starts working, this file must go red so the ledger gets updated in the
# same commit rather than quietly becoming a lie.

using Test
using MeTTaCore
const MC = MeTTaCore
# The interpreter lives in the self-contained `Eval` submodule, and several names are deliberately
# DIFFERENT functions in the two scopes — `load_metta!` dispatches on Eval.Space here and on CoreSpace
# at MeTTaCore level, and `parse_metta` at MeTTaCore level is the MORK-lane parser feeding `core_add!`,
# not Eval's. Qualifying instead of `using` both keeps that distinction visible rather than ambiguous.
const EV = MeTTaCore.Eval
# Atom/Sym/Grounded are owned by the StandardMeTTa submodule (Atoms.jl:15-17), which Eval `using`s —
# they are not bindings of MeTTaCore itself, so qualify them at their real owner.
const SM = MeTTaCore.StandardMeTTa

@testset "Space registry — construction, kinds, capability ledger" begin

    @testset "the four Core kinds are registered, sorted, and owned" begin
        ks = MC.space_kinds()
        @test ks == sort(ks)                       # stable across load orders, so the list is diffable
        for k in (:vector, :fork, :mork, :mork_shared)
            @test k in ks
            @test MC.space_kind(k).provider == "MeTTaCore"
        end
    end

    @testset "unknown kind names what IS available" begin
        err = try MC.make_space(:no_such_kind); catch e; e; end
        @test err isa ArgumentError
        # The diagnostic must list the registered kinds — an unknown kind is nearly always a typo or an
        # unloaded provider package, and both are diagnosed by seeing the list.
        @test occursin("vector", err.msg) && occursin("mork", err.msg)
    end

    @testset "a second provider cannot claim a registered name" begin
        caps = MC.space_caps(:vector)
        @test_throws ArgumentError MC.register_space_kind!(
            MC.SpaceKind(:vector, "SomeOtherPackage", EV.Space, (; kwargs...) -> nothing, caps))
        # ...and the original entry survives the rejected attempt.
        @test MC.space_kind(:vector).provider == "MeTTaCore"
    end

    @testset ":vector — the evaluable store, and it really does evaluate" begin
        s = MC.make_space(:vector)
        @test s isa EV.Space
        @test MC.space_caps(:vector).evaluate
        # DECLARED evaluate=true ⇒ MeTTa reduction must actually RUN against it, not merely typecheck.
        EV.load_metta!(s, raw"(= (twice $x) (+ $x $x))")
        @test EV.load_metta!(s, "!(twice 21)") == SM.Atom[SM.Grounded(42)]
    end

    @testset ":vector — bindings are CAPTURED, not merely filtered" begin
        @test MC.space_caps(:vector).bindings
        s = MC.make_space(:vector)
        EV.load_metta!(s, "(belief a 0.9 0.8)\n(belief b 0.1 0.2)")
        got = EV.load_metta!(s, raw"!(match &self (belief $k $s $c) $k)")
        # The variable's WITNESS comes back — precisely the query the MORK kinds below cannot serve.
        @test Set(got) == Set(SM.Atom[SM.Sym("a"), SM.Sym("b")])
    end

    @testset ":fork — the c2_spaces isolation contract holds" begin
        parent = MC.make_space(:vector)
        EV.load_metta!(parent, "(A)")
        fork = MC.make_space(:fork; parent = parent)
        @test fork isa EV.Space
        @test fork !== parent
        EV.load_metta!(fork, "(B)")
        # parent → (A); fork → (A B). A later add on the FORK must not propagate back to the parent.
        @test isempty(EV.load_metta!(parent, "!(match &self (B) found)"))
        @test EV.load_metta!(fork, "!(match &self (B) found)") == SM.Atom[SM.Sym("found")]
        # ...while the snapshot the fork was taken FROM is present in both.
        @test EV.load_metta!(parent, "!(match &self (A) found)") == SM.Atom[SM.Sym("found")]
        @test EV.load_metta!(fork, "!(match &self (A) found)") == SM.Atom[SM.Sym("found")]
    end

    @testset ":fork rejects a CoreSpace parent, and says what to use instead" begin
        cs = MC.make_space(:mork)
        err = try MC.make_space(:fork; parent = cs); catch e; e; end
        @test err isa ArgumentError
        # A CoreSpace has no fork op — its isolation comes from disjoint prefixes — so the message must
        # point at the kind that DOES provide it rather than just refusing.
        @test occursin("mork_shared", err.msg)
    end

    @testset ":mork — isolated trie: stores, and its atoms are its own" begin
        a = MC.make_space(:mork)
        b = MC.make_space(:mork)
        @test a isa MC.CoreSpace
        @test a.inner !== b.inner          # :mork is isolated BY CONSTRUCTION — its own fresh trie
        @test isempty(a.prefix)            # ...at the root prefix (= whole trie)
        MC.core_add!(a, [:only_in_a, 1])
        @test [:only_in_a, 1] ∈ MC.core_atoms(a)
        @test [:only_in_a, 1] ∉ MC.core_atoms(b)
    end

    @testset "🔴 :mork DECLINES evaluate — and the decline is real (compile-arrow 6)" begin
        @test !MC.space_caps(:mork).evaluate
        @test !MC.space_caps(:mork_shared).evaluate
        cs = MC.make_space(:mork)
        # The trie-backed store LOADS but does not EVALUATE: load_metta!(::CoreSpace) accepts only
        # `import!` and `remove-atom` and RAISES on every other directive, by design (silently skipping
        # one would load a library that only LOOKS complete). This is the gap COMPILE_ARROW_STATUS.md
        # tracks; the ledger's `false` is this behaviour, written down.
        @test_throws Exception MC.load_metta!(cs, "!(+ 1 2)")
        # Storage on the same space is unaffected — it is evaluation that is missing, not the store.
        MC.load_metta!(cs, "(fact 1)")
        @test [:fact, 1] ∈ MC.core_atoms(cs)
    end

    @testset "🔴 :mork DECLINES bindings — core_match FILTERS, it does not BIND" begin
        @test !MC.space_caps(:mork).bindings
        cs = MC.make_space(:mork)
        MC.core_add!(cs, [:belief, :a, 9])
        MC.core_add!(cs, [:belief, :b, 1])
        hits = MC.core_match(cs, [:belief, Symbol("\$k"), Symbol("\$v")])
        # Both atoms match, so the pattern is doing real work — but what comes back are the ATOMS, never
        # a binding for $k. `_shape_match` returns Bool and `_is_var_symbol(pattern) && return true`
        # accepts a variable position without capturing it (CoreSpace.jl:436-437).
        @test length(hits) == 2
        @test all(h -> h isa Vector && h[1] === :belief, hits)
        @test [:belief, :a, 9] ∈ hits
    end

    @testset ":mork_shared — siblings co-reside in ONE trie and do not bleed (whitepaper Fig. 4)" begin
        @test MC.space_caps(:mork_shared).shared
        @test !MC.space_caps(:mork).shared
        games  = MC.make_space(:mork_shared; name = Symbol("&app/games"))
        social = MC.make_space(:mork_shared; name = Symbol("&app/social"))
        # ONE trie, two regions — that is the whole model, and it is what :mork cannot do.
        @test games.inner === social.inner
        @test games.inner === MC.get_node_shared()
        @test games.prefix != social.prefix
        MC.core_add!(games,  [:score, 10])
        MC.core_add!(social, [:score, 99])
        @test [:score, 10] ∈ MC.core_atoms(games)
        @test [:score, 99] ∉ MC.core_atoms(games)
        @test [:score, 99] ∈ MC.core_atoms(social)
        # ...and a pattern query does not bleed across the prefix boundary either.
        @test length(MC.core_match(games, [:score, Symbol("\$v")])) == 1
    end

    @testset ":mork_shared REGISTERS the name — un-orphaning the prefix registry" begin
        nm = Symbol("&common")
        MC.unregister_prefix!(nm)                       # start from a known state
        @test MC.lookup_prefix(nm) === nothing
        s = MC.make_space(:mork_shared; name = nm)
        # The name→prefix half of the Figure-4 model had ZERO callers before this registry existed:
        # register_prefix!/derive_prefix_from_name/lookup_prefix were exported and never used, and the
        # `_resolve_space` their docstrings named as the consumer does not exist. Construction by NAME
        # is what makes a shared space addressable rather than hand-built from bytes.
        @test MC.lookup_prefix(nm) == Vector{UInt8}("common:/")
        @test s.prefix == Vector{UInt8}("common:/")
    end

    @testset ":mork_shared rejects a name it cannot derive a prefix from" begin
        # No leading `&` ⇒ not a space reference at all (it would bind as an ordinary atom), so there is
        # no prefix to derive and guessing one would invent a region silently.
        err = try MC.make_space(:mork_shared; name = :plain_name); catch e; e; end
        @test err isa ArgumentError
        @test occursin("&", err.msg)
        # ...and neither argument at all is also an error, rather than a silent root-prefix space that
        # would alias the whole shared trie.
        @test_throws ArgumentError MC.make_space(:mork_shared)
    end

    @testset ":mork_shared accepts an explicit prefix, bypassing name derivation" begin
        s = MC.make_space(:mork_shared; prefix = Vector{UInt8}("explicit_region/"))
        @test s.prefix == Vector{UInt8}("explicit_region/")
        @test s.inner === MC.get_node_shared()
    end

    @testset "persist is declared exactly where it holds" begin
        @test MC.space_caps(:mork).persist && MC.space_caps(:mork_shared).persist
        @test !MC.space_caps(:vector).persist && !MC.space_caps(:fork).persist
        dir = mktempdir()
        MC.set_act_dir!(dir)
        s = MC.make_space(:mork_shared; prefix = Vector{UInt8}("persist_probe/"))
        # An EMPTY region returns false — the guard is `n_atoms == 0`, not "root prefix".
        @test MC.snapshot_space_to_act!(s, "empty_probe") === false
        MC.core_add!(s, [:durable, 1])
        @test MC.snapshot_space_to_act!(s, "filled_probe") === true
        @test MC.act_exists("filled_probe")
    end

    @testset "every kind declares an atomicity model and a note" begin
        # Whitepaper §2.2.1 leaves consistency/failure behaviour "backend-specific" — which obliges the
        # backend to DECLARE it, not to skip the question. An empty string here is a skipped question.
        for k in MC.space_kinds()
            c = MC.space_caps(k)
            @test !isempty(strip(c.atomicity))
            @test !isempty(strip(c.note))
        end
    end

    @testset "the ledger renders" begin
        io = IOBuffer()
        MC.space_ledger(io)
        out = String(take!(io))
        for k in MC.space_kinds()
            @test occursin(string(k), out)
        end
        @test occursin("provider", out)
    end
end
