# ── Space KIND registry + the capability ledger, verified BY EXECUTION ───────────────────────────────
#
# 🔴 THE POINT OF THIS FILE. A capability table is worthless if only asserted against itself —
# `@test space_caps(:mork).evaluate == false` proves nothing except that someone typed `false`. Every
# declared capability that can be exercised IS exercised here, and the test asserts that BEHAVIOUR and
# DECLARATION agree. A ledger that drifts from the code it describes then fails, which is the only way a
# ledger stays true (`[[feedback_parses_is_not_fires]]`,
# `[[feedback_run_the_check_before_making_the_claim]]`).
#
# The declines are tested as hard as the grants, deliberately. `:mork` declining `evaluate` IS
# compile-arrow 6; if that ever starts working this file must go RED so the ledger is updated in the
# same commit rather than quietly becoming a lie.
#
# ⚠️ AND THE AXES ARE TESTED AS A PROPERTY, not just per-kind (see the final testset). The first version
# of this registry shipped `:mork_shared` and `:fork` as KINDS — modes wearing a kind's clothing, and
# the first generation of a `:neural_shared_readonly` explosion. A guard that fails on a kind NAME
# containing a mode word is cheap, mechanical, and fires on the next person rather than on a reviewer.

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

@testset "Space registry — kinds, access modes, capability ledger" begin

    @testset "the Core kinds are registered, sorted, and owned" begin
        ks = MC.space_kinds()
        @test ks == sort(ks)                       # stable across load orders, so the list is diffable
        for k in (:vector, :mork)
            @test k in ks
            @test MC.space_kind(k).provider == "MeTTaCore"
        end
    end

    @testset "unknown kind names what IS available" begin
        err = try MC.make_space(:no_such_kind); catch e; e; end
        @test err isa ArgumentError
        # An unknown kind is nearly always a typo or an unloaded provider package; both are diagnosed
        # by seeing the list, so the message must carry it.
        @test occursin("vector", err.msg) && occursin("mork", err.msg)
    end

    @testset "a second provider cannot claim a registered name" begin
        k = MC.space_kind(:vector)
        @test_throws ArgumentError MC.register_space_kind!(
            MC.SpaceKind(:vector, "SomeOtherPackage", EV.Space, [MC.Private], MC.Native,
                         (; kwargs...) -> nothing, k.caps))
        @test MC.space_kind(:vector).provider == "MeTTaCore"   # original survives the rejected attempt
    end

    @testset "a kind with no access modes is rejected at registration" begin
        k = MC.space_kind(:vector)
        # A kind nothing can be constructed at is a typo; caught here rather than much later at the
        # make_space call with a confusing message.
        @test_throws ArgumentError MC.register_space_kind!(
            MC.SpaceKind(:modeless, "MeTTaCore", EV.Space, MC.AccessMode[], MC.Native,
                         (; kwargs...) -> nothing, k.caps))
        @test :modeless ∉ MC.space_kinds()
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
        # The variable's WITNESS comes back — precisely the query the MORK kind below cannot serve.
        @test Set(got) == Set(SM.Atom[SM.Sym("a"), SM.Sym("b")])
    end

    @testset ":vector; parent = … — a fork is a SEEDED PRIVATE region, not a kind" begin
        parent = MC.make_space(:vector)
        EV.load_metta!(parent, "(A)")
        fork = MC.make_space(:vector; parent = parent)
        @test fork isa EV.Space
        @test fork !== parent
        EV.load_metta!(fork, "(B)")
        # The c2_spaces isolation contract: parent → (A); fork → (A B). A later add on the FORK must
        # not propagate back.
        @test isempty(EV.load_metta!(parent, "!(match &self (B) found)"))
        @test EV.load_metta!(fork, "!(match &self (B) found)") == SM.Atom[SM.Sym("found")]
        # ...while the snapshot the fork was taken FROM is present in both.
        @test EV.load_metta!(parent, "!(match &self (A) found)") == SM.Atom[SM.Sym("found")]
        @test EV.load_metta!(fork, "!(match &self (A) found)") == SM.Atom[SM.Sym("found")]
    end

    @testset ":vector rejects a CoreSpace parent, and says what to use instead" begin
        cs = MC.make_space(:mork)
        err = try MC.make_space(:vector; parent = cs); catch e; e; end
        @test err isa ArgumentError
        # A CoreSpace has no snapshot-fork — its isolation comes from disjoint prefixes — so the message
        # must point at what DOES provide independence rather than merely refusing.
        @test occursin("mork", err.msg) && occursin("Shared", err.msg)
    end

    @testset ":vector rejects parent AND atoms together" begin
        p = MC.make_space(:vector)
        # Supplying both would silently discard one seed; better to refuse than to pick.
        @test_throws ArgumentError MC.make_space(:vector; parent = p, atoms = SM.Atom[])
    end

    @testset ":mork at Private — an isolated trie, and its atoms are its own" begin
        a = MC.make_space(:mork)
        b = MC.make_space(:mork)
        @test a isa MC.CoreSpace
        @test a.inner !== b.inner          # Private :mork is isolated BY CONSTRUCTION — its own trie
        @test isempty(a.prefix)            # ...at the root prefix (= whole trie)
        MC.core_add!(a, [:only_in_a, 1])
        @test [:only_in_a, 1] ∈ MC.core_atoms(a)
        @test [:only_in_a, 1] ∉ MC.core_atoms(b)
    end

    @testset ":mork at Private refuses a name/prefix" begin
        # A private MORK space owns its whole trie at the root; accepting a name here would silently
        # produce something that is not what the caller asked for.
        @test_throws ArgumentError MC.make_space(:mork; name = Symbol("&nope"))
        @test_throws ArgumentError MC.make_space(:mork; prefix = Vector{UInt8}("nope/"))
    end

    @testset "🔴 :mork DECLINES evaluate — and the decline is real (compile-arrow 6)" begin
        @test !MC.space_caps(:mork).evaluate
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

    @testset "✅ :mork BINDS — core_match_bind captures; core_match still only filters" begin
        # WAS a decline. Flipped by the space-design §2 seam: the binding primitive was one layer down
        # the whole time (`space_query_multi_at`) and `core_match` simply called something else. This
        # testset is the ledger's proof — if `bindings` is ever set true without the capture working,
        # or the capture regresses while the flag stays, one of these fails.
        @test MC.space_caps(:mork).bindings
        cs = MC.make_space(:mork)
        MC.core_add!(cs, [:belief, :a, 9])
        MC.core_add!(cs, [:belief, :b, 1])
        # core_match: still a FILTER — returns the matching ATOMS, no witness for $k.
        hits = MC.core_match(cs, [:belief, Symbol("\$k"), Symbol("\$v")])
        @test length(hits) == 2
        @test all(h -> h isa Vector && h[1] === :belief, hits)
        # core_match_bind: the WITNESS comes back, which is what Λ needs over a MORK-backed S_rule.
        bs = MC.core_match_bind(cs, [:belief, Symbol("\$k"), Symbol("\$v")])
        @test length(bs) == 2
        @test Set(b[Symbol("\$k")] for b in bs) == Set([:a, :b])
        @test Set(b[Symbol("\$v")] for b in bs) == Set([9, 1])
        # ⚠️ the value must be the BOUND SUB-ATOM, not the remaining tail. Decoding the ExprEnv cursor
        # naively yields `$k => "a 9"` — measured — which is why bindings are taken from `loc`.
        @test all(b -> b[Symbol("\$k")] isa Symbol, bs)
        # a pinned position binds only the remaining variable
        pinned = MC.core_match_bind(cs, [:belief, :a, Symbol("\$v")])
        @test length(pinned) == 1 && pinned[1] == Dict(Symbol("\$v") => 9)
        @test isempty(MC.core_match_bind(cs, [:belief, :nope, Symbol("\$v")]))
    end

    @testset ":mork binding — a REPEATED variable must agree (non-linear pattern)" begin
        cs = MC.make_space(:mork)
        MC.core_add!(cs, [:link, :x, :x])
        MC.core_add!(cs, [:link, :p, :q])
        # `(link $x $x)` must match ONLY the reflexive atom. A positional walk that overwrites instead
        # of checking would return both, binding $x to whatever came last — silently wrong, not an error.
        bs = MC.core_match_bind(cs, [:link, Symbol("\$x"), Symbol("\$x")])
        @test length(bs) == 1
        @test bs[1] == Dict(Symbol("\$x") => :x)
    end

    @testset ":mork binding is REGION-SCOPED — a sibling's atoms stay invisible" begin
        a = MC.make_space(:mork; mode = MC.Shared, prefix = Vector{UInt8}("bind_iso_a/"))
        b = MC.make_space(:mork; mode = MC.Shared, prefix = Vector{UInt8}("bind_iso_b/"))
        MC.core_add!(a, [:belief, :mine, 1])
        MC.core_add!(b, [:belief, :theirs, 2])
        # The indexed descent must honour s.prefix exactly as the filtering walk does — otherwise the
        # Figure-4 isolation the shared model rests on would hold for match and leak for bind.
        got = MC.core_match_bind(a, [:belief, Symbol("\$k"), Symbol("\$v")])
        @test length(got) == 1
        @test got[1][Symbol("\$k")] === :mine
    end

    @testset ":mork at Shared — siblings co-reside in ONE trie and do not bleed (whitepaper Fig. 4)" begin
        games  = MC.make_space(:mork; mode = MC.Shared, name = Symbol("&app/games"))
        social = MC.make_space(:mork; mode = MC.Shared, name = Symbol("&app/social"))
        # ONE trie, two regions — that is the whole model, and it is what Private cannot do. Same KIND,
        # different ACCESS MODE: exactly the axis separation this registry exists to hold.
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

    @testset ":mork at Shared REGISTERS the name — un-orphaning the prefix registry" begin
        nm = Symbol("&common")
        MC.unregister_prefix!(nm)                       # start from a known state
        @test MC.lookup_prefix(nm) === nothing
        s = MC.make_space(:mork; mode = MC.Shared, name = nm)
        # The name→prefix half of the Figure-4 model had ZERO callers before this registry existed:
        # register_prefix!/derive_prefix_from_name/lookup_prefix were exported and never used, and
        # `_resolve_space` — their docstrings' named consumer — is 0 across all 9 live repos.
        # Construction BY NAME is what makes a shared space addressable rather than hand-built.
        @test MC.lookup_prefix(nm) == Vector{UInt8}("common:/")
        @test s.prefix == Vector{UInt8}("common:/")
    end

    @testset ":mork at Shared rejects a name it cannot derive a prefix from" begin
        # No leading `&` ⇒ not a space reference at all (it would bind as an ordinary atom), so there is
        # no prefix to derive and guessing one would invent a region silently.
        err = try MC.make_space(:mork; mode = MC.Shared, name = :plain_name); catch e; e; end
        @test err isa ArgumentError
        @test occursin("&", err.msg)
        # ...and neither argument at all is an error too, rather than a silent root-prefix space that
        # would alias the whole shared trie.
        @test_throws ArgumentError MC.make_space(:mork; mode = MC.Shared)
    end

    @testset ":mork at Shared accepts an explicit prefix, bypassing name derivation" begin
        s = MC.make_space(:mork; mode = MC.Shared, prefix = Vector{UInt8}("explicit_region/"))
        @test s.prefix == Vector{UInt8}("explicit_region/")
        @test s.inner === MC.get_node_shared()
    end

    @testset "an unsupported access mode THROWS rather than silently falling back" begin
        # A caller who asked for Shared and received an isolated space gets no error and wrong
        # isolation — the worst available outcome, so the refusal must be loud and name what IS
        # supported.
        @test MC.Shared ∉ MC.space_modes(:vector)
        err = try MC.make_space(:vector; mode = MC.Shared); catch e; e; end
        @test err isa ArgumentError
        @test occursin("Private", err.msg)
        # CopyOnWrite is in the enum and implemented by NOTHING — reserved, not offered.
        for k in MC.space_kinds()
            @test MC.CopyOnWrite ∉ MC.space_modes(k)
        end
    end

    @testset "persist is declared exactly where it holds" begin
        @test MC.space_caps(:mork).persist
        @test !MC.space_caps(:vector).persist
        dir = mktempdir()
        MC.set_act_dir!(dir)
        s = MC.make_space(:mork; mode = MC.Shared, prefix = Vector{UInt8}("persist_probe/"))
        # An EMPTY region returns false — the guard is `n_atoms == 0`, not "root prefix".
        @test MC.snapshot_space_to_act!(s, "empty_probe") === false
        MC.core_add!(s, [:durable, 1])
        @test MC.snapshot_space_to_act!(s, "filled_probe") === true
        @test MC.act_exists("filled_probe")
    end

    @testset "every kind declares an atomicity model and a note" begin
        # §2.2.1 leaves consistency/failure behaviour "backend-specific" — which OBLIGES the backend to
        # declare it, not to skip the question. An empty string here is a skipped question.
        for k in MC.space_kinds()
            c = MC.space_caps(k)
            @test !isempty(strip(c.atomicity))
            @test !isempty(strip(c.note))
        end
    end

    @testset "🔴 AXIS GUARD — no access mode may be folded into a kind NAME" begin
        # This is the guard for the mistake this registry already made once: `:mork_shared` and `:fork`
        # shipped as kinds, which is the first generation of `:neural_shared_readonly`. Mechanical, so
        # it fires on whoever adds the next kind rather than on a reviewer who happens to notice
        # (`[[feedback_enforcement_works_prose_memory_does_not]]`).
        banned = ("shared", "private", "readonly", "read_only", "cow", "copyonwrite", "fork")
        for k in MC.space_kinds()
            s = lowercase(string(k))
            for b in banned
                @test !occursin(b, s)
            end
        end
        # ...and the axes really are independent: at least one kind offers more than one access mode,
        # which is what makes the separation load-bearing rather than decorative.
        @test any(k -> length(MC.space_modes(k)) > 1, MC.space_kinds())
    end

    @testset "_resolve_space — the consumer the prefix registry never had" begin
        nm = Symbol("&resolve_probe")
        MC.unregister_prefix!(nm)
        @test MC._resolve_space(nm) === nothing        # unregistered resolves to nothing, never mints
        g = MC.make_space(:mork; mode = MC.Shared, name = nm)
        MC.core_add!(g, [:score, 10])
        # BY NAME — this is what `register_prefix!` existed for and had no caller of.
        @test [:score, 10] ∈ MC.core_atoms(MC._resolve_space(nm))
        # BY SYMBOLIC HANDLE — same function, second job (space design §4.2). `(SpaceRef &name)` is a
        # plain expression: matchable and serializable, never a grounded atom holding a live space.
        # Upstream's `capture` is built as CaptureOp::new(space.clone(), …), which makes every captured
        # atom process-local; that is the shape being avoided.
        @test MC.space_ref(nm) == [:SpaceRef, nm]
        @test [:score, 10] ∈ MC.core_atoms(MC._resolve_space(MC.space_ref(nm)))
        # already-resolved is identity, so callers need no branch
        @test MC._resolve_space(g) === g
        # non-handles resolve to nothing rather than throwing — `match` over mixed atoms stays cheap
        @test MC._resolve_space([:not, :a, :handle]) === nothing
        @test MC._resolve_space(nothing) === nothing
    end

    @testset "CONTAINMENT_POLICY :flat — nesting is rejected, siblings are not" begin
        @test MC.CONTAINMENT_POLICY === :flat
        # ✅ MEASURED: name-derived regions CANNOT nest. The `:/` suffix makes `&app` -> "app:/" and
        # `&app/games` -> "app/games:/" diverge at `:` vs `/`, so they are SHARING, not PREFIX_OF. The
        # suffix its docstring calls "human-debuggable" is doing load-bearing structural work.
        @test MC.prefix_compare(Vector{UInt8}("app:/"), Vector{UInt8}("app/games:/"))[1] === MC.PREFIX_SHARING
        # ...so the policy only governs HAND-PASSED prefixes, which genuinely can nest.
        @test MC.prefix_compare(Vector{UInt8}("app/"), Vector{UInt8}("app/games/"))[1] === MC.PREFIX_OF
        MC.register_prefix!(:policy_parent, Vector{UInt8}("polp/"))
        try
            err = try MC.check_prefix_free(:policy_child, Vector{UInt8}("polp/kid/")); nothing catch e; e end
            @test err isa ArgumentError
            @test occursin("NESTS", err.msg)
            # a genuine sibling must still be accepted — that IS Figure 4
            @test MC.check_prefix_free(:policy_sib, Vector{UInt8}("pols/")) === nothing
            # and one region may not have two names
            err2 = try MC.check_prefix_free(:policy_alias, Vector{UInt8}("polp/")); nothing catch e; e end
            @test err2 isa ArgumentError
        finally
            MC.unregister_prefix!(:policy_parent)
        end
    end

    @testset "the ledger renders, and shows both non-capability axes" begin
        io = IOBuffer()
        MC.space_ledger(io)
        out = String(take!(io))
        for k in MC.space_kinds()
            @test occursin(string(k), out)
        end
        @test occursin("integration", out)      # IntegrationMode axis is visible
        @test occursin("access modes", out)     # AccessMode axis is visible
        @test occursin("Native", out)
    end
end
