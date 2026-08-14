# ── Spaces.jl — the Space KIND registry, its capability ledger, and the three axes they sit on ───────
#
# WHY THIS EXISTS. Hyperon Deep-Dive Whitepaper 2026 v5 §2.2.1 requires that a conforming Space backend
# retain "the same declared semantics" for match/bind/rewrite, with only "latency, consistency,
# availability, and failure behavior" left as "backend-specific operational properties". That sentence
# imposes TWO obligations and only the first is usually noticed:
#
#   1. a backend must present the declared interface, and
#   2. its operational properties must be DECLARED — "backend-specific" means the backend states its
#      behaviour, not that the question may be skipped.
#
# Obligation 2 is what this file is really for. The failure mode it guards against is already in the
# tree: `new-mork-space` is registered as an ALIAS of `new-space` (`standard/Eval.jl`, TOKEN_REGISTRY),
# so MeTTa code asking for a MORK-backed atomspace receives a Vector-backed one. That is defensible for
# the isolation contract its corpus tests, and it is exactly how a capability gap becomes invisible. A
# registry whose entries carry a capability record cannot make that mistake silently, because declining
# a capability is a value someone has to write down.
#
# ── 🔴 THREE AXES, NOT ONE. Read this before adding a kind. ──────────────────────────────────────────
#
# The first version of this file got this wrong and shipped `:mork` and `:mork_shared` as separate
# KINDS. That is the start of a combinatorial explosion — the same mistake generates `:mork_readonly`,
# and then `:neural_shared`, `:neural_shared_readonly`. The axes are independent and must stay so:
#
#   KIND             what BACKS the payload         — MORK trie, interpreter vector, VSA arena, tensors
#   ACCESS MODE      who can SEE and WRITE it       — Private, Shared, ReadOnly, CopyOnWrite
#   INTEGRATION MODE where EXECUTION lives          — Native, Bridge, External (whitepaper §2.4)
#
# "A shared space" is not a kind; it is a kind at `Shared`. "A fork" is not a kind either — it is a
# Private region seeded from a parent, which is why `:fork` was removed and `make_space(:vector;
# parent = s)` replaced it. Applying the rule to `:mork_shared` and not to `:fork` would have been
# half a fix.
#
# ⚠️ INTEGRATION MODE IS PER-REGION IN THE ARCHITECTURE, AND PER-KIND HERE. §2.4 is explicit that the
# three modes COEXIST: one system may run a remote frontier model (External), a local instrumented
# transformer with symbolic heads (Bridge) and a native QuantiMORK network (Native) — all three being
# Neural Spaces. So integration mode properly belongs to a region BINDING, not to a kind. We do not yet
# have a region object to hang it on (that is the region/view rework, deferred), so it is declared
# per-kind and ASSERTED at registration as "the only binding currently realizable for this kind". When
# regions become first-class this field moves; it is recorded here so that move is a rename, not a
# rediscovery.
#
# ── ⚠️ THREE REGISTRIES, AND THIS IS ONLY ONE OF THEM. Do not let the names blur. ────────────────────
#
#   1. THIS FILE — a KIND/CONSTRUCTOR table. Which backends exist and how to build one.
#   2. The REGION REGISTRY — prefix allocation, containment, region lifecycle in the shared trie. We
#      have this in embryo as `PREFIX_REGISTRY` + `NODE_SHARED` (`space/CoreSpace.jl`); it is not yet a
#      registry with lifecycle, and it is the storage layer, not this one.
#   3. The MODULE SPACE REGISTRY — whitepaper §6.3. A CAPABILITY BROKER: modules keyed by cognitive
#      capability, with input/output atom types, endpoint, cost, latency, trust score, health, load,
#      module SELECTION and FALLBACK CHAINS. It is a typed service directory, not an allocator.
#      🔴 WE DO NOT HAVE IT, and nothing in this file may be called by that name. A `ModuleSpaceRegistry`
#      would REFERENCE kinds and regions while being keyed by capability — a separate component.
#
# ⚠️ AND WHAT THIS FILE IS NOT: a universal Space API. The kinds below return DIFFERENT Julia types with
# different operation sets — `Eval.Space` is queried with `Eval.query`, a `CoreSpace` with `core_match`.
# Unifying them is the store seam (`AbstractStore`/`VectorStore`, landed `d9f6116`; `Space{S<:AbstractStore}`
# still to come). The ledger here makes the remaining distance MEASURABLE rather than rhetorical. Do not
# read a registered kind as a conforming backend; read its `SpaceCaps`.

"""
    AccessMode

Who can see and write a space. Orthogonal to kind — every kind should eventually support every mode it
can meaningfully support, and no mode may ever be folded into a kind name.

`CopyOnWrite` is declared and NOT implemented anywhere. It is in the enum deliberately: MORK's stated
model (§2.3) is that trie nodes are immutable and updates create versions, so copy-on-write is
ultimately a property of the substrate rather than a feature to add on top. ⚠️ But that is the
ARCHITECTURE's claim, not a measured property of our port — `CoreSpace`'s read/write permits are
pass-throughs (CORE-INT-1, audit 2026-06-05) and Core adds no concurrency coordination at all. So the
name is reserved and any kind offering it must earn it.
"""
@enum AccessMode Private Shared ReadOnly CopyOnWrite

"""
    IntegrationMode

Where execution lives for a space's payload — whitepaper §2.4's three neural-integration modes,
generalized to any backend.

* `Native`   — payload sits directly in the store the kernel matches, so rewrites and the supercompiler
               operate at the same granularity. No handles, no call-out.
* `Bridge`   — handle-refs (`(VecRef h)`, `(EpisodeRef h)`, `(TensorRef h)`) live in the trie while the
               payload lives in a side arena. Joins stay legal and run on the handles; a grounded call
               dereferences only after the join has narrowed the candidates.
* `External` — the backend is invoked as a service in its own framework. ⚠️ Its RESULTS are Atoms and
               are natively matchable thereafter, which is why this is not "opaque".

⚠️ The atom-store kinds are declared `Native` in the sense of "matched in place, no handles and no
call-out". That is a generalization of a term §2.4 introduces for NEURAL integration, and the stretch is
worth naming rather than hiding: for `:vector` "the kernel" is the evaluator, for `:mork` it is the MORK
kernels, and those are not the same kernel. The distinction will matter as soon as a second kind claims
`Native`, and it is the reason `integration` is asserted at registration rather than inferred.
"""
@enum IntegrationMode Native Bridge External

"""
    SpaceCaps

What a Space kind can and cannot do, declared per whitepaper §2.2.1 obligation 2.

Every field is a claim verifiable from the code body of the backend it describes — these are
measurements, not aspirations, and a `false` is a finding rather than a TODO. `atomicity` is prose
because no boolean captures it; the survey's §8.4 conclusion is that any backend permitting concurrent
writers owes this declaration, and that "single-writer, no rollback" is an honest answer where true.

⚠️ There is deliberately NO `shared` field. Sharing is an ACCESS MODE, and carrying it here as well
would put the same axis in two places — which is precisely how `:mork_shared` became a kind.
"""
struct SpaceCaps
    add         :: Bool      # insert an atom
    remove      :: Bool      # delete an atom
    atoms       :: Bool      # materialize the whole store (hyperon: OPT-IN, never assumed)
    match       :: Bool      # pattern query at all
    bindings    :: Bool      # ...and does that query CAPTURE variables, or only filter?
    evaluate    :: Bool      # can MeTTa reduction run against it? (this is compile-arrow 6)
    conjunction :: Bool      # native n-way join AT THIS API — 4 of 4 upstreams put it in the space
    persist     :: Bool      # durable snapshot / reload
    partition   :: Bool      # split into independent iterators (JeTTa's `chunks`)
    atomicity   :: String    # declared concurrency/rollback model
    note        :: String    # the one thing a caller most needs to know
end

"""
    SpaceKind

A registered constructor, the access modes it supports, its integration binding, and its capabilities.

`ctor` is called as `ctor(; mode, kwargs...)` — keyword-only, so every kind documents its own parameters
and none is positional by accident. `result_type` is recorded because kinds deliberately do NOT share a
type yet; a caller that must branch can branch on this rather than on the kind name.
"""
struct SpaceKind
    name        :: Symbol
    provider    :: String              # kinds are open, so every entry says who owns it
    result_type :: Type
    modes       :: Vector{AccessMode}  # access modes this kind can actually be built at
    integration :: IntegrationMode     # ⚠️ per-kind today, per-REGION in the architecture — see header
    ctor        :: Function
    caps        :: SpaceCaps
end

const SPACE_KINDS = Dict{Symbol, SpaceKind}()

"""
    register_space_kind!(k::SpaceKind) -> SpaceKind

Register a Space kind. Re-registering the same name from the SAME provider replaces the entry (so a
package reloading under Revise is not an error); a DIFFERENT provider claiming a registered name throws,
because two packages silently contending for `:neural` is exactly what this table exists to prevent.

Also rejects a kind declaring no access modes — a kind nothing can be constructed at is a typo, and it
would otherwise fail much later at the `make_space` call with a confusing message.
"""
function register_space_kind!(k::SpaceKind)
    prev = get(SPACE_KINDS, k.name, nothing)
    if prev !== nothing && prev.provider != k.provider
        throw(ArgumentError(
            "space kind :$(k.name) is already registered by $(prev.provider); " *
            "$(k.provider) must choose another name"))
    end
    isempty(k.modes) && throw(ArgumentError(
        "space kind :$(k.name) declares no access modes — nothing could ever be constructed from it"))
    SPACE_KINDS[k.name] = k
end

"""
    space_kinds() -> Vector{Symbol}

Registered kind names, sorted — stable across load orders, so the list is diffable rather than
chronological.
"""
space_kinds() = sort!(collect(keys(SPACE_KINDS)))

"""
    space_kind(name::Symbol) -> SpaceKind

Look up a kind, with an error listing what IS available. An unknown kind is nearly always a typo or an
unloaded provider package, and seeing the list diagnoses both.
"""
function space_kind(name::Symbol)
    k = get(SPACE_KINDS, name, nothing)
    k === nothing && throw(ArgumentError(
        "unknown space kind :$name — registered: $(join(string.(space_kinds()), ", ")). " *
        "Kinds are registered by their providing package, so a missing one usually means that " *
        "package is not loaded."))
    k
end

"""
    space_caps(name::Symbol) -> SpaceCaps

The capability declaration for a kind. Call this before assuming a store can do something — the answer
differs per backend, which is the entire point of writing it down.
"""
space_caps(name::Symbol) = space_kind(name).caps

"""
    space_modes(name::Symbol) -> Vector{AccessMode}

Access modes a kind can be constructed at.
"""
space_modes(name::Symbol) = space_kind(name).modes

"""
    make_space(name::Symbol; mode::AccessMode = Private, kwargs...)

Construct a Space of the given kind at the given access mode. Remaining keywords are forwarded verbatim
to the backend's own constructor.

    make_space(:vector)                                              # a private interpreter store
    make_space(:vector; parent = s)                                  # ...seeded from s (a "fork")
    make_space(:mork)                                                # an isolated MORK trie
    make_space(:mork; mode = Shared, name = Symbol("&app/games"))    # a region of the node-shared trie

An unsupported mode throws and names the modes that ARE supported, rather than silently falling back to
`Private` — a caller who asked for `Shared` and received an isolated space would get no error and wrong
isolation, which is the worst available outcome.
"""
function make_space(name::Symbol; mode::AccessMode = Private, kwargs...)
    k = space_kind(name)
    mode in k.modes || throw(ArgumentError(
        "space kind :$name does not support access mode $mode — supported: " *
        "$(join(string.(k.modes), ", "))"))
    k.ctor(; mode = mode, kwargs...)
end

"""
    space_ledger(io::IO = stdout)

Print the capability ledger — every registered kind against every declared capability, plus its access
modes and integration binding.

This is the deliberate deliverable half of the registry. §2.2.1 promises "MeTTa code is substantially
Space-independent"; this table measures how far that is true HERE, and is meant to read as a gap list.
"""
function space_ledger(io::IO = stdout)
    ks = space_kinds()
    isempty(ks) && (println(io, "(no space kinds registered)"); return nothing)
    cols = ["add", "rm", "atoms", "match", "bind", "eval", "conj", "persist", "chunks"]
    getters = (c -> c.add, c -> c.remove, c -> c.atoms, c -> c.match, c -> c.bindings,
               c -> c.evaluate, c -> c.conjunction, c -> c.persist, c -> c.partition)
    w = maximum(length.(string.(ks)))
    println(io, rpad("kind", w), " │ ", join(cols, " "), " │ integration │ access modes")
    println(io, "─"^w, "─┼─", "─"^(sum(length.(cols)) + length(cols) - 1), "─┼─────────────┼─────────────")
    for n in ks
        k = SPACE_KINDS[n]
        cells = [rpad(g(k.caps) ? "✔" : "·", length(c)) for (g, c) in zip(getters, cols)]
        println(io, rpad(string(n), w), " │ ", join(cells, " "), " │ ",
                rpad(string(k.integration), 11), " │ ", join(string.(k.modes), ", "))
    end
    println(io)
    for n in ks
        k = SPACE_KINDS[n]
        println(io, ":$(n)  [$(k.result_type)]  provider=$(k.provider)")
        println(io, "    atomicity: ", k.caps.atomicity)
        println(io, "    ", k.caps.note)
    end
    nothing
end

# ── Core's own kinds ────────────────────────────────────────────────────────────────────────────────
#
# TWO, not four. `:mork_shared` collapsed into `:mork` at `Shared`, and `:fork` into `:vector` with a
# `parent` seed — both were modes wearing a kind's clothing. Every `false` below was read out of the
# code body, and the ones that matter are cited so the next reader can re-check rather than re-derive.

const _CAPS_VECTOR = SpaceCaps(
    #= add =# true, #= remove =# true, #= atoms =# true, #= match =# true,
    #= bindings =# true,       # Eval.query returns Vector{Bindings} — this is the store that BINDS
    #= evaluate =# true,       # the live interpreter's store; the ONLY evaluable kind today
    #= conjunction =# false,   # `(, p1 p2 …)` is threaded in MATCH, not handed to the store. 4 of 4
                               # upstreams put conjunction IN the space; the July verdict called this
                               # "a faithfulness bug, not just a missing optimization".
    #= persist =# false, #= partition =# false,
    "single-writer, no rollback, no isolation — plain mutation of a Julia struct; no `with_mutex` or " *
    "`transaction` counterpart exists at any level (survey §8.4)",
    "The interpreter's store, INDEXED — not a naive vector: a (head, arg1-head) first-argument index, " *
    "a wildcard bucket, and a lazy per-bucket discrimination trie, mirroring hyperon's AtomIndex and " *
    "CeTTa's eq_idx. Backed by VectorStore since the store seam landed (d9f6116). Pass `parent = s` " *
    "for a snapshot-isolated copy (the c2_spaces fork contract).")

# ⚠️ THE MORK KIND DECLINES `bindings` AND `evaluate`, AND BOTH DECLINES ARE LOAD-BEARING.
#
#  · bindings — WAS false, now TRUE, and the history is the lesson. `_shape_match(pattern, atom)::Bool`
#    (CoreSpace.jl) returns a Bool and accepts a variable position WITHOUT capturing it, so `core_match`
#    returns only the matching ATOMS. That was read as "the trie cannot bind". It could: the binding
#    primitive was one layer down the whole time (`space_query_multi_at`), and `core_match_bind` now
#    routes to it. ⇒ A DECLINE AT AN API IS NOT AN ABSENCE IN THE SUBSTRATE — this row was three
#    declines deep in that same pattern (bindings, conjunction, partition), each with a live primitive
#    behind it and no exposure.
#
#  · evaluate=false — this is compile-arrow 6 (`docs/specs/COMPILE_ARROW_STATUS.md`). The trie-backed
#    store LOADS but does not EVALUATE: `load_metta!(::CoreSpace)` supports only `import!` and
#    `remove-atom` and rejects every other directive. Figure 2's caption makes this architecture rather
#    than aspiration — "MeTTa-IL … leverages MORK Atomspace" — so the decline is a gap against the
#    whitepaper, and writing it down is the point.

const _CAPS_MORK = SpaceCaps(
    #= add =# true, #= remove =# true, #= atoms =# true, #= match =# true,
    #= bindings =# true,       # ⇠ FLIPPED (space design §2). `core_match_bind` routes to
                               # `space_query_multi_at`'s indexed descent and returns
                               # Dict{Symbol,SExprConvertible} per match. `core_match` still FILTERS —
                               # both exist; the KIND can now bind, which is what this column declares.
    #= evaluate =# false, #= conjunction =# false,
    #= persist =# true,        # snapshot_space_to_act! / load_act_source. Returns false for an EMPTY
                               # region (n_atoms == 0), NOT for a root prefix — a root snapshot works
                               # and is merely slower, as CoreSpaceActIO's own comment says.
    #= partition =# false,     # ⚠️ the PRIMITIVE exists — MORKTensorNetworks' ShardZipper
                               # `partition_trie(space, l_max)` IS JeTTa's `chunks`, over this same
                               # trie — but MORKTN is not a Core dependency and nothing exposes it on a
                               # Space. Declared false because it is not reachable HERE, not absent.
    "declared single-writer. Core adds no concurrency coordination of its own — the read/write permits " *
    "on CoreSpace are pass-throughs (CORE-INT-1, audit 2026-06-05), because upstream keeps status_map.rs " *
    "in the mork-server crate, not the kernel. A concurrent embedding needs an external coarse lock. " *
    "No rollback anywhere. ⚠️ MORK's stated model (§2.3 — immutable nodes, versioned updates, atomic " *
    "delta merge, snapshot reads) is the ARCHITECTURE's claim and is NOT measured in this port.",
    "A MORK trie. At Private: its own Space at the root prefix. At Shared: a byte-prefix region of the " *
    "process-shared trie — whitepaper Figure 4, a `common:/` atomspace with per-app siblings " *
    "(`app/games:/`) in ONE trie, mutually invisible when prefixes are disjoint (test_corespace.jl:35-64 " *
    "proves isolation AND that cross-prefix match does not bleed). Atoms are Expr bytes as trie paths, " *
    "so atom identity IS the path. `core_match` filters, `core_match_bind` BINDS (indexed, region-scoped); " *
    "still loads but does not evaluate — that decline is compile-arrow 6.")

# `parent` turns this into what used to be the `:fork` kind: a snapshot-isolated copy. It is the same
# ACCESS MODE (Private) over the same KIND, seeded differently — which is why it is a keyword and not a
# kind of its own.
function _make_vector_space(; mode::AccessMode, atoms = nothing, parent = nothing)
    if parent !== nothing
        parent isa Eval.Space || throw(ArgumentError(
            "make_space(:vector; parent = …) needs an interpreter Eval.Space; got $(typeof(parent)). " *
            "A CoreSpace has no snapshot-fork operation — its isolation comes from disjoint prefixes " *
            "instead, so use make_space(:mork; mode = Shared, name = …) for an independent region."))
        atoms === nothing || throw(ArgumentError(
            "make_space(:vector) takes `parent` OR `atoms`, not both — a fork is seeded from its " *
            "parent's snapshot, so supplying atoms as well would silently discard one of them"))
        return Eval.clone_store(parent)
    end
    atoms === nothing ? Eval.Space() : Eval.Space(atoms)
end

# At Shared this is where the node-shared trie and the NAME→PREFIX derivation finally meet a caller.
# Both halves were built and then left unreachable: `derive_prefix_from_name`, `register_prefix!`,
# `lookup_prefix` and `rebind_to_shared_prefix` are all exported from MeTTaCore with ZERO callers in
# src/ or test/, and their docstrings named `_resolve_space` as the consumer — a function that is 0
# across all 9 live repos and survives only in the legacy ~/PRIMUS tree. The prefix REGISTRY is what
# makes a shared space addressable BY NAME rather than by hand-built bytes, which is the difference
# between Figure 4's model and a few tests that happen to pass byte strings.
function _make_mork_space(; mode::AccessMode, name = nothing, prefix = nothing)
    if mode === Private
        (name === nothing && prefix === nothing) || throw(ArgumentError(
            "make_space(:mork) at Private takes no `name`/`prefix` — a private MORK space owns its " *
            "whole trie at the root prefix. Pass `mode = Shared` to place it in the node-shared trie."))
        return new_core_space()
    end
    # mode === Shared
    if prefix === nothing
        name === nothing && throw(ArgumentError(
            "make_space(:mork; mode = Shared) needs either `name` (a MeTTa space name such as " *
            "Symbol(\"&app/games\")) or an explicit `prefix::Vector{UInt8}`"))
        nm = name isa Symbol ? name : Symbol(name)
        prefix = derive_prefix_from_name(nm)
        prefix === nothing && throw(ArgumentError(
            "shared-space name must begin with `&` so a trie prefix can be derived from it " *
            "(`:&common` → \"common:/\"); got :$nm. Names without `&` bind as ordinary atoms, " *
            "not as space references."))
        register_prefix!(nm, prefix)     # addressable by name, not only by these bytes
    end
    new_core_space(get_node_shared(), prefix isa Vector{UInt8} ? prefix : Vector{UInt8}(prefix))
end

function _register_core_space_kinds!()
    register_space_kind!(SpaceKind(:vector, "MeTTaCore", Eval.Space,
                                   [Private], Native, _make_vector_space, _CAPS_VECTOR))
    register_space_kind!(SpaceKind(:mork, "MeTTaCore", CoreSpace,
                                   [Private, Shared], Native, _make_mork_space, _CAPS_MORK))
    nothing
end

# Registered at module-load time (MeTTaCore has no `__init__`), so Core's kinds are baked into the
# precompile image and present the instant the package is usable. A FOREIGN provider must instead
# register from its own `__init__` — its constructor cannot exist in Core's image, and registering at
# runtime is what keeps the dependency arrow pointing at Core.
_register_core_space_kinds!()
