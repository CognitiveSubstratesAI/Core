# ── Spaces.jl — the Space CONSTRUCTOR REGISTRY, and the capability ledger that keeps it honest ──────
#
# WHY THIS EXISTS. Hyperon Deep-Dive Whitepaper 2026 v5 §2.2.1 requires that a conforming Space backend
# retain "the same declared semantics" for match/bind/rewrite, with only "latency, consistency,
# availability, and failure behavior" left as "backend-specific operational properties". Read carefully,
# that sentence imposes TWO obligations, and only the first is usually noticed:
#
#   1. a backend must present the declared interface, and
#   2. its operational properties must be DECLARED — "backend-specific" means the backend states its
#      behaviour, not that the question may be skipped.
#
# Obligation 2 is what this file is really for. We currently have several stores with GENUINELY
# different capabilities, and until now nothing recorded which was which. The failure mode that
# produced is already in the tree: `new-mork-space` is registered as an ALIAS of `new-space`
# (`standard/Eval.jl`, TOKEN_REGISTRY), so MeTTa code asking for a MORK-backed atomspace receives a
# Vector-backed one. That is defensible for the isolation contract its corpus tests — and it is exactly
# how a capability gap becomes invisible. A registry whose entries carry a capability record cannot
# make that mistake silently, because declining a capability is a value someone has to write down.
#
# WHY A REGISTRY AND NOT A `make_space(::Val{:mork})` LADDER. Construction belongs to the backend.
# metta-wam reached this first and most explicitly: `new_space` is dispatched through its 3-place
# `space_type_method(Type, Op, Method)` table like any other operation, so a backend owns its own
# constructor (see `docs/specs/space_api_upstream_survey_2026-08-13.md` §2 point 6). ADR-016's
# "Registry Pattern" prescribed the same decomposition for us, in vocabulary that has since gone stale.
#
# It also solves a concrete LAYERING problem rather than merely being tidy. `Core/Project.toml` depends
# on MORK, PathMap and MorkSupercompiler — NOT on FactorVSA, HMH or MORKTensorNetworks. Core must
# therefore never reach outward to construct a vector/tensor-backed space; those packages register
# THEMSELVES by calling `register_space_kind!` at load time. The dependency arrow stays pointing at
# Core, and the registry is open without Core knowing its members.
#
# ⚠️ WHAT THIS FILE IS NOT. It is a CONSTRUCTION and DECLARATION surface, not a universal Space API.
# The kinds below return DIFFERENT Julia types with different operation sets — `Eval.Space` is queried
# with `Eval.query`, a `CoreSpace` with `core_match`. Unifying them is the store seam
# (`AbstractStore`/`VectorStore`, landed in `d9f6116`; `Space{S<:AbstractStore}` still to come), and the
# ledger here is what makes the remaining distance MEASURABLE instead of rhetorical. Do not read a
# registered kind as a conforming backend; read its `SpaceCaps`.

"""
    SpaceCaps

What a Space kind can and cannot do, declared per whitepaper §2.2.1 obligation 2.

Every field is a claim that must be verifiable from the code body of the backend it describes — these
are not aspirations, and a `false` here is a measurement, not a TODO. `atomicity` is prose because no
boolean captures it; the survey's §8.4 finding is that upstreams which permit concurrent writers all owe
this declaration, and that "single-writer, no rollback" is an honest answer where it is the true one.
"""
struct SpaceCaps
    add         :: Bool      # insert an atom
    remove      :: Bool      # delete an atom
    atoms       :: Bool      # materialize the whole store (hyperon: an OPT-IN capability, never assumed)
    match       :: Bool      # pattern query at all
    bindings    :: Bool      # ...and does that query CAPTURE variables, or only filter?
    evaluate    :: Bool      # can MeTTa reduction run against it? (this is the compile-lane's arrow 6)
    conjunction :: Bool      # native n-way join AT THIS API — 4 of 4 upstreams put it in the space
    persist     :: Bool      # durable snapshot / reload
    partition   :: Bool      # split into independent iterators (JeTTa's `chunks`)
    shared      :: Bool      # can co-reside with sibling spaces in one substrate
    atomicity   :: String    # declared concurrency/rollback model
    note        :: String    # the one thing a caller most needs to know
end

"""
    SpaceKind

A registered constructor plus its capability declaration.

`ctor` is called as `ctor(; kwargs...)` — keyword-only, so every kind documents its own parameters and
none is positional-by-accident. `result_type` is recorded because the kinds deliberately do NOT share a
type yet; a caller that must branch can branch on this instead of on the kind name.
"""
struct SpaceKind
    name        :: Symbol
    provider    :: String    # the package that registered it — kinds are open, so say who owns each
    result_type :: Type
    ctor        :: Function
    caps        :: SpaceCaps
end

const SPACE_KINDS = Dict{Symbol, SpaceKind}()

"""
    register_space_kind!(k::SpaceKind) -> SpaceKind

Register a Space kind. Re-registering the SAME name from the SAME provider replaces the entry (so a
package reloading under Revise is not an error); a DIFFERENT provider claiming a registered name throws,
because two packages silently fighting over `:neural` is precisely the failure this table exists to make
impossible.
"""
function register_space_kind!(k::SpaceKind)
    prev = get(SPACE_KINDS, k.name, nothing)
    if prev !== nothing && prev.provider != k.provider
        throw(ArgumentError(
            "space kind :$(k.name) is already registered by $(prev.provider); " *
            "$(k.provider) must choose another name"))
    end
    SPACE_KINDS[k.name] = k
end

"""
    space_kinds() -> Vector{Symbol}

Registered kind names, sorted. Sorted rather than insertion-ordered so that output is stable across
load orders — a diffable list is worth more than a chronological one.
"""
space_kinds() = sort!(collect(keys(SPACE_KINDS)))

"""
    space_kind(name::Symbol) -> SpaceKind

Look up a kind, with an error that lists what IS available. An unknown kind is nearly always a typo or
an unloaded provider package, and both are diagnosed by seeing the list.
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

The capability declaration for a kind. Call this before assuming a store can do something; the whole
point of the table is that the answer differs per backend and is written down.
"""
space_caps(name::Symbol) = space_kind(name).caps

"""
    make_space(name::Symbol; kwargs...)

Construct a Space of the given kind. Keyword arguments are forwarded verbatim to the backend's own
constructor — see each kind's registration for what it accepts.

    make_space(:vector)                        # the interpreter's evaluable store
    make_space(:fork; parent = s)              # snapshot-isolated copy of an interpreter space
    make_space(:mork)                          # an isolated MORK trie (own trie, root prefix)
    make_space(:mork_shared; name = Symbol("&app/games"))   # a sibling region of the node-shared trie
"""
make_space(name::Symbol; kwargs...) = space_kind(name).ctor(; kwargs...)

"""
    space_ledger(io::IO = stdout)

Print the capability ledger — every registered kind against every declared capability.

This is the deliverable half of the registry. Whitepaper §2.2.1's promise is that "MeTTa code is
substantially Space-independent"; this table is the measurement of how far that is true HERE, and it is
meant to be read as a gap list, not as a feature list.
"""
function space_ledger(io::IO = stdout)
    ks = space_kinds()
    isempty(ks) && (println(io, "(no space kinds registered)"); return nothing)
    cols = ["add", "rm", "atoms", "match", "bind", "eval", "conj", "persist", "chunks", "shared"]
    getters = (c -> c.add, c -> c.remove, c -> c.atoms, c -> c.match, c -> c.bindings,
               c -> c.evaluate, c -> c.conjunction, c -> c.persist, c -> c.partition, c -> c.shared)
    w = maximum(length.(string.(ks)))
    println(io, rpad("kind", w), " │ ", join(cols, " "), "  provider")
    println(io, "─"^w, "─┼─", "─"^(sum(length.(cols)) + length(cols) - 1), "──────────")
    for n in ks
        k = SPACE_KINDS[n]
        cells = [rpad(g(k.caps) ? "✔" : "·", length(c)) for (g, c) in zip(getters, cols)]
        println(io, rpad(string(n), w), " │ ", join(cells, " "), "  ", k.provider)
    end
    println(io)
    for n in ks
        k = SPACE_KINDS[n]
        println(io, ":$(n)  [$(k.result_type)]")
        println(io, "    atomicity: ", k.caps.atomicity)
        println(io, "    ", k.caps.note)
    end
    nothing
end

# ── Core's own kinds ────────────────────────────────────────────────────────────────────────────────
#
# Four, and they are deliberately NOT four names for one thing. `:vector` is the only kind MeTTa can
# currently reduce against; the two MORK kinds are the only ones that persist; only `:mork_shared`
# co-resides with siblings. Every `false` below was read out of the code body, and the ones that matter
# most are cited so the next reader can re-check rather than re-derive.

const _CAPS_VECTOR = SpaceCaps(
    #= add =# true, #= remove =# true, #= atoms =# true, #= match =# true,
    #= bindings =# true,       # Eval.query returns Vector{Bindings} — this is the store that binds
    #= evaluate =# true,       # the live interpreter's store; the ONLY evaluable kind today
    #= conjunction =# false,   # `(, p1 p2 …)` is threaded in MATCH, not handed to the store. 4 of 4
                               # upstreams put conjunction IN the space; this is the faithfulness gap
                               # the July verdict called "not just a missing optimization".
    #= persist =# false, #= partition =# false, #= shared =# false,
    "single-writer, no rollback, no isolation — plain mutation of a Julia struct; no `with_mutex` or " *
    "`transaction` counterpart exists at any level (survey §8.4)",
    "The interpreter's store, indexed — NOT a naive vector: a (head, arg1-head) first-argument index, " *
    "a wildcard bucket, and a lazy per-bucket discrimination trie, mirroring hyperon's AtomIndex and " *
    "CeTTa's eq_idx. Backed by VectorStore since the store seam landed (d9f6116).")

const _CAPS_FORK = SpaceCaps(
    true, true, true, true, true, true, false, false, false, false,
    "single-writer, no rollback; the FORK is independent of its parent from the moment it is taken",
    "A snapshot-isolated copy of an interpreter space (clone_store, Eval.jl:641): the c2_spaces " *
    "isolation contract — a later add/remove on the fork does NOT propagate to the parent. lib_count " *
    "is preserved so get-atoms on the fork still excludes flattened library atoms.")

# ⚠️ THE TWO MORK KINDS DECLINE `bindings` AND `evaluate`, AND BOTH DECLINES ARE LOAD-BEARING.
#
#  · bindings=false — VERIFIED in the body, not inferred: `_shape_match(pattern, atom)::Bool`
#    (CoreSpace.jl:436) returns a Bool, and its first line `_is_var_symbol(pattern) && return true`
#    (:437) accepts a variable position WITHOUT capturing what it matched. `core_match` accordingly
#    returns `Vector{SExprConvertible}` — the matching ATOMS (:614). So these stores FILTER; they do not
#    BIND, and `(match &S (belief $k $s $c) $k)` cannot be served from here.
#    The native binding primitive DOES exist one layer down — `MORK.space_query_multi` streams
#    `effect(::Dict{ExprVar,ExprEnv}, loc)::Bool` — it is simply not what `core_match` calls.
#
#  · evaluate=false — this is compile-arrow 6 (`docs/specs/COMPILE_ARROW_STATUS.md`). The trie-backed
#    store LOADS but does not EVALUATE: `load_metta!(::CoreSpace)` supports only `import!` and
#    `remove-atom` and rejects every other directive. Figure 2's caption makes this architecture rather
#    than aspiration — "MeTTa-IL … leverages MORK Atomspace" — so the decline is a gap against the
#    whitepaper, and writing it here is the point.
#
# conjunction is declared false for the same reason as `:vector`: `space_query_multi` is the n-way join
# and `core_match` does not route to it. The capability is HELD by the substrate and not EXPOSED at this
# API, which is a different statement from "absent" — hence the note rather than silence.

const _MORK_ATOMICITY =
    "declared single-writer. Core adds no concurrency coordination of its own — the read/write permits " *
    "on CoreSpace are pass-throughs (CORE-INT-1, audit 2026-06-05), because upstream keeps status_map.rs " *
    "in the mork-server crate, not the kernel. A concurrent embedding needs an external coarse lock. " *
    "No rollback anywhere."

const _CAPS_MORK = SpaceCaps(
    #= add =# true, #= remove =# true, #= atoms =# true, #= match =# true,
    #= bindings =# false, #= evaluate =# false, #= conjunction =# false,
    #= persist =# true,        # snapshot_space_to_act! / load_act_source; returns false for an EMPTY
                               # region (n_atoms == 0), NOT for a root prefix — a root snapshot works
                               # and is merely slower, as CoreSpaceActIO's own comment says.
    #= partition =# false,     # see :mork_shared — partition_trie lives in MORKTensorNetworks, which is
                               # not a Core dependency; that package registers its own kind.
    #= shared =# false,        # own fresh trie, root prefix — isolated by construction
    _MORK_ATOMICITY,
    "An isolated MORK trie: its OWN Space, root prefix (= whole trie). Atoms are Expr bytes as trie " *
    "paths, so atom identity IS the path. Filters but does not bind; loads but does not evaluate.")

const _CAPS_MORK_SHARED = SpaceCaps(
    true, true, true, true, false, false, false, true,
    #= partition =# false,
    #= shared =# true,         # THE point of this kind
    _MORK_ATOMICITY,
    "A byte-prefix region of the process-shared MORK trie — whitepaper Figure 4: a `common:/` shared " *
    "atomspace with per-app siblings (`app/games:/`, `app/social:/`) living in ONE trie. Siblings with " *
    "disjoint prefixes are mutually invisible (test_corespace.jl:35-64 proves isolation AND that " *
    "cross-prefix match does not bleed). Cross-space queries are byte-walks at different prefixes.")

function _make_vector_space(; atoms = nothing)
    atoms === nothing ? Eval.Space() : Eval.Space(atoms)
end

function _make_fork_space(; parent)
    parent isa Eval.Space || throw(ArgumentError(
        "make_space(:fork) needs `parent` to be an interpreter Eval.Space; got $(typeof(parent)). " *
        "A CoreSpace has no fork operation — its isolation comes from disjoint prefixes instead, " *
        "so use make_space(:mork_shared; name = …) for a sibling region."))
    Eval.clone_store(parent)
end

_make_mork_space(;) = new_core_space()

# `:mork_shared` is where the node-shared trie and the NAME→PREFIX derivation finally meet a caller.
# Both halves were built and then left unreachable: `derive_prefix_from_name`, `register_prefix!`,
# `lookup_prefix` and `rebind_to_shared_prefix` are all exported from MeTTaCore with ZERO callers in
# src/ or test/, and their docstrings name `_resolve_space` as the consumer — a function that does not
# exist anywhere in the package (it belonged to the retired evaluator). The prefix REGISTRY is what
# makes a shared space addressable BY NAME rather than by hand-built bytes, which is the difference
# between Figure 4's model and four tests that happen to pass byte strings.
function _make_mork_shared_space(; name = nothing, prefix = nothing)
    if prefix === nothing
        name === nothing && throw(ArgumentError(
            "make_space(:mork_shared) needs either `name` (a MeTTa space name such as " *
            "Symbol(\"&app/games\")) or an explicit `prefix::Vector{UInt8}`"))
        nm = name isa Symbol ? name : Symbol(name)
        prefix = derive_prefix_from_name(nm)
        prefix === nothing && throw(ArgumentError(
            "shared-space name must begin with `&` so a trie prefix can be derived from it " *
            "(`:&common` → \"common:/\"); got :$nm. Names without `&` bind as ordinary atoms, " *
            "not as space references."))
        register_prefix!(nm, prefix)     # make it addressable by name, not only by these bytes
    end
    new_core_space(get_node_shared(), prefix isa Vector{UInt8} ? prefix : Vector{UInt8}(prefix))
end

function _register_core_space_kinds!()
    register_space_kind!(SpaceKind(:vector, "MeTTaCore", Eval.Space,
                                   _make_vector_space, _CAPS_VECTOR))
    register_space_kind!(SpaceKind(:fork, "MeTTaCore", Eval.Space,
                                   _make_fork_space, _CAPS_FORK))
    register_space_kind!(SpaceKind(:mork, "MeTTaCore", CoreSpace,
                                   _make_mork_space, _CAPS_MORK))
    register_space_kind!(SpaceKind(:mork_shared, "MeTTaCore", CoreSpace,
                                   _make_mork_shared_space, _CAPS_MORK_SHARED))
    nothing
end

# Registered at module-load time (MeTTaCore has no `__init__`), so Core's four kinds are baked into the
# precompile image and are present the instant the package is usable. A FOREIGN provider must instead
# register from its own `__init__` — its constructor cannot exist in Core's image, and registering at
# runtime is what keeps the dependency arrow pointing at Core.
_register_core_space_kinds!()
