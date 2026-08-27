"""
CoreSpace — MORK.Space-backed atom space.

Every atom is stored as a byte-path in a MORK PathMap trie.
S-expression strings are the interchange format between Julia and MORK.
"""

# ── Atom ↔ S-expression conversion ───────────────────────────────────────────

"""
Convert any Julia value to a MORK-compatible S-expression string.

Variables (Symbol starting with a dollar sign) are encoded as ground symbols `__var_NAME`
so they survive the MORK byte-trie round-trip. MORK's native dollar-variable syntax
anonymises variable names (de Bruijn); __var_x preserves them.

For query patterns, call `to_sexpr_query` which uses dollar-variables directly.
"""
# The S-expression-convertible domain: exactly what to_sexpr / to_sexpr_atom / to_sexpr_query and
# core_add! / core_remove! accept (the MORK "Vector-form" representation + raw sexpr strings). An
# explicit union — NOT `::Any` — so the store boundary fails CLOSED at dispatch on an unexpected
# type (e.g. an interpreter `Atom`, which must go through `typed_atom_to_expr`, not the old
# `string(x)` fallback that silently mis-serialised it). GUARANTEE not CONVENTION.
const SExprConvertible = Union{AbstractString, Symbol, Bool, Number, Tuple, AbstractVector}

# 🔴 STREAMED — 2026-08-15, same fix as `EmitIL.il_text` (`4076652`/`86df565`), applied to the HOTTER
# path: this runs on every atom written to a MORK-backed space, not just on IL serialization.
# The old body built `to_sexpr.(x)` — a full Array of Strings — then `join`ed it, then interpolated
# into a THIRD String, recursively, at every node. Measured on `il_text`'s identical shape: 19 440
# allocations and 999 KiB to produce an 11 KB string; streaming took it to 16 allocs / 25.5 KiB.
# Adopted from PeTTa PR #167 (DCG `swrite/2` → `with_output_to/2`, 20-77x less peak memory).
# `sprint(f, args…)` is Julia's `with_output_to(string(S), Goal)`; the writer takes `::IO` so a
# caller holding a stream can serialize straight into it without materializing the String.
#
# ⚠️ SEMANTICS PRESERVED EXACTLY — this is the STORAGE encoder, and its every branch is load-bearing:
#   * `$x` → `__var_x` is the storage form (see the header above and `from_sexpr`'s decode).
#   * `AbstractString` passes through RAW (a raw S-expr fragment), NOT quoted — `to_sexpr_atom` is
#     the quoting variant. Getting this backwards silently changes what lands in the trie.
#   * `Bool` MUST be tested before `Number` (`Bool <: Integer`), preserved by the if/elseif order.
to_sexpr(x::SExprConvertible)::String = sprint(_to_sexpr!, x)

function _to_sexpr!(io::IO, x::SExprConvertible)::IO
    if x isa Symbol
        s = string(x)
        if startswith(s, "\$")
            write(io, "__var_")
            write(io, SubString(s, 2))
        else
            write(io, s)
        end
    elseif x isa AbstractString
        write(io, x)                       # passthrough: raw S-expr for core_add!/core_remove!
    elseif x isa Bool
        write(io, x ? "True" : "False")    # must precede Number (Bool <: Integer)
    elseif x isa Number
        print(io, x)
    else                                   # Tuple or AbstractVector — same rendering
        write(io, '(')
        firstc = true
        for e in x
            firstc ? (firstc = false) : write(io, ' ')
            _to_sexpr!(io, e)
        end
        write(io, ')')
    end
    io
end

"""
    to_sexpr_atom(x) → String

Like `to_sexpr` but for the *grounded-dispatch* boundary: Julia String values
are treated as MeTTa string literals (quoted, escape_string'd) so primitives
like `get-type`, `type-cast`, `is-symbol` can distinguish "hi" from the
symbol `:hi`.

`to_sexpr` itself preserves the legacy raw-S-expr passthrough semantics for
String inputs (used by `core_add!`/`core_remove!`).
"""
function to_sexpr_atom(x::SExprConvertible)::String
    x isa AbstractString && return "\"" * escape_string(String(x)) * "\""
    to_sexpr(x)
end

"""
Convert a pattern to S-expression, keeping dollar-variables as MORK wildcards.
Use for `core_match` queries — do NOT use for storage (variable names lost).
"""
function to_sexpr_query(x::SExprConvertible)::String
    if x isa Symbol
        s = string(x)
        # __var_x is the storage form of $x — convert back so MORK treats it as wildcard
        startswith(s, "__var_") && return "\$" * s[7:end]
        return s   # $x stays as-is — MORK parses it as a wildcard variable
    end
    x isa AbstractString && return String(x)   # passthrough — query patterns may contain raw S-expr fragments
    x isa Bool && return x ? "True" : "False"   # must precede Number (Bool <: Integer)
    x isa Number && return string(x)
    x isa Tuple && return "($(join(to_sexpr_query.(x), " ")))"
    "($(join(to_sexpr_query.(x), " ")))"       # x::AbstractVector
end

"""Parse a MORK S-expression string into a Julia value."""
# Returns `nothing` for an EMPTY string (line below) — so the honest type is a Union, not `Any`.
# `Any` hid that: callers pushing into a `Vector{SExprConvertible}` accept `nothing` silently under
# `Any` and a null atom enters the store. Typed, that same push is a MethodError at the boundary.
from_sexpr(s::AbstractString)::Union{SExprConvertible, Nothing} = from_sexpr(String(s))
function from_sexpr(s::String)::Union{SExprConvertible, Nothing}
    s = strip(s)
    isempty(s) && return nothing
    s == "True" && return true
    s == "False" && return false

    # String literal — preserves type tag from to_sexpr round-trip
    if startswith(s, "\"") && endswith(s, "\"") && length(s) >= 2
        return unescape_string(s[2:(end - 1)])
    end

    n = tryparse(Int, s)
    n !== nothing && return n
    n = tryparse(Float64, s)
    n !== nothing && return n

    # MORK variable encoding: __var_NAME → Symbol("$NAME")
    startswith(s, "__var_") && return Symbol("\$" * s[7:end])
    # Legacy $x form (from MORK parser)
    startswith(s, "\$") && return Symbol(s)

    if startswith(s, "(") && endswith(s, ")")
        inner = s[2:(end - 1)]
        tokens = _tokenise(inner)
        isempty(tokens) && return SExprConvertible[]   # NOT `[]` — a bare literal is Vector{Any}
        # SExprConvertible, not Any: `_tokenise` never yields an empty token, so no element can be
        # `nothing` here — and if that ever changes this throws at the boundary instead of storing a
        # null atom. Fails CLOSED, per this file's stated store-boundary discipline (line 21).
        return SExprConvertible[from_sexpr(t) for t in tokens]
    end

    Symbol(s)
end

export _tokenise
_tokenise(s::AbstractString) = _tokenise(String(s))
function _tokenise(s::String)::Vector{String}
    tokens = String[]
    depth = 0
    start = 1
    i = 1
    in_str = false
    while i <= length(s)
        c = s[i]
        if in_str
            # Inside a quoted string: only an unescaped " ends it
            if c == '\\' && i + 1 <= length(s)
                i += 2
                continue
            elseif c == '"'
                in_str = false
            end
        elseif c == '"'
            in_str = true
        elseif c == '('
            depth += 1
        elseif c == ')'
            depth -= 1
            if depth == 0
                push!(tokens, strip(s[start:i]))
                start = i + 1
            end
        elseif isspace(c) && depth == 0
            tok = strip(s[start:(i - 1)])
            !isempty(tok) && push!(tokens, tok)
            start = i + 1
        end
        i += 1
    end
    tok = strip(s[start:end])
    !isempty(tok) && push!(tokens, tok)
    tokens
end

# ── CoreSpace ─────────────────────────────────────────────────────────────────

"""
    CoreSpace

MeTTa atom space — a reference to a shared `MORK.Space` byte trie PLUS a
byte-prefix that scopes this space's operations to a region within the trie.

Stage 1 (single-node) lets many CoreSpaces share one `Space` (one trie) with
disjoint prefixes — implementing the whitepaper's Figure 4 model where a
`common:/` shared-knowledge atomspace and per-app atomspaces (`app/games:/`,
`app/social:/`, `app/bio:/`, `app/math:/`) live as siblings in one trie.

Backward-compatible: `new_core_space()` still creates a CoreSpace with its
own fresh trie and empty prefix (= root = whole trie), so existing isolated-
atomspace callers see no change.

Fields:
- `inner`  — the shared `MORK.Space` (the byte trie). May be shared across
             many CoreSpaces on the same node.
- `prefix` — this space's byte-region within `inner`. Empty = root.
- `rule_cache`       — per-space; cached `(= head body)` rules.
- `named_spaces`     — per-space `bind!`/`with-space` registry (Symbol → CoreSpace).
- `use_supercompiler`— route exec atoms through `MorkSupercompiler.plan!`.
"""
mutable struct CoreSpace
    inner::Space
    prefix::Vector{UInt8}
    rule_cache::Dict{Symbol, Vector{Tuple{Vector{SExprConvertible}, SExprConvertible}}}
    named_spaces::Dict{Symbol, CoreSpace}
    use_supercompiler::Bool
end

"""
    new_core_space() :: CoreSpace

Create a CoreSpace with its own fresh shared trie and empty prefix (= root).
Backward-compatible — every existing caller gets an isolated atomspace.

For shared-trie semantics (multi-space on one node), prefer
`make_space(:mork_shared; name = Symbol("&app/games"))` (space/Spaces.jl), which derives the
prefix from the name, registers it, and attaches to the node-shared trie in one step. The
lower-level `new_core_space(shared::Space, prefix::Vector{UInt8})` remains available.

⚠️ This docstring previously directed the reader to `_resolve_space`, which has not existed in
this package since the legacy evaluator was retired — a pointer that outlived its target. The
registry is the live consumer; see `docs/specs/space_creation_registry_2026-08-14.md` §2.3.
"""
new_core_space() = CoreSpace(new_space(),
    UInt8[],
    Dict{Symbol, Vector{Tuple{Vector{SExprConvertible}, SExprConvertible}}}(),
    Dict{Symbol, CoreSpace}(),
    false)

"""
    new_core_space(shared::Space, prefix::Vector{UInt8}) :: CoreSpace

Create a CoreSpace as a `(shared trie, byte-prefix)` reference. Atoms live
in `shared`; this CoreSpace's operations are scoped to `prefix`.

Two CoreSpaces with the same `shared` and `prefix_compare(p1, p2) ==
PREFIX_DISJOINT` address non-overlapping regions of the trie and are
mutually independent. Core itself adds no concurrency coordination — that
is a server-tier concern (see the permit pass-throughs below, CORE-INT-1);
a concurrent embedding without an external coarse lock would reattach it there.
"""
new_core_space(shared::Space, prefix::Vector{UInt8}) =
    CoreSpace(shared, copy(prefix),
        Dict{Symbol, Vector{Tuple{Vector{SExprConvertible}, SExprConvertible}}}(),
        Dict{Symbol, CoreSpace}(),
        false)

# ── Node-level prefix registry ────────────────────────────────────────────────
# Stage 1: process-level Symbol → byte-prefix mapping, materializing named spaces
# like `&common`, `&app/games` as `(shared, prefix)` CoreSpaces.
#
# ⚠️ The consumer named here used to be `Eval.jl`'s `_resolve_space`, which no
# longer exists anywhere in the package (it belonged to the retired evaluator).
# Between that removal and 2026-08-14 this registry had ZERO callers in src/ or
# test/ — the mechanism worked and nothing could address it by name. The live
# consumer is now `make_space(:mork_shared; name = …)` in space/Spaces.jl.
#
# Multi-node concerns (Stage 2) will replace this with a per-node registry
# stored on the shared Space itself, but Stage 1 keeps it process-global for
# simplicity and ergonomic single-node use.

const PREFIX_REGISTRY = Dict{Symbol, Vector{UInt8}}()

"""
    register_prefix!(name::Symbol, prefix::Vector{UInt8})

Register a symbolic name → byte-prefix mapping in the process-level
`PREFIX_REGISTRY`.  The bytes are stored verbatim (a raw prefix into the
trie, NOT an S-expression).  By convention, prefixes end with `:/`
(e.g. `Vector{UInt8}("common:/")`) to be human-debuggable and to guarantee
disjointness across siblings (`prefix_compare` will return `PREFIX_DISJOINT`).
"""
function register_prefix!(name::Symbol, prefix::Vector{UInt8})
    PREFIX_REGISTRY[name] = copy(prefix)
    nothing
end

"""
    lookup_prefix(name::Symbol) :: Union{Vector{UInt8}, Nothing}

Retrieve a registered prefix or `nothing` if unregistered.
"""
lookup_prefix(name::Symbol) = get(PREFIX_REGISTRY, name, nothing)

"""
    unregister_prefix!(name::Symbol)

Remove a name → prefix mapping.  Used by `with-space`'s exit cleanup when
the bound name didn't exist prior to the scope.
"""
unregister_prefix!(name::Symbol) = (delete!(PREFIX_REGISTRY, name); nothing)

# ── Node-shared trie (Stage 1 C′ — shared-default + bind-required-for-prefix) ──
#
# A single MORK.Space per process for all named-and-bound CoreSpaces.
# `(bind! &name (new-space))` attaches the bound name to a derived prefix
# in this shared trie; cross-space queries are byte-walks at different
# prefixes in the same trie (matching the metagraph-philosophy default).
#
# Anonymous `(new-space)` calls — those NOT bound to a name — keep their
# own fresh trie (preserves the canonical "scratch space" pattern).  Only
# `bind!` triggers prefix derivation + shared-trie attachment.

const NODE_SHARED = Ref{Union{Space, Nothing}}(nothing)

"""
    get_node_shared() :: Space

Return the process-level shared MORK.Space, lazy-initializing on first
access.  Multi-node concerns (Stage 2) replace this with a per-node
context bound to a specific physical machine.
"""
function get_node_shared()::Space
    NODE_SHARED[] === nothing && (NODE_SHARED[] = new_space())
    NODE_SHARED[]
end

"""
    derive_prefix_from_name(name::Symbol) :: Union{Vector{UInt8}, Nothing}

Derive a byte-prefix from a MeTTa name:
  `:&common`      → `"common:/"`
  `:&app/games`   → `"app/games:/"`
  `:&app/social`  → `"app/social:/"`

Returns `nothing` for names that don't start with `&` (those bind as
regular `(= name val)` atoms, not as space references).

The `:/` suffix is a human-debuggable separator that also guarantees
`prefix_compare(p1, p2) == PREFIX_DISJOINT` for distinct sibling names
(no name is a byte-prefix of another).  E.g. `"app:/"` vs `"app/games:/"`
remain disjoint because the trailing `/` of `"app:/"` differs from the
`/games` continuation.
"""
function derive_prefix_from_name(name::Symbol)::Union{Vector{UInt8}, Nothing}
    s = string(name)
    startswith(s, "&") || return nothing
    Vector{UInt8}(s[2:end] * ":/")
end

# ── _resolve_space — the consumer this registry never had ─────────────────────
#
# 🔴 WHY, AND THE RULE IT SETTLES. `derive_prefix_from_name`, `register_prefix!`, `lookup_prefix` and
# `rebind_to_shared_prefix` were built, exported, and left with ZERO callers; their docstrings named
# `_resolve_space` as the consumer, and that function is 0 across all nine live repos — it survives only
# in the legacy `~/PRIMUS` tree (`PRIMUS_Core/src/interpreter/SpecialForms.jl:535`), left behind by the
# migration while the docstrings outlived it. Both halves built, the seam never closed.
#
# ⇒ RULE: no registry object lands before its consumer. This function IS that consumer, and it is
# deliberately ONE function serving BOTH needs the design note identified:
#   · the prefix registry's missing reader — `&common` becomes reachable by NAME, not hand-built bytes;
#   · the resolver for SYMBOLIC handles — `(SpaceRef &common)`, per "ground the verbs, not the nouns".
#
# ⚠️ HANDLES STAY SYMBOLIC ON PURPOSE. Upstream's `SpaceType` wraps a LIVE object, and stdlib `capture`
# ("wraps an atom and captures the current space") is constructed as `CaptureOp::new(space.clone(), …)`
# — so every captured atom becomes process-local and unserializable. `(SpaceRef id)` is a plain
# expression: matchable, serializable, process-independent. The verbs resolve it; the space never
# becomes an opaque grounded object. Same argument that put `(VecRef h)` in the trie, not the tensor.

"""
    CONTAINMENT_POLICY

How the region registry treats a NESTED prefix — `PREFIX_OF` / `PREFIX_PREFIXED_BY` from
`MORK.prefix_compare`. Byte-prefix regions give containment whether or not you asked for it: if
`&app` and `&app/games` are both registered, a match on `&app` structurally sees `&app/games`'s atoms.

`:flat` (the choice, 2026-08-14) — REJECT a registration that nests with an existing one. Every region
is mutually disjoint, which is exactly the isolation `test_corespace.jl` already proves in both
directions, and a violation fails LOUDLY at registration rather than silently widening a later query.

`:nested` — the alternative, deliberately not taken: it buys free module subtrees, at the cost that
isolation depends on REGISTRATION ORDER. Registering `&app` after `&app/games` would silently change
what a `&app` query returns.

⚠️ Pick-once: retrofitting changes what existing matches return, which is why this is a constant with a
reason attached rather than a keyword argument.

✅ **AND MEASURED 2026-08-14: NAME-DERIVED REGIONS CANNOT NEST, so this policy only governs EXPLICIT
prefixes.** `derive_prefix_from_name` appends `:/`, so `&app` → `"app:/"` and `&app/games` →
`"app/games:/"` diverge at `:` vs `/` — `prefix_compare` returns `PREFIX_SHARING`, not `PREFIX_OF`. The
suffix its docstring justifies as "human-debuggable" is doing load-bearing structural work: it makes the
`&app` / `&app/games` hazard unreachable through the naming path. Nesting can therefore only arrive via
a hand-passed `prefix = …`, which is exactly where `check_prefix_free` still guards.
"""
const CONTAINMENT_POLICY = :flat

"""
    check_prefix_free(name, prefix) -> Nothing

Enforce `CONTAINMENT_POLICY` against everything already in `PREFIX_REGISTRY`. Throws on a nesting or a
name/prefix conflict; a `PREFIX_SHARING` or `PREFIX_DISJOINT` sibling is fine — that IS Figure 4.

Uses `MORK.prefix_compare`, which already returns the full containment lattice
(`EQUALS`/`OF`/`PREFIXED_BY`/`SHARING`/`DISJOINT` + the empty cases) — written on the `server` branch,
so ⚠️ the port-inventory ratchet cannot see it and will show neither coverage nor gaps for it.
"""
function check_prefix_free(name::Symbol, prefix::Vector{UInt8})
    for (other, op) in PREFIX_REGISTRY
        other === name && continue
        rel, _ = prefix_compare(prefix, op)
        if rel === PREFIX_EQUALS
            throw(
                ArgumentError(
                    "region prefix $(String(copy(prefix))) is already registered as :$other — " *
                    "two names for one region would make `(SpaceRef …)` ambiguous")
            )
        elseif CONTAINMENT_POLICY === :flat &&
            (rel === PREFIX_OF || rel === PREFIX_PREFIXED_BY)
            inner, outer = rel === PREFIX_OF ? (name, other) : (other, name)
            throw(
                ArgumentError(
                    "region :$name ($(String(copy(prefix)))) NESTS with :$other ($(String(copy(op)))) — " *
                    "a query on :$outer would structurally include :$inner's atoms. CONTAINMENT_POLICY is " *
                    ":flat, so regions must be mutually disjoint; give them sibling names " *
                    "(`&app/games` + `&app/social`, not `&app` + `&app/games`).")
            )
        end
    end
    nothing
end

"""
    _resolve_space(x) -> Union{CoreSpace, Nothing}

Resolve a space REFERENCE to a live `CoreSpace` on the node-shared trie. `nothing` when the reference
names nothing — callers decide whether that is an error.

Accepts the three forms a caller actually holds:

    _resolve_space(:&common)                  # a registered name
    _resolve_space([:SpaceRef, :&common])     # the symbolic handle, as a plain matchable expression
    _resolve_space(cs::CoreSpace)             # already resolved — identity, so callers need no branch

⚠️ Resolution is BY NAME through `PREFIX_REGISTRY`, so an unregistered name returns `nothing` rather
than silently minting a region. Creating one is `make_space(:mork; mode = Shared, name = …)`, which is
a different act and should look like one.
"""
_resolve_space(cs::CoreSpace) = cs
_resolve_space(::Nothing) = nothing
function _resolve_space(name::Symbol)
    p = lookup_prefix(name)
    p === nothing && return nothing
    new_core_space(get_node_shared(), p)
end
function _resolve_space(x::AbstractVector)
    # (SpaceRef &name) — the symbolic handle. Length 2 with a `SpaceRef` head; anything else is not a
    # handle and resolves to nothing rather than throwing, so `match` over mixed atoms stays cheap.
    (length(x) == 2 && x[1] === :SpaceRef) || return nothing
    _resolve_space(x[2])
end
_resolve_space(::SExprConvertible) = nothing     # typed catch-all: fails CLOSED, never `::Any`

"""
    space_ref(name::Symbol) -> Vector{SExprConvertible}

The symbolic handle for a registered region: `(SpaceRef &common)`. A plain expression — matchable,
serializable, process-independent — never a grounded atom wrapping a live object.
"""
space_ref(name::Symbol) = SExprConvertible[:SpaceRef, name]

"""
    rebind_to_shared_prefix(src::CoreSpace, prefix::Vector{UInt8}) :: CoreSpace

Construct a `(shared, prefix)` CoreSpace, migrating any pre-existing atoms
from `src` into the new prefix region.  This is the C′-mode transformation
applied by `_eval_bind!` when a name is bound to a CoreSpace value.

For the canonical pattern `(bind! &name (new-space))`, `src` is empty and
this is just an allocation.  For pre-populated sources, atoms migrate via
`core_atoms` + `core_add!`.
"""
function rebind_to_shared_prefix(src::CoreSpace, prefix::Vector{UInt8})::CoreSpace
    shared = get_node_shared()
    wrapped = new_core_space(shared, prefix)
    # Migrate atoms from src (typically empty for the (bind! &name (new-space))
    # pattern; non-empty if user pre-populated before binding).
    for atom in core_atoms(src)
        core_add!(wrapped, atom)
    end
    wrapped
end

# ── Concurrency permits — pass-through (CORE-INT-1, audit 2026-06-05) ──────────
# These were once backed by MORK's `StatusMap` (per-prefix read/write permits).
# That was a LAYERING ERROR: upstream keeps `status_map.rs` in the `mork-server`
# crate (used only by server_space.rs/main.rs/commands.rs) — the kernel `Space`
# carries no concurrency coordination, and neither should the Core interpreter
# library.  Concurrent access is a *server-tier* concern:
#   * embedded Core is single-threaded → permits never contend;
#   * served Core (MettaJam) already serializes every eval under one coarse
#     `ReentrantLock`, exactly as MorkServer fronts the substrate with StatusMap.
# So Core no longer imports `StatusMap`/`sm_*` (that import was also the sole
# blocker to bumping Core onto the post-split hardened MORK — CORE-INT-1).
#
# The two wrappers are kept as thin pass-throughs: they preserve the call-site
# seam so a future *concurrent embedding without an external coarse lock* can
# reattach real coordination HERE (or, upstream-faithfully, behind a Core
# server tier) without touching every caller.
with_read_permit(f::Function, ::CoreSpace) = f()
with_write_permit(f::Function, ::CoreSpace) = f()

"""
    enable_sc!(space) → space

Enable Rule-of-64 decomposed execution for all exec atoms in this space.

Grain note: the flag is per-space, not per-rule.  Every exec atom evaluated
against this space goes through `MorkSupercompiler.plan!`.  This is fine for
a space holding a coherent body of rules (a single algorithm's library).
For a space mixing decomposition-safe and decomposition-unsafe rules, the
per-space flag is too coarse — you would need per-exec-atom markers
(extending the byte-trie's `_EXEC_PREFIX` machinery) to express that.
"""
enable_sc!(s::CoreSpace) = (s.use_supercompiler=true; s)

# ── Atom operations ───────────────────────────────────────────────────────────

"""Add an atom to the space. Accepts any Julia value (converted to S-expr).

The atom is stored at byte-path `s.prefix ++ atom_bytes` in the shared trie.
For root-prefixed spaces (`s.prefix == UInt8[]`), this is the original
whole-trie behavior — `space_add_all_sexpr!` is used directly.
For prefixed spaces (Stage 1 multi-space), the atom is parsed once and
stored via byte-level `set_val_at!` with the prefix prepended.
"""
function core_add!(s::CoreSpace, atom::SExprConvertible)
    sexpr = to_sexpr(atom)
    isempty(sexpr) && return nothing
    with_write_permit(s) do
        try
            if isempty(s.prefix)
                # Root prefix: original fast path, preserves multi-atom sexpr parsing.
                space_add_all_sexpr!(s.inner, sexpr)
            else
                # Prefixed: parse to bytes, prepend prefix, set_val_at!.
                # Single-atom semantics — to_sexpr produces one atom per call.
                e = sexpr_to_expr(sexpr)
                set_val_at!(s.inner.btm, vcat(s.prefix, e.buf), UNIT_VAL)
            end
        catch e
            @warn "core_add! failed" atom=sexpr exception=e
        end
        # Per-head cache invalidation: adding (= (head args) body) can only affect
        # lookups for `head` — other heads' cached rules are unchanged.
        # Full flush (empty!) only when the affected head can't be identified.
        if atom isa Vector && length(atom) == 3 && atom[1] === Symbol("=")
            head_expr = atom[2]
            head_sym = if head_expr isa Vector && !isempty(head_expr)
                head_expr[1]
            elseif head_expr isa Symbol
                head_expr
            else
                nothing
            end
            head_sym isa Symbol ? delete!(s.rule_cache, head_sym) : empty!(s.rule_cache)
        end
    end
    nothing
end

"""Remove an atom from the space by its S-expression form.

The atom is looked up at byte-path `s.prefix ++ atom_bytes`; only that
exact path is removed.  For root-prefixed spaces this is unchanged from
the pre-Stage-1 behavior.
"""
function core_remove!(s::CoreSpace, atom::SExprConvertible)
    sexpr = to_sexpr(atom)
    isempty(sexpr) && return nothing
    with_write_permit(s) do
        try
            e = sexpr_to_expr(sexpr)
            remove_val_at!(s.inner.btm, vcat(s.prefix, e.buf))
        catch e
            @warn "core_remove! failed" atom=sexpr exception=e
        end
        empty!(s.rule_cache)   # removing anything could affect rule lookups
    end
    nothing
end

"""
    _is_var_symbol(x) → Bool

Variable check: a dollar-prefixed name or storage form `__var_name`.  Used by the structural
pre-filter to know which positions are wildcards.
"""
_is_var_symbol(x) =
    x isa Symbol && (startswith(string(x), "\$") || startswith(string(x), "__var_"))

"""
    _shape_match(pattern, atom) → Bool

Top-level structural compatibility check (no binding).  Returns true when
`atom` could possibly unify with `pattern`:

  - pattern is a variable → match
  - both are Vectors of same length, with element-wise shape match
  - both are equal scalars → match
  - else → false

This is a cheap pre-filter that lets us reject obviously-incompatible atoms
without paying the cost of `_unify` (which lives in Eval.jl and would create
a circular include).  `_eval_match` still runs full `_unify` on whatever
passes — the filter only narrows the candidate set.
"""
function _shape_match(@nospecialize(pattern), @nospecialize(atom))::Bool
    _is_var_symbol(pattern) && return true
    if pattern isa Vector
        atom isa Vector || return false
        length(pattern) == length(atom) || return false
        for i in eachindex(pattern)
            _shape_match(pattern[i], atom[i]) || return false
        end
        return true
    end
    pattern == atom
end

"""
    _walk_atoms(s::CoreSpace) → Iterator-like callback path

Internal: walk every stored value under `s.prefix` and invoke `f(atom)` for
each.  Uses `space_dump_all_sexpr` (whole-trie text dump) for root-prefix —
matches `core_atoms`'s fast path.  For prefixed spaces, walks the subtrie
via `read_zipper_at_path` + `zipper_to_next_val!` and serializes each
relative-to-anchor path through `expr_serialize`.

Why we walk instead of `space_query_multi` — ⚠️ CORRECTED 2026-07-29, the original reason
here was WRONG and it steered work away from the right primitive.

The claim was: "`space_query_multi` short-circuits arity-1 patterns (`(, single)`)
and returns the pattern itself without iterating, so any single-pattern match
finds nothing."  Measured, that is false.  The short-circuit at
`MORK/src/kernel/Space.jl:370` fires on `n_factors == 1`, and `n_factors` is
the TOP-LEVEL arity — `(, P)` encodes as `[Arity(2)][,][P]`, i.e. **arity 2**,
so it does NOT short-circuit and DOES iterate the trie correctly:

    (, (likes \$who pizza))   -> 2 matches, correct atoms
    (, (= (dbl \$x) \$rhs))    -> 1 match, exactly that rule
    (likes \$who pizza)       -> 0   <- UNWRAPPED: arity 3, read as a THREE-FACTOR
                                       conjunction (likes ⋈ \$who ⋈ pizza)
    (foo)                    -> short-circuits (genuine arity 1)

So what broke `(match &self pat tpl)` was passing the pattern **without the
`(, …)` wrapper**, not an arity-1 short-circuit.  `PatternMiner.jl` wraps and
gets correct counts from the same primitive.

The walk is retained because it is the canonical "enumerate ALL atoms" path
(mirroring `space_dump_all_sexpr`) and `core_match` returns candidates for a
Julia-side `_unify`.  But it is O(N) where an indexed descent is available.

✅ **TAKEN 2026-08-14** (`core_match_bind`, below): the comma-wrapped route is
no longer a proposal.  `core_match_bind` calls `space_query_multi_at` with a
`(, …)`-wrapped pattern and returns BINDINGS.  The arity facts above were
re-measured that day and hold — `(, P)` encodes as `ExprArity(0x02)`, so the
`n_factors == 1` short-circuit is avoided; unwrapped `(belief \$k \$v)` is arity
3 and yields 0.  `core_match` itself still takes this walk; only the binding
entry point is indexed.
"""
function _walk_atoms(f::Function, s::CoreSpace)
    if isempty(s.prefix)
        for line in split(space_dump_all_sexpr(s.inner), '\n')
            ls = strip(line)
            isempty(ls) && continue
            # CORE-2 fix (audit 2026-06-05): guard ONLY the parse, not the callback. The old
            # bare `catch; end` swallowed both malformed-atom parse failures AND bugs in the
            # user's `f`, silently dropping atoms from match/enumerate results (SP-1 class).
            local atom
            try
                atom = from_sexpr(ls)
            catch err
                @warn "CoreSpace _walk_atoms: skipping unparseable atom" line=ls exception=err maxlog=5
                continue
            end
            f(atom)
        end
    else
        rz = read_zipper_at_path(s.inner.btm, s.prefix)
        while zipper_to_next_val!(rz)
            rel_bytes = collect(zipper_path(rz))
            local atom
            try
                atom = from_sexpr(strip(expr_serialize(rel_bytes)))
            catch err
                @warn "CoreSpace _walk_atoms: skipping unparseable atom (prefixed)" exception=err maxlog=5
                continue
            end
            f(atom)
        end
    end
end

"""
    core_match(s, pattern) → Vector{SExprConvertible}

Query the trie for atoms matching `pattern`. Dollar-prefixed variables act as wildcards.
Returns a list of CANDIDATE atoms — callers (typically `_eval_match`) apply
`_unify` for the final binding-correct filter.

The query is scoped to `s.prefix` — only atoms stored under the space's byte
prefix participate.

Implementation note: walks the trie via `_walk_atoms` + `_shape_match`
structural pre-filter rather than `space_query_multi`'s arity-1 fast-path,
which returns the pattern itself without iterating (see `_walk_atoms`
docstring).  Cost is O(N) in trie size with a cheap shape rejection.

⚠️ **UPDATED 2026-08-14 — "a future optimization" is no longer accurate.**
`core_match_bind` (above) now runs the indexed `space_query_multi_at` descent
and returns bindings; this function was left on the walk deliberately, because
36 call sites and the conformance corpus depend on its `Vector{SExprConvertible}`
return.  So the choice here is COMPATIBILITY, not a missing primitive.  Prefer
`core_match_bind` for new callers, and for anything that needs a witness — this
one cannot give you one, by construction (`_shape_match` returns a `Bool`).
"""
# ── Prefix-narrowed query ─────────────────────────────────────────────────────
# A stored atom's trie path is [ExprArity(n)][ExprSymbol item]… — exactly the
# encoding core_add!/sexpr_to_expr produce.  When a pattern has a concrete
# functor PLUS one or more concrete leading args (variables only later), those
# leading items form a genuine byte-prefix of every atom that could match it.
# Descending the trie to that prefix and walking only the resulting subtrie
# turns the O(N) full scan into O(subtrie).  This is what makes a by-key query
# (e.g. reverse-keyed `(in <post> $pre $cnt)`) cheap at connectome scale.
# Patterns that start with a variable, or pin only the functor (e.g.
# `(syn $r $p $c)` — every atom is `syn`), yield `nothing` → full-walk fallback.

_concrete_token(el::Integer) = string(el)
_concrete_token(el::AbstractFloat) = string(el)
function _concrete_token(el::Symbol)
    str = string(el)
    (startswith(str, "\$") || startswith(str, "__var_")) ? nothing : str
end
# Typed catch-all: String / Bool / Tuple / nested Vector -> not a pinnable token. NOT `::Any`, which
# fails OPEN (silently accepts any type); this fails CLOSED — an element outside the store's declared
# union is a MethodError at the boundary rather than a silent `nothing` that degrades to a full scan.
_concrete_token(::SExprConvertible) = nothing

# Emit the constant byte-prefix of `el` into `bytes`, mirroring MORK's structural pre-order
# encoding (arity byte; symbol = size byte + token bytes; nested expr = arity byte + children).
# Returns (pinned_count, stopped): stopped=true means a variable / non-concrete element was
# hit, so NO further sibling may be pinned — a trie prefix must be contiguous, and everything
# after the first variable is non-constant.  Recursing into nested exprs is what lets a RULE
# pattern `(= (f a) $body)` narrow on its nested head `f` (measured: O(N)→O(1), commit that
# added benchmark/store_match_scaling.jl); the previous flat-only walk pinned just `=` and
# full-scanned, because a nested head is not a `_concrete_token`.  Mirrors `_const_prefix`
# (MORK Space.jl) — same walk, on the Julia Vector form instead of MORK.Expr bytes.
function _emit_prefix!(bytes::Vector{UInt8}, el)::Tuple{Int, Bool}
    if el isa Vector && !isempty(el)
        push!(bytes, item_byte(ExprArity(UInt8(length(el)))))
        n = 0
        for child in el
            c, stopped = _emit_prefix!(bytes, child)
            n += c
            stopped && return (n, true)      # variable inside the nested expr → prefix ends here
        end
        return (n, false)
    end
    tok = _concrete_token(el)
    tok === nothing && return (0, true)      # variable / other → stop
    tb = Vector{UInt8}(tok)
    length(tb) > 63 && return (0, true)      # multi-byte symbol size — stop pinning here
    push!(bytes, item_byte(ExprSymbol(UInt8(length(tb)))))
    append!(bytes, tb)
    (1, false)
end

function _pattern_prefix_bytes(pattern)
    (pattern isa Vector && length(pattern) >= 2) || return nothing
    bytes = UInt8[item_byte(ExprArity(UInt8(length(pattern))))]
    pinned = 0
    for el in pattern
        n, stopped = _emit_prefix!(bytes, el)
        pinned += n
        stopped && break
    end
    # Worth narrowing only if at least one ARG-side symbol beyond the functor is pinned.
    pinned >= 2 ? bytes : nothing
end

function _walk_atoms_narrowed(f::Function, s::CoreSpace, prefix_bytes::Vector{UInt8})
    rz = read_zipper_at_path(s.inner.btm, vcat(s.prefix, prefix_bytes))
    while zipper_to_next_val!(rz)
        full = vcat(prefix_bytes, collect(zipper_path(rz)))   # full atom bytes (no region prefix)
        # CORE-2 fix (audit 2026-06-05): guard ONLY the parse, let callback errors propagate.
        local atom
        try
            atom = from_sexpr(strip(expr_serialize(full)))
        catch err
            @warn "CoreSpace _walk_atoms_narrowed: skipping unparseable atom" exception=err maxlog=5
            continue
        end
        f(atom)
    end
end

# ── core_match_bind — the BINDING seam (space design §2) ──────────────────────────────────────────────
#
# 🔴 WHY THIS EXISTS. `core_match` FILTERS: `_shape_match` returns a Bool and accepts a variable position
# without capturing it, so this store could answer "does anything match?" but never "what did $k match?".
# That made `(match &S (belief $k $s $c) $k)` unservable from the trie — and it is the slice's blocker,
# because Λ (the query-Core step) retrieves cases and rules and carries their CONTENTS forward, over an
# `S_rule` that is MORK-backed for scale. A store that declines to bind cannot host it.
#
# The capability was never missing from the substrate — only from this API. `space_query_multi_at`
# performs the INDEXED descent and hands back the matched location; this routes to it.
#
# ⚠️ THE `(, …)` WRAPPER IS MANDATORY, NOT STYLISTIC. `space_query_multi*` short-circuits `n_factors == 1`
# by calling `effect(Dict(), pat_expr.buf)` — echoing the PATTERN with EMPTY bindings (Space.jl:634-637).
# An unwrapped `(belief $k $v)` is arity 3, read as a three-factor conjunction, and yields 0. Wrapped, it
# is `ExprArity(0x02)` and queries correctly. MEASURED, not assumed.
#
# 🔴 AND BINDINGS ARE TAKEN FROM `loc`, NOT FROM THE `ExprEnv` DICT — this is the non-obvious part, and
# reading the dict naively produces SILENTLY WRONG VALUES. Measured on `(belief $k $v)` over
# `(belief a 9)`: the dict is keyed `(0x00,0x00)`/`(0x00,0x01)` (source id, var index — MORK's encoding
# drops variable NAMES, they are de Bruijn), and each `ExprEnv` is a CURSOR: `base.buf[offset+1:end]` is
# the whole REMAINING TAIL, so `$k` decodes as `"a 9"` rather than `"a"`. Extracting one item needs span
# arithmetic over the tail. `loc` already carries the exact matched atom `(belief a 9)`, so walking the
# pattern against it is correct by construction and needs no span logic.
#
# ⚠️ SCOPE: single-pattern queries. Multi-factor conjunction is NOT exposed here, and `conjunction`
# stays `false` in the ledger until it is.
#
# 🔴 BUT THE REASON GIVEN HERE WAS WRONG, AND IT COST AN OVERESTIMATE. This comment used to read: "a
# genuine multi-factor conjunction binds ACROSS factors, where `loc` is one location and the
# `ExprEnv` dict is the real answer — that path needs the span arithmetic above". That is a plausible
# mental model and it is not what the code does. CORRECTED 2026-08-27 by reading the kernel:
#
#     MORK/src/kernel/Space.jl:840   combined = collect(pzg_origin_path(loc))
#     MORK/src/kernel/Space.jl:877   return effect(trie_bindings, combined)
#
# `pzg_origin_path` is the ProductZipperG's ORIGIN PATH, which for an N-factor product is the
# CONCATENATION of all N matched factor paths. So the effect callback ALREADY RECEIVES EVERY MATCHED
# ATOM — the `ExprEnv` dict is not needed, and neither is the cursor-tail span arithmetic this
# comment warned about (that warning is still correct ABOUT THE DICT; it is simply not on this path).
# CODEMAP:169 corroborates for the fast lanes: `_trie_join_emit!` "reconstructs combined path, SAME
# value-gate / `_expr_unify_inplace!` / effect contract".
#
# ⇒ WHAT A MULTI-PATTERN `core_match_bind` ACTUALLY NEEDS: accept a Vector, wrap `(, p1 p2 … pn)`,
# SPLIT `combined` into n successive expressions (prefix-free encoding ⇒ span-walking, the same
# `expr_span` split `_binary_join_emit!` already does), and run `_bind_walk!` per factor into ONE
# dict — cross-factor consistency then falls out of the repeat-must-agree check at :845-847.
#
# ⚠️ STILL UNVERIFIED, AND IT IS THE PART THAT COULD SINK IT: whether the trie-join FAST PATHS hand
# the effect a `combined` with the SAME LAYOUT as ProductZipper's. "Byte-identical RESULT SET" (which
# is what CODEMAP claims) is NOT that claim — the result set is what the effect EMITS; `combined` is
# what it RECEIVES. A fast path could order or merge factors differently and still emit identically.
# If the layouts differ, the split must be lane-aware, which is materially more work. Check by
# comparing the `combined` BYTES with the fast paths on and off, not the answers.
#
# ⇒ WHY THIS DISAGREED WITH THE LEDGER. `space/Spaces.jl`'s `_CAPS_MORK` calls exposing conjunction "a
# CORE-SIDE SIGNATURE CHANGE ... NOT blocked on upstream". The ledger was reasoning about the kernel
# primitive; this comment was reasoning about the dict. Both were describing real things and neither
# was describing the same mechanism, which is how one document read "afternoon" and the other read
# "not attempted". The kernel is the arbiter.

# Bind `pattern`'s variables against a concrete `atom`, structurally. Returns false on shape mismatch or
# on an INCONSISTENT repeat (`(link $x $x)` must not match `(link a b)`) — the non-linear case a
# positional walk gets wrong if it just overwrites.
function _bind_walk!(b::Dict{Symbol, SExprConvertible}, pattern, atom)::Bool
    if pattern isa Vector
        atom isa Vector && length(atom) == length(pattern) || return false
        for (p, a) in zip(pattern, atom)
            _bind_walk!(b, p, a) || return false
        end
        return true
    end
    if pattern isa Symbol
        ps = string(pattern)
        if startswith(ps, "\$") || startswith(ps, "__var_")
            prev = get(b, pattern, nothing)
            prev === nothing && (b[pattern]=atom; return true)
            return prev == atom                      # repeated var must agree
        end
    end
    pattern == atom
end

"""
    core_match_bind(s, pattern) → Vector{Dict{Symbol, SExprConvertible}}

Query the trie and return VARIABLE BINDINGS, one dict per match, keyed by the pattern's own variable
symbols (`:\$k`), values being the matched sub-atoms.

This is `core_match`'s binding counterpart and the operation Λ needs. Scoped to `s.prefix` like every
other region op — verified: a sibling region's atoms do not appear.

Empty-pattern and non-vector patterns return no matches rather than erroring, matching `core_match`'s
tolerance at the same boundary.
"""
core_match_bind(::CoreSpace, ::Nothing) = Dict{Symbol, SExprConvertible}[]
function core_match_bind(
    s::CoreSpace, pattern::SExprConvertible
)::Vector{Dict{Symbol, SExprConvertible}}
    out = Dict{Symbol, SExprConvertible}[]
    (pattern isa Vector && !isempty(pattern)) || return out
    pat = try
        sexpr_to_expr("(, $(to_sexpr_query(pattern)))")   # to_sexpr_query keeps `$` vars AS variables;
    catch err                                             # plain to_sexpr maps them to ground __var_ names
        @warn "core_match_bind: unencodable pattern" pattern exception=err maxlog=5
        return out
    end
    with_read_permit(s) do
        space_query_multi_at(
            s.inner.btm,
            s.prefix,
            pat,
            UInt8(0),
            function (_bindings, loc)
                local atom
                try
                    atom = from_sexpr(strip(expr_serialize(loc)))
                catch err
                    @warn "core_match_bind: skipping unparseable match" exception=err maxlog=5
                    return true
                end
                b = Dict{Symbol, SExprConvertible}()
                _bind_walk!(b, pattern, atom) && push!(out, b)
                true
            end
        )
    end
    out
end

core_match(::CoreSpace, ::Nothing) = SExprConvertible[]   # explicit, was an `=== nothing` guard under `::Any`
function core_match(s::CoreSpace, pattern::SExprConvertible)::Vector{SExprConvertible}
    results = SExprConvertible[]
    prefix = _pattern_prefix_bytes(pattern)
    with_read_permit(s) do
        if prefix === nothing
            _walk_atoms(s) do atom               # full scan — no concrete prefix to pin
                _shape_match(pattern, atom) && push!(results, atom)
            end
        else
            _walk_atoms_narrowed(s, prefix) do atom   # O(subtrie) — descend to the pinned prefix
                _shape_match(pattern, atom) && push!(results, atom)
            end
        end
    end
    results
end

"""
    core_rules(s, head_sym) → Vector{Tuple{Vector{SExprConvertible}, SExprConvertible}}

Scan the trie for `(= (head_sym args...) body)` rule atoms.
Returns list of (head_args, body) tuples.

Scoped to `s.prefix` like `core_match` — only rules stored under this space's
prefix region are returned.  Result is cached per-head; cache invalidated
by `core_add!`/`core_remove!`.

Implementation note: same trie-walk + Julia-side filter as `core_match`
(MORK's arity-1 fast-path returns the pattern itself, which would never
match real rules).  The narrow shape filter `atom[1] === :(=) && atom[2][1]
=== head_sym` rejects ~99% of stdlib atoms without allocation.
"""
function core_rules(
    s::CoreSpace, head_sym::Symbol
)::Vector{Tuple{Vector{SExprConvertible}, SExprConvertible}}
    cached = get(s.rule_cache, head_sym, nothing)
    cached !== nothing && return cached

    rules = Tuple{Vector{SExprConvertible}, SExprConvertible}[]
    with_read_permit(s) do
        _walk_atoms(s) do atom
            # Stay inside the length-3 gate — preserves inertness of malformed
            # `=` atoms (arity 0/1/4+) which must not become rules under any
            # rewriter shape (current first-match or future fan-out).
            atom isa Vector && length(atom) == 3 && atom[1] === :(=) || return nothing
            head_part = atom[2]
            body = atom[3]
            # Two LHS shapes both inside the length-3 gate:
            #   expression-LHS:  (= (head args...) body)  → params = args
            #   symbol-LHS:      (= head body)            → params = []
            # The symbol-LHS branch covers named constants like (= Nil ())
            # and (= pi 3.14159) — previously dead code per audit section E.
            if head_part isa Vector && !isempty(head_part) && head_part[1] === head_sym
                push!(rules, (head_part[2:end], body))
            elseif head_part isa Symbol && head_part === head_sym
                push!(rules, (SExprConvertible[], body))
            end
        end
    end
    s.rule_cache[head_sym] = rules
    rules
end

"""Return all atoms in the space as Julia values.

Scoped to `s.prefix`:
- Empty prefix → original fast-path via `space_dump_all_sexpr` (whole trie)
- Non-empty prefix → walk the subtrie anchored at `s.prefix` via a read
  zipper; `zipper_path(rz)` returns paths RELATIVE to the anchor so they
  are the bare atom expression bytes (no manual prefix stripping needed).
"""
function core_atoms(s::CoreSpace)::Vector{SExprConvertible}
    if isempty(s.prefix)
        return [
            from_sexpr(strip(line))
            for line in split(space_dump_all_sexpr(s.inner), '\n')
            if !isempty(strip(line))
        ]
    end
    # Prefix-scoped: walk subtrie under s.prefix, serialize each value's
    # relative-to-anchor path.  Mirrors the cmd_copy pattern in MORK Commands.jl.
    # Acquired under read permit so concurrent writers in the same prefix
    # serialize properly.
    results = SExprConvertible[]
    with_read_permit(s) do
        rz = read_zipper_at_path(s.inner.btm, s.prefix)
        while zipper_to_next_val!(rz)
            rel_bytes = collect(zipper_path(rz))
            try
                str = expr_serialize(rel_bytes)
                push!(results, from_sexpr(strip(str)))
            catch e
                @warn "core_atoms: failed to deserialize atom in prefix region" exception=e
            end
        end
    end
    results
end

"""Forward MORK exec-atom calculus (runs MM2 exec atoms).

For empty `s.prefix` (the only state achievable through `bind!` in Stage 1's
shipped C-mode), this is `space_metta_calculus!` against the whole trie.

For non-empty `s.prefix` (Stage 2+ shared-trie multi-space — currently
unreachable from MeTTa-level `bind!`), this errors loudly so the missing
upstream primitive surfaces rather than silently no-op'ing.  The fix path
is to land `space_metta_calculus_in_prefix!` in `sivaji1012/MORK` and
restore the prefix-scoped call here.
"""
function core_calculus!(s::CoreSpace, steps::Int=typemax(Int))
    n = 0
    with_write_permit(s) do
        if isempty(s.prefix)
            n = space_metta_calculus!(s.inner, steps)
        else
            error(
                "core_calculus! on prefixed CoreSpace requires space_metta_calculus_in_prefix! in upstream MORK — Stage 2 work"
            )
        end
    end
    n
end

"""Like `core_calculus!` but anchored at an explicit thread-id `loc`
(an `AbstractString`).  Uses MORK's the exec loc-scoping form thread-scoping
convention for finer-grained execution.

For root-prefix spaces, this is the pre-Stage-1 behavior unchanged.
For prefixed spaces, see `core_calculus!`'s note on the missing upstream
primitive.
"""
core_calculus_at!(s::CoreSpace, loc::AbstractString, steps::Int=typemax(Int)) =
    if isempty(s.prefix)
        space_metta_calculus_at!(s.inner, loc, steps)
    else
        error(
            "core_calculus_at! on prefixed CoreSpace requires upstream MORK Stage 2 primitives"
        )
    end

"""
    core_match_bind_multi(s, patterns) → Vector{Dict{Symbol, SExprConvertible}}

Multi-factor conjunctive query with BINDINGS: match `patterns` jointly against the trie and return
one dict per solution, with variables shared ACROSS factors.

⚠️ WHY NOT A `core_match_bind` METHOD. A single pattern IS a `Vector` (`(belief \$k \$v)` is
`[:belief, :\$k, :\$v]`), so dispatching on `Vector` cannot distinguish one pattern from a list of
them — it would silently read one pattern's elements as three factors and return nothing. A separate
name fails loudly instead of quietly.

HOW IT WORKS, and every step of this was verified against the kernel rather than assumed:
`space_query_multi_at` hands the effect `combined = pzg_origin_path(loc)`
(`MORK/src/kernel/Space.jl:840`), which for an N-factor product is the CONCATENATION of all N matched
atoms — not one location. So the bindings need no `ExprEnv` cursor arithmetic: split `combined` with
`expr_span` (the encoding is prefix-free, so each call yields exactly one factor) and run the same
`_bind_walk!` the single-factor path uses, accumulating into ONE dict. Cross-factor consistency then
falls out of `_bind_walk!`'s repeat-must-agree check (:845-847) — a variable bound by factor 1 must
agree when factor 2 binds it, or the whole solution is rejected.

⚠️ RESULT SET, NOT SEQUENCE. Callback ORDER is lane-dependent: with the trie-join fast paths on, P5's
cardinality-greedy reorder (`_CARD_REORDER_ENABLED`) visits factors smallest-first, so solutions
arrive in a different order than under the plain ProductZipper. MEASURED on
`(, (edge \$x \$y) (edge \$y \$z))` over `(edge a b) (edge b c) (edge c d)`: identical multisets,
different sequence. Callers and tests must compare SETS. Pinning an order passes with the fast paths
off and fails with them on.

Layout, by contrast, is lane-INDEPENDENT — verified by comparing the `combined` bytes the effect
receives with `_TRIE_JOIN_ENABLED` on and off, not the answers it emits. That distinction matters:
"byte-identical result set" is a claim about what is EMITTED, and the split depends on what is
RECEIVED.
"""
function core_match_bind_multi(
    s::CoreSpace, patterns::AbstractVector
)::Vector{Dict{Symbol, SExprConvertible}}
    out = Dict{Symbol, SExprConvertible}[]
    isempty(patterns) && return out
    all(p -> p isa Vector && !isempty(p), patterns) || return out
    n = length(patterns)
    pat = try
        sexpr_to_expr("(, " * join((to_sexpr_query(p) for p in patterns), " ") * ")")
    catch err
        @warn "core_match_bind_multi: unencodable patterns" patterns exception=err maxlog=5
        return out
    end
    with_read_permit(s) do
        space_query_multi_at(
            s.inner.btm,
            s.prefix,
            pat,
            UInt8(0),
            function (_bindings, loc)
                e = loc isa MORK.Expr ? loc : MORK.Expr(Vector{UInt8}(loc))
                b = Dict{Symbol, SExprConvertible}()
                i = 1
                for k in 1:n
                    i <= length(e.buf) || return true       # combined shorter than n factors — skip
                    sp = expr_span(e, i)
                    atom = try
                        from_sexpr(strip(expr_serialize(collect(sp))))
                    catch err
                        @warn "core_match_bind_multi: unparseable factor" k exception=err maxlog=5
                        return true
                    end
                    # ONE dict across all factors ⇒ a shared variable must agree, or reject.
                    _bind_walk!(b, patterns[k], atom) || return true
                    i += length(sp)
                end
                push!(out, b)
                true
            end
        )
    end
    out
end
