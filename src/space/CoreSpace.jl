"""
CoreSpace — MORK.Space-backed atom space.

Every atom is stored as a byte-path in a MORK PathMap trie.
S-expression strings are the interchange format between Julia and MORK.
"""

# ── Atom ↔ S-expression conversion ───────────────────────────────────────────

"""
Convert any Julia value to a MORK-compatible S-expression string.

Variables (Symbol starting with '\$') are encoded as ground symbols `__var_NAME`
so they survive the MORK byte-trie round-trip. MORK's native \$x syntax
anonymises variable names (de Bruijn); __var_x preserves them.

For query patterns, call `to_sexpr_query` which uses \$x directly.
"""
function to_sexpr(x::Any) :: String
    if x isa Symbol
        s = string(x)
        startswith(s, "\$") && return "__var_" * s[2:end]
        return s
    end
    x isa String  && return x   # passthrough: String input is treated as raw S-expr by core_add!/core_remove!
    x isa Bool    && return x ? "True" : "False"   # must precede Number (Bool <: Integer)
    x isa Number  && return string(x)
    x isa Tuple   && return "($(join(to_sexpr.(x), " ")))"   # Tuple same as Vector
    x isa Vector  && return "($(join(to_sexpr.(x), " ")))"
    string(x)
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
function to_sexpr_atom(x::Any) :: String
    x isa String && return "\"" * escape_string(x) * "\""
    to_sexpr(x)
end

"""
Convert a pattern to S-expression, keeping \$x as MORK wildcards.
Use for `core_match` queries — do NOT use for storage (variable names lost).
"""
function to_sexpr_query(x::Any) :: String
    if x isa Symbol
        s = string(x)
        # __var_x is the storage form of $x — convert back so MORK treats it as wildcard
        startswith(s, "__var_") && return "\$" * s[7:end]
        return s   # $x stays as-is — MORK parses it as a wildcard variable
    end
    x isa String  && return x   # passthrough — query patterns may contain raw S-expr fragments
    x isa Bool    && return x ? "True" : "False"   # must precede Number (Bool <: Integer)
    x isa Number  && return string(x)
    x isa Vector  && return "($(join(to_sexpr_query.(x), " ")))"
    string(x)
end

"""Parse a MORK S-expression string into a Julia value."""
from_sexpr(s::AbstractString) :: Any = from_sexpr(String(s))
function from_sexpr(s::String) :: Any
    s = strip(s)
    isempty(s) && return nothing
    s == "True"  && return true
    s == "False" && return false

    # String literal — preserves type tag from to_sexpr round-trip
    if startswith(s, "\"") && endswith(s, "\"") && length(s) >= 2
        return unescape_string(s[2:end-1])
    end

    n = tryparse(Int, s);     n !== nothing && return n
    n = tryparse(Float64, s); n !== nothing && return n

    # MORK variable encoding: __var_NAME → Symbol("$NAME")
    startswith(s, "__var_") && return Symbol("\$" * s[7:end])
    # Legacy $x form (from MORK parser)
    startswith(s, "\$") && return Symbol(s)

    if startswith(s, "(") && endswith(s, ")")
        inner  = s[2:end-1]
        tokens = _tokenise(inner)
        isempty(tokens) && return []
        return Any[from_sexpr(t) for t in tokens]
    end

    Symbol(s)
end

export _tokenise
_tokenise(s::AbstractString) = _tokenise(String(s))
function _tokenise(s::String) :: Vector{String}
    tokens = String[]; depth = 0; start = 1; i = 1
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
            if depth == 0; push!(tokens, strip(s[start:i])); start = i + 1; end
        elseif isspace(c) && depth == 0
            tok = strip(s[start:i-1])
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
    inner            :: Space
    prefix           :: Vector{UInt8}
    rule_cache       :: Dict{Symbol, Vector{Tuple{Vector{Any}, Any}}}
    named_spaces     :: Dict{Symbol, CoreSpace}
    use_supercompiler :: Bool
end

"""
    new_core_space() :: CoreSpace

Create a CoreSpace with its own fresh shared trie and empty prefix (= root).
Backward-compatible — every existing caller gets an isolated atomspace.

For shared-trie semantics (multi-space on one node), use
`new_core_space(shared::Space, prefix::Vector{UInt8})` or
`register_prefix!(name, prefix)` to materialize via `_resolve_space`.
"""
new_core_space() = CoreSpace(new_space(),
    UInt8[],
    Dict{Symbol, Vector{Tuple{Vector{Any}, Any}}}(),
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
              Dict{Symbol, Vector{Tuple{Vector{Any}, Any}}}(),
              Dict{Symbol, CoreSpace}(),
              false)

# ── Node-level prefix registry ────────────────────────────────────────────────
# Stage 1: process-level Symbol → byte-prefix mapping.  Used by Eval.jl's
# `_resolve_space` to materialize named spaces like `&common`, `&app/games`
# as `(shared, prefix)` CoreSpaces.
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
function get_node_shared() :: Space
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
function derive_prefix_from_name(name::Symbol) :: Union{Vector{UInt8}, Nothing}
    s = string(name)
    startswith(s, "&") || return nothing
    Vector{UInt8}(s[2:end] * ":/")
end

"""
    rebind_to_shared_prefix(src::CoreSpace, prefix::Vector{UInt8}) :: CoreSpace

Construct a `(shared, prefix)` CoreSpace, migrating any pre-existing atoms
from `src` into the new prefix region.  This is the C′-mode transformation
applied by `_eval_bind!` when a name is bound to a CoreSpace value.

For the canonical pattern `(bind! &name (new-space))`, `src` is empty and
this is just an allocation.  For pre-populated sources, atoms migrate via
`core_atoms` + `core_add!`.
"""
function rebind_to_shared_prefix(src::CoreSpace, prefix::Vector{UInt8}) :: CoreSpace
    shared  = get_node_shared()
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
with_read_permit(f::Function, ::CoreSpace)  = f()
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
enable_sc!(s::CoreSpace) = (s.use_supercompiler = true; s)

# ── Atom operations ───────────────────────────────────────────────────────────

"""Add an atom to the space. Accepts any Julia value (converted to S-expr).

The atom is stored at byte-path `s.prefix ++ atom_bytes` in the shared trie.
For root-prefixed spaces (`s.prefix == UInt8[]`), this is the original
whole-trie behavior — `space_add_all_sexpr!` is used directly.
For prefixed spaces (Stage 1 multi-space), the atom is parsed once and
stored via byte-level `set_val_at!` with the prefix prepended.
"""
function core_add!(s::CoreSpace, atom::Any)
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
        catch e; @warn "core_add! failed" atom=sexpr exception=e; end
        # Per-head cache invalidation: adding (= (head args) body) can only affect
        # lookups for `head` — other heads' cached rules are unchanged.
        # Full flush (empty!) only when the affected head can't be identified.
        if atom isa Vector && length(atom) == 3 && atom[1] === Symbol("=")
            head_expr = atom[2]
            head_sym  = head_expr isa Vector && !isempty(head_expr) ? head_expr[1] :
                        head_expr isa Symbol ? head_expr : nothing
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
function core_remove!(s::CoreSpace, atom::Any)
    sexpr = to_sexpr(atom)
    isempty(sexpr) && return nothing
    with_write_permit(s) do
        try
            e = sexpr_to_expr(sexpr)
            remove_val_at!(s.inner.btm, vcat(s.prefix, e.buf))
        catch e; @warn "core_remove! failed" atom=sexpr exception=e; end
        empty!(s.rule_cache)   # removing anything could affect rule lookups
    end
    nothing
end

"""
    _is_var_symbol(x) → Bool

Variable check: `\$name` or storage form `__var_name`.  Used by the structural
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
function _shape_match(@nospecialize(pattern), @nospecialize(atom)) :: Bool
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

Why we walk instead of `space_query_multi`: MORK's `space_query_multi` short-
circuits arity-1 patterns (`(, single)`) and returns the pattern itself
without iterating the trie.  Any single-pattern match would therefore find
nothing — which broke `(match &self pat tpl)` until this rewrite.  The
read-zipper walk is the canonical "enumerate atoms" path (mirroring
`space_dump_all_sexpr`); callers do structural filtering in Julia.
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
    core_match(s, pattern) → Vector{Any}

Query the trie for atoms matching `pattern`. Dollar-prefixed variables act as wildcards.
Returns a list of CANDIDATE atoms — callers (typically `_eval_match`) apply
`_unify` for the final binding-correct filter.

The query is scoped to `s.prefix` — only atoms stored under the space's byte
prefix participate.

Implementation note: walks the trie via `_walk_atoms` + `_shape_match`
structural pre-filter rather than `space_query_multi`'s arity-1 fast-path,
which returns the pattern itself without iterating (see `_walk_atoms`
docstring).  Cost is O(N) in trie size with a cheap shape rejection — the
proper structural-trie-matching primitive in MORK is a future optimization.
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

_concrete_token(el::Integer)       = string(el)
_concrete_token(el::AbstractFloat) = string(el)
function _concrete_token(el::Symbol)
    str = string(el)
    (startswith(str, "\$") || startswith(str, "__var_")) ? nothing : str
end
_concrete_token(::Any) = nothing   # nested expr / variable / other → stop pinning

function _pattern_prefix_bytes(pattern)
    (pattern isa Vector && length(pattern) >= 2) || return nothing
    bytes  = UInt8[item_byte(ExprArity(UInt8(length(pattern))))]
    pinned = 0
    for el in pattern
        tok = _concrete_token(el)
        tok === nothing && break
        tb = Vector{UInt8}(tok)
        length(tb) > 63 && break          # multi-byte symbol size — stop pinning here
        push!(bytes, item_byte(ExprSymbol(UInt8(length(tb)))))
        append!(bytes, tb)
        pinned += 1
    end
    # Worth narrowing only if at least one ARG beyond the functor is pinned.
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

function core_match(s::CoreSpace, pattern::Any) :: Vector{Any}
    pattern === nothing && return Any[]
    results = Any[]
    prefix  = _pattern_prefix_bytes(pattern)
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
    core_rules(s, head_sym) → Vector{Tuple{Vector{Any}, Any}}

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
function core_rules(s::CoreSpace, head_sym::Symbol) :: Vector{Tuple{Vector{Any}, Any}}
    cached = get(s.rule_cache, head_sym, nothing)
    cached !== nothing && return cached

    rules = Tuple{Vector{Any}, Any}[]
    with_read_permit(s) do
        _walk_atoms(s) do atom
            # Stay inside the length-3 gate — preserves inertness of malformed
            # `=` atoms (arity 0/1/4+) which must not become rules under any
            # rewriter shape (current first-match or future fan-out).
            atom isa Vector && length(atom) == 3 && atom[1] === :(=) || return
            head_part = atom[2]
            body      = atom[3]
            # Two LHS shapes both inside the length-3 gate:
            #   expression-LHS:  (= (head args...) body)  → params = args
            #   symbol-LHS:      (= head body)            → params = []
            # The symbol-LHS branch covers named constants like (= Nil ())
            # and (= pi 3.14159) — previously dead code per audit section E.
            if head_part isa Vector && !isempty(head_part) && head_part[1] === head_sym
                push!(rules, (head_part[2:end], body))
            elseif head_part isa Symbol && head_part === head_sym
                push!(rules, (Any[], body))
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
function core_atoms(s::CoreSpace) :: Vector{Any}
    if isempty(s.prefix)
        return [from_sexpr(strip(line))
                for line in split(space_dump_all_sexpr(s.inner), '\n')
                if !isempty(strip(line))]
    end
    # Prefix-scoped: walk subtrie under s.prefix, serialize each value's
    # relative-to-anchor path.  Mirrors the cmd_copy pattern in MORK Commands.jl.
    # Acquired under read permit so concurrent writers in the same prefix
    # serialize properly.
    results = Any[]
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
function core_calculus!(s::CoreSpace, steps::Int = typemax(Int))
    n = 0
    with_write_permit(s) do
        if isempty(s.prefix)
            n = space_metta_calculus!(s.inner, steps)
        else
            error("core_calculus! on prefixed CoreSpace requires space_metta_calculus_in_prefix! in upstream MORK — Stage 2 work")
        end
    end
    n
end

"""Like `core_calculus!` but anchored at an explicit thread-id `loc`
(an `AbstractString`).  Uses MORK's `(exec (loc \$) \$ \$)` thread-scoping
convention for finer-grained execution.

For root-prefix spaces, this is the pre-Stage-1 behavior unchanged.
For prefixed spaces, see `core_calculus!`'s note on the missing upstream
primitive.
"""
core_calculus_at!(s::CoreSpace, loc::AbstractString, steps::Int = typemax(Int)) =
    if isempty(s.prefix)
        space_metta_calculus_at!(s.inner, loc, steps)
    else
        error("core_calculus_at! on prefixed CoreSpace requires upstream MORK Stage 2 primitives")
    end
