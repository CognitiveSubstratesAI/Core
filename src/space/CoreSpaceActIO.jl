# packages/Core/src/space/CoreSpaceActIO.jl
#
# .act lifecycle wiring for CoreSpace — durability (Stage 1, single-node).
#
# Three responsibilities:
#   1. SAVE a prefix-region of a CoreSpace as a .act file on disk
#   2. LOAD a .act file as an mmap'd read-only source (no RAM copy)
#   3. open_node! / close_node! convenience for clean startup/shutdown
#
# Layer boundary: ALL .act primitives are MORK's (ACTSink, ACTSource,
# act_from_zipper, act_save, act_open_mmap).  This file is pure wiring —
# decides WHEN Core calls them and WHICH prefix to scope to.
#
# Important upstream correctness note (verified against
# packages/MORK/src/kernel/Sinks.jl::sink_finalize!):
#   `act_from_zipper(m, map_val)` takes a PathMap, NOT a ReadZipper.
#   The "direct path" using `read_zipper_at_path(btm, prefix)` followed by
#   `act_from_zipper(rz, ...)` will NOT compile.  The canonical pattern is:
#   1. materialize a fresh PathMap from the prefix region (walk + set_val_at!)
#   2. act_from_zipper(temp_pm, _ -> UInt64(0))
#   3. act_save(tree, filepath)

# ── SAVE ───────────────────────────────────────────────────────────────────────

"""
    snapshot_space_to_act!(s::CoreSpace, name::AbstractString) → Bool

Persist this CoreSpace's atoms (those under `s.prefix`) to `<name>.act`
in `ACT_PATH[]`.

Returns `true` if a file was written, `false` if the space's prefix region
contained no atoms (no `.act` file produced).

The save path materializes a temporary PathMap from the prefix region first
(this is what `act_from_zipper` requires; it takes a PathMap, not a
ReadZipper).  For root-prefix spaces (empty `s.prefix`), this snapshots the
entire trie.

Acquires a read permit on the space's prefix — concurrent writes in the
same prefix region will serialize against this snapshot.
"""
function snapshot_space_to_act!(s::CoreSpace, name::AbstractString)::Bool
    temp_pm = PathMap{UnitVal}()
    n_atoms = 0
    with_read_permit(s) do
        # Walk the space's prefix region.  For root prefix, this iterates the
        # whole trie (still correct — just slower).
        rz = read_zipper_at_path(s.inner.btm, s.prefix)
        while zipper_to_next_val!(rz)
            rel_bytes = collect(zipper_path(rz))
            set_val_at!(temp_pm, rel_bytes, UNIT_VAL)
            n_atoms += 1
        end
    end
    n_atoms == 0 && return false

    # Now temp_pm has just the prefix region's atoms.  Hand to act_from_zipper.
    tree     = act_from_zipper(temp_pm, _ -> UInt64(0))
    filepath = joinpath(ACT_PATH[], String(name) * ".act")
    mkpath(dirname(filepath))
    act_save(tree, filepath)
    true
end

# ── LOAD ───────────────────────────────────────────────────────────────────────

"""
    load_act_source(name::AbstractString) → (ACTSource, mmaps_cache)

Open `<name>.act` from `ACT_PATH[]` as a memory-mapped read-only source.
The atoms are queryable as a factor in the multi-source engine WITHOUT
being copied into any RAM trie — this is the read-mostly shared-knowledge
path.

Returns the source handle and an `mmaps_cache` Dict that must be retained
for the lifetime of the source (dropping it releases the mmap).
"""
function load_act_source(name::AbstractString)
    filepath = joinpath(ACT_PATH[], String(name) * ".act")
    isfile(filepath) || error("load_act_source: $filepath not found")
    # The (ACT <name> $x) source expression routes asource_new → ACTSource.
    src_expr = sexpr_to_expr("(ACT $name \$x)")
    src      = asource_new(src_expr)
    mmaps    = Dict{String, ArenaCompactTree}()
    # Prime the mmap cache so the first real query doesn't pay open cost.
    source_factor(src, PathMap{UnitVal}(), mmaps)
    (src, mmaps)
end

"""
    act_exists(name) → Bool

True iff `<ACT_PATH>/<name>.act` is present on disk.
"""
act_exists(name::AbstractString)::Bool = isfile(joinpath(ACT_PATH[], String(name) * ".act"))

# ── Lifecycle convenience ─────────────────────────────────────────────────────

"""
    set_act_dir!(dir)

Point MORK's `ACT_PATH[]` at `dir` (created if missing).  All `.act`
loads/saves resolve relative to this.  Call once at startup.
"""
function set_act_dir!(dir::AbstractString)
    isdir(dir) || mkpath(dir)
    ACT_PATH[] = String(dir)
    nothing
end

"""
    open_node!(; act_dir, common_name="common") → (ACTSource, mmaps) | nothing

Single-node startup:

 1. Set the `.act` directory
 2. If a saved `<common_name>.act` exists, wire it as an mmap'd read-only source

Returns the source handle (hold for process lifetime) or `nothing` on first
run when no saved KB exists.

Per Stage 1 metagraph philosophy (one unified metagraph; spaces are
subgraph views via prefixes), the common-name convention defaults to
`"common"` for the whitepaper Figure 4 shared-knowledge atomspace.
"""
function open_node!(; act_dir::AbstractString, common_name::AbstractString = "common")
    set_act_dir!(act_dir)
    act_exists(common_name) || return nothing
    load_act_source(common_name)
end

"""
    close_node!(s::CoreSpace; name="common") → Bool

Single-node shutdown: snapshot the space's prefix region to `<name>.act`
so the next run can mmap it.  Returns true if a file was written.

Call at clean shutdown or phase boundary.  For multi-space nodes (Stage 1
shared-trie + per-app prefixes), call once per space whose state should
persist across runs (typically just `&common`).
"""
close_node!(s::CoreSpace; name::AbstractString = "common")::Bool = snapshot_space_to_act!(s, name)

export snapshot_space_to_act!, load_act_source, act_exists, set_act_dir!, open_node!, close_node!
