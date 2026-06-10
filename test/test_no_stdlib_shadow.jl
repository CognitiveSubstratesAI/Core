# test/test_no_stdlib_shadow.jl
#
# Structural lint: no `lib/**/*.metta` definition may shadow a Core-provided name
# (a grounded op registered in src/primitives/, or a stdlib rule in stdlib/*.metta),
# unless it is a deliberate, documented override on the allowlist below.
#
# This closes the duplication class found in the 2026-06-10 primitive audit
# (clamp ×5, MOSES List.* / localized xor·is-member·~=). The reference impls
# (PeTTa host builtins, CeTTa namespaced stdlib, hyperon Rust grounded) don't need
# this lint because their canonical layer is exhaustive; Core does, until its stdlib
# is filled out. See docs/PRIMITIVE_SURFACE_AND_ECOSYSTEM_TOOLING_2026-06-10.md.
using Test

const _LINT_ROOT = normpath(joinpath(@__DIR__, ".."))

# Deliberate, documented overrides allowed to shadow a Core-provided name.
const _SHADOW_ALLOWLIST = Set([
    "trace!",   # PLN stubs trace! to identity (quiet PLN runs) — pln_core_logic.metta.
])

_metta_files(dir) = (fs = String[]; for (r, _, files) in walkdir(dir), f in files
                        endswith(f, ".metta") && push!(fs, joinpath(r, f)); end; fs)

function _heads(files, rx)
    s = Set{String}()
    for f in files, line in eachline(f)
        m = match(rx, line); m === nothing || push!(s, m.captures[1])
    end
    s
end

@testset "lint — no lib/ definition shadows a Core-provided name" begin
    srcfiles    = filter(f -> endswith(f, ".jl"), readdir(joinpath(_LINT_ROOT, "src", "primitives"); join = true))
    stdlibfiles = filter(f -> endswith(f, ".metta"), readdir(joinpath(_LINT_ROOT, "stdlib"); join = true))
    libfiles    = _metta_files(joinpath(_LINT_ROOT, "lib"))

    grounded   = _heads(srcfiles, r"register_grounded!\(\"([^\"]+)\"")
    stdlibdefs = _heads(stdlibfiles, r"^\(=\s+\(([^\s()]+)")
    corenames  = union(grounded, stdlibdefs)

    offenders = Dict{String, Vector{String}}()
    for f in libfiles, line in eachline(f)
        m = match(r"^\(=\s+\(([^\s()]+)", line); m === nothing && continue
        name = m.captures[1]
        (name in corenames && !(name in _SHADOW_ALLOWLIST)) || continue
        push!(get!(offenders, name, String[]), relpath(f, _LINT_ROOT))
    end

    for (n, fs) in offenders
        @warn "lib/ definition shadows a Core-provided name — move it to Core, delegate, or allowlist" name = n files = unique(fs)
    end
    @test isempty(offenders)
end
