# Core health gate — the live Core repo's canonical "is the substrate healthy?" check.
#
# Replaces the obsolete `primus health` (which lived in ~/PRIMUS and ran PRIMUS_Core's
# tests/integration/test_substrate_health.jl — a different, dead substrate, NOT this repo).
#
# Run:   ./bin/health          # fast gate: conformance + lints + types
#        ./bin/health full     # also runs the (slower) ECAN acceptance suite
#
# Exits 0 iff every check passes (N/N), non-zero otherwise — so it can gate a commit/CI step.

using MeTTaCore, Test

const _HROOT = @__DIR__
const _HFULL = ("full" in ARGS) || (get(ENV, "CORE_HEALTH_FULL", "") == "1")

# (name, test file) — each is a self-contained @testset that throws on failure.
const _HCHECKS = Tuple{String,String}[
    ("hyperon conformance (234 directives)", joinpath(_HROOT, "standard", "test_conformance.jl")),
    ("no dangling lib ops",                  joinpath(_HROOT, "test_no_dangling_ops.jl")),
    ("no stdlib shadowing",                  joinpath(_HROOT, "test_no_stdlib_shadow.jl")),
    ("type system",                          joinpath(_HROOT, "test_types.jl")),
]
_HFULL && push!(_HCHECKS, ("ECAN acceptance (13 examples)", joinpath(_HROOT, "ecan", "test_ecan.jl")))

_hresults = Tuple{String,Bool}[]
for (name, path) in _HCHECKS
    @info "── health: $name ──"
    ok = try
        include(path)
        true
    catch e
        @warn "HEALTH CHECK FAILED: $name" exception = (e, catch_backtrace())
        false
    end
    push!(_hresults, (name, ok))
end

_hpass = count(r -> r[2], _hresults)
_htot  = length(_hresults)
println("\n" * "="^58)
println("  CORE HEALTH GATE: $(_hpass)/$(_htot) PASS" * (_HFULL ? "  (full)" : ""))
for (name, ok) in _hresults
    println("  ", ok ? "✓" : "✗", "  ", name)
end
println("="^58)
exit(_hpass == _htot ? 0 : 1)
