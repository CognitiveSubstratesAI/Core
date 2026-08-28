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
# NOT immutable: `full` appends to this below. `const` binds the NAME, so `push!` is legal.
const _HCHECKS = Tuple{String, String}[
    (
        "hyperon conformance (234 directives)",
        joinpath(_HROOT, "standard", "test_conformance.jl")
    ),
    (
        "LeaTTa proved-oracle (CORE_BUG gate)",
        joinpath(_HROOT, "oracle", "leatta", "test_leatta_oracle.jl")
    ),
    ("no dangling lib ops", joinpath(_HROOT, "test_no_dangling_ops.jl")),
    ("no stdlib shadowing", joinpath(_HROOT, "test_no_stdlib_shadow.jl")),
    # A `$name` in a docstring is INTERPOLATION and breaks PRECOMPILE — cost three failures on
    # 2026-08-16/17, each quoting an upstream `$tbl_*` predicate or a MeTTa `$variable`.
    (
        "no docstring \$-interpolation",
        joinpath(_HROOT, "test_no_docstring_interpolation.jl")
    ),
    ("type system", joinpath(_HROOT, "test_types.jl"))
]

# 🔴 `full` PARSED ITS FLAG AND THEN GATED NOTHING — fixed 2026-08-28.
# `_HFULL` was read at :14 and used at exactly ONE site: the banner, which appended "  (full)".
# So `./bin/health full` printed `6/6 PASS (full)` while running the IDENTICAL six checks. The
# 2026-07-28 whitepaper audit called it exactly right — "it prints that it ran more than it ran" —
# and it survived because the flag DID something visible, so the output looked like evidence.
#
# ⚠️ AND THE SUITE IT NAMES RAN NOWHERE AT ALL: `test/pln/test_pln_ecan.jl` (156 lines, §4.9 PLN↔ECAN
# acceptance, T1-T4) is not in `runtests.jl` either. It was reachable only through a flag that did
# not work — a test orphaned twice over. Verified passing before wiring: 13/13 (+2/2 silent-test
# guard) via `tools/run_tests.sh`.
_HFULL && push!(
    _HCHECKS,
    ("§4.9 PLN↔ECAN acceptance (full only)", joinpath(_HROOT, "pln", "test_pln_ecan.jl"))
)

_hresults = Tuple{String, Bool}[]
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
_htot = length(_hresults)
println("\n" * "="^58)
println("  CORE HEALTH GATE: $(_hpass)/$(_htot) PASS" * (_HFULL ? "  (full)" : ""))
for (name, ok) in _hresults
    println("  ", ok ? "✓" : "✗", "  ", name)
end
println("="^58)
exit(_hpass == _htot ? 0 : 1)
