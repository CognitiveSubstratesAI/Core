#!/usr/bin/env julia
# tools/repl.jl — warm development REPL for MeTTaCore (mirrors MORK/FactorVSA tools/repl.jl).
#
# Interactive (recommended — Revise hot-reload, no restart on function edits):
#   julia --project=. -i tools/repl.jl
# Scripted (pipe a targeted snippet — foreground, NO background, NO polling):
#   printf 'include("/tmp/snippet.jl")\n' | julia --project=. -i tools/repl.jl
#
# NEVER cold-start `julia test/runtests.jl` for iteration — use tstd()/sm() here and debug with
# @show / println / @info. Re-run t() only for the final full-suite gate.
#
# Dev tools (Revise, BenchmarkTools, JET, Cthulhu) live in the GLOBAL env (on the default
# LOAD_PATH) — no MeTTaCore dependency. Revise auto-loads via ~/.julia/config/startup.jl in
# interactive sessions; guarded here too. Heavier tools on demand: `using BenchmarkTools` etc.
#
# NOTE (Revise limitation): editing a STRUCT's fields needs a fresh session; function-body edits
# hot-reload. Relevant when touching StandardMeTTa Atoms (Sym/Var/Expression) or Bindings.

try; using Revise; catch; @warn "Revise unavailable — install into the global env for hot-reload"; end

using MeTTaCore
using Test, Profile

# The StandardMeTTa evaluator is the active dev surface. Alias its namespaces to avoid the
# Space / Expression name clashes with the legacy MORK-backed engine (two distinct atom worlds).
const SM = MeTTaCore.Minimal                       # metta_run / load_metta! / Space / parse
const SA = MeTTaCore.Minimal.StandardMeTTa         # Sym / Var / Expression / Bindings / match_atoms

const _STDLIB = joinpath(dirname(@__DIR__), "src", "standard", "stdlib.metta")

"Eval StandardMeTTa `src` in a fresh space with the real stdlib.metta loaded; return results."
function sm(src::AbstractString)
    sp = SM.Space()
    SM.load_metta!(sp, read(_STDLIB, String))
    SM.load_metta!(sp, src)
end

"Run ONLY the StandardMeTTa testsets (fast warm iteration)."
tstd() = for f in ("test_atoms","test_minimal","test_interpreter","test_stdlib","test_conformance")
    include(joinpath(dirname(@__DIR__), "test", "standard", f * ".jl"))
end
"Run the full MeTTaCore test suite."
t() = include(joinpath(dirname(@__DIR__), "test", "runtests.jl"))

if isinteractive()
    println("MeTTaCore REPL ready — Revise tracking src/. StandardMeTTa = SM / SA.")
    println("  sm(\"!(+ 1 2)\")  — eval in fresh stdlib space")
    println("  tstd()          — StandardMeTTa testsets    t()  — full suite")
end
