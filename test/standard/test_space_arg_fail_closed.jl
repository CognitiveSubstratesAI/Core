# test_space_arg_fail_closed.jl
# ─────────────────────────────────────────────────────────────────────────────
# The space-taking grounded ops (`get-atoms`, `match`, `add-atom`, `remove-atom`) must REFUSE a first
# argument that is a concrete non-Space value, rather than silently retargeting the ambient space.
#
# Each used to read:
#     tgt = (xs[1] isa Grounded && xs[1].value isa Space) ? xs[1].value::Space : space
#
# so `(add-atom 42 (belief x))` did not error — it wrote into whatever space the evaluation was
# running in, and returned unit. During a `lib/pln` evaluation the ambient space is the RULE LIBRARY,
# which means a mistyped space argument silently injected a fact into the space holding
# `(= (Truth_Deduction …) …)`. Nothing surfaced it: no error, no wrong-looking value, just a fact in
# the wrong store that every later query would then see.
#
# The DISTINCTION being preserved matters as much as the fix. An unresolved token or an unbound
# variable still falls back to `&self` — that is the documented default and several stdlib idioms rely
# on it. Only a Grounded holding a concrete non-Space is refused, because there the caller
# unambiguously named a specific thing and it was not a space.
#
# This is also the precondition for ADR-016's multi-backend Space. Once a MORK-trie-backed store can be
# passed as an argument, "not the concrete `Space` struct" stops meaning "not a space", and a silent
# fallback would route those writes into the interpreter's own store instead of erroring.

using Test
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa

@testset "space ops fail CLOSED on a non-Space argument" begin
    sp = Space()
    load_core_stdlib!(sp)
    res(expr) = string.(load_metta!(sp, "!$expr"))
    one(expr) = (r=res(expr); isempty(r) ? "" : r[1])

    # ── (1) a real space still works, by name and by value ────────────────────────────────────────
    load_metta!(sp, "!(bind! &kb2 (new-space))")
    @test one("(add-atom &kb2 (fact 1))") == "()"
    @test one("(match &kb2 (fact \$x) \$x)") == "1"
    @test one("(get-atoms &kb2)") == "(fact 1)"
    @test one("(remove-atom &kb2 (fact 1))") == "()"
    @test one("(get-atoms &kb2)") == ""

    # ── (2) THE REGRESSION: a concrete non-Space must ERROR, not write somewhere else ──────────────
    # Sample the ambient space before and after: the point is not only that we get an error, it is
    # that NOTHING WAS WRITTEN. The old code returned "()" here and left `(leaked …)` in `sp`.
    # Only GROUNDED values are refused. `42` parses to `Grounded{Int64}` and `"a-string"` to
    # `Grounded{String}` — concrete values, so the caller named something specific and it was not a
    # space. A bare `(f 1)` parses to an `Expression` and a bare symbol to a `Sym`; neither is a
    # concrete value, so both keep the documented `&self` fallback (covered in (3) below).
    before = length(load_metta!(sp, "!(get-atoms &self)"))
    for bad in ("42", "\"a-string\"")
        r = one("(add-atom $bad (leaked $bad))")
        @test occursin("add-atom", r) && occursin("not a Space", r)
    end
    after = length(load_metta!(sp, "!(get-atoms &self)"))
    @test after == before                                  # ← the actual safety property
    @test isempty(one("(match &self (leaked \$x) \$x)"))    # …and nothing leaked in under that shape

    # the other three ops refuse the same way
    @test occursin("not a Space", one("(get-atoms 42)"))
    @test occursin("not a Space", one("(match 42 (\$a) \$a)"))
    @test occursin("not a Space", one("(remove-atom 42 (fact 1))"))

    # ── (3) the &self fallback for an UNRESOLVED token is PRESERVED (not a regression) ─────────────
    # A bare symbol that names no space is not a concrete value — it stays the documented default.
    load_metta!(sp, "(sentinel-for-fallback 7)")
    @test one("(match never-bound-token (sentinel-for-fallback \$x) \$x)") == "7"
end
