# test_debruijn_storage_gate.jl — the GATE for the de Bruijn storage migration (Stage 0b).
#
# Plan: docs/specs/debruijn_storage_migration_scope_2026-07-11.md §5, build order in revision R9.
# Sibling: test_corespace_load.jl's "storage form: core_add! rules are INERT" testset, which pins the
# fix ORDER (read paths before storage). This file pins the DESTINATION.
#
# ─── HOW TO READ THE `@test_broken`s, AND WHY THEY ARE NOT SKIPS ─────────────────────────────────
# Gate-first discipline says write the test before the fix and confirm it FAILS. A bare failing
# `@test` would make the suite red for as long as the migration takes, and a permanently-red gate
# gets ignored — the same argument the MM2 conformance ratchet is built on.
#
# `@test_broken` is the Julia idiom that keeps both properties: it PASSES (reported "Broken") while
# the expression is false, and **FAILS LOUDLY the moment the expression becomes true**. So when
# Stage 2 flips `to_sexpr` to emit real variables, THIS FILE FAILS — and the fix is to change
# `@test_broken` to `@test`, which is exactly the bookkeeping the migration should be forced to do.
# ⚠️ A `@test_broken` that starts passing is NOT a false alarm. It is the gate firing.
#
# EVERY expectation below was MEASURED against the current tree before being written
# (`~/csai-work/gates/probes/debruijn_stage0b_probe.jl`, 2026-09-18) — none is predicted.
#
#   5.2 alpha-variant collapse   BROKEN today: core_add! stores 2 atoms, native storage stores 1
#   5.3 distinct vars            PASSES today: 2 and 2 — a guard against OVER-collapsing
#   5.4 co-reference read-back   PASSES today — and only since Stage 0a (Core 4a81c5a); this test is
#                                what stops the read paths regressing to `expr_serialize`
#   5.5 round-trip execute       BROKEN today: ground query sees 0 through core_add! storage, 1 native

using MeTTaCore, Test
const MC = MeTTaCore

@testset "de Bruijn storage migration — the gate (Stage 0b)" begin
    _v(s) = Symbol("\$" * s)
    _dump(cs) = strip(MC.space_dump_all_sexpr(cs.inner))
    _natoms(cs) = (d = _dump(cs); isempty(d) ? 0 : length(split(d, '\n')))
    _ask(cs, q) = MC.space_query_multi(cs.inner.btm, MC.sexpr_to_expr(q), (_b, _l) -> true)

    @testset "5.2 alpha-variants collapse to ONE stored atom" begin
        # `(= (f $x) $x)` and `(= (f $y) $y)` are the SAME rule up to renaming; MeTTa is
        # alpha-invariant (stdlib.metta `assertAlphaEqual`). De Bruijn storage makes them one byte
        # path; the `__var_` form makes them two, because the NAME is in the key.
        cs = MC.new_core_space()
        MC.core_add!(cs, [:(=), [:f, _v("x")], _v("x")])
        MC.core_add!(cs, [:(=), [:f, _v("y")], _v("y")])
        @test_broken _natoms(cs) == 1          # today 2 — the name is part of the stored key

        # The destination, reachable today only through the native writer: ONE atom, name regenerated.
        native = MC.new_core_space()
        MC.space_add_all_sexpr!(native.inner, "(= (f \$x) \$x)")
        MC.space_add_all_sexpr!(native.inner, "(= (f \$y) \$y)")
        @test _natoms(native) == 1
        @test _dump(native) == "(= (f \$a) \$a)"
    end

    @testset "5.3 DISTINCT variables must NOT collapse" begin
        # The failure mode on the other side of 5.2: collapsing too much. `(f $x $y)` and `(f $x $x)`
        # differ in CO-REFERENCE, not in names, so no encoding may merge them.
        cs = MC.new_core_space()
        MC.core_add!(cs, [:f, _v("x"), _v("y")])
        MC.core_add!(cs, [:f, _v("x"), _v("x")])
        @test _natoms(cs) == 2

        native = MC.new_core_space()
        MC.space_add_all_sexpr!(native.inner, "(f \$x \$y)")
        MC.space_add_all_sexpr!(native.inner, "(f \$x \$x)")
        @test _natoms(native) == 2                       # holds under de Bruijn too
        @test occursin("(f \$a \$b)", _dump(native))      # two binders
        @test occursin("(f \$a \$a)", _dump(native))      # binder + back-reference
    end

    @testset "5.4 co-reference survives the READ path (this is Stage 0a's property)" begin
        # 🔴 REGRESSION GUARD, not a future expectation. Before Core 4a81c5a the CoreSpace readers
        # called `expr_serialize`, which renders `NewVar => "$"` and `VarRef(r) => "_{r+1}"` — so
        # `(p $x $x)` came back as `(p $ _1)`: a bare `$` (ungrammatical as a MeTTa variable) and a
        # GROUND symbol `_1`. Moving the readers to `expr_serialize2` is what makes this pass.
        # If someone reverts that, this test is the thing that says so.
        cs = MC.new_core_space()
        MC.space_add_all_sexpr!(cs.inner, "(p \$x \$x)")
        atoms = MC.core_atoms(cs)
        @test length(atoms) == 1
        a = atoms[1]
        @test length(a) == 3
        @test a[2] === a[3]                  # co-referential: the SAME symbol in both positions
        @test MC._is_var_symbol(a[2])        # …and still recognised AS a variable
        @test !occursin("_1", string(a[3]))  # the lossy VarRef-as-ground rendering is gone
    end

    @testset "5.5 a stored rule fires against a GROUND query (round-trip execute)" begin
        # The defect in one assertion: a rule written through `core_add!` is INERT to MORK's own
        # matcher, because `to_sexpr` puts a ground symbol where a variable belongs. Same rule, same
        # trie, same matcher through the native writer — it fires.
        ground = "(, (= (f 5) \$r))"
        cs = MC.new_core_space()
        MC.core_add!(cs, [:(=), [:f, _v("x")], _v("x")])
        @test_broken _ask(cs, ground) == 1     # today 0 — `5` cannot unify with `__var_x`

        native = MC.new_core_space()
        MC.space_add_all_sexpr!(native.inner, "(= (f \$x) \$x)")
        @test _ask(native, ground) == 1        # the destination, already reachable

        # ⚠️ The WILDCARD control fires in BOTH — which is why this stayed invisible for so long.
        # Any query whose variable positions are wildcards matches the ground symbol fine; only
        # rule APPLICATION (a ground argument) is affected.
        wild = "(, (= (f \$y) \$r))"
        @test _ask(cs, wild) == 1
        @test _ask(native, wild) == 1
    end
end
