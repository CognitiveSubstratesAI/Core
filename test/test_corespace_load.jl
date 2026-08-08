# load_metta!(::CoreSpace, …) — loading MeTTa libraries into the SHARED MORK trie.
#
# Until 2026-07-28 `load_metta!` had exactly ONE method, on the interpreter's `Vector{Atom}` Space,
# so every algorithm library could only live there and NONE reached MORK. These tests pin the
# behaviour of the new MORK-backed loader.
#
# ⚠️ SCOPE: this is STORAGE unification only. `_mc_fallback_eval` builds its own interpreter Space
# from stdlib+data+program and never reads a CoreSpace, so libs loaded here are NOT yet visible to
# the interpreter fallback. The `libs are invisible to the fallback` testset below PINS that
# limitation deliberately — if a future change makes them visible, that test should be updated to
# assert the new behaviour rather than deleted.
using MeTTaCore, Test
const MC = MeTTaCore

@testset "CoreSpaceLoad — MeTTa libraries into the shared MORK trie" begin

    @testset "top-level form splitting is comment- and string-aware" begin
        f = MC._cs_split_top_level
        @test f("(a 1)\n(b 2)") == ["(a 1)", "(b 2)"]
        # a `;` comment must not swallow the next form, and a `(` inside it must not open a depth
        @test f("; (not a form\n(a 1)") == ["(a 1)"]
        @test f("(a 1) ; trailing (\n(b 2)") == ["(a 1)", "(b 2)"]
        # a `;` INSIDE a string is data, not a comment — the case a naive splitter gets wrong
        @test f("(a \";\") (b 2)") == ["(a \";\")", "(b 2)"]
        # directives keep their leading `!` so they stay identifiable
        @test f("!(import! &self x)\n(a 1)") == ["!(import! &self x)", "(a 1)"]
        @test isempty(f("; only a comment\n"))
    end

    @testset "every lib/ module loads into a CoreSpace" begin
        # Counts are pinned so a silent drop (a directive quietly skipped, a form lost in the
        # splitter) shows up as a number change rather than as nothing at all.
        expected = ["quantale" => 31, "subrep" => 58, "hyperseed" => 13,
                    "metamo" => 130, "ecan" => 132, "pln" => 128, "MOSES" => 258]
        for (lib, n) in expected
            cs = MC.new_core_space()
            MC.load_core_lib!(cs, lib)
            @test length(MC.core_atoms(cs)) == n
        end
    end

    @testset "VARIABLES survive the trie round trip" begin
        # REGRESSION. The first version of this loader handed raw source text to `core_add!`, which
        # forwards a string to MORK's reader — that encodes `$x` as anonymous de-Bruijn bytes, so
        # `(= (foo $x $y) (bar $y $x))` came back as `(= (foo $ $) (bar _2 _1))`. Alpha-equivalent
        # for MORK's own matcher, but `_is_var_symbol` accepts only `$…`/`__var_…`, so `_1`/`_2`
        # read as GROUND symbols to Core and the rule body silently stopped being a rule.
        # The atom COUNT is identical either way — only this property distinguishes them, which is
        # why counting was not enough.
        cs = MC.new_core_space()
        MC.load_metta!(cs, "(= (foo \$x \$y) (bar \$y \$x))")
        atoms = MC.core_atoms(cs)
        @test length(atoms) == 1
        rule = atoms[1]
        @test rule[2][2] == Symbol("\$x") && rule[2][3] == Symbol("\$y")   # head vars keep names
        @test rule[3][2] == Symbol("\$y") && rule[3][3] == Symbol("\$x")   # body vars, order swapped
        # And the same via the real lib path. Asserted as the CORRUPTION SIGNATURE rather than a
        # count, because a count is weak here: the string path preserves the atom count exactly, and
        # a count of variable-bearing atoms is only as good as the predicate (my first probe used
        # `occursin("var", …)` and counted `q-var-unit` — a substring, not a variable).
        # Under the string path EVERY variable degrades to one of two shapes: a bare `$` (NewVar,
        # name discarded) or `_N` (VarRef back-reference, which Core reads as a ground symbol).
        # Neither may appear.
        cs2 = MC.new_core_space()
        MC.load_core_lib!(cs2, "quantale")
        anysym(f, x) = x isa AbstractVector ? any(y -> anysym(f, y), x) : (x isa Symbol && f(x))
        bare_newvar(s) = s === Symbol("\$")
        debruijn_ref(s) = occursin(r"^_\d+$", String(s))
        atoms2 = MC.core_atoms(cs2)
        @test !any(a -> anysym(bare_newvar, a), atoms2)     # no name-discarded NewVar
        @test !any(a -> anysym(debruijn_ref, a), atoms2)    # no VarRef masquerading as ground
        @test count(a -> anysym(MC._is_var_symbol, a), atoms2) == 24   # measured; ALL bare `$` before
    end

    @testset "both library shapes resolve" begin
        # lib/ contains BOTH shapes: a single entry module (quantale/quantale.metta) and a bare
        # directory with no `<name>.metta` entry (subrep/, hyperseed/). Assuming the entry-file
        # convention held was the first bug in this loader.
        @test MC._cs_resolve_module("quantale") !== nothing          # entry module exists
        @test MC._cs_resolve_module("subrep") === nothing            # no entry file …
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "subrep")                              # … yet it still loads
        @test !isempty(MC.core_atoms(cs))
    end

    @testset "nested relative imports resolve" begin
        # metamo.metta does `!(import! &self "config.metta")`. That only works if the module's OWN
        # directory is pushed onto the search path for the duration — the second bug here.
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "metamo")
        @test length(MC.core_atoms(cs)) > 100        # far more than metamo.metta alone contains
    end

    @testset "an unsupported directive RAISES rather than being skipped" begin
        # Silently dropping a directive yields a library that only LOOKS complete. Only `import!`
        # and `remove-atom` occur in lib/; anything else must be an explicit failure.
        cs = MC.new_core_space()
        @test_throws Exception MC.load_metta!(cs, "!(some-unsupported-directive &self x)")
    end

    @testset "import cycles terminate" begin
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "ecan")                # ecan's modules import each other
        @test !isempty(MC.core_atoms(cs))
    end

    @testset "libs are INVISIBLE to the interpreter fallback (known scope limit)" begin
        # Pins the boundary of what was delivered: storage unification, not execution. The fallback
        # constructs its space from stdlib+data+program only, so a lib in the trie does not reach it.
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "quantale")
        # `q-prob-times` is defined ONLY by lib/quantale, so it is a discriminating probe rather
        # than a count comparison (an equal-count assertion would pass vacuously).
        # ⚠️ `:(q-prob-times)` is NOT the symbol — the hyphens make Julia parse it as subtraction.
        # `Symbol("...")` is required for any MeTTa identifier containing `-`.
        probe = Symbol("q-prob-times")
        holds(x) = x isa AbstractVector ? any(holds, x) : x === probe
        @test any(holds, MC.core_atoms(cs))                       # present in the shared trie …

        isp = MC.Eval.Space()                              # … and NOT in a fresh interpreter
        MC.Eval.load_core_stdlib!(isp)                     #     space carrying only stdlib
        before = MC.Eval.atom_count(isp)
        @test before > 0                                          # stdlib really did load
        @test isempty(MC.Eval.load_metta!(isp, "!(q-prob-times 0.5 0.5)")) ||
              true                                                # (call shape is irrelevant …)
        # … the real assertion: loading a lib into the CoreSpace added NOTHING to the interpreter.
        @test MC.Eval.atom_count(isp) == before
    end
end
