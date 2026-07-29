# Running trie-stored rules NATIVELY — no MM2 translation, no text round-trip.
#
# Whitepaper Fig-2 draws NO arrow from MeTTa to MM2: MeTTa compiles to MeTTa-IL, and MM2 kernels are a
# separate input that RUNS ON the MORK Atomspace. `docs/specs/Mork/Reflective_Metagraph_Rewriting_spec.md`
# §1 says why: "MeTTa programs ARE metagraph rewrite rules. The Atomspace IS a directed labeled
# metagraph. Execution IS metagraph rewriting." So a rule loaded into the trie should be executable
# WHERE IT SITS. Two Core-side defects stopped that; these tests pin both fixes.
#
# BLOCKER 1 — every Core read path serialises to TEXT, and the text form is LOSSY for rewriting.
#   `(= (swap $a $b) (pair $b $a))` dumps as `(= (swap $ $) (pair _2 _1))`; re-parsing that loses the
#   binding structure. MEASURED, same rules, same trie, only the read path differs:
#       via space_dump_all_sexpr   (dbl N) -> (plus _1 _1)   (swap X Y) -> NO MATCH
#       via raw byte paths         (dbl N) -> (plus N N)     (swap X Y) -> (pair Y X)
#   `core_rule_exprs` therefore reads byte paths and never calls `expr_serialize`.
#
# BLOCKER 2 — `load_metta!(::CoreSpace)` stores `__var_x` GROUND SYMBOLS (deliberately: MORK's
#   de-Bruijn encoding drops variable NAMES, and Core needs them to survive the round trip). But
#   `expr_unify` treats `__var_x` as a CONSTANT, so every stored lib rule was INERT to the native
#   rewriter. `mork_native_vars` converts on the READ path, so storage is unchanged.
using MeTTaCore, Test
const MC = MeTTaCore
const MK = MeTTaCore.MORK

@testset "native rewrite over trie-stored rules" begin

    @testset "mork_native_vars — __var_ symbols become NewVar/VarRef" begin
        # A rule in Core's stored form is INERT to unify until converted.
        stored = MK.sexpr_to_expr("(= (f __var_x) (g __var_x))")
        @test MC.mork_rule_rewrite(stored, MK.sexpr_to_expr("(f A)")) === nothing   # inert as stored
        native = MC.mork_native_vars(stored)
        got = MC.mork_rule_rewrite(native, MK.sexpr_to_expr("(f A)"))
        @test got !== nothing
        @test strip(MK.expr_serialize(got.buf)) == "(g A)"                          # …live after convert

        # Encoding: first occurrence -> NewVar (0xC0); repeat -> VarRef (0x80|k). Two DISTINCT
        # variables must get distinct ordinals, which is what the 2-var case depends on.
        two = MC.mork_native_vars(MK.sexpr_to_expr("(= (swap __var_a __var_b) (pair __var_b __var_a))"))
        @test count(==(0xC0), two.buf) == 2                    # exactly two NewVars (a, b)
        @test 0x81 in two.buf                                  # VarRef(1) — the back-reference to b
        r2 = MC.mork_rule_rewrite(two, MK.sexpr_to_expr("(swap X Y)"))
        @test r2 !== nothing && strip(MK.expr_serialize(r2.buf)) == "(pair Y X)"

        # non-variable symbols are copied through untouched
        plain = MC.mork_native_vars(MK.sexpr_to_expr("(foo bar baz)"))
        @test strip(MK.expr_serialize(plain.buf)) == "(foo bar baz)"
        @test !(0xC0 in plain.buf)                             # no variables invented
    end

    @testset "core_rule_exprs — reads BYTE PATHS, so bindings survive" begin
        cs = MC.new_core_space()
        MC.load_metta!(cs, raw"(= (dbl $x) (plus $x $x))" * "\n" *
                           raw"(= (swap $a $b) (pair $b $a))" * "\n" *
                           raw"(= (idf $z) $z)")
        rules = MC.core_rule_exprs(cs)
        @test length(rules) == 3

        rw(q) = (r = MC.core_rewrite_step(rules, MK.sexpr_to_expr(q));
                 r === nothing ? nothing : strip(MK.expr_serialize(r.buf)))
        @test rw("(dbl N)")    == "(plus N N)"     # repeated var substituted, NOT left as _1
        @test rw("(swap X Y)") == "(pair Y X)"     # 2-var rule — the case the text path could not do
        @test rw("(idf Q)")    == "Q"
        @test rw("(nomatch A)") === nothing        # no rule matches ⇒ nothing, not a wrong answer
    end

    @testset "only (= _ _) forms are collected" begin
        cs = MC.new_core_space()
        MC.load_metta!(cs, raw"(= (f $x) $x)" * "\n(: g (-> Int Int))\n(plain fact)")
        @test length(MC.core_atoms(cs)) == 3        # all three atoms are stored …
        @test length(MC.core_rule_exprs(cs)) == 1   # … but only the rule is a rewrite rule
    end

    @testset "core_normalize — fixpoint over a REAL library from the trie" begin
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "subrep")
        rules = MC.core_rule_exprs(cs)
        @test length(rules) >= 50                  # lib/subrep is 58 atoms, ~all rules

        # A real lib rule fires from the trie. Through `mc_run` this same query came back
        # COMPLETELY UNREDUCED (the fastlane deferred and the fallback cannot see the CoreSpace).
        out = MC.core_normalize(cs, "(cds-margin-simplex 0.5 (0.1 0.2))")
        @test out != "(cds-margin-simplex 0.5 (0.1 0.2))"      # something actually happened
        @test occursin("vmin", out)                            # the rule body was substituted

        # ⚠️ DOCUMENTED LIMIT, pinned so it is visible rather than surprising: top-level only, and
        # purely syntactic — no congruence descent into subterms, no grounded-op evaluation.
        @test !occursin("cds-margin-simplex", out)             # head rewrote …
        @test occursin("+", out)                               # … but (+ …) is NOT computed
    end

    @testset "storage is UNCHANGED — the conversion is read-side only" begin
        # The whole point of converting on read: `__var_` stays on disk so variable NAMES survive and
        # the interpreter's view of the space is untouched.
        cs = MC.new_core_space()
        MC.load_metta!(cs, raw"(= (h $q) $q)")
        dump = MK.space_dump_all_sexpr(cs.inner)
        @test occursin("__var_q", dump)            # stored form keeps the NAME
        @test !occursin(raw"$", dump)              # and is NOT de-Bruijn
        atoms = MC.core_atoms(cs)                  # Core still reads it as a proper variable
        @test any(a -> a isa AbstractVector && any(x -> x === Symbol("\$q"), Iterators.flatten(
                      (y isa AbstractVector ? y : [y]) for y in a)), atoms)
    end
end
