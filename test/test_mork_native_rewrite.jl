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
        two = MC.mork_native_vars(
            MK.sexpr_to_expr("(= (swap __var_a __var_b) (pair __var_b __var_a))")
        )
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
        MC.load_metta!(
            cs,
            raw"(= (dbl $x) (plus $x $x))" * "\n" *
            raw"(= (swap $a $b) (pair $b $a))" * "\n" *
            raw"(= (idf $z) $z)"
        )
        rules = MC.core_rule_exprs(cs)
        @test length(rules) == 3

        rw(q) = (r=MC.core_rewrite_step(rules, MK.sexpr_to_expr(q));
            r === nothing ? nothing : strip(MK.expr_serialize(r.buf)))
        @test rw("(dbl N)") == "(plus N N)"     # repeated var substituted, NOT left as _1
        @test rw("(swap X Y)") == "(pair Y X)"     # 2-var rule — the case the text path could not do
        @test rw("(idf Q)") == "Q"
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

    @testset "RULE ORDER is TRIE order, not SOURCE order — measured limit" begin
        # MeTTa's answer set depends on source order. The MORK trie stores no insertion order, so a
        # multi-clause head resolves byte-lexicographically instead. Pinned because the first version
        # of `core_rewrite_step`'s docstring claimed the opposite ("first match wins, source order").
        src_a = raw"(= (f $n) nonzero)" * "\n" * raw"(= (f 0) zero)"
        src_b = raw"(= (f 0) zero)" * "\n" * raw"(= (f $n) nonzero)"   # SAME rules, reversed

        step(src) = begin
            cs = MC.new_core_space()
            MC.load_metta!(cs, src)
            r = MC.core_rewrite_step(MC.core_rule_exprs(cs), MK.sexpr_to_expr("(f 0)"))
            r === nothing ? nothing : strip(MK.expr_serialize(r.buf))
        end
        @test step(src_a) == step(src_b)      # reversing the SOURCE changes nothing …
        @test step(src_a) == "zero"           # … it is the byte-lexicographically first clause

        # The interpreter — the source-ordered store — disagrees on BOTH counts: it returns ALL
        # matches, and their order follows the source. This is the gap a single store has to close.
        IN = MC.Eval
        interp(src) = begin
            sp = IN.Space()
            IN.load_metta!(sp, src)
            [string(a) for a in IN.metta_run(IN.parse_program("!(f 0)")[1][2], sp)]
        end
        @test interp(src_a) == ["zero", "nonzero"]
        @test interp(src_b) == ["nonzero", "zero"]     # source order IS observable here
        @test length(interp(src_a)) == 2               # …and it is NOT single-answer
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
        @test any(
            a ->
                a isa AbstractVector && any(
                    x -> x === Symbol("\$q"),
                    Iterators.flatten(
                        (y isa AbstractVector ? y : [y]) for y in a)
                ), atoms)
    end
end

# ─────────────────────────────────────────────────────────────────────────────────────────────────
# BLOCKER 3 — a FREE right-hand-side variable took a DIFFERENT variable's binding.
#
# `mork_apply` called the 3-arg `expr_apply`, which hardcodes `original_intros = 0`. Upstream resolves
# a NewVar as `bindings.get(&(n, original_intros))` (expr/src/lib.rs:2126), so that argument is the de
# Bruijn LEVEL the walked sub-expression STARTS at. A rule body is a SUBTERM: in `(= (f $x) (h $y))`
# it begins after one binder, so its `$y` is level 1. Told it was level 0, the body's first variable
# resolved to key (0,0) — `$x`'s binding — and the free variable silently became `5`.
#
# ⚠️ It is the `CRUX` note at the top of MorkBridge.jl, HALF-APPLIED: that note established head and
# body share one namespace and must be split with `ee_args!`, and `ee_args!` computes this very base
# (`env.v + new_var_count`). The base was never missing; `mork_apply` discarded it — the same shape
# `Sinks.jl`'s `_expr_rebase_varrefs` documents for a different consumer.
#
# ORACLE: Core's own interpreter, which returns `(h $y#N)` — a free variable, alpha-renamed.
# Tags, never text: `expr_serialize` prints a NewVar and a ground symbol indistinguishably.
@testset "BLOCKER 3 — a FREE rhs variable must NOT take another variable's binding" begin
    tags(e) = begin
        out = String[]; i = 1
        while i <= length(e.buf)
            t = MK.byte_item(e.buf[i])
            if t isa MK.ExprSymbol
                push!(out, "Sym(" * String(e.buf[(i + 1):(i + Int(t.size))]) * ")")
                i += 1 + Int(t.size)
            else
                push!(out, t isa MK.ExprNewVar ? "NewVar" :
                           t isa MK.ExprVarRef ? "VarRef$(Int(t.idx))" :
                           t isa MK.ExprArity  ? "Arity$(Int(t.arity))" : "?")
                i += 1
            end
        end
        out
    end
    rw(rule, data) = MC.mork_rule_rewrite(MK.sexpr_to_expr(rule), MK.sexpr_to_expr(data))

    # THE DEFECT: `$y` is free — it never appears in the head, so nothing can bind it.
    r = rw("(= (f \$x) (h \$y))", "(f 5)")
    @test r !== nothing
    @test tags(r) == ["Arity2", "Sym(h)", "NewVar"]      # was ["Arity2","Sym(h)","Sym(5)"]

    # One free, one bound — the mixed case, which is where an off-by-base is easiest to miss.
    r2 = rw("(= (f \$x) (h \$y \$x))", "(f 5)")
    @test tags(r2) == ["Arity3", "Sym(h)", "NewVar", "Sym(5)"]

    # CONTROLS — these passed even with the bug, which is exactly why it hid: when every rhs variable
    # also appears on the lhs, the off-by-base lookup still lands on a real binding.
    @test tags(rw("(= (f \$x \$y) (h \$y \$x))", "(f a b)")) ==
          ["Arity3", "Sym(h)", "Sym(b)", "Sym(a)"]
    @test tags(rw("(= (f \$x) (h \$x))", "(f 5)")) == ["Arity2", "Sym(h)", "Sym(5)"]

    # Co-reference among free variables must survive too: one binder, one back-reference.
    r3 = rw("(= (f \$x) (h \$y \$y))", "(f 5)")
    @test tags(r3) == ["Arity3", "Sym(h)", "NewVar", "VarRef0"]
end
