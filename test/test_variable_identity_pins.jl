# test_variable_identity_pins.jl — the three properties Core owns about VARIABLE IDENTITY crossing
# the MORK boundary. Each exists because a real defect got through without it.
#
# PIN 1  no live `src/` path may call `expr_serialize` (the lossy serializer), display allowlisted
# PIN 2  two DISTINCT Core `Var`s must never MERGE into one MORK variable
# PIN 3  a variable appearing ONLY on a rule's right-hand side must survive as a VARIABLE
#
# 🔴 WHY PIN 3 IS A PROPERTY AND NOT A CASE. BLOCKER 3 (`mork_apply` dropped the de Bruijn base,
# fixed in ef36ec4) survived review because BOTH of its controls passed: when every rhs variable also
# appears on the lhs, an off-by-base lookup still lands on a real binding. `test_mork_native_rewrite.jl`
# pins the specific case; this pins the GENERAL rule over a family, so the next consumer that drops a
# base is caught by construction rather than by someone thinking to write that case.
#
# Three consumers of `ee_args!` were audited 2026-09-18; two had dropped the base it computes
# (MorkBridge's `mork_apply`, and historically `PureSink` — see Sinks.jl `_expr_rebase_varrefs`).
# The invariant that separates the broken ones: IF THE ZIPPER DOES NOT START AT POSITION 1 OF ITS OWN
# `Expr`, THE BASE CANNOT BE 0.
#
# Everything here compares TAGS, never text: `expr_serialize` renders a NewVar and a ground symbol
# indistinguishably, so a text assertion would beg the question (MORK's unit_serialize_roundtrip.jl
# pins that separately).

using MeTTaCore, Test
const MC = MeTTaCore
const MK = MeTTaCore.MORK
const AT = MeTTaCore.StandardMeTTa

@testset "variable identity across the MORK boundary" begin
    function tagwalk(e)
        out = String[]
        i = 1
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

    @testset "PIN 1 — `expr_serialize` is banned from live src/ paths" begin
        # The lossy serializer is fine for HUMANS (logs, errors, a REPL line) and wrong for anything
        # re-parsed or stored. Rather than re-audit by hand each time, the allowlist IS the audit:
        # adding a call site to live code fails this test until it is justified here by name.
        #
        # ⚠️ Keep this list SHORT and give each entry a reason. An entry with no reason is a defect
        # waiting to be rediscovered — that is precisely how the four sites below accumulated.
        ALLOWED = Dict(
            # file => why a LOSSY rendering is acceptable at this site
            "src/eval/MorkBridge.jl" =>
                "String-contract convenience wrappers; migrating to serialize2 (de Bruijn plan, stage a)",
            "src/standard/MeTTaIL.jl" =>
                "re-parses its own output; the round trip itself is slated for deletion (stage a)",
            "src/primitives/Primitives.jl" =>
                "WILLIAM.lgg — anti-unification output; unregistered today, see the side finding",
        )

        root = normpath(joinpath(@__DIR__, ".."))
        offenders = String[]
        for (dir, _, files) in walkdir(joinpath(root, "src")), f in files
            endswith(f, ".jl") || continue
            path = joinpath(dir, f)
            rel = replace(relpath(path, root), '\\' => '/')
            txt = read(path, String)
            # `expr_serialize(` but NOT `expr_serialize2(`
            occursin(r"expr_serialize\(", txt) || continue
            haskey(ALLOWED, rel) || push!(offenders, rel)
        end
        # Every offender is a NEW lossy site: either use expr_serialize2, or allowlist it with a reason.
        @test offenders == String[]

        # The allowlist must not rot: an entry whose file stopped calling it should be removed.
        stale = [rel for rel in keys(ALLOWED)
                 if !occursin(r"expr_serialize\(", read(joinpath(root, rel), String))]
        @test stale == String[]
    end

    @testset "PIN 2 — distinct Core Vars must not MERGE into one MORK variable" begin
        # `typed_atom_to_expr` carries variable identity as a PRINTED NAME (`$x#7`), and MORK's
        # frontend de-Bruijns BY NAME. So distinctness holds only while the printed names differ.
        distinct = AT.Expression(AT.Atom[AT.Sym("f"), AT.Var("x", UInt64(7)), AT.Var("x", UInt64(9))])
        tg = tagwalk(MK.sexpr_to_expr(MC.typed_atom_to_expr(distinct)))
        @test tg == ["Arity3", "Sym(f)", "NewVar", "NewVar"]      # two binders, NOT a back-reference

        # 🔴 THE COLLISION, MEASURED 2026-09-18: `Var("x", 7)` prints `$x#7`, and so does a Var
        # literally NAMED "x#7". Two different variables, one rendered name, and they merge silently.
        #
        # ⚠️ THERE ARE TWO HALVES, AND THE `#` PARSE GUARD ONLY CLOSES ONE. Read this before
        # concluding "guard landed but the test is still broken" — that is the CORRECT state.
        #
        #   HALF A — PROGRAMMATIC (below): `AT.Var("x#7", 0)` built directly in Julia. The guard does
        #     NOT close this and is not meant to; it stays `@test_broken` until BLOCKER 2 gives `Var`
        #     a positional NewVar/VarRef level, at which point there is no name left to collide.
        #   HALF B — SOURCE-REACHABLE (further below): `parse_atom("$x#7")`. The guard DOES close
        #     this; that `@test_broken` is the one expected to flip, and flipping it is how the guard
        #     is verified.
        #
        # ESCAPE AUDIT, 2026-09-18 — the guard is not bypassed by the renamers it protects.
        # Every `Var` construction site that synthesises a name was checked: `freshvar(name) =
        # (…; Var(name, _VAR_COUNTER[]))` (Eval.jl:987) keeps the counter in the ID FIELD and passes
        # the base name through; `rename_fresh` calls `freshvar(v.name)`; `_variant_rename`
        # (Tabling.jl:1011) builds `Var("_v", UInt64(n))`. None can put a `#` into a name. So after
        # the guard the residual hole is EXACTLY hand-written `Var`s — not source, not renaming.
        collide = AT.Expression(AT.Atom[AT.Sym("f"), AT.Var("x", UInt64(7)), AT.Var("x#7", UInt64(0))])
        tgc = tagwalk(MK.sexpr_to_expr(MC.typed_atom_to_expr(collide)))
        @test_broken tgc == ["Arity3", "Sym(f)", "NewVar", "NewVar"]   # HALF A — BLOCKER 2 flips this
        @test tgc == ["Arity3", "Sym(f)", "NewVar", "VarRef0"]         # today: MERGED — the hole, pinned

        # HALF B — reachable from ORDINARY SOURCE: our parser accepts `#` in a variable name, which
        # the HE grammar reserves precisely to prevent this. 🔴 THE `#` GUARD FLIPS THIS ONE.
        @test MC.Eval.parse_atom("\$x#7") isa AT.Var
        @test_broken MC.Eval.parse_atom("\$x#7").name != "x#7"
    end

    @testset "PIN 3 — a variable only on the RHS survives as a variable (the general property)" begin
        rw(rule, data) = MC.mork_rule_rewrite(MK.sexpr_to_expr(rule), MK.sexpr_to_expr(data))
        isvar(t) = t == "NewVar" || startswith(t, "VarRef")

        # FAMILY: each rule has at least one rhs-only variable. Whatever else the result contains,
        # a variable MUST remain — substituting a binding for it is the BLOCKER 3 wrong answer.
        RHS_ONLY = [
            ("(= (f \$x) (h \$y))",            "(f 5)"),
            ("(= (f \$x) (h \$y \$x))",        "(f 5)"),
            ("(= (f \$x) (h \$y \$y))",        "(f 5)"),
            ("(= (f \$x) (h (g \$y)))",        "(f 5)"),      # nested
            ("(= (f \$x \$y) (h \$z \$x))",    "(f a b)"),    # two bound, one free
            ("(= (p \$a) (q \$b \$c))",        "(p 1)"),      # two distinct free vars
        ]
        for (rule, data) in RHS_ONLY
            r = rw(rule, data)
            @test r !== nothing
            @test any(isvar, tagwalk(r))
        end

        # Two distinct free variables must stay DISTINCT, not collapse to one.
        @test tagwalk(rw("(= (p \$a) (q \$b \$c))", "(p 1)")) ==
              ["Arity3", "Sym(q)", "NewVar", "NewVar"]

        # CONTROL FAMILY: no rhs-only variable ⇒ a fully ground result. These passed WHILE BLOCKER 3
        # WAS BROKEN, which is exactly why the property above is the test that matters.
        for (rule, data, expect) in [
            ("(= (f \$x) (h \$x))",         "(f 5)",   ["Arity2", "Sym(h)", "Sym(5)"]),
            ("(= (f \$x \$y) (h \$y \$x))", "(f a b)", ["Arity3", "Sym(h)", "Sym(b)", "Sym(a)"]),
        ]
            @test tagwalk(rw(rule, data)) == expect
        end
    end
end
