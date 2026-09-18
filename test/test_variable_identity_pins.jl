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
        # 🟢 EMPTY as of 2026-09-18 — stage (a) closed the last three sites:
        #   Primitives.jl  WILLIAM.lgg              -> expr_serialize2  (bb34ae5)
        #   MeTTaIL.jl     _normalize_subterm       -> Expr in/Expr out; the round trip DELETED
        #   MorkBridge.jl  both String wrappers     -> expr_serialize2 at the API edge
        # An empty allowlist is the strong form of this pin: ANY new `expr_serialize(` in live src/
        # now fails, and re-opening the list requires writing down why.
        ALLOWED = Dict{String, String}()

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

        # ✅ Primitives.jl was REMOVED from this list on 2026-09-18 when WILLIAM.lgg moved to
        # `expr_serialize2`. The stale-entry check below is what confirms the site is really gone —
        # dropping an entry without fixing the code fails PIN 1's first assertion instead.
        #
        # The allowlist must not rot: an entry whose file stopped calling it should be removed.
        stale = [rel for rel in keys(ALLOWED)
                 if !occursin(r"expr_serialize\(", read(joinpath(root, rel), String))]
        @test stale == String[]

        # WILLIAM.lgg — the site the allowlist just lost, asserted on BEHAVIOUR not on the file text.
        # Anti-unification's output IS variables, so it is the sharpest test of the renderer.
        # MEASURED: `_au_merge!` emits `NewVar NewVar` (correct — two INDEPENDENT generalisation
        # positions); `expr_serialize` flattened both to a bare `$`, and "(g $ $)" re-parses as
        # `NewVar VarRef0` — "any g whose two arguments are EQUAL", strictly more specific than the
        # least general generalisation. The algorithm was never wrong; the rendering was.
        MC.register_core_primitives!()          # opt-in registry (MeTTaCore.jl:250-253), not auto
        lgg = MC.MORK.GROUNDED_REGISTRY["WILLIAM.lgg"]
        @test tagwalk(MK.sexpr_to_expr(String(lgg(["(g 1 2)", "(g 3 4)"])))) ==
              ["Arity3", "Sym(g)", "NewVar", "NewVar"]
        # …and co-reference that is GENUINE must survive: `(p 1 1)` vs `(p 2 2)` really is `(p $a $a)`.
        @test tagwalk(MK.sexpr_to_expr(String(lgg(["(p 1 1)", "(p 2 2)"])))) ==
              ["Arity3", "Sym(p)", "NewVar", "VarRef0"]
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

        # ✅ HALF A — CLOSED 2026-09-18 by `_var_key` becoming a `(name, id)` TUPLE. The collision was
        # in the identity KEY (`string(name, "#", id)` made both variables `"x#7"`), not in either
        # renderer — so the BYTE path is the one that had to change, and it is the one asserted here.
        encb = MC.atom_to_expr(collide)
        @test encb.declined === nothing
        @test tagwalk(encb.expr) == ["Arity3", "Sym(f)", "NewVar", "NewVar"]   # two DISTINCT binders

        # ⚠️ THE STRING PATH STILL MERGES, and that is expected, not a regression: `typed_atom_to_expr`
        # prints `$x#7` for both, and MORK's frontend de-Bruijns BY NAME. Nothing keyed on a printed
        # name can distinguish them. That half closes when `Var` carries a positional level and the
        # bridge stops rendering identity as text (design note §4/§7 step 4).
        tgc = tagwalk(MK.sexpr_to_expr(MC.typed_atom_to_expr(collide)))
        @test tgc == ["Arity3", "Sym(f)", "NewVar", "VarRef0"]         # string path: still MERGED

        # HALF B — reachable from ORDINARY SOURCE, and it is a SPEC VIOLATION, not a convention.
        # `docs/specs/metta grammar/metta_language_spec.md` §1.2 states it normatively:
        #   "`#` is reserved: used internally by HE to represent auto-generated variables, so it
        #    cannot appear inside a variable name."
        # The reservation is what makes GENERATED names (`$x#7`, which `typed_atom_to_expr` emits)
        # safe from collision — so a parser that accepts `#` in a USER variable breaks the very
        # guarantee the generated form relies on. 🔴 THE `#` GUARD FLIPS THIS ONE.
        @test MC.Eval.parse_atom("\$x#7") isa AT.Var
        @test_broken MC.Eval.parse_atom("\$x#7").name != "x#7"

        # 🔴 THE SAME CLASS, SECOND INSTANCE — a BARE `$` parses to a variable with an EMPTY NAME.
        # Grammar: `VARIABLE ::= '$', ( CHAR | '"' ), { CHAR | '"' }` — at least ONE character is
        # REQUIRED after `$`, so `$` alone is ungrammatical and must not yield a Var.
        #
        # ⚠️ WHY THIS ONE MATTERS BEYOND CONFORMANCE: `expr_serialize` renders EVERY `NewVar` as a
        # bare `$`. Each one parses back to `Var("")`, and `Var("") == Var("")`, so every variable in
        # a lossily-serialised term becomes THE SAME VARIABLE. That is the typed-lane mechanism
        # behind the byte-lane merge pinned in MORK's unit_serialize_roundtrip.jl, where
        # `(p $x $y $x)` round-trips as `NewVar VarRef0 Sym(_1)`. Two lanes, one cause.
        @test MC.Eval.parse_atom("\$") isa AT.Var                       # today: a Var…
        @test MC.Eval.parse_atom("\$").name == ""                       # …with an empty name
        @test_broken !(MC.Eval.parse_atom("\$") isa AT.Var)             # grammar: NOT a variable
    end

    @testset "PIN 5 — everything `atom_to_expr` produces is WELL-SCOPED (step-4 baseline)" begin
        # BLOCKER 2 step 4 safety net, landed BEFORE `Var` changes shape so that a red afterwards is
        # SIGNAL rather than ambiguity. The invariant lives in MORK (`expr_has_unbound`, pinned in
        # unit_varref_scope_verifier.jl); this is the CORE-side claim: our encoder never emits a
        # VarRef out of scope, so today's green is a real baseline and not an untested assumption.
        wellscoped(a) = begin
            e = MC.atom_to_expr(a)
            e.declined === nothing && !MK.expr_has_unbound(e.expr)
        end
        _v(n, i=0) = AT.Var(n, UInt64(i))
        CASES = [
            AT.Sym("a"),
            AT.Expression(AT.Atom[AT.Sym("k"), AT.Sym("1"), AT.Sym("2")]),          # ground
            AT.Expression(AT.Atom[AT.Sym("g"), _v("a")]),                            # one binder
            AT.Expression(AT.Atom[AT.Sym("g"), _v("a"), _v("a")]),                   # binder + backref
            AT.Expression(AT.Atom[AT.Sym("g"), _v("a"), _v("b")]),                   # two binders
            AT.Expression(AT.Atom[AT.Sym("p"), _v("a"), _v("b"), _v("a")]),          # NewVar NewVar VarRef0
            # NESTED, and the subterm's binder is to the LEFT in a SIBLING — levels are ABSOLUTE, so
            # this is the shape that would break first if a rebase were wrong.
            AT.Expression(AT.Atom[AT.Sym("q"), _v("z"),
                                  AT.Expression(AT.Atom[AT.Sym("path"), _v("z"), _v("y")])]),
            AT.Expression(AT.Atom[AT.Sym("r"), _v("a"), _v("b"),
                                  AT.Expression(AT.Atom[AT.Sym("path"), _v("x"), _v("x")])]),
        ]
        for a in CASES
            @test wellscoped(a)
        end

        # …and the same over a REAL loaded corpus, not only constructed shapes: every atom a library
        # puts in the store must encode well-scoped.
        cs = MC.new_core_space()
        MC.load_core_lib!(cs, "metamo")
        bad = Any[]
        for a in MC.core_atoms(cs)
            enc = try MC.atom_to_expr(MC.Eval.parse_atom(MC.to_sexpr(a))) catch; nothing end
            enc === nothing && continue
            enc.declined === nothing && MK.expr_has_unbound(enc.expr) && push!(bad, a)
        end
        @test bad == Any[]
    end

    @testset "PIN 4 — the Rule of 64 DECLINES; it never truncates or aliases" begin
        # The Rule of 64 caps three things (Data-in-MORK: Arity 0..63, SymbolSize 1..63, VarRef a de
        # Bruijn LEVEL 0..63). The dangerous outcome would be SILENT TRUNCATION — `VarRef` is 6 bits,
        # so variable 65 aliasing variable 1 would make two distinct variables co-referent, the same
        # wrong-answer shape as the merge cases above. MEASURED 2026-09-18: it does not happen on any
        # path. This pins the ABSENCE, because an absence is what silently stops being true.
        #
        # ⚠️ NEST when building the over-limit case. A flat `(f $v1 … $v65)` has arity 66, so the
        # ARITY guard fires first and the VARIABLE limit is never reached — an earlier probe measured
        # exactly that and would have reported one guard as the other.
        function nvars(n)
            chunks = AT.Atom[]; i = 1
            while i <= n
                hi = min(i + 29, n)
                push!(chunks, AT.Expression(AT.Atom[AT.Sym("g");
                                                    [AT.Var("v$(k)", UInt64(k)) for k in i:hi]]))
                i = hi + 1
            end
            AT.Expression(AT.Atom[AT.Sym("f"); chunks])
        end

        # 64 distinct variables ENCODE, and stay 64 DISTINCT binders — no aliasing at the boundary.
        enc64 = MC.atom_to_expr(nvars(64))
        @test enc64.declined === nothing
        tg64 = tagwalk(enc64.expr)
        @test count(==("NewVar"), tg64) == 64
        @test count(t -> startswith(t, "VarRef"), tg64) == 0

        # 65 DECLINES on the byte path, with a reason rather than a bare flag.
        enc65 = MC.atom_to_expr(nvars(65))
        @test enc65.declined !== nothing
        @test occursin("64 distinct variables", enc65.declined)
        @test enc65.expr === nothing

        # …and THROWS on the string path — outcome (b), a real exception with a meaningful message.
        @test_throws Exception MK.sexpr_to_expr(MC.typed_atom_to_expr(nvars(65)))

        # THE CASE THAT OUTLIVES THE CALL: an over-limit atom must not be half-stored.
        cs = MC.new_core_space()
        MC.core_add!(cs, MC.typed_atom_to_expr(nvars(65)))     # warns, does not throw
        @test strip(MC.space_dump_all_sexpr(cs.inner)) == ""   # nothing stored — declined, not corrupted

        # Arity and symbol length decline the same way (the byte path guards all THREE).
        @test MC.atom_to_expr(AT.Expression(AT.Atom[AT.Sym("f");
              [AT.Sym("a$(i)") for i in 1:63]])).declined !== nothing      # arity 64
        @test MC.atom_to_expr(AT.Sym("s"^64)).declined !== nothing          # symbol 64 bytes
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
