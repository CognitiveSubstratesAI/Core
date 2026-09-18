# test_core_match_differential.jl — SEAM 1: `core_match` against `match_atoms`, the oracle.
#
# `match_atoms` is AUTHORITATIVE. `CORE_MATCH_ENABLED` is OFF and `core_match` is on no live path.
# This file records where the two agree and, more importantly, WHERE THEY DO NOT — the same shape as
# the trie-vs-`_ANSWER_TABLE` mirror the tabling migration used to find its disagreements before they
# became answers.
#
# 🔴 COMPARED AS A MULTISET OF DEREFERENCED SUBSTITUTIONS. Order is free (invariant I7), cardinality
# is NOT, so a set comparison would hide a dropped or duplicated solution. And the maps are never
# compared STRUCTURALLY: upstream warns that a solved form's shape varies (path compression, which
# end of a var-var equation survived), so two engines can denote the same substitution with different
# storage. A variable-valued binding is therefore compared as an equality CLASS, not a representative
# — which was not a precaution but a repair: the first run reported `(f $x $x)` vs `(f $y $y)` as a
# disagreement purely because `match_atoms` kept `$x` and MORK kept `$y`.

using Test
using MeTTaCore
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
const MC = MeTTaCore
const EV = MeTTaCore.Eval
const AT = MeTTaCore.StandardMeTTa
P(s) = EV.parse_program(s)[1][2]

@testset "core_match vs match_atoms — the differential (seam 1)" begin

    @testset "the flag is OFF and nothing live consults core_match" begin
        @test MC.CORE_MATCH_ENABLED[] == false
    end

    @testset "AGREEMENT on the corpus that broke things this week" begin
        cases = [
            ("plain match",                P("(f \$x \$y)"),          P("(f a b)")),
            ("repeated var in PATTERN",    P("(f \$x \$x)"),          P("(f a a)")),
            ("repeated var, MISMATCH",     P("(f \$x \$x)"),          P("(f a b)")),
            ("repeated var in DATA too",   P("(f \$x \$x)"),          P("(f \$y \$y)")),
            ("RHS-only var (BLOCKER 3)",   P("(= (f \$x) (g \$y))"),  P("(= (f a) (g b))")),
            ("var bound to a TERM",        P("(f \$x)"),              P("(f (g a))")),
            ("bound to a term WITH a var", P("(f \$x)"),              P("(f (g \$y))")),
            ("ground, equal",              P("(f a)"),                P("(f a)")),
            ("ground, unequal",            P("(f a)"),                P("(f b)")),
            ("arity mismatch",             P("(f a)"),                P("(f a b)")),
            ("nested, shared across args", P("(h (k \$a) (k \$a))"),  P("(h (k 1) (k 1))")),
            ("nested, shared MISMATCH",    P("(h (k \$a) (k \$a))"),  P("(h (k 1) (k 2))")),
        ]
        for (why, p, d) in cases
            r = MC.core_match_differential(p, d)
            @test r.agree || "$(why): oracle=$(r.oracle) ours=$(r.ours)" == ""
        end
    end

    @testset "✅ RESOLVED — the occurs divergence was a DEFECT IN `match_atoms`, now fixed" begin
        # HISTORY, kept because the sequence is the point. This testset first landed asserting a
        # DIVERGENCE: `match_atoms` ACCEPTED `(f $x $x)` against `(f $y (g $y))` — a cyclic binding —
        # where `core_match` rejected. The differential found it; the reference engines settled it.
        #
        #   workflows/metta_xcheck.sh, 2026-09-18, with two controls matching in EVERY engine:
        #     hyperon-experimental   []                 REJECTS   <- the reference
        #     CeTTa                  (no result)        REJECTS
        #     PeTTa                  CYCLE-ACCEPTED     accepts
        #     Core, before the fix   CYCLE-ACCEPTED     accepts   <- the defect
        #
        # So `core_match` was already right and `match_atoms` — the AUTHORITATIVE matcher — carried a
        # live wrong-answer class. Fixed THERE rather than carried as a permanent exception here,
        # which is what makes this differential clean instead of exceptional.
        #
        # The defect was NOT "no occurs check": the DIRECT case `(f $x)` vs `(f (g $x))` was rejected
        # correctly all along. `_occurs` was not ALIAS-AWARE — it asked whether `$x` literally occurs,
        # not whether $x's equality CLASS does. Three places had to change, and the first two alone
        # changed nothing: `add_var_binding`, the class-merge in `add_var_equality`/
        # `_extend_eq_inplace!`, and `merge_bindings`, which was testing only for `:fork` and
        # SILENTLY DISCARDING the `:fail` the new check returned.
        for (why, p, d) in [
            ("alias, bind-then-equate", P("(f \$x \$x)"), P("(f \$y (g \$y))")),
            ("alias, equate-then-bind", P("(f \$x \$x)"), P("(f (g \$y) \$y)")),
        ]
            @test isempty(AT.match_atoms(p, d))          # rejects the cycle, as hyperon does
            @test isempty(MC.core_match(p, d))           # and so does core_match
            @test MC.core_match_differential(p, d).agree # ⇒ no divergence left
        end
        # 🔴 CONTROLS — without these a matcher that rejected EVERYTHING would pass the loop above.
        for (why, p, d) in [
            ("same shape, NO cycle", P("(f \$x \$x)"), P("(f \$y \$y)")),
            ("plain bind to a term", P("(k \$x)"),     P("(k (g \$y))")),
        ]
            @test !isempty(AT.match_atoms(p, d))
            @test !isempty(MC.core_match(p, d))
            @test MC.core_match_differential(p, d).agree
        end
    end

    @testset "🔴 OPEN + REACHABLE — the two engines disagree about the NAMESPACE" begin
        # `core_match` puts the pattern at ExprEnv source 0 and the data at source 1, so a variable
        # NAME appearing on both sides is TWO variables. `match_atoms` has ONE namespace, so it is
        # one variable. Both engines are self-consistent; they disagree about the model.
        p, d = P("(pair \$t X)"), P("(pair Y \$t)")
        @test isempty(AT.match_atoms(p, d))              # one namespace: $t = Y AND $t = X, conflict
        @test !isempty(MC.core_match(p, d))              # two sources: both bind freely
        @test !MC.core_match_differential(p, d).agree
        # CONTROL — with DISTINCT names they agree, which localises the disagreement to the SHARED
        # NAME rather than to the shape.
        @test MC.core_match_differential(P("(pair \$t X)"), P("(pair Y \$u)")).agree

        # 🔴 AND IT IS REACHABLE. An earlier version of this pin said it was not, reasoning that
        # `rename_fresh` alpha-renames stored rules before matching. That is true of the RULE path
        # and false in general — CENSUSED 2026-09-18, and two live sites pass BOTH arguments through
        # the SAME bindings, so any surviving variable is from ONE namespace by construction:
        #
        #   Eval.jl:1834  match_types_b   match_atoms(subst(t1, b), subst(t2, b))
        #   EmitJulia.jl:200 _bind_step!  match_atoms(subst(step[2], sigma), subst(step[3], sigma))
        #
        # `match_types_b`'s own comment states the intent: "Applying `b` first lets a type variable
        # bound by an earlier argument constrain a later one (polymorphism)."
        #
        # ⚠️ AND THE ONE-NAMESPACE READING IS THE CORRECT ONE THERE, measured end to end:
        @test !isempty(AT.match_atoms(P("(-> \$t \$t)"), P("(-> Number Number)")))
        @test isempty(AT.match_atoms(P("(-> \$t \$t)"), P("(-> Number String)")))
        # (that pair is sharing WITHIN the pattern, so `core_match` agrees — it is level 0 then
        #  VarRef 0 inside source 0. The disagreement needs the name on BOTH sides, as above.)
        @test MC.core_match_differential(P("(-> \$t \$t)"), P("(-> Number String)")).agree

        # ⇒ CONSEQUENCE FOR SEAM 1, and it revises this file's own header: `core_match` is NOT a
        # drop-in for EVERY `match_atoms` call site. It is correct where the two sides come from
        # DIFFERENT namespaces (a pattern against a freshly renamed stored rule) and WRONG where they
        # share one (type unification, `:unify` plan steps). "Delete match_atoms from the live path"
        # therefore needs either a same-namespace MODE for `core_match` — encode both sides into ONE
        # source so a shared name maps to one de Bruijn level — or `match_atoms` surviving at those
        # sites. Not decided here; recorded before the flag can flip.
    end

    @testset "🔴 THE CORPUS GATE READS TWO COUNTS, and the classifier is an OVER-APPROXIMATION" begin
        # Triaging hundreds of corpus disagreements by inspection is where the signal gets lost, so
        # the class is computed FROM THE INPUTS, before either matcher runs:
        #   :namespace — a variable NAME occurs on BOTH sides ⇒ the engines answer DIFFERENT
        #                questions (one namespace vs two sources). Not a defect in either; the count
        #                measures how much of `match_atoms` survives seam 1.
        #   :semantic  — no shared name ⇒ SAME question, and a difference is a defect. Gate: zero.
        @test MC.disagreement_class(P("(pair \$t X)"), P("(pair Y \$t)")) === :namespace
        @test MC.disagreement_class(P("(pair \$t X)"), P("(pair Y \$u)")) === :semantic
        @test MC.disagreement_class(P("(f a)"), P("(f b)")) === :semantic          # no variables

        # ⚠️ IT IS DELIBERATELY AN OVER-APPROXIMATION, and reading the counts without knowing that
        # would misattribute them. A shared NAME makes a pair namespace-SENSITIVE; it only produces a
        # DISAGREEMENT when the shared variable is actually constrained on both sides. MEASURED over
        # stdlib rule heads x stdlib atoms (6,273 pairs): 482 pairs were in the namespace class and
        # ZERO of them disagreed (429 agreed, 53 declined). So the class flags more than it needs to,
        # which is the safe direction — it can over-report expected disagreements, never hide a
        # semantic one.
        agreeing_shared = (P("(pair \$t X)"), P("(pair \$t X)"))
        @test MC.disagreement_class(agreeing_shared...) === :namespace   # flagged …
        @test MC.core_match_differential(agreeing_shared...).agree       # … and yet agrees

        # 🔴 AND THE COUNT IS ONLY EVIDENCE IF THE CLASS IS EXERCISED. A first corpus run reported
        # "0 namespace disagreements" without measuring how many pairs were IN the class — a clean
        # result on data that could not have shown the defect. The distribution has to be counted
        # over ALL pairs, not over the disagreeing ones.
        MC.reset_core_match_disagreements!()
        @test MC.core_match_disagreement_counts().total == 0
        MC.core_match_differential(P("(pair \$t X)"), P("(pair Y \$t)"))   # a namespace disagreement
        c = MC.core_match_disagreement_counts()
        @test c.namespace == 1 && c.semantic == 0 && c.total == 1
        MC.reset_core_match_disagreements!()                             # leave no residue
        @test MC.core_match_disagreement_counts().total == 0
    end

    @testset "🔴 DECLINE IS PART OF THE CONTRACT — and the differential covers it" begin
        # Over-limit inputs are exactly where the two engines differ in MECHANISM, so leaving them
        # out of the differential would untest the path most likely to diverge.
        over_arity = P("(f " * join(["a" for _ in 1:70], " ") * ")")
        @test MC.core_match(over_arity, over_arity) === nothing     # DECLINED, not "no match"
        r = MC.core_match_differential(over_arity, over_arity)
        @test r.declined
        @test r.agree                                               # a decline is not a disagreement
        # and `match_atoms` still answers it, which is what makes the fallback correct
        @test !isempty(AT.match_atoms(over_arity, over_arity))

        # over the VARIABLE limit, nested so every arity stays <= 31 and the ARITY guard cannot be
        # what fires (a flat 65-variable atom has arity 66 — the confound that fooled an earlier probe)
        # ⚠️ `\$v$(i)`, NOT `\$v\$i`. Escaping BOTH dollars names every variable the literal string
        # `\$v\$i`, i.e. ONE variable — so the first draft of this case had 2 distinct variables, never
        # reached the 64-variable guard, and asserted a decline that could not happen. The same
        # "does the data actually exercise the case" failure the flat-arity confound produced.
        nested = P("(f (g " * join(["\$v$(i)" for i in 1:30], " ") * ") (g " *
                   join(["\$w$(i)" for i in 1:30], " ") * ") (g \$p1 \$p2 \$p3 \$p4 \$p5))")
        @test length(MC.collect_vars(nested)) == 65          # the case IS reached
        @test all(c -> !(c isa AT.Expression) || length(c.children) <= 31, nested.children)
        @test MC.core_match(nested, nested) === nothing
        @test occursin("more than 64 distinct variables", MC.atom_to_expr(nested).declined)
        @test MC.core_match_differential(nested, nested).declined

        # 🔴 NEGATIVE CONTROL: a decline must be DISTINGUISHABLE from "no match". Without this, a
        # `core_match` that returned `nothing` for everything would pass every test above.
        @test MC.core_match(P("(f a)"), P("(f b)")) == AT.Bindings[]   # no match, NOT nothing
        @test MC.core_match(P("(f a)"), P("(f a)")) !== nothing        # a match, NOT a decline
    end

    @testset "🔴 GROUNDED values are recovered BY POSITION, exactly" begin
        # The reason bindings are not translated by decoding: of these, only Int survives a byte
        # round trip. Position recovery returns the ORIGINAL object for all of them.
        for v in (true, false, "hello", :sym, 7, 3.5)
            p = P("(f \$x)")
            d = AT.Expression(AT.Atom[AT.Sym("f"), AT.Grounded(v)])
            ours = MC.core_match(p, d)
            @test ours !== nothing && length(ours) == 1
            @test length(ours[1].entries) == 1
            got = ours[1].entries[1].val
            @test got isa AT.Grounded
            @test got.value == v
            @test got === d.children[2]                     # the ORIGINAL object
            @test MC.core_match_differential(p, d).agree
            # prove the byte path really would have lost it, for the four lossy types
            if v isa Bool || v isa AbstractString || v isa Symbol
                @test !((MC.expr_to_atom(MC.atom_to_expr(d).expr)::AT.Expression).children[2] isa AT.Grounded)
            end
        end
    end
end
