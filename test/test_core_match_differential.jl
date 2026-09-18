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

    @testset "🔴 KNOWN DIVERGENCE — `match_atoms` has NO OCCURS CHECK" begin
        # (f $x $x) vs (f $y (g $y)): $x aliases $y, then $x must also equal (g $y) — CYCLIC.
        #   match_atoms : x => (g $y)   ACCEPTS
        #   core_match  : []            rejects, via `expr_unify_cycle_safe`
        # Pinned as a DIVERGENCE, not silently resolved: which engine is right is a MeTTa-semantics
        # question, and the flag is off precisely so this can be decided rather than shipped.
        p, d = P("(f \$x \$x)"), P("(f \$y (g \$y))")
        oracle = AT.match_atoms(p, d)
        ours = MC.core_match(p, d)
        @test !isempty(oracle)            # match_atoms accepts
        @test ours !== nothing            # not a decline — a genuine, considered rejection
        @test isempty(ours)               # core_match rejects
        # CONTROL, so this is about the CYCLE and not about var-var binding in general: the same
        # shape without the cycle must be accepted by BOTH.
        p2, d2 = P("(f \$x \$x)"), P("(f \$y \$y)")
        @test !isempty(AT.match_atoms(p2, d2))
        @test !isempty(MC.core_match(p2, d2))
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
