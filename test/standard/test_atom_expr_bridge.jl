# test_atom_expr_bridge.jl — the typed `Atom` ⇄ MORK `Expr` BYTE pair.
#
# Covers `atom_to_expr` (Atom → bytes, added 2026-08-27) against its two siblings in
# `src/standard/AtomExprBridge.jl`. The pair was ASYMMETRIC before: `expr_to_atom` reads bytes, but
# `typed_atom_to_expr` returns a **String** despite its name and lets `space_add_all_sexpr!` do the
# encoding. So Atom → bytes did not exist, and `MorkBridge.jl` BLOCKER 2 was the consequence — Core
# stores `$x` as the ground symbol `__var_x`, which `expr_unify` reads as a CONSTANT, leaving every
# stored lib rule inert to the native rewriter.
#
# ─── WHY THERE ARE TWO KINDS OF TEST HERE, NOT ONE ───────────────────────────────────────────────
# NO-REGRESSION (set A) is byte equality against `sexpr_to_expr(typed_atom_to_expr(·))`. That proves
# the new path agrees with the working one — but ONLY on atoms the text path can represent, which is
# exactly the population that never needed a byte path. It cannot speak to the gap.
# GAP-CLOSING (sets B/D) is behavioural: a rule whose variables came from Core `Atom`s must UNIFY,
# and must survive a bytes → Atom round trip with co-reference intact.
#
# 🔴 WHAT IS *NOT* CLAIMED. Core's `Atom` model still has no MORK-variable type. `atom_to_expr`
# translates a `Var` into `NewVar`/`VarRef` tags AT ENCODE TIME. "Variables now survive storage" is
# true; "Core represents MORK variables" is not.
using MeTTaCore
using Test

const _AB_S = MeTTaCore.StandardMeTTa
const _AB_M = MeTTaCore.MORK

_ab_mk(xs...) = _AB_S.Expression(_AB_S.Atom[xs...])
_ab_sym(s)    = _AB_S.Sym(Symbol(s))
_ab_var(n, id = 0) = _AB_S.Var(n, UInt64(id))

@testset "AtomExprBridge — atom_to_expr" begin

    @testset "A. no regression: bytes agree with the text path" begin
        # The first two are the De Bruijn LEVELS discriminator. Levels count bindings introduced to
        # the LEFT, so the ordinal tracks the VARIABLE, not the distance to its binder:
        #     (f $x $y $x $y) -> [5] <f> $ $ &0 &1
        #     (g $a $b $b $a) -> [5] <g> $ $ &1 &0
        # An encoder using de Bruijn INDICES would swap both. Keeping BOTH orders is what makes the
        # pair discriminating; either alone passes under either convention.
        cases = [
            _ab_mk(_ab_sym("f"), _ab_var("x"), _ab_var("y"), _ab_var("x"), _ab_var("y")),
            _ab_mk(_ab_sym("g"), _ab_var("a"), _ab_var("b"), _ab_var("b"), _ab_var("a")),
            _ab_mk(_ab_var("x"), _ab_var("x")),
            _ab_mk(_ab_sym("="), _ab_mk(_ab_sym("swap"), _ab_var("a"), _ab_var("b")),
                _ab_mk(_ab_sym("pair"), _ab_var("b"), _ab_var("a"))),
            _ab_mk(_ab_sym("edge"), _ab_sym("a"), _ab_sym("b")),
            _ab_mk(_ab_sym("f"), _ab_var("x", 7), _ab_var("x", 9)),
        ]
        for a in cases
            enc = MeTTaCore.atom_to_expr(a)
            @test enc.declined === nothing
            @test enc.expr.buf == _AB_M.sexpr_to_expr(MeTTaCore.typed_atom_to_expr(a)).buf
        end
    end

    # ⚠️ THE LAST CASE ABOVE AGREES FOR A DIFFERENT REASON ON EACH SIDE, AND THAT MATTERS.
    # `(f $x#7 $x#9)` is two DISTINCT `Var`s sharing a base name (what `rename_fresh` produces).
    # Our encoder keeps them apart because `_var_key` is name+id. The REFERENCE side keeps them apart
    # because `typed_atom_to_expr` PRINTS `$x#7`/`$x#9`, so MORK's parser sees two distinct NAMES.
    # Same bytes, different mechanism. So if `typed_atom_to_expr` ever stops rendering `#id`, this
    # comparison silently stops discriminating — both sides would then collapse. The assertion below
    # pins the SHAPE directly and does not depend on the reference at all.
    @testset "A2. same base name + different id must NOT collapse (capture guard)" begin
        a = _ab_mk(_ab_sym("f"), _ab_var("x", 7), _ab_var("x", 9))
        buf = MeTTaCore.atom_to_expr(a).expr.buf
        tags = [_AB_M.byte_item(buf[i]) for i in (1, 4, 5)]   # arity, then the two var slots
        @test tags[1] isa _AB_M.ExprArity
        @test tags[2] isa _AB_M.ExprNewVar     # first `x` binds
        @test tags[3] isa _AB_M.ExprNewVar     # second is a DIFFERENT variable — NOT VarRef(0)
        # keyed on bare `name` this would be [Arity, NewVar, VarRef(0)] and one byte shorter
        @test length(buf) == 5
    end

    @testset "B. the gap: Core-authored variables unify natively" begin
        rule = _ab_mk(_ab_sym("="), _ab_mk(_ab_sym("dbl"), _ab_var("n")),
            _ab_mk(_ab_sym("plus"), _ab_var("n"), _ab_var("n")))
        enc = MeTTaCore.atom_to_expr(rule)
        @test enc.declined === nothing
        out = MeTTaCore.mork_rule_rewrite(enc.expr, _AB_M.sexpr_to_expr("(dbl 7)"))
        @test out !== nothing
        @test strip(_AB_M.expr_serialize(out.buf)) == "(plus 7 7)"

        # The contrast that makes the above meaningful: Core's `__var_` STORAGE form is a ground
        # symbol, so `expr_unify` treats it as a constant and the same rule is inert (BLOCKER 2).
        inert = _AB_M.sexpr_to_expr("(= (dbl __var_n) (plus __var_n __var_n))")
        @test MeTTaCore.mork_rule_rewrite(inert, _AB_M.sexpr_to_expr("(dbl 7)")) === nothing
    end

    @testset "C. declines carry a REASON — never throw, never wrap" begin
        # NESTED so every arity stays < 64. The first version of this test used a FLAT 70-child
        # expression, which declined on ARITY (71) and never reached the variable-count path at all —
        # a test that passed while exercising nothing. Keep the nesting.
        rows = _AB_S.Atom[_ab_mk([_ab_var("v$(r)_$(c)") for c in 1:7]...) for r in 1:10]   # 70 vars
        d_many = MeTTaCore.atom_to_expr(_ab_mk(_ab_sym("f"), rows...))                     # arity 11
        @test d_many.expr === nothing
        @test occursin("64 distinct variables", d_many.declined)

        # ...and the boundary on the other side, so the ceiling is not off by one.
        ok = _AB_S.Atom[_ab_mk([_ab_var("w$(r)_$(c)") for c in 1:7]...) for r in 1:9]       # 63 vars
        @test MeTTaCore.atom_to_expr(_ab_mk(_ab_sym("f"), ok...)).expr !== nothing

        # Arity ceiling. Masking instead of declining WRAPS ACROSS A TAG BOUNDARY
        # (64 & 0x3f == 0 ⇒ NewVar) — the CID incident, Expr.jl:57-63.
        flat = MeTTaCore.atom_to_expr(_ab_mk([_ab_sym("s$i") for i in 1:70]...))
        @test flat.expr === nothing && occursin("arity", flat.declined)

        big_sym = MeTTaCore.atom_to_expr(_ab_sym("x"^80))
        @test big_sym.expr === nothing && occursin("Rule of 64", big_sym.declined)

        # No grounded TAG exists (Data-in-MORK: four live classes, none grounded), so a Grounded
        # encodes as its WORD. A value printing as an EXPRESSION has no symbol encoding at all.
        st = MeTTaCore.atom_to_expr(_AB_S.Grounded("(State 1)"))
        @test st.expr === nothing && occursin("single WORD", st.declined)
    end

    @testset "D. round trip: co-reference survives atom_to_expr → expr_to_atom" begin
        # `expr_to_atom`'s docstring claims a `VarRef(idx)` returns the SAME `Var` OBJECT as the
        # idx-th `NewVar`. With both halves of the pair present that is finally checkable, and it is
        # the property the lossy `$`/`_N` TEXT dump cannot express.
        a = _ab_mk(_ab_sym("="), _ab_mk(_ab_sym("f"), _ab_var("x")), _ab_var("x"))
        back = MeTTaCore.expr_to_atom(MeTTaCore.atom_to_expr(a).expr)
        @test back isa _AB_S.Expression
        head = (back::_AB_S.Expression).children[2]::_AB_S.Expression   # (f $x)
        tail = (back::_AB_S.Expression).children[3]                     # $x
        @test head.children[2] === tail        # SAME object, not merely equal

        # Two distinct variables must come back distinct.
        b = _ab_mk(_ab_sym("g"), _ab_var("p"), _ab_var("q"))
        bb = MeTTaCore.expr_to_atom(MeTTaCore.atom_to_expr(b).expr)::_AB_S.Expression
        @test bb.children[2] !== bb.children[3]

        # THREE occurrences, which is the case two cannot reach. With `$n` appearing once as the
        # binder and TWICE as a reference, `[$ … &0 … &0]`, a reader that returned "the previous
        # reference" instead of "the idx-th NewVar" is still correct at two occurrences and wrong
        # here. All three must be the SAME object.
        r = _ab_mk(_ab_sym("="), _ab_mk(_ab_sym("dbl"), _ab_var("n")),
            _ab_mk(_ab_sym("plus"), _ab_var("n"), _ab_var("n")))
        rb = MeTTaCore.expr_to_atom(MeTTaCore.atom_to_expr(r).expr)::_AB_S.Expression
        binder = (rb.children[2]::_AB_S.Expression).children[2]     # $n in (dbl $n)
        body   = rb.children[3]::_AB_S.Expression                   # (plus $n $n)
        @test binder === body.children[2]
        @test binder === body.children[3]

        # And the byte form is a fixpoint: re-encoding the read-back atom reproduces the bytes.
        # (Variable NAMES are synthetic after the trip — identity is positional — so compare BYTES.)
        # ⚠️ BELT AND BRACES, NOT INDEPENDENT EVIDENCE. This fails if two distinct vars were merged
        # (`(g $p $q)` would encode `$ &0`) or if one var were split (`$ $` — different length), which
        # is exactly what the `===` / `!==` assertions above already assert directly. Do not read a
        # green here as separate confirmation of co-reference; read those.
        @test MeTTaCore.atom_to_expr(back).expr.buf == MeTTaCore.atom_to_expr(a).expr.buf
    end
end
