# How a WFS bottom (⊥) travels through the interpreter — the two properties that a corpus can only
# test end-to-end, pinned directly.
#
# 🔴 BOTH OF THESE WERE WRONG UNTIL 2026-08-18, and the symptom was four XSB gold programs
# (p15/p17/p26/p27) reporting every atom UNDEFINED where upstream says some are TRUE and the rest
# FALSE. The cause was NOT in the SLG engine — the alternating fixpoint was correct throughout — but
# in two absorbing sites here, which truncated rule bodies so the tabling engine never saw the full
# component. See `tabling/upstream/test_xsb_wfs_corpus.jl` for the full account.
#
# The distinction that matters: STRICT operations absorb a bottom (`1 + ⊥ = ⊥` — you cannot add an
# unknown); CONSTRUCTORS and CONTROL forms do not, because `(f ⊥)` is a perfectly good TERM and
# binding a variable to ⊥ is a perfectly good match.

using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const _WP = Eval

"A space with a paradox `(para)` — the only way to obtain a genuine ⊥ VALUE — plus a marker."
function _wp_space()
    _WP.untable_all!(); _WP.abolish_all_tables!()
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, raw"(= (para) (tnot (para)))" * "\n" *
                   raw"(= (marker) True)" * "\n" *
                   raw"(= (ignore1 $x) (marker))" * "\n" *
                   raw"(= (useit $x) $x)" * "\n")
    _WP.table!(:para)
    s
end

_wp_run(s, src) = load_metta!(s, src * "\n")
_wp_undef(xs) = !isempty(xs) && all(_WP.is_undefined, xs)

@testset "WFS ⊥ propagation — constructors and control forms must NOT absorb" begin
    s = _wp_space()
    try
        # ANTI-VACUITY: without a real bottom every claim below is about nothing.
        @test _wp_undef(_wp_run(s, "!(para)"))

        # 🔴 A RULE THAT IGNORES ITS ARGUMENT MUST STILL FIRE. This is the whole defect in one line:
        # the interpreter rebuilds a reduced expression with `cons-atom`, and while `cons_atom` ran
        # `propagated_undefined` on its arguments, ONE undefined argument collapsed the rebuilt
        # expression before the rule could be applied.
        @test _wp_run(s, raw"!(ignore1 (para))") == Atom[Sym("True")]
        @test _wp_run(s, raw"!(ignore1 (ignore1 (para)))") == Atom[Sym("True")]

        # …and a rule that RETURNS its argument must still be undefined — absorbing was wrong, but so
        # would be laundering. This is the half that proves the fix did not simply delete propagation.
        @test _wp_undef(_wp_run(s, raw"!(useit (para))"))

        # STRICT ops keep absorbing: you cannot add an unknown.
        @test _wp_undef(_wp_run(s, raw"!(+ 1 (para))"))

        # `let` is `(unify $atom $pattern $template Empty)` (stdlib.metta:153), so a bottom bound to a
        # bare variable must bind and the body must run. This is Prolog's "delay and continue" for the
        # conjunction encoding, and without it a body stops at its first undefined literal.
        @test _wp_run(s, raw"!(let $x (para) (marker))") == Atom[Sym("True")]
    finally
        _WP.untable_all!(); _WP.abolish_all_tables!()
    end
end

@testset "WFS ⊥ propagation — unify must not launder ⊥ into the else branch" begin
    s = _wp_space()
    try
        # 🔴 THE PROPERTY THE ORIGINAL CHECK EXISTED FOR, and which the narrowing had to preserve.
        # `unify` is a CONTROL instruction: it picks `then` or `else`. Given ⊥ and a CONCRETE pattern
        # nothing matches — and concluding `else` would convert "we do not know" into "we know it is
        # the else case". It must return the bottom instead.
        #
        # ⚠️ `let` IS REQUIRED TO CREATE THE CONDITION, and this cost three wrong probes: `unify` takes
        # its arguments UNEVALUATED, and `chain` binds the UNREDUCED atom (traced: satom=(para),
        # undef=false). Only `let` reaches `unify` with a reduced argument. A version of this test
        # written with `chain` passes while testing nothing.
        @test _wp_undef(_wp_run(s, raw"!(let $b (para) (unify $b (SomeConcreteThing) Then Else))"))

        # …while a BARE VARIABLE pattern matches a bottom, which is a legitimate binding, not a
        # laundering. These two assertions are the whole boundary.
        @test _wp_run(s, raw"!(let $b (para) (unify $b $v Then Else))") == Atom[Sym("Then")]

        # definite values are untouched by any of this
        @test _wp_run(s, raw"!(unify (Foo) (Foo) Then Else)") == Atom[Sym("Then")]
        @test _wp_run(s, raw"!(unify (Foo) (Bar) Then Else)") == Atom[Sym("Else")]
    finally
        _WP.untable_all!(); _WP.abolish_all_tables!()
    end
end
