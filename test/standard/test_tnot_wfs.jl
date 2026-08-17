# WFS tabled negation (`tnot`) — SLG stratified negation + an HONEST `undefined` third truth value.
# Verified against the SWI-Prolog 9.0.4 differential oracle in test/oracle/wfs/*.pl (win/move game,
# p:-tnot(p) paradox, a strictly-2-valued stratified control). The interpreter classifies a tabled goal's
# COMPLETE answer set three ways: a real answer ⇒ ¬G false (Empty); only-`undefined` ⇒ ¬G undefined; no
# answers ⇒ ¬G true. The WFS `undefined` value is an OUT-OF-BAND Grounded sentinel (Eval.UNDEFINED),
# NOT a `Sym("undefined")` — the last testset is the regression that a user datum named `undefined` no longer
# collides with the truth value (the Hazard-A soundness bug).
using MeTTaCore.Eval
using MeTTaCore.StandardMeTTa
using Test

const U = Eval.UNDEFINED               # WFS bottom / third truth value (out-of-band sentinel)

# load a program then run one query, on a fresh space with global tabling reset (tabling state is global).

# 🔴 THE BOTTOM IS RESIDUATED SINCE 2026-08-17 (roadmap 7.A), SO EQUALITY TO `UNDEFINED` IS NO LONGER
# THE RIGHT TEST. `WFSBottom` now carries the DNF of literals it is waiting on, so a bottom produced
# by a real derivation is NOT `==` to the bare constant — `Atom[undefined] == Atom[U]` fails while
# both print "undefined". That was the predicted fallout of the sweep, and it is a TEST-LAYER
# instance of the same defect the sweep fixed in src: `== UNDEFINED` was always a TYPE test wearing a
# value test's clothes.
#
# This file compares TRUTH VALUES, not reasons — the residual is `test_delays.jl`'s subject — so the
# harness canonicalises every bottom to the bare constant on the way out. That keeps each assertion
# below reading as it did and confines the change to one place, rather than rewriting 17 comparisons
# into something less legible. `[[feedback_recurring_defect_derive_the_rule]]`
_wfs_canonical(xs::Vector{Atom})::Vector{Atom} =
    Atom[Eval.is_undefined(x) ? Eval.UNDEFINED : x for x in xs]

function _wfs(prog::AbstractString, query::AbstractString)::Vector{Atom}
    Eval.untable_all!()
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, prog)
    _wfs_canonical(load_metta!(s, query))
end

@testset "WFS tnot — stratified negation + honest undefined (swipl-oracle verified)" begin
    # ── Program B — the paradox  p :- tnot(p)  ⇒ undefined ─────────────────────────
    prB = "!(table! p) (= (p) (tnot (p)))"
    @test _wfs(prB, "!(p)") == Atom[U]

    # ── Program A — win/move game. WON=[True], LOST=[] (empty), DRAW=[undefined].
    #    moves a→b g→h f→g (chains), c→c self-loop, d↔e 2-cycle; b,h are sinks (LOST). ──
    prA = raw"""
        !(table! win)
        (move a b) (move g h) (move f g) (move c c) (move d e) (move e d)
        (= (win $x) (match &self (move $x $y) (tnot (win $y))))
    """
    win(x) = _wfs(prA, "!(win $x)")
    @test win("a") == Atom[Sym("True")]       # WON — moves to sink b
    @test win("g") == Atom[Sym("True")]       # WON — moves to sink h
    @test isempty(win("b"))                   # LOST — sink
    @test isempty(win("f"))                   # LOST — only move is to WON g
    @test isempty(win("h"))                   # LOST — sink
    @test win("c") == Atom[U]                 # DRAW — self-loop c→c
    @test win("d") == Atom[U]                 # DRAW — d↔e
    @test win("e") == Atom[U]                 # DRAW — d↔e

    # ── Program C — stratified control. MUST be strictly 2-valued (never undefined). ──
    prC = "!(table! p) !(table! s) (= (p) yes) (= (q) (tnot (p))) (= (t) (tnot (s)))"
    @test _wfs(prC, "!(p)") == Atom[Sym("yes")]
    @test isempty(_wfs(prC, "!(q)"))                   # p provably true  ⇒ ¬p false
    @test _wfs(prC, "!(t)") == Atom[Sym("True")]       # s fails          ⇒ ¬s true
    @test !any(==(U), _wfs(prC, "!(q)"))               # no undefined leak in a stratified program
    @test !any(==(U), _wfs(prC, "!(t)"))

    # ── two-stable-model  pp:-tnot(qq). qq:-tnot(pp)  ⇒ both undefined ──────────────
    pr2 = "!(table! pp) !(table! qq) (= (pp) (tnot (qq))) (= (qq) (tnot (pp)))"
    @test _wfs(pr2, "!(pp)") == Atom[U]
    @test _wfs(pr2, "!(qq)") == Atom[U]

    # ── WFS Stage B increment 2 — canonical dynamically-stratified SCC (Van Gelder alternating fixpoint).
    #    A POSITIVE cycle (g2:-g1) fused with a negative edge (g1:-tnot(g2)); g2 is founded TRUE via tnot(g3)
    #    INDEPENDENT of the loop, so g1 is FALSE. swipl 9.0.4 WFS (verified): g1=false, g2=true(unconditional),
    #    g3=false. Pre-inc-2 Core returned g1=undefined (the tnot-taint over-conservatism). g1-as-entry builds
    #    the {g1,g2} SCC via the positive g2:-g1 consumer edge ⇒ _wfs_complete! ⇒ FALSE. ──
    prG = raw"""
        !(table! g1) !(table! g2) !(table! g3)
        (= (g1) (tnot (g2)))
        (= (g1) (g3))
        (= (g2) (tnot (g3)))
        (= (g2) (g1))
        (= (g2) (g2))
    """
    @test isempty(_wfs(prG, "!(g1)"))                       # g1 FALSE (was Atom[U] before Stage B inc-2)
    Eval.untable_all!()
    sG = Space(); load_core_stdlib!(sG); load_metta!(sG, prG)
    @test isempty(load_metta!(sG, "!(g1)"))                 # FALSE
    @test load_metta!(sG, "!(g2)") == Atom[Sym("True")]     # TRUE (cached member of the completed SCC)
    @test isempty(load_metta!(sG, "!(g3)"))                 # FALSE (no rule)

    # ── REGRESSION (Hazard A): a user datum literally named `undefined` must NOT collide with the WFS truth
    #    value. `foo` reduces to the SYMBOL `undefined`; tnot(foo) must see foo as provably-true ⇒ EMPTY
    #    (false), NOT `undefined`. Before UNDEFINED became an out-of-band Grounded sentinel this returned
    #    [undefined] — an unsound 2-valued→3-valued mislabel. ──
    prCol = "!(table! foo) (= (foo) undefined) (= (barc) (tnot (foo)))"
    @test _wfs(prCol, "!(foo)") == Atom[Sym("undefined")]   # the datum survives as a plain Sym …
    @test Sym("undefined") != U                             # … which is DISTINCT from the truth value
    @test isempty(_wfs(prCol, "!(barc)"))                   # ¬foo is FALSE (foo has a real answer)
end

@testset "WFS tnot — UNDEFINED propagates through strict grounded ops (soundness)" begin
    # A strict grounded op (arithmetic/comparison) fed the WFS `undefined` sentinel must PROPAGATE it, not
    # leave a stuck term a downstream tnot misreads as a real answer. Confirmed hole (2026-07-08, upstream
    # conformance audit): `(+ 1 (tnot u))` used to stick as `(+ 1 undefined)` ⇒ tnot of it returned Empty
    # (unsound); the guard in _num_binop/_num_cmp now propagates UNDEFINED ⇒ tnot correctly stays undefined.
    U0 = "!(table! u) !(table! g) (= (u) (tnot (u)))"       # u :- ¬u  ⇒ u = undefined
    @test _wfs(U0 * " (= (g) (+ 1 (tnot (u))))", "!(g)") == Atom[U]         # (+ 1 undefined) ⇒ undefined
    @test _wfs(U0 * " (= (g) (+ 1 (tnot (u))))", "!(tnot (g))") == Atom[U]  # ¬g undefined (was Empty — the bug)
    @test _wfs(U0 * " (= (g) (< (tnot (u)) 2))", "!(tnot (g))") == Atom[U]  # (< undefined 2) ⇒ undefined
    # the fix must trigger ONLY on the sentinel — normal arithmetic/comparison is unchanged:
    @test _wfs("", "!(+ 1 2)") == Atom[Grounded(3)]
    @test _wfs("", "!(< 1 2)") == Atom[Sym("True")]
    @test _wfs("", "!(< 3 2)") == Atom[Sym("False")]
    # systemic fix (2026-07-08 grounded-op audit): the sentinel is contagious through EVERY strict grounded op,
    # not just arithmetic — boolean / equality / case / list / math-library all propagate it now.
    @test _wfs(U0 * " (= (g) (not (tnot (u))))", "!(g)") == Atom[U]              # ¬⊥ = ⊥
    @test _wfs(U0 * " (= (g) (and (tnot (u)) True))", "!(g)") == Atom[U]         # and/or propagate (sound; full Kleene deferred)
    @test _wfs(U0 * " (= (g) (or (tnot (u)) False))", "!(g)") == Atom[U]
    @test _wfs(U0 * " (= (g) (== (tnot (u)) 1))", "!(g)") == Atom[U]             # == contagious (no fabricated False)
    @test _wfs(U0 * " (= (g) (case (tnot (u)) ((\$x hit))))", "!(g)") == Atom[U]  # case: no catch-all launder
    @test _wfs(U0 * " (= (g) (size-atom (tnot (u))))", "!(g)") == Atom[U]        # list op
    @test _wfs(U0 * " (= (g) (sqrt-math (tnot (u))))", "!(g)") == Atom[U]        # math library (was the Error-atom class)
    # normal grounded ops UNAFFECTED (fix triggers ONLY on the out-of-band sentinel):
    @test _wfs("", "!(and True False)") == Atom[Sym("False")]
    @test _wfs("", "!(not True)") == Atom[Sym("False")]
    @test _wfs("", "!(size-atom (a b c))") == Atom[Grounded(3)]
end
