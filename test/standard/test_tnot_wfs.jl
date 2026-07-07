# WFS tabled negation (`tnot`) — SLG stratified negation + an HONEST `undefined` third truth value.
# Verified against the SWI-Prolog 9.0.4 differential oracle in test/oracle/wfs/*.pl (win/move game,
# p:-tnot(p) paradox, a strictly-2-valued stratified control). The interpreter classifies a tabled goal's
# COMPLETE answer set three ways: a real answer ⇒ ¬G false (Empty); only-`undefined` ⇒ ¬G undefined; no
# answers ⇒ ¬G true. The WFS `undefined` value is an OUT-OF-BAND Grounded sentinel (Interpreter.UNDEFINED),
# NOT a `Sym("undefined")` — the last testset is the regression that a user datum named `undefined` no longer
# collides with the truth value (the Hazard-A soundness bug).
using MeTTaCore.Interpreter
using MeTTaCore.Interpreter.StandardMeTTa
using Test

const U = Interpreter.UNDEFINED               # WFS bottom / third truth value (out-of-band sentinel)

# load a program then run one query, on a fresh space with global tabling reset (tabling state is global).
function _wfs(prog::AbstractString, query::AbstractString)::Vector{Atom}
    Interpreter.untable_all!()
    s = Space(); load_core_stdlib!(s)
    load_metta!(s, prog)
    load_metta!(s, query)
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

    # ── REGRESSION (Hazard A): a user datum literally named `undefined` must NOT collide with the WFS truth
    #    value. `foo` reduces to the SYMBOL `undefined`; tnot(foo) must see foo as provably-true ⇒ EMPTY
    #    (false), NOT `undefined`. Before UNDEFINED became an out-of-band Grounded sentinel this returned
    #    [undefined] — an unsound 2-valued→3-valued mislabel. ──
    prCol = "!(table! foo) (= (foo) undefined) (= (barc) (tnot (foo)))"
    @test _wfs(prCol, "!(foo)") == Atom[Sym("undefined")]   # the datum survives as a plain Sym …
    @test Sym("undefined") != U                             # … which is DISTINCT from the truth value
    @test isempty(_wfs(prCol, "!(barc)"))                   # ¬foo is FALSE (foo has a real answer)
end
