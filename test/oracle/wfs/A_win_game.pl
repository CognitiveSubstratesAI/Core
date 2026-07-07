% ===================================================================
% WFS ORACLE — Program A: win/move game (tabled negation)
% SWI-Prolog well-founded semantics conformance oracle.
% ===================================================================
:- use_module(library(wfs)).      % call_delays/2, delays_residual_program/2

:- table win/1.
win(X) :- move(X, Y), tnot(win(Y)).

% ---- Move graph -------------------------------------------------
% WON/LOST chain (stratified, two-valued):
%   b : sink (no outgoing move)  => LOST  (win(b) = false)
%   a -> b                       => WON   (win(a) = true)
%   h : sink                     => LOST  (win(h) = false)
%   g -> h                       => WON   (win(g) = true)
%   f -> g   (g is WON)          => LOST  (win(f) = false)
move(a, b).
move(g, h).
move(f, g).

% DRAW self-loop (negative 1-cycle) => UNDEFINED:
%   c -> c
move(c, c).

% DRAW 2-cycle (negative 2-cycle) => UNDEFINED:
%   d <-> e
move(d, e).
move(e, d).

% ---- Classifier: true / false / undefined under WFS -------------
% call_delays(Goal, Delays): Goal true & Delays==true  => unconditional TRUE
%                            Goal true & Delays\==true  => UNDEFINED (has delays)
%                            Goal fails                 => FALSE
classify(Goal, Result) :-
    (   call_delays(Goal, Delays)
    ->  (   Delays == true
        ->  Result = true
        ;   Result = undefined
        )
    ;   Result = false
    ).

report(Goal) :-
    classify(Goal, R),
    format("~w~t~20|=> ~w~n", [Goal, R]).

main :-
    format("=== Program A: win/move game (WFS) ===~n"),
    forall(member(P, [a,b,c,d,e,f,g,h]), report(win(P))),
    nl,
    format("--- raw residual (undefined) programs ---~n"),
    forall(member(P, [c,d]),
        (   call_delays(win(P), Delays),
            Delays \== true
        ->  format("win(~w) residual:~n", [P]),
            delays_residual_program(Delays, Clauses),
            forall(member(Cl, Clauses), (print(Cl), nl))
        ;   true
        )),
    halt.

:- initialization(main).
