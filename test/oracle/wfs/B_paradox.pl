% ===================================================================
% WFS ORACLE — Program B: the paradigm undefined case  p :- tnot(p).
% Under WFS, p is UNDEFINED (neither true nor false; NOT an error).
% ===================================================================
:- use_module(library(wfs)).

:- table p/0.
p :- tnot(p).

classify(Goal, Result) :-
    (   call_delays(Goal, Delays)
    ->  (   Delays == true -> Result = true ; Result = undefined )
    ;   Result = false
    ).

main :-
    format("=== Program B: p :- tnot(p)  (WFS) ===~n"),
    classify(p, R),
    format("p~t~20|=> ~w~n", [R]),
    nl,
    format("--- residual program for p ---~n"),
    (   call_delays(p, Delays), Delays \== true
    ->  delays_residual_program(Delays, Clauses),
        forall(member(Cl, Clauses), (print(Cl), nl))
    ;   format("(no residual — p is not undefined)~n")
    ),
    halt.

:- initialization(main).
