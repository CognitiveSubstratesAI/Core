% ===================================================================
% WFS ORACLE — Program C: STRATIFIED negation (no negative cycle).
% Contrast case: every atom is cleanly true/false, NEVER undefined.
% reachable/1 : positive recursion (tabled).
% unreachable/1 : negation applied to a LOWER stratum (reachable),
%                 so no negative cycle exists.
% ===================================================================
:- use_module(library(wfs)).

edge(a, b).
edge(b, c).
% node d is isolated (not reachable from a)
node(a). node(b). node(c). node(d).

:- table reachable/1.
reachable(a).
reachable(X) :- edge(Y, X), reachable(Y).

:- table unreachable/1.
unreachable(X) :- node(X), tnot(reachable(X)).

classify(Goal, Result) :-
    (   call_delays(Goal, Delays)
    ->  (   Delays == true -> Result = true ; Result = undefined )
    ;   Result = false
    ).

report(Goal) :-
    classify(Goal, R),
    format("~w~t~24|=> ~w~n", [Goal, R]).

main :-
    format("=== Program C: stratified negation (WFS) ===~n"),
    format("- reachable/1 -~n"),
    forall(member(N, [a,b,c,d]), report(reachable(N))),
    nl,
    format("- unreachable/1 -~n"),
    forall(member(N, [a,b,c,d]), report(unreachable(N))),
    halt.

:- initialization(main).
