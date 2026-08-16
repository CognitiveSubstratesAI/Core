% modes_73.pl — SWI-Prolog manual §7.3 "Answer subsumption / mode-directed tabling".
%
% ORACLE for Core/src/standard/tabling/Aggregation.jl. Exercises the two mode families and the
% built-in aliases against a LIVE swipl, so our port is compared with upstream rather than with our
% own expectations.
%
%   lattice(F/3)  — F(S0,S1,S) merges stored S0 with new S1
%   po(F/2)       — F(S0,S1) TRUE keeps S0        (boot/tabling.pl:1478)
%   aliases       — first / - / last / min / max / sum   (boot/tabling.pl:1503-1508)
%
% Prints `name(args) => value` lines, the format `_swipl_pairs` parses.

:- use_module(library(tabling)).

% ── shortest path: the canonical §7.3 example. Third argument aggregates with min. ───────────────
:- table path(_,_,min).

edge(a, b, 1).
edge(b, c, 2).
edge(a, c, 9).
edge(c, d, 1).

path(X, Y, D)  :- edge(X, Y, D).
path(X, Y, D)  :- path(X, Z, D1), edge(Z, Y, D2), D is D1+D2.

% ── sum aggregation: total weight over all derivations of the same key. ──────────────────────────
:- table tot(_,sum).

item(k, 1).
item(k, 2).
item(k, 4).
item(m, 10).

tot(K, W) :- item(K, W).

% ── max, and a po/2 whose test is @=< (so the STORED value is kept when it precedes). ────────────
:- table best(_,max).
best(K, W) :- item(K, W).

:- table keep(_,po(leq/2)).
leq(A, B) :- A @=< B.
keep(K, W) :- item(K, W).

main :-
    forall(member(Y-D, [b-_, c-_, d-_]),
           ( path(a, Y, D0) -> format("path(a,~w) => ~w~n", [Y, D0]) ; true )),
    ( tot(k, TK)  -> format("tot(k) => ~w~n",  [TK])  ; true ),
    ( tot(m, TM)  -> format("tot(m) => ~w~n",  [TM])  ; true ),
    ( best(k, BK) -> format("best(k) => ~w~n", [BK]) ; true ),
    ( keep(k, KK) -> format("keep(k) => ~w~n", [KK]) ; true ),
    halt(0).

:- initialization(main).
