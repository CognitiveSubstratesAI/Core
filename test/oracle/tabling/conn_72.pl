% conn_72.pl — SWI-Prolog manual §7.2 "Example 2: avoiding non-termination".
%
% THE ORACLE for the property §7.2 exists to demonstrate: a LEFT-RECURSIVE and
% SYMMETRIC relation that does NOT terminate under plain SLD resolution, but does
% under tabling.
%
%     connection(X, Y) :- connection(Y, X).            % symmetric  — infinite under SLD
%     connection(X, Y) :- connection(X, Z), connection(Z, Y).   % LEFT-recursive — infinite under SLD
%
% Prints one line per reachable pair, sorted:
%     conn(amsterdam,haarlem)
% which the differential compares as a SET against Core's answers.
%
% ⚠️ THE SET IS THE POINT, NOT THE ORDER. Tabling is set-semantics by design in
% every implementation (the delimited-control paper dedups in store_answer/2; SWI
% dedups structurally via the answer trie), so both sides must be compared as sets.
% Lower-case atoms so the MeTTa side can use the same symbols verbatim.

:- table connection/2.

connection(X, Y) :- connection(Y, X).
connection(X, Y) :- connection(X, Z), connection(Z, Y).

connection(amsterdam, schiphol).
connection(amsterdam, haarlem).
connection(schiphol,  leiden).
connection(haarlem,   leiden).

main :-
    findall(X-Y, connection(X, Y), Ps0),
    sort(Ps0, Ps),
    forall(member(X-Y, Ps), format("conn(~w,~w)~n", [X, Y])),
    length(Ps, N),
    format("count => ~w~n", [N]),
    halt(0).

:- initialization(main).
