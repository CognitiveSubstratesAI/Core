% conn_72.pl — SWI-Prolog manual §7.2 "Example 2: avoiding non-termination".
%
% THE ORACLE for the property §7.2 exists to demonstrate: a LEFT-RECURSIVE and
% SYMMETRIC relation that does NOT terminate under plain SLD resolution, but does
% under tabling.
%
%     connection(X, Y) :- connection(Y, X).            % symmetric  — infinite under SLD
%     connection(X, Y) :- connection(X, Z), connection(Z, Y).   % LEFT-recursive — infinite under SLD
%
% Prints one line per reachable pair, sorted, then `count => 16`.
%
% 🔴 WHAT THE DIFFERENTIAL ACTUALLY USES, corrected 2026-08-16 — an earlier version
% of this header said "the differential compares as a SET against Core's answers".
% IT DOES NOT, and must not:
%
%   * THIS FILE AND THE MeTTa SIDE ARE DIFFERENT PROGRAMS. Here: 4 edge facts and
%     both the symmetric and the transitive rule. There: 2 edges and the symmetric
%     rule only. The closures cannot match, and were never meant to.
%   * §7.2 is a TERMINATION property, so it is asserted as one. The `count => 16`
%     line is used as a POSITIVE CONTROL — under plain SLD this program does not
%     finish at all, so the mere existence of that line IS §7.2 holding on the
%     Prolog side. §7.1 (fib_71.pl) is where exact VALUE agreement is asserted.
%
% See the "WHAT IS AND IS NOT COMPARED" header of
% `test/standard/test_tabling_swipl_differential.jl`, which is authoritative.
%
% (Set-vs-multiset is a separate matter: tabling is set-semantics by design in every
% implementation, and where MeTTa's MULTISET semantics differs is roadmap 2.0, pinned
% by its own test. Not re-litigated here.)
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
