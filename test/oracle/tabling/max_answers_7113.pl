% max_answers_7113.pl — SWI-Prolog manual §7.11.3, the `max_answers(Count)` restraint.
%
% ORACLE for Core/src/standard/tabling/Restraints.jl.
%
% 🔴 THE POINT OF THIS ORACLE, and it corrected our port. A bound of 2 over four derivable answers
% does NOT yield two answers. It yields THREE:
%
%     answers => [2,1,_G]     count => 3
%
% The third is a FREE VARIABLE. The per-predicate restraint triggers `bounded_rationality`, which
% deletes the offending answer and calls `generalise_answer_substitution` (pl-tabling.c:3641-3654),
% replacing the truncated remainder with the most general term — one that SUBSUMES every answer the
% bound stopped computing — and marks the table with `answer_count_restraint`.
%
% So the restraint converts an exact answer set into a sound OVER-approximation. An implementation
% that simply DROPS the excess produces a silently INCOMPLETE table: the opposite direction, and
% unsound for any consumer reading absence as failure. Ours dropped until this oracle was run.
%
% Note the answer ORDER is [2,1,...] — tabled answer order is not the derivation order, so the
% differential compares as a SET plus the count, never positionally.

:- use_module(library(tabling)).

:- table p/1 as max_answers(2).

q(1).
q(2).
q(3).
q(4).

p(X) :- q(X).

main :-
    findall(X, p(X), Xs),
    length(Xs, N),
    % how many of the answers are still unbound (the generalised one)?
    include(var, Xs, Vars),
    length(Vars, NV),
    include(nonvar, Xs, Ground),
    msort(Ground, GroundS),
    format("count => ~w~n", [N]),
    format("ground => ~w~n", [GroundS]),
    format("general => ~w~n", [NV]),
    halt(0).

:- initialization(main).
