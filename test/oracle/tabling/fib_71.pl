% fib_71.pl — SWI-Prolog manual §7.1 "Example 1: using tabling for memoizing".
%
% THE ORACLE for Core's `table!` on the memoizing case. Prints one line per goal:
%     fib(20) => 6765
% which `test_tabling_swipl_differential.jl` parses and compares against Core's
% `!(fib N)` under `table!(:fib)`.
%
% Base cases are fib(0)=0, fib(1)=1 so the relation matches the MeTTa side's
% `(if (< $n 2) $n …)` exactly — a differential is only meaningful if BOTH sides
% compute the same function.
%
% ⚠️ WITHOUT `:- table fib/2` this is exponential and the larger goals do not
% finish; that is the property §7.1 exists to demonstrate, and it is why the
% MeTTa side must be tabled too for the comparison to be like-for-like.

:- table fib/2.

fib(0, 0).
fib(1, 1).
fib(N, F) :-
    N > 1,
    N1 is N-1,
    N2 is N-2,
    fib(N1, F1),
    fib(N2, F2),
    F is F1+F2.

report(N) :-
    fib(N, F),
    format("fib(~w) => ~w~n", [N, F]).

main :-
    forall(member(N, [0, 1, 2, 5, 10, 20, 25, 30]), report(N)),
    halt(0).

:- initialization(main).
