% translate_corpus.pl — turn one XSB wfs_tests program into MeTTa, or REFUSE it.
%
% ─── WHY PROLOG PARSES THIS AND NOT A REGEX ──────────────────────────────────────────────────────
% The clauses are real Prolog terms. A regex handles `p :- q, tnot(r).` and then quietly mangles
% `win(A) :- m(A,B), tnot(win(B)).` — and a WRONG TRANSLATOR IS THE WORST ARTIFACT AVAILABLE HERE,
% because its output looks like conformance evidence. `read_term/3` is exact and we have the binary.
%
% ─── THE MAPPING ─────────────────────────────────────────────────────────────────────────────────
%   :- table p/0.          declaration      ->  collected, emitted as TABLED
%   q.                     0-arity fact     ->  (= (q) True)
%   p :- fail.             always fails     ->  CLAUSE DROPPED (an empty table IS "false")
%   p :- tnot(r).          negation         ->  (= (p) (tnot (r)))
%   p :- q, tnot(r).       conjunction      ->  (= (p) (let $c1 (q) (tnot (r))))
%   p :- q.  p :- r.       disjunction      ->  two rules, same head
%
% Conjunction is `let`, not `and`: in MeTTa a subterm producing nothing makes the whole expression
% produce nothing, which IS Prolog's "both must hold", with no truth table to get wrong. Each `let`
% gets a DISTINCT binder so a nest cannot shadow itself.
%
% ─── WHAT IT REFUSES, AND WHY REFUSING IS THE POINT ──────────────────────────────────────────────
% A body literal on a predicate that is NOT tabled is DATA — `m(A,B)` in the win/1 graphs — and it
% translates to a binding `(match &self ...)`, not a call. That form is correct but it is a second
% translation path with its own failure modes, so this program does not guess at it: it prints
% REFUSED and says why. Those programs are hand-translated and reviewed instead.
% Same for anything else unexpected. A translator that silently emits SOMETHING for input it does
% not understand converts a parse failure into a wrong conformance result.
:- initialization(main, main).

:- dynamic tabled/2.

main([File]) :-
    retractall(tabled(_,_)),
    catch(run(File), E, (message_to_codes(E), fail)).
main(_) :- true.

message_to_codes(E) :- print_message(error, E).

run(File) :-
    read_clauses(File, Clauses),
    collect_tabled(Clauses),
    findall(S, (member(C, Clauses), clause_metta(C, S)), Ss),
    ( memberchk(refused(Why), Ss)
    -> format("REFUSED\t~w~n", [Why])
    ;  exclude(==(skip), Ss, Keep),
       atomic_list_concat(Keep, '\\n', Prog),
       findall(T, tabled(T,_), Ts0), sort(Ts0, Ts),
       atomic_list_concat(Ts, ',', TabS),
       % 🔑 THE GOLD SETS COME OUT OF THE SAME PASS AS THE PROGRAM, in the same notation. Emitting
       % them separately is how a program and its expectation drift apart, and a drifted expectation
       % is indistinguishable from a passing test.
       ( member(query(_,_,SGs,TS,US), Clauses)
       -> goals_metta(SGs, GS), goals_metta(TS, TSS), goals_metta(US, USS)
       ;  GS = '', TSS = '', USS = '' ),
       format("OK\t~w\t~w\t~w\t~w\t~w~n", [TabS, Prog, GS, TSS, USS])
    ).

% a gold set is a list of goal TERMS; render each the way the program renders calls, then join.
goals_metta(L, S) :-
    copy_term(L, L2), numbervars(L2, 0, _),
    findall(X, (member(G, L2), term_metta(G, X)), Xs),
    atomic_list_concat(Xs, ',', S).

read_clauses(File, Cs) :-
    setup_call_cleanup(open(File, read, S),
                       read_all(S, Cs),
                       close(S)).
read_all(S, Out) :-
    read_term(S, T, []),
    ( T == end_of_file -> Out = []
    ; Out = [T|Rest], read_all(S, Rest) ).

collect_tabled(Cs) :-
    forall(( member((:- table Spec), Cs), spec_member(Spec, N/A) ),
           ( tabled(N,A) -> true ; assertz(tabled(N,A)) )).
spec_member((A,B), X) :- !, ( spec_member(A, X) ; spec_member(B, X) ).
spec_member(N/A, N/A).

% ─── clause -> MeTTa ─────────────────────────────────────────────────────────────────────────────
clause_metta((:- _), skip) :- !.
clause_metta(query(_,_,_,_,_), skip) :- !.
clause_metta(Clause, Out) :-
    ( Clause = (H :- B) -> true ; H = Clause, B = true ),
    copy_term(H-B, H2-B2),
    numbervars(H2-B2, 0, _),
    (  contains_fail(B2)
    -> Out = skip                                   % `p :- fail.` contributes nothing
    ;  head_metta(H2, HS)
    -> ( body_metta(B2, BS)
       -> format(atom(Out), "(= ~w ~w)", [HS, BS])
       ;  Out = refused('body literal on a non-tabled predicate (data), needs the match form') )
    ;  Out = refused('head is not a tabled predicate') ).

contains_fail((A,B)) :- !, ( contains_fail(A) ; contains_fail(B) ).
contains_fail(fail).

head_metta(H, S) :- functor(H, N, A), tabled(N, A), term_metta(H, S).

body_metta(true, "True") :- !.                      % a bare fact: `q.` -> (= (q) True)
body_metta(B, S) :-
    conj_list(B, Ls),
    lits_metta(Ls, 1, S).

conj_list((A,B), [A|T]) :- !, conj_list(B, T).
conj_list(A, [A]).

lits_metta([L], _, S) :- !, lit_metta(L, S).
lits_metta([L|Ls], N, S) :-
    lit_metta(L, LS),
    N1 is N+1,
    lits_metta(Ls, N1, RS),
    format(atom(S), "(let $c~w ~w ~w)", [N, LS, RS]).

lit_metta(tnot(G), S) :- !, term_metta(G, GS), format(atom(S), "(tnot ~w)", [GS]).
lit_metta(L, S) :- functor(L, N, A), tabled(N, A), term_metta(L, S).
%  anything else is DATA and needs the binding match form — deliberately unhandled, see the header.

% a term becomes a MeTTa expression; '$VAR'(N) becomes a MeTTa variable
term_metta('$VAR'(N), S) :- !, format(atom(S), "$v~w", [N]).
term_metta(T, S) :- atom(T), !, format(atom(S), "(~w)", [T]).
term_metta(T, S) :-
    compound(T), T =.. [F|Args],
    maplist(term_metta_arg, Args, As),
    atomic_list_concat(As, ' ', ArgS),
    format(atom(S), "(~w ~w)", [F, ArgS]).

% arguments are NOT wrapped in parens — `win(a)` is `(win a)`, not `(win (a))`
term_metta_arg('$VAR'(N), S) :- !, format(atom(S), "$v~w", [N]).
term_metta_arg(T, S) :- atom(T), !, S = T.
term_metta_arg(T, S) :- term_metta(T, S).
