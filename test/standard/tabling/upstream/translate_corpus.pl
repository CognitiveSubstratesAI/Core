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
:- dynamic has_rule/2.

main([File]) :-
    retractall(tabled(_,_)), retractall(has_rule(_,_)),
    catch(run(File), E, (message_to_codes(E), fail)).
main(_) :- true.

message_to_codes(E) :- print_message(error, E).

run(File) :-
    read_clauses(File, Clauses),
    collect_tabled(Clauses),
    collect_rules(Clauses),
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

% 🔴 "IS IT DATA?" IS NOT "IS IT TABLED" — corrected 2026-08-19 while generalising the match form.
% A predicate with only FACTS (`q(a,b).`) is DATA: a body literal on it BINDS by lookup, so it becomes
% `(match &self ...)`. A predicate with a RULE is a CALL even when it is not tabled — p31's
% `p(_A) :- r.` is exactly that, and matching it would look for facts that do not exist and silently
% find nothing. Tabling is an orthogonal DECLARATION, not what makes something callable.
collect_rules(Cs) :-
    forall(( member(C, Cs), C = (H :- _), callable(H), functor(H, N, A) ),
           ( has_rule(N,A) -> true ; assertz(has_rule(N,A)) )).
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
    ;  is_data_pred(H2), B2 == true
    -> term_metta(H2, Out)                          % a DATA fact: emit the atom itself, not a rule
    ;  term_var_nums(H2, HeadVars), body_metta(B2, BS, HeadVars)
    -> term_metta(H2, HS), format(atom(Out), "(= ~w ~w)", [HS, BS])
    ;  Out = refused('clause shape not handled') ).

% DATA = NOT tabled AND has no rule anywhere in the program.
% ⚠️ BOTH CONDITIONS. A first cut tested only "has no rule" and broke p06: `q.` is a TABLED fact, so
% it was emitted as the bare atom `(q)` instead of the rule `(= (q) True)`, and a tabled call to it
% then had nothing to reduce. A tabled predicate is ALWAYS a call — that is what `:- table` declares.
is_data_pred(H) :- callable(H), functor(H, N, A), \+ tabled(N, A), \+ has_rule(N, A).

contains_fail((A,B)) :- !, ( contains_fail(A) ; contains_fail(B) ).
contains_fail(fail).

head_metta(H, S) :- functor(H, N, A), tabled(N, A), term_metta(H, S).

body_metta(true, "True", _) :- !.                   % a bare fact: `q.` -> (= (q) True)
body_metta(B, S, HeadVars) :-
    conj_list(B, Ls),
    lits_metta(Ls, 1, HeadVars, S).

conj_list((A,B), [A|T]) :- !, conj_list(B, T).
conj_list(A, [A]).

% ─── the body, left to right, threading the set of ALREADY-BOUND variables ───────────────────────
% 🔴 THIS IS WHAT THE TRANSLATOR REFUSED TO GUESS AT until 2026-08-19. A body literal on a NON-tabled
% predicate is DATA: `q(A,C)` does not CALL anything, it looks a fact up and BINDS `C`. So it becomes
% a binding `match` whose `let` binder carries the newly-bound variables, not a call.
%
% Which variables are new is the whole difficulty, and it is why goals are asked GROUND: with a ground
% goal every head variable is already bound, so the ONLY new variables come from data literals, and a
% single left-to-right pass with a seen-set is exact. (Upstream's gold rows list per-instance goals —
% `r(a,b)`, `r(a,c)` — so nothing is lost by asking them ground.)
lits_metta([L], N, Seen, S) :- !, lit_metta(L, N, Seen, _, S).
lits_metta([L|Ls], N, Seen, S) :-
    lit_metta(L, N, Seen, Seen1, LS),
    N1 is N+1,
    lits_metta(Ls, N1, Seen1, RS),
    ( binder_of(L, Seen, Pat), Pat \== none
    -> format(atom(S), "(let ~w ~w ~w)", [Pat, LS, RS])
    ;  format(atom(S), "(let $c~w ~w ~w)", [N, LS, RS]) ).

% tnot: a call, binds nothing (our `tnot` requires a ground goal anyway)
lit_metta(tnot(G), _, Seen, Seen, S) :- !, term_metta(G, GS), format(atom(S), "(tnot ~w)", [GS]).
% anything with a RULE is a CALL — tabled or not (p31's `p(_A) :- r.`)
lit_metta(L, _, Seen, Seen, S) :- functor(L, N, A), (tabled(N,A) ; has_rule(N,A)), !, term_metta(L, S).
% DATA: a binding `match`. New variables become the binder AND the match template.
lit_metta(L, _, Seen, Seen1, S) :-
    term_metta(L, LS),
    new_vars(L, Seen, New),
    append(Seen, New, Seen1),
    ( New == []
    -> format(atom(S), "(match &self ~w True)", [LS])      % no new vars ⇒ a pure TEST
    ;  pat_of(New, Pat), format(atom(S), "(match &self ~w ~w)", [LS, Pat]) ).

% the `let` binder for a literal: its new variables, or `none` when it binds nothing
binder_of(tnot(_), _, none) :- !.
binder_of(L, _, none) :- functor(L, N, A), (tabled(N,A) ; has_rule(N,A)), !.
binder_of(L, Seen, Pat) :- new_vars(L, Seen, New),
    ( New == [] -> Pat = none ; pat_of(New, Pat) ).

pat_of([V], S) :- !, var_metta(V, S).
pat_of(Vs, S) :- findall(X, (member(V, Vs), var_metta(V, X)), Xs),
                 atomic_list_concat(Xs, ' ', Inner), format(atom(S), "(~w)", [Inner]).

var_metta(N, S) :- format(atom(S), "$v~w", [N]).

% every '\$VAR'(N) number in a term, in order, without duplicates
term_var_nums(T, Ns) :- findall(N, sub_var_num(T, N), Ns0), list_to_set(Ns0, Ns).
sub_var_num('$VAR'(N), N).
sub_var_num(T, N) :- compound(T), T \= '$VAR'(_), arg(_, T, A), sub_var_num(A, N).

new_vars(L, Seen, New) :- term_var_nums(L, Ns), subtract(Ns, Seen, New).

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
