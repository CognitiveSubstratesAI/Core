% verify_corpus.pl — check each XSB wfs_tests program against its OWN declared query/5 gold row.
%
% Run by verify_corpus.sh. Loads one program in module `m`, then for every subgoal the gold row
% names, asks the live engine for its well-founded truth value and compares.
%
% THE TRUTH-VALUE PROBE, and why it is three-way rather than two:
%   m:S succeeds and m:tnot(S) also succeeds  -> UNDEFINED  (both the goal and its negation hold)
%   m:S succeeds and m:tnot(S) fails          -> TRUE
%   m:S fails                                 -> FALSE
% That middle line is the whole point of WFS: an undefined atom is one where G and tnot(G) are BOTH
% derivable, which no two-valued probe can distinguish from true.
:- initialization(main, main).

tv(M, S, undefined) :- call(M:S), call(M:tnot(S)), !.
tv(M, S, true)      :- call(M:S), !.
tv(_, _, false).

main([File]) :-
    catch(run(File), E, (print_message(error, E), format("ERROR~n"))).

run(File) :-
    use_module(library(dialect/xsb/source)),
    load_files(m:File, [dialect(xsb), silent(true)]),
    m:query(Name, _Goal, SGs, TrueSet, UndefSet),
    findall(S-TV, (member(S, SGs), tv(m, S, TV)), Got),
    findall(S, member(S-true,      Got), GotTrue),
    findall(S, member(S-undefined, Got), GotUndef),
    msort(TrueSet, T0),  msort(GotTrue,  T1),
    msort(UndefSet, U0), msort(GotUndef, U1),
    ( T0 == T1, U0 == U1
    -> format("OK   ~w~n", [Name])
    ;  format("DIFF ~w~n  gold  true=~q undef=~q~n  live  true=~q undef=~q~n",
              [Name, T0, U0, T1, U1])
    ).
