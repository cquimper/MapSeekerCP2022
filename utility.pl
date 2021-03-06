/*
    The contents of this file are subject to the Mozilla Public License
    Version  1.1  (the "License"); you may not use this file except in
    compliance with the License. You may obtain a copy of the License at:

    http://www.mozilla.org/MPL/
*/

% Purpose: List utilities and constraint term creation utilities
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(utility,[gen_sum_term/3,
                   length_same_prefix/2,
                   memberchks/2,
                   eq_memberchks/2,
                   sum_prod_after/2,
                   remove_values/3,
                   same_args/4,
                   write_list/2]).

:- use_module(library(lists)).

gen_sum_term([], _, 0) :- !.
gen_sum_term([V|R], var, V+S) :- !,
    gen_sum_term(R, var, S).
gen_sum_term([V|R], var_neq(Val), (V #\= Val) + S) :-
    gen_sum_term(R, var_neq(Val), S).

length_same_prefix([], 0) :- !.
length_same_prefix([V|R], Res) :-
    length_same_prefix(R, V, 1, Res).

length_same_prefix([V|R], V, Cur, Res) :- !,
    Next is Cur+1,
    length_same_prefix(R, V, Next, Res).
length_same_prefix(_, _, Res, Res).

memberchks([], _) :- !.
memberchks([V|R], L) :-
    memberchk(V, L),
    memberchks(R, L).

eq_memberchks(L1, L2) :-
    length(L1, N),
    length(L2, N),
    memberchks(L1, L2).

sum_prod_after(L, Res) :-
    sliding_sum(L, 0, S),
    sum_prod_after(L, S, 0, Res).

sliding_sum([], _, []) :- !.
sliding_sum([X|R], Prev, [Y|S]) :-
    Y is Prev + X,
    sliding_sum(R, Y, S).

sum_prod_after([], _, Res, Res) :- !.
sum_prod_after([X|R], [Y|S], Prev, Res) :-
    Cur is Prev + X*Y,
    sum_prod_after(R, S, Cur, Res).

remove_values([Value|R], Value, S) :- !,
    remove_values(R, Value, S).
remove_values(L, _, L).

same_args(I, N, _, _) :-
    I > N, !.
same_args(I, N, Term1, Term2) :-
    arg(I, Term1, V),
    arg(I, Term2, V),
    I1 is I+1,
    same_args(I1, N, Term1, Term2).

write_list([], _) :- !.
write_list([P|R], Sout) :-
    format(Sout,'~w.~n',[P]),
    write_list(R, Sout).
