%    The contents of this file are subject to the Mozilla Public License
%    Version  1.1  (the "License"); you may not use this file except in
%    compliance with the License. You may obtain a copy of the License at:
%
%    http://www.mozilla.org/MPL/
%
%    Software  distributed  under  the License is distributed on an "AS
%    IS"  basis,  WITHOUT  WARRANTY  OF  ANY  KIND,  either  express or
%    implied.
%
% Purpose: CHECK THE MONOTONICITY OF EACH BOUND WRT THE BIGGEST GENERATED SIZE
%  This sanity check is done as limiting ourself to a given maximum number of vertices may produce some tables where
%  some entries contain wrong lower/upper bounds, specially when the number of vertices is not part of the input parameters.
%  (normally gen_data is supposed to filter such entries, see valid_optimal/5 in gen_data.pl)
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(utility). 

top(X3) :- 
    max_size_combi(X3, X7),                                                    
    atoms_concat(['data/',X3,'/found_problems_',X3,'.tex'], X4), 
    open(X4, write, X6),                                                     
    top(X3, X7, X6), 
    findall(X5, found_problem(X5), X2),
    sort(X2, X1),
    print_name_of_tables_with_a_problem(X1, X6),
    close(X6).

print_name_of_tables_with_a_problem([], _) :- !.
print_name_of_tables_with_a_problem([X1|X3], X2) :-
    (X3 = [_|_] ->
        format(X2, '~w,~n', [X1])
    ;
        format(X2, '~w.~n', [X1])
    ),
    print_name_of_tables_with_a_problem(X3, X2).

top(X6, X13, X11) :- 
    get_tables(X6, _, _, _, X8), 
    sort(X8, X1),                                             
    member(X7, X1),                                          
    X12 is X13-1,                                                              
    X15 in 2..X12,                                                             
    indomain(X15),                                                            
    consult_data_and_get_nb_cols(X6, X7, X13, X2, X10, X9), 
    consult_data_and_get_nb_cols(X6, X7, X15, X3, X10, X9), 
    check_table(X2, X3, X10, X9, X7, X15, X11),   
    retractall(signature(_,_,_)),                                           
    functor(X4, X7, X2),                               
    retractall(X4),
    (X2 = X3 -> true                                     ;
                                functor(X5, X7, X3),   
                                retractall(X5)                   ), 
    false.                                                                  
top(_, _).

check_table(X3, X3, X7, X5, X4, X11, X9) :- !, 
    functor(X10, X4, X3),                                   
    findall(X10, call(X10), X8),                                    
    length(X7, X6),                                               
    project_terms(X8, X6, X7, X5, X1),         
    keysort(X1, X2),                                
    check_table1(X2, X4, X11, X9).                         
check_table(_, _, _, _, _, _, _).                                        

project_terms([], _, _, _, []) :- !.
project_terms([X1|X7], X2, X5, X3, [X4-X6|X8]) :-
    functor(X4, t, X2),                 
    project_term(X5, X1, X4),        
    arg(X3, X1, X6),                   
    project_terms(X7, X2, X5, X3, X8).

project_term([], _, _) :- !.
project_term([X4|X5], X2, X1) :-
    arg(X4, X2, X3),
    arg(X4, X1, X3),
    project_term(X5, X2, X1).

check_table1([], _, _, _) :- !.
check_table1([_], _, _, _) :- !.
check_table1([X3-X4,X3-X4|X5], X1, X6, X2) :- !,
    check_table1([X3-X4|X5], X1, X6, X2).
check_table1([X3-X4,X3-X5|_], X1, X7, X2) :- !,
    assert(found_problem(X1)),
    format(X2, 'PROBLEM WITH: ~w(~w) ~w-~w ~w-~w~n', [X1,X7,X3,X4,X3,X5]).
check_table1([_,X4-X5|X6], X1, X7, X2) :-
    check_table1([X4-X5|X6], X1, X7, X2).

consult_data_and_get_nb_cols(X1, X6, X9, X2, X8, X7) :- 
    number_codes(X9, X3),                         
    atom_codes(X4, X3),                       
    atoms_concat(['data/',X1,                       
                  '/data',X4,                        
                  '/',                                     
                  X6,                                 
                  '.pl'], X5),                       
    consult(X5),                                     
    signature(X6, X9, X10),                        
    functor(X10, t, X2),                           
    findall(X11, (X11 in 1..X2, indomain(X11),            
                arg(X11, X10, t(_,primary,input))), X8),
    findall(X11, (X11 in 1..X2, indomain(X11),            
                arg(X11, X10, t(_,_,output))), [X7]).
