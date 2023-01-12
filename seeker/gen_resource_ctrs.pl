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
% Purpose: Program to run to generate resource constraints (disjunctive, diffn, cumulative) in the context of the model seeker (not used for combinatorial objects);
%          this has to be executed after running the main that generates formulae for some attributes of the tables.
%          Handle the different tables which are mentionned in some acquired formula).
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(table_access).
:- use_module(utility).
:- use_module(gen_candidate_tables).

:- multifile table_metadata/31.
:- dynamic table_metadata/31.
top :-
    X4 = 'data/model_seeker/found_model.pl',
    consult(X4),
    get_tables(model_seeker, _, _, _, X13),
    sort(X13, X5),
    gen_resource_ctrs(X5, X8),
    open(X4, append, X19),
    (foreach(X18,X5), foreach(X10, X8), param(X19)
    do
     (foreach(X12, X10), param([X19,X18])
     do
      (X12 = X20-diffn(X16,X6,X3,X11,X9) ->
          X14 = [col(X18, X6),
                       col(X18, X3),
                       col(X18, X11),
                       col(X18, X9)],
          X1 = diffn(X16)
      ;
       X12 = X20-disjunctive(X16,X6,X11,X9) ->
          X14 = [col(X18, X6),
                       col(X18, X11),
                       col(X18, X9)],
          X1 = disjunctive(X16)
      ;
          write(gen_resource_ctrs1(X12)),nl,halt
      ),
      (foreach(X15,X14), foreach(X17, X7), param(X18)
      do
       tab_get_name(X15, X17)
      ),
      X2 = conjecture(resource, col(X18,0),           
                                      none, 0, X20,
                                      t(X14, X7,
                                        [],
                                        X1)),
      portray_clause(X19, X2)
     )
    ),
    close(X19).

gen_resource_ctrs([], []) :- !.
gen_resource_ctrs([X11|X15], [X3|X16]) :-
    X9 = 'data/model_seeker/data',
    gen_table_and_metadata_file_names(X9, 0, X11, X7, X4),
    consult(X7),
    consult(X4),
    findall(X8-X10, conjecture(_,col(X11,X8),_,_,_,X10), X6),
    extract_non_machine_attrs(X6, X2),
    sort(X2, X1),
    gen_resource_ctr(X11, X6, X1, X3),
    remove_signature_and_table_facts(X11),    
    gen_resource_ctrs(X15, X16).

gen_resource_ctr(X7, X2, X1, X3) :-
    nl, write('TABLE: '), write(X7), nl,
    write('----------------------------------------------------------------------------------------------------'), nl,
    tab_get_pks(col(X7,_),    X11),
    tab_get_arity(col(X7,_),  X4),
    tab_get_types(col(X7,_),  X8),
    tab_get_equals(col(X7,_), X6),
    tab_get_cmps(col(X7,_),   X9),
    tab_get_ctrs(col(X7,_),   X10),
    gen_disjunctive_ctrs(X11, X7, X2, X1, X4, X8, X6, X9, X10, X5),
    X3 = X5,
    write(X5), nl.

extract_non_machine_attrs([], []) :- !.
extract_non_machine_attrs([X1|X5], X4) :-
    extract_non_machine_attrs1(X1, X3),
    extract_non_machine_attrs(X5, X2),
    append(X3, X2, X4).

extract_non_machine_attrs1(X1, [X2]) :-
    X1 = X2-t(_, _, _, X3),
    functor(X3, X4, _),
    memberchk(X4, [bool, if, cases]),
    !.
extract_non_machine_attrs1(X1, [X2|X4]) :-
    X1 = X2-t(X3, _, _, _),
    findall(X5, member(col(_,X5),X3), X4).

gen_disjunctive_ctrs(X47, X28, X17, X5, X29, X41, X39, X44, X45, X34) :-

    (X47 = [] ->         
        X22 = X5,
        X6 = [],                                                                         
        collect_temporal_attrs(1, X29, 0, 0, X28, X41, X39, X44, X30)         
    ;                                                                                                 
     X47 = [_-[X42]|_] ->                                                                           
        arg(X42, X45, X31),                                                                  
        (memberchk(include_except_default_value_no_cycle(X42,X35,_,X32), X31) ->    
            findall(X46, (member(precedence(X33,_,_,_),  X32), member(col(X28,X46), X33 )), X15 ),
            findall(X46, (member(precedence(_,_,_,X23), X32), member(col(X28,X46), X23)), X12),
            append(X15, X12, X40),
            sort(X40, X24),

            
            
            findall(X4,  (member(precedence(X33,_,_,_),  X32),            
                                          X33  = [col(X28,X4)]),  X2),                                          
            findall(X3, (member(precedence(_,_,_,X23),  X32),           
                                          X23 = [col(X28,X3)]), X1),
            append(X2, X1, X6),
            
            get_duration_attr_from_conjectures(X28, X17, X24,                    
                                               X6, X36),                             
            append(X36, X24, X25),                                                  
            sort(X25, X30),
            append([[X42,X35],X15,X12,X5], X22)          
        ;                                                                                             
            X22 = [X42|X5],                                                     
            X6 = [],                                                                     
            collect_temporal_attrs(1, X29, X42, 0, X28, X41, X39, X44, X30) 
        )
    ;
        X47 = [_-X26|_],
        append(X26, X5, X22),
        collect_temporal_attrs(1, X29, 0, 0, X28, X41, X39, X44, X24),       
        remove_elements_from_unsorted_list(X24, X26, X30)                         
    ),
    findall(X49, (X49 in 1..X29,indomain(X49),arg(X49,X41,set)), X18),                        
    append(X22, X18, X19),
    sort(X19, X9),
    findall(X49, (X49 in 1..X29,indomain(X49),\+memberchk(X49,X9)), X20),           
    findall(t(X37,X43,X13), (member(X37, X20),                            
                                             member(X43, X30),
                                             X43 \== X37,
                                             member(X13, X30),
                                             X13 \== X37,
                                             X13 \== X43),          X7),
    X21 in 0..1000000,
    (minimize(check_disjunctive_ctrs(X29, X28, X7, X6, X21, X10), X21) ->
        (X10 = t(X38,X11,X16,X14) ->
            arg(X11, X44, X27),
            (memberchk(within(col(X28,X11),col(X28,X8)), X27) ->
                X34 = [X21-diffn(X38,X11,X8,X16,X14)]
            ;
                X34 = [X21-disjunctive(X38,X11,X16,X14)]
            )
        ;
            X34 = [], X21 = 1000000
        )
    ;
        X34 = [], X21 = 1000000
    ).

get_duration_attr_from_conjectures(X7, X2, X8, X1, X9) :-
    findall(X10, (member(X3, X2),
                  X3 = X4-t([col(X7,X5),col(X7,X6)],
                                          _, _, polynom([monome([t(_,1)],1),monome([t(_,1)],1)])),
                  memberchk(X4, X8),
                  ((memberchk(X5,X8), nonmember(X6,X8), nonmember(X6,X1)) ->
                        X10 = X6
                  ;
                   (memberchk(X6,X8), nonmember(X5,X8), nonmember(X5,X1)) ->
                        X10 = X5
                  ;
                        false
                  )),
                  X9).

check_disjunctive_ctrs(_, _, [], _, 1000000, []) :- !.
check_disjunctive_ctrs(X6, X7, X1, X2, X5, X3) :-
    member(X4, X1),
    check_disjunctive_ctr(X6, X7, X4, X2, X5, X3).

check_disjunctive_ctr(X7, X8, X2, X1, X5, X3) :-
    X2 = t(X10,X13,X4),
    findall(X11,
            (functor(X6, X8, X7),
             functor(X11, t, 3),
             unify_variables([X10,X13,X4], 1, X6, X11),
             call(X6)),
            X9),
    sort(X9, X12),
    length(X9, X15),
    length(X12,    X15),
    (memberchk(X4, X1) -> 
        X14 = 1                                  
    ;                                             
        X14 in 0..1                              
    ),
    check_disjunctive_ctr1(X12, _, X14, 0, 1, X5),
    X3 = t(X14,X10,X13,X4).

check_disjunctive_ctr1([t(X5,_,_)], X2, X6, X3, X4, X1) :-
    (X2 = X5 -> X7 = 0 ; X7 = 1),
    (integer(X6)  -> (X6 = 0 -> X1 is X3+X7 ; X1 is X4+X7) ;
     X3 =< X4 ->  X6 = 0,   X1 is X3+X7                             ;
	                X6 = 1,   X1 is X4+X7                             ).

check_disjunctive_ctr1([t(X16,X17,X11),t(X18,X19,X12)|X20], X9, X10, X5, X6, X2) :-
    fd_max(X2, X1),
    (X16 = X18 ->
         fd_min(X10, X7),
         (X7 = 0 ->
              X13 is X17+X11,
              (X13 =< X19 ->
               X3 is X5 + X19 - X13,
               (X3 > X1 -> X10 = 1 ; true)
              ;
                                              X10 = 1
              )
         ;
              true
         ),
         fd_max(X10, X8),
         (X8 = 1 ->
              X14 = X11,
              (X14 =< X19 ->
                   X4 is X6 + X19 - X14,
                   (X4 > X1 -> X10 = 0 ; true)
              ;
                   X10 = 0
              )
         ;
              true
         )
    ;
         (integer(X9) ->
              ((X9 < X16, X16 < X18) -> X15 = 1 ; X15 = 0)
         ;
          X16 < X18  -> X15 = 1
         ;
                      X15 = 0
         ),
         (fd_min(X10, 0) -> X3 is X5 + X15 ; true),
         (fd_max(X10, 1) -> X4 is X6 + X15 ; true)
    ),
    check_disjunctive_ctr1([t(X18,X19,X12)|X20], X16, X10, X3, X4, X2).
