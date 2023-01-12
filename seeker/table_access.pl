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
% Purpose: Primitives for accessing a table
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(table_access,[consult_metadata_of_functor/4, 
                        get_metadata_arity/1,
                        get_metadata_attributes/1,
                        tab_get_arity/2,
                        tab_get_nb_rows/2,
                        tab_get_maxn/2,
                        tab_get_name/2,
                        tab_get_kind/2,
                        tab_get_inout/2,
                        tab_get_min/2,
                        tab_get_max/2,
                        tab_get_types/2,
                        tab_get_type/2,
                        tab_get_nval/2,
                        tab_get_median/2,
                        tab_get_gcd/2,
                        tab_get_sum/2,
                        tab_get_mean/2,
                        tab_get_equals/2,
                        tab_get_equal/2,
                        tab_get_fd/2,
                        tab_get_fd_eq/2,
                        tab_get_nb_fd/2,
                        tab_get_cmps/2,
                        tab_get_cmp/2,
                        tab_get_nb_cmp/2,
                        tab_get_ctrs/2,
                        tab_get_ctr/2,
                        tab_get_maxocc/2,
                        tab_get_maxoccval/2,
                        tab_get_pks/2,
                        tab_get_fks/2,
                        tab_get_affinity/2,
                        tab_get_inf_sup/3,
                        tab_get_ranked_fd/2,
                        tab_get_distinct_val/2,
                        tab_get_distinct_val_count/2,
                        tab_get_vals_fd/2,
                        tab_get_monotonicity/2,
                        tab_get_min_max/3,
                        tab_get_mins_attr_names/2,
                        tab_get_maxs_attr_names/2,
                        tab_get_vals_attr_names/4,
                        tab_get_vals_attr_names/6,
                        tab_get_indices_in_range_attr_names/5,
                        tab_get_indices_neg_min_attr_names/3,
                        tab_get_primaries/2,
                        tab_get_secondaries/2,
                        tab_get_primaries_secondaries/2,
                        tab_get_inputs/2,
                        tab_get_small_fd/2,
                        tab_get_bound_col/2,
                        tab_get_index_identical_column/2,
                        tab_get_fk_columns/2,
                        get_fk_columns/2,
                        tab_get_max_name_length/3,
                        tab_get_bound_type/3]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).

:- multifile table_metadata/31.
:- dynamic table_metadata/31.

consult_metadata_of_functor(X7, X2, X3, X11) :- 
    X13 in X2..X3,
    indomain(X13),                                              
    number_codes(X13, X8),                               
    atom_codes(X9, X8),                             
    atom_concat('data/', X7, X10),                   
    atom_concat(X10, '/data', X12),                     
    atom_concat(X12, X9, X4),                 
    atom_concat(X4, '/', X6),                   
    atom_concat(X6, X11, X1),         
    atom_concat(X1, '_metadata.pl', X5), 
    consult(X5),
    false.
consult_metadata_of_functor(_, _, _, _). 

get_metadata_arity(31).

get_metadata_attributes([1-table_name,       
                         2-max_n,            
                         3-nb_columns,       
                         4-nb_rows,          
                         5-col_names,        
                         6-kinds,            
                         7-in_outs,          
                         8-mins,             
                         9-maxs,             
                         10-types,           
                         11-nvals,           
                         12-medians,         
                         13-gcds,            
                         14-sums,            
                         15-means,           
                         16-equals,          
                         17-fds,             
                         18-nb_fds,          
                         19-cmps,            
                         20-nb_cmps,         
                         21-ctrs,            
                         22-maxoccs,         
                         23-maxoccvals,      
                         24-pks,             
                                             
                         25-fks,             
                                             
                                             
                                             
                                             
                         26-affinities,      
                                             
                         27-inf_sup,         
                         28-ranked_fds,      
                         29-distinct_vals,   
                         30-vals_fds,        
                                             
                         31-monotonicities]).

tab_get_metadata_field(X4, X5, X1):-
    get_metadata_arity(X2),
    functor(X3,table_metadata,X2),
    arg(1,   X3, X4),
    call(user:X3), !,
    arg(X5, X3, X1).

tab_get_metadata_fields(X6, X5, X1):-
    get_metadata_arity(X2),
    functor(X4,table_metadata,X2),
    arg(1,   X4, X6),
    call(user:X4), !,
    (foreach(X7,X5), foreach(X3,X1), param(X4)
    do
     arg(X7, X4, X3)
    ).

tab_get_maxn(col(X2,_), X1)       :- tab_get_metadata_field(X2,  2, X1).

tab_get_arity(col(X2,_), X1)     :- tab_get_metadata_field(X2,  3, X1).

tab_get_nb_rows(col(X2,_), X1)  :- tab_get_metadata_field(X2,  4, X1).

tab_get_name(col(X3,X4), X2)     :- tab_get_metadata_field(X3,  5, X1), arg(X4,X1,X2).

tab_get_kind(col(X3,X4), X2)     :- tab_get_metadata_field(X3,  6, X1), arg(X4,X1,X2).

tab_get_inout(col(X3,X4), X2)   :- tab_get_metadata_field(X3,  7, X1), arg(X4,X1,X2).

tab_get_min(col(X2,X3), X4)       :- tab_get_metadata_field(X2,  8, X1), arg(X3,X1,X4).

tab_get_max(col(X2,X3), X4)       :- tab_get_metadata_field(X2,  9, X1), arg(X3,X1,X4).

tab_get_types(col(X2,_), X1)     :- tab_get_metadata_field(X2, 10, X1).

tab_get_type(col(X3,X4), X2)     :- tab_get_metadata_field(X3, 10, X1), arg(X4,X1,X2).

tab_get_nval(col(X3,X4), X2)     :- tab_get_metadata_field(X3, 11, X1), arg(X4,X1,X2).

tab_get_median(col(X3,X4), X2) :- tab_get_metadata_field(X3, 12, X1), arg(X4,X1,X2).

tab_get_gcd(col(X2,X3), X4)       :- tab_get_metadata_field(X2, 13, X1), arg(X3,X1,X4).

tab_get_sum(col(X2,X3), X4)       :- tab_get_metadata_field(X2, 14, X1), arg(X3,X1,X4).

tab_get_mean(col(X3,X4), X2)     :- tab_get_metadata_field(X3, 15, X1), arg(X4,X1,X2).

tab_get_equals(col(X2,_), X1)   :- tab_get_metadata_field(X2, 16, X1).

tab_get_equal(col(X3,X4), X2)   :- tab_get_metadata_field(X3, 16, X1), arg(X4,X1,X2).

tab_get_fd(col(X1,X2), X4)         :- tab_get_metadata_field(X1, 17, X3), arg(X2,X3,X4).

tab_get_fd_eq(col(X5,X6), X8) :-
    tab_get_metadata_fields(X5, [6,     16,     17 ],
                                 [X2, X1, X7]),
    arg(X6, X7, X9),
    (X9 = [] ->
        arg(X6, X1, X3),
        (X3 > 0 ->
            arg(X3, X2, X4),
            (memberchk(X4,[low,up]) ->
                arg(X3, X7, X8)
            ;
                X8 = []
            )
        ;
            X8 = []
        )
    ;
        X8 = X9
    ).

tab_get_nb_fd(col(X3,X4), X2)          :- tab_get_metadata_field(X3, 18, X1), arg(X4,X1,X2).

tab_get_cmps(col(X2,_), X1)             :- tab_get_metadata_field(X2, 19, X1).

tab_get_cmp(col(X2,X3), X4)             :- tab_get_metadata_field(X2, 19, X1), arg(X3,X1,X4).

tab_get_nb_cmp(col(X3,X4), X2)        :- tab_get_metadata_field(X3, 20, X1), arg(X4,X1,X2).

tab_get_ctrs(col(X2,_), X1)             :- tab_get_metadata_field(X2, 21, X1).

tab_get_ctr(col(X2,X3), X4)             :- tab_get_metadata_field(X2, 21, X1), arg(X3,X1,X4).

tab_get_maxocc(col(X3,X4), X2)       :- tab_get_metadata_field(X3, 22, X1), arg(X4,X1,X2).

tab_get_maxoccval(col(X3,X4), X2) :- tab_get_metadata_field(X3, 23, X1), arg(X4,X1,X2).

tab_get_pks(col(X1,_), X2)               :- tab_get_metadata_field(X1, 24, X2).

tab_get_fks(col(X1,_), X2)               :- tab_get_metadata_field(X1, 25, X2).

tab_get_affinity(col(X3,X4), X2)   :- tab_get_metadata_field(X3, 26, X1), arg(X4,X1,X2).

tab_get_inf_sup(col(X1,_), X2, X3)      :- tab_get_metadata_field(X1, 27, X2-X3).

tab_get_ranked_fd(col(X3,X4), X2)  :- tab_get_metadata_field(X3, 28, X1), arg(X4,X1,X2).

tab_get_distinct_val(col(X4,X5), X3):-
    tab_get_metadata_field(X4, 29, X2),
    arg(X5, X2, X1),
    (foreach(X6-_,X1), foreach(X6,X3) do true).

tab_get_distinct_val_count(col(X3,X4), X1) :- tab_get_metadata_field(X3, 29, X2), arg(X4, X2, X1).

tab_get_vals_fd(col(X3,X4), X2)                      :- tab_get_metadata_field(X3, 30, X1), arg(X4,X1,X2).

tab_get_monotonicity(col(X3,X4), X2)           :- tab_get_metadata_field(X3, 31, X1), arg(X4,X1,X2).

tab_get_min_max(col(X3,X4), X5, X6) :-
    tab_get_metadata_fields(X3, [8,    9   ],
                                 [X1, X2]),
    arg(X4,X1,X5), arg(X4,X2,X6).

tab_get_mins_attr_names([], []) :- !.
tab_get_mins_attr_names([X1|X3], [X2|X4]) :-
    tab_get_min(X1, X2),
    tab_get_mins_attr_names(X3, X4).

tab_get_maxs_attr_names([], []) :- !.
tab_get_maxs_attr_names([X1|X3], [X2|X4]) :-
    tab_get_max(X1, X2),
    tab_get_maxs_attr_names(X3, X4).

tab_get_vals_attr_names(_, _, _, X1) :- ground(X1), !.
tab_get_vals_attr_names([], _, _, []) :- !.
tab_get_vals_attr_names([X1|X5], X2, X3, [X4|X6]) :-
    tab_get_vals_attr_name(X1, X2, X3, X4),
    tab_get_vals_attr_names(X5, X2, X3, X6).

tab_get_vals_attr_name(col(X5,X6), X2, X3, X4) :-
    tab_get_arity(col(X5,_), X10),
    findall(X7, (functor(X8, X5, X10),
                  call(user:X8),
                  arg(X6, X8, X7),
                  X7 >= X2,
                  X7 =< X3), X1),
    sort(X1, X4).

tab_get_vals_attr_names(_, _, _, _, _, X1) :- ground(X1), !.
tab_get_vals_attr_names([], _, _, _, _, []) :- !.
tab_get_vals_attr_names([X3|X7], X4, X5, X1, X2, [X6|X8]) :-
    tab_get_vals_attr_name(X3, X4, X5, X1, X2, X6),
    tab_get_vals_attr_names(X7, X4, X5, X1, X2, X8).

tab_get_vals_attr_name(col(X7,X8), X4, X5, col(X7,X1), X2, X6) :-
    tab_get_arity(col(X7,_), X12),
    findall(X9, (functor(X10, X7, X12),
                  call(user:X10),
                  arg(X1, X10, X2),
                  arg(X8,       X10, X9),
                  X9 >= X4,
                  X9 =< X5), X3),
    sort(X3, X6).

tab_get_indices_in_range_attr_names([], _, _, _, []) :- !.
tab_get_indices_in_range_attr_names([X1|X9], X4, X8, X3, X5) :-
    tab_get_min(X1, X6),
    (X6 >= X4 ->
        tab_get_max(X1, X7),
        (X7 =< X8 -> X5 = [X3|X10] ; X5 = X10)
    ;
        X5 = X10
    ),
    X2 is X3+1,
    tab_get_indices_in_range_attr_names(X9, X4, X8, X2, X10).

tab_get_indices_neg_min_attr_names([], _, []) :- !.
tab_get_indices_neg_min_attr_names([X1|X6], X3, X4) :-
    tab_get_min(X1, X5),
    (X5 < 1 -> X4 = [X3|X7] ; X4 = X7),
    X2 is X3+1,
    tab_get_indices_neg_min_attr_names(X6, X2, X7).

tab_get_primaries(X3, X1) :-
    tab_get_metadata_fields(X3, [3, 6],
                                 [X4, X2]),
    findall(col(X3,X5), (X5 in 1..X4, indomain(X5), arg(X5, X2, primary)), X1).

tab_get_secondaries(X3, X1) :-
    tab_get_metadata_fields(X3, [3, 6],
                                 [X4, X2]),
    findall(col(X3,X5), (X5 in 1..X4, indomain(X5), arg(X5, X2, secondary)), X1).

tab_get_primaries_secondaries(X4, X1) :-
    tab_get_metadata_fields(X4, [3, 6],
                                 [X5, X2]),
    findall(col(X4,X6), (X6 in 1..X5, indomain(X6), arg(X6, X2, X3), memberchk(X3, [primary,secondary])), X1).

tab_get_inputs(X3, X1) :-
    tab_get_metadata_fields(X3, [3, 7],
                                 [X4, X2]),
    findall(col(X3,X5), (X5 in 1..X4, indomain(X5), arg(X5, X2, input)), X1).

tab_get_small_fd(X8, X2) :-
    tab_get_metadata_fields(X8, [3, 6,    17],
                                 [X13, X4,X9]),
    findall(X14, (X14 in 1..X13, indomain(X14), arg(X14, X4, X7), memberchk(X7,[low,up])), [X3]),
    arg(X3, X9, X1),
    X1 = [X10|_],
    length(X10, X11),
    X5 is X11+1,
    findall(X12, (member(X12, X1), length(X12, X6), X6 =< X5), X2).

tab_get_bound_col(X4, X1) :-
    tab_get_metadata_fields(X4, [3, 6],
                                 [X5, X2]),
    findall(X6, (X6 in 1..X5, indomain(X6), arg(X6, X2, X3), memberchk(X3,[low,up])), [X1]).

tab_get_index_identical_column(col(X2,X3), X1) :-
    tab_get_equal(col(X2,X3), X1),
    X1 > 0,
    !.
tab_get_index_identical_column(col(X5,X6), X2) :-
    tab_get_metadata_fields(X5, [3, 16],
                                 [X7, X4]),
    X3 is X6+1,
    findall(X8, (X8 in X3..X7, indomain(X8), arg(X8, X4, X6)), X1),
    X1 = [X2|_].

tab_get_fk_columns(X2, X1) :-
   tab_get_fks(col(X2,_), X3),
   get_fk_columns(X3, X1).

get_fk_columns(X4, X2) :-
   (var(X4) -> write(tab_get_fk_columns), nl, halt ; true),      
   findall(X5, member([ind(_,_, fk(X5))|_], X4), X1), 
   append(X1, X3),
   sort(X3, X2).                                       

tab_get_max_name_length(X3, X6, X1) :-            
    tab_get_arity(col(X3,_), X4),                           
    findall(X8, (X10 in 1..X4,                                  
                  indomain(X10),
                  tab_get_kind(col(X3,X10), X6),
                  tab_get_name(col(X3,X10), X7),
                  atom_codes(X7, X5),
                  length(X5, X8)),              X2),
    max_member(X1, X2),
    !.
tab_get_max_name_length(_, _, 100000).

tab_get_bound_type(X1, X5, X2) :-
    X1 \== model_seeker,
    tab_get_arity(col(X5,_), X3),
    findall(X4, (X6 in 1..X3, indomain(X6), tab_get_kind(col(X5,X6), X4), memberchk(X4, [low,up])), [X2]). 
