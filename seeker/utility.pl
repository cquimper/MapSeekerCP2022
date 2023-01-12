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
% Purpose: List utilities and constraint term creation utilities
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(utility,[formula_pattern/2,
                   forbid_cols_which_can_be_leq0/4,
                   var_diff_from_values/2,
                   gen_table_ctr_wrt_authorised_cmp/6,
                   gen_table_ctr_wrt_forbidden_cmp/5,
                   get_all_col_pairs_in_cmps/4,
                   shift_pairs/2,
                   gen_combinations_of_values/2,
                   scalar_prod/3,
                   gen_integer_list_from_low_to_up/3,
                   gen_count_ctrs/3,
                   gen_or_ctrs/3,
                   gen_or_term/3,
                   gen_sum_term/3,
                   gen_linear_sum/3,
                   gen_lists_dvars/5,
                   gen_list_dvars_min_maxs/3,
                   get_pos_value/5,
                   prefixes_length/3,
                   suffixes_length/3,
                   length_same_prefix/2,
                   flatten/2,
                   members/2,
                   memberchks/2,
                   eq_memberchks/2,
                   lists_member/2,
                   nths1/3,
                   sublist/2,
                   sublist_max_card/3,
                   sublist_max_card/5,
                   sum_prod_after/2,
                   remove_values/3,
                   args/3, 
                   same_args/4,
                   get_common_intersection_and_complement/3,
                   gcd/2,                                       
                   gcd/3,                                       
                   get_max_abs_dvars/2,
                   gen_signature/2,
                   gen_cost_sum_abs/2,
                   gen_cost_sum_abs/3,
                   gen_cost_sum_abs_max1/2,
                   gen_cost_diff0/2,
                   gen_cost_max_abs/2,
                   atoms_concat/2,
                   atom_proper_suffix_add_underscore/2,
                   add_key/2,
                   prodlist/2,
                   gen_occ_vars/4,
                   gen_occ_vars/5,
                   compute_max_abs/3,
                   split_list_wrt_smallest_length/3,
                   cartesian_product_without_sort/3,
                   cartesian_product_with_sort/3,
                   sort_wrt_list_length/2,
                   listify/2,
                   build_continuation_list/3,
                   create_list_of_empty_lists/2,
                   remove_first_last_elements/4,
                   remove_first_last_elements/2,
                   complement_elements/3,
                   intersect_elements/3,
                   more_than_one_unique_value/1,
                   write_list/1,
                   write_list/2,
                   write_spaces/1,
                   call_with_time_out/1,
                   binary_term_calculation/5,
                   intersect_lists/3,
                   remove_elements_from_unsorted_list/3,
                   remove_elements_from_list/3,
                   del/3,
                   gen_all_element_subset_pairs/2,
                   group_same_keys/2,
                   combine_lists/3,
                   combine_lists_exclusive/3,
                   merge_lists/3,
                   length_prefix/4,     
                   remove_first_elem/3, 
                   sum_squares/2,       
                   get_non_zero_exponents/3,
                   count_distinct_vals/3,
                   unify_variables/4,   
                   collect_temporal_attrs/9]). 

:- use_module(library(timeout)).
:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(table_access).     

formula_pattern(X2, X1) :- 
    memberchk(X2, X1).

forbid_cols_which_can_be_leq0(X5, X1, X3, X7) :-
    findall(X8,
            (X9 in 1..X5,
             indomain(X9),                   
             nth1(X9, X1, X2), 
             tab_get_min(X2, X6),  
             (X6  =< 0  -> true ;         
                             false),
             X8 is X9 + X3),
            X4),
    var_diff_from_values(X4, X7).       

var_diff_from_values([], _) :- !.
var_diff_from_values([X1|X3], X2) :-
    X2 #\= X1,
    var_diff_from_values(X3, X2).

gen_table_ctr_wrt_authorised_cmp(X8, 2, X6, X2, X7, X4) :- !,
    get_all_col_pairs_in_cmps(X8, X6, X2, X1),
    (X1 = [] ->
        false
    ;
        (X7 = 0 ->
            X5 = X1
        ;                                              
            shift_pairs(X1, X3), 
            X5 = [[1,1]|X3]           
        ),                                             
        call(table([X4], X5))
    ).
gen_table_ctr_wrt_authorised_cmp(X8, 3, X6, X2, X7, X3) :-
    get_all_col_triples_in_cmps(X8, X6, X2, X1),
    (X1 = [] ->
        false
    ;
        (X7 = 0 ->
            X5 = X1
        ;                                                  
            shift_triples(X1, X4), 
            X5 = [[1,1,1]|X4]             
        ),                                                 
        call(table([X3], X5))
    ).

gen_table_ctr_wrt_forbidden_cmp(X7, X4, X2, X6, X3) :-
    get_all_col_pairs_in_cmps(X7, X4, X2, X1),
    (X6 = 0 ->
        X5 = X1
    ;
        shift_pairs(X1, X5)
  
    ),
    call(#\table([X3], X5)).

shift_pairs([], []) :- !.
shift_pairs([[X,X4]|X5], [[X1,X2]|X6]) :-
    X1 is X+1, X2 is X4+1,
    shift_pairs(X5, X6).

shift_triples([], []) :- !.
shift_triples([[X,X5,X6]|X7], [[X1,X2,X3]|X8]) :-
    X1 is X+1, X2 is X5+1, X3 is X6+1,
    shift_triples(X7, X8).

get_all_col_pairs_in_cmps(X8, X2, X9, X6) :-
    findall([X12,X13],
            (X12 in 1..X8,
             indomain(X12),                      
             nth1(X12, X2, X3),    
             tab_get_cmp(X3, X5), 
             member(X11, X9),                
             functor(X10, X11, 2),            
             arg(1, X10, X3),          
             arg(2, X10, X4),          
             findall(X4, member(X10,X5), X1),
             member(X4, X1),    
             nth1(X13, X2, X4)),   
            X7),
    sort(X7, X6).                        

get_all_col_triples_in_cmps(X11, X1, X12, X8) :-
    findall([X15,X16,X17],
            (X15 in 1..X11,
             indomain(X15),
             nth1(X15, X1, X2),
             tab_get_cmp(X2, X5), 
             member(X9, X5),          
             functor(X9, X13, 2),		   
             memberchk(X13, X12),            
             arg(2, X9, X3),         
             X3 \== X2,          
             tab_get_cmp(X3, X6), 
             member(X10, X6),          
             functor(X10, X14, 2),		   
             memberchk(X14, X12),            
             arg(2, X10, X4),         
             X4 \== X2,          
             X4 \== X3,          
             nth1(X16, X1, X3),    
             nth1(X17, X1, X4)),   
            X7),
	sort(X7, X8).                      

gen_combinations_of_values([], _) :- !.
gen_combinations_of_values([X2|X3], X1) :- member(X2, X1), gen_combinations_of_values(X3, X1).

scalar_prod(X1, X2, X3) :-
    scalar_prod(X1, X2, 0, X3).

scalar_prod([], [], X1, X1) :- !.
scalar_prod([X1|X6], [X2|X7], X4, X5) :-
    X3 is X4 + X1*X2,
    scalar_prod(X6, X7, X3, X5).

gen_integer_list_from_low_to_up(X2, X1, []) :- X2 > X1, !.
gen_integer_list_from_low_to_up(X3, X1, [X3|X4]) :-
    X3 =< X1,
    X2 is X3+1,
    gen_integer_list_from_low_to_up(X2, X1, X4).

gen_count_ctrs([], _, _) :- !.
gen_count_ctrs([X1|X7], X2, X3) :-
    (X3 = eq([X4|X8])  ->                  count(X2, X1, #=,  X4), gen_count_ctrs(X7, X2, eq(X8) ) ;
     X3 = eq(X4)      ->                  count(X2, X1, #=,  X4), gen_count_ctrs(X7, X2, X3   ) ;
     X3 = geq([X4|X8]) ->                  count(X2, X1, #>=, X4), gen_count_ctrs(X7, X2, geq(X8)) ;
     X3 = geq(X4)     ->                  count(X2, X1, #>=, X4), gen_count_ctrs(X7, X2, X3   ) ;
     X3 = in(X5,X6)  -> X4 in X5..X6, count(X2, X1, #=,  X4), gen_count_ctrs(X7, X2, X3   ) ;
                                            write(gen_count_ctrs), nl, halt                            ).

gen_or_ctrs([], _, []) :- !.
gen_or_ctrs([X3|X4], X1, [X5|X6]) :-
    gen_or_term(X3, X1, X2),
    call(X5 #= X2),
    gen_or_ctrs(X4, X1, X6).

gen_or_term([], _, 0) :- !.
gen_or_term([X1|X2], var, X1 #\/ X3) :- !,
    gen_or_term(X2, var, X3).
gen_or_term([X2|X3], var_neq(X1), (X2 #\= X1) #\/ X4) :-
    gen_or_term(X3, var_neq(X1), X4).

gen_sum_term([], _, 0) :- !.
gen_sum_term([X1|X2], var, X1+X3) :- !,
    gen_sum_term(X2, var, X3).
gen_sum_term([X2|X3], var_neq(X1), (X2 #\= X1) + X4) :-
    gen_sum_term(X3, var_neq(X1), X4).

gen_linear_sum([], [], 0) :- !.
gen_linear_sum([X1], [X2], X1*X2) :- !.
gen_linear_sum([X1|X2], [X3|X4], X1*X3+X5) :-
    gen_linear_sum(X2, X4, X5).

gen_lists_dvars(0, _, _, _, []) :- !.
gen_lists_dvars(X6, X2, X3, X4, [X1|X7]) :-
    X6 > 0,
    length(X1, X2),
    domain(X1, X3, X4),
    X5 is X6-1,
    gen_lists_dvars(X5, X2, X3, X4, X7).

gen_list_dvars_min_maxs([], _, []) :- !.
gen_list_dvars_min_maxs([X3|X4], X1, [X2|X5]) :-
    X3 in X1..X2,
    gen_list_dvars_min_maxs(X4, X1, X5).

get_pos_value([], _, _, _, []) :- !.
get_pos_value([X3|X4], X3, X5, X6, [X5|X7]) :- !,
    X1 is X5+1,
    X2 is X6-1,
    (X2 = 0 -> X7 = [] ; get_pos_value(X4, X3, X1, X2, X7)).
get_pos_value([_|X3], X4, X5, X6, X7) :- !,
    X1 is X5+1,
    get_pos_value(X3, X4, X1, X6, X7).

prefixes_length([], [], _) :- !.
prefixes_length([X2|X4], [X1|X5], X3) :-
    prefix_length(X2, X1, X3),
    prefixes_length(X4, X5, X3).

suffixes_length([], [], _) :- !.
suffixes_length([X2|X4], [X1|X5], X3) :-
    suffix_length(X2, X1, X3),
    suffixes_length(X4, X5, X3).

length_same_prefix([], 0) :- !.
length_same_prefix([X2|X3], X1) :-
    length_same_prefix(X3, X2, 1, X1).

length_same_prefix([X4|X5], X4, X2, X3) :- !,
    X1 is X2+1,
    length_same_prefix(X5, X4, X1, X3).
length_same_prefix(_, _, X1, X1).

flatten(X2, X1) :-
    flatten(X2, X1, []).

flatten([], X1, X1):- !.
flatten([X1|X2], X, X4) :-
    is_list(X1), !,
    flatten(X1, X, X5),
    flatten(X2, X5, X4).
flatten([X1|X2], [X1|X], X4) :-
    flatten(X2, X, X4).

members([], _) :- !.
members([X1|X2], X3) :-
    member(X1, X3),
    members(X2, X3).

memberchks([], _) :- !.
memberchks([X1|X2], X3) :-
    memberchk(X1, X3),
    memberchks(X2, X3).

eq_memberchks(X1, X2) :-
    length(X1, X3),
    length(X2, X3),
    memberchks(X1, X2).

lists_member([X1|_], X2) :-
    member(X2, X1).
lists_member([_|X3], X1) :-
    lists_member(X3, X1).

nths1([], _, _) :- !.
nths1([X3|X4], X1, X2) :-
    nth1(X3, X1, X2),
    nths1(X4, X1, X2).

sublist(X1, X2) :-
    length(X1, X3),
    X4 in 1..X3,
    indomain(X4),
    length(X2, X4),
    sublist1(X2, X1).

sublist_max_card(X1, X4, X2) :-
    length(X1, X5),
    X3 is min(X5, X4),
    X6 in 1..X3,
    indomain(X6),
    length(X2, X6),
    sublist1(X2, X1).

sublist_max_card(X1, X2, X9, X8, X5) :-
    length(X1, X12),
    length(X2, X13),
    X10 is X12+X13,
    X3 is min(X10, X8), X11 in 1..X3,
    X6  is min(X12,  X8), X14  in 0..X6,
    X7  is min(X13,  X9),  X15  in 0..X7,
    X11 #= X14 + X15, labeling([], [X11,X15,X14]),
    length_anchor(X14, X5, X4),
    length(X4, X15),
    sublist1(X4, X2),
    sublist1(X5, X1).

length_anchor(0, X1, X1) :- !.
length_anchor(X2, [_|X4], X5) :-
    X2 > 0,
    X1 is X2-1,
    length_anchor(X1, X4, X5).

sublist1([], _) :- !.
sublist1([X1|_], _) :-
    ground(X1), !.
sublist1([X1|X2], [X1|X3]) :-
    sublist1(X2, X3).
sublist1([X1|X2], [_|X4]) :-
    sublist1([X1|X2], X4).

sum_prod_after(X2, X1) :-
    sliding_sum(X2, 0, X3),
    sum_prod_after(X2, X3, 0, X1).

sliding_sum([], _, []) :- !.
sliding_sum([X|X3], X1, [X4|X5]) :-
    X4 is X1 + X,
    sliding_sum(X3, X4, X5).

sum_prod_after([], _, X1, X1) :- !.
sum_prod_after([X|X5], [X6|X7], X1, X2) :-
    X3 is X1 + X*X6,
    sum_prod_after(X5, X7, X3, X2).

remove_values([X1|X2], X1, X3) :- !,
    remove_values(X2, X1, X3).
remove_values(X1, _, X1).

args([], _, []) :- !.           
args([X2|X4], X1, [X3|X5]) :- 
    arg(X2, X1, X3),        
    args(X4, X1, X5).           

same_args(X1, X2, _, _) :-
    X1 > X2, !.
same_args(X4, X5, X1, X2) :-
    arg(X4, X1, X6),
    arg(X4, X2, X6),
    X3 is X4+1,
    same_args(X3, X5, X1, X2).

get_common_intersection_and_complement(X3, X1, X2) :-
    X3 = [X4|X5],
    common_intersection(X5, X4, X1),
    not_in_intersection(X3, X1, X2).

common_intersection(_, [], []) :- !.
common_intersection([], X1, X1) :- !.
common_intersection([X3|X5], X2, X4) :-
    intersection(X2, X3, X1),
    common_intersection(X5, X1, X4).

intersection([], _, []) :- !.
intersection([X1|X2], X3, [X1|X4]) :-
        memberchk(X1, X3),
        !,
        intersection(X2, X3, X4).
intersection([_|X2], X3, X4) :-
        intersection(X2, X3, X4).

not_in_intersection(X5, X3, X1) :-
    flatten(X5, X4),
    sort(X4, X2),
    findall(X6, (member(X6,X2), \+ memberchk(X6,X3)), X1).

gcd([X1], X1) :- !.
gcd([X1,X2|X3], X4) :-
    gcd(X1, X2, X5),
    gcd([X5|X3], X4).

gcd(0, X1, X1) :- !.
gcd(X1, 0, X1) :- !.
gcd(X, X, X) :- !.
gcd(X, X3, X4) :-
    X > X3, !,
    X1 is X mod X3,
    gcd(X1, X3, X4).
gcd(X, X2, X3) :-
    X < X2,
    gcd(X2, X, X3).

get_max_abs_dvars(X2, X1) :-
    get_max_abs_dvars(X2, 0, X1).

get_max_abs_dvars([], X1, X1) :- !.
get_max_abs_dvars([X6|X7], X3, X1) :-
    fd_min(X6, X4),
    fd_max(X6, X5),
    X2 is max(X3, max(abs(X4),abs(X5))),
    get_max_abs_dvars(X7, X2, X1).

gen_signature([], []) :- !.
gen_signature([X1|X3], [X2|X4]) :-
    X2 in 0..2,
    X1 #< 0 #<=> X2 #= 0,
    X1 #= 0 #<=> X2 #= 1,
    X1 #> 0 #<=> X2 #= 2,
    gen_signature(X3, X4).

gen_cost_sum_abs(X3, X2) :-
    gen_sum_abs(X3, 0, X1),
    call(X1 #= X2).

gen_cost_sum_abs(X6, X3, X4) :-
    length(X3, X5),
    X2 is (X5+1) // 2,
    gen_sum_abs(X6, X2, X1),
    call(X1 #= X4).

gen_sum_abs([], X1, X1) :- !.
gen_sum_abs([X2|X3], X1, abs(X2)+X4) :-
    gen_sum_abs(X3, X1, X4).

gen_cost_sum_abs_max1(X3, X2) :-
    gen_sum_abs_max1(X3, X1),
    call(X1 #= X2).

gen_sum_abs_max1([], 0) :- !.
gen_sum_abs_max1([X1|X2], max(1,abs(X1))+X3) :-
    gen_sum_abs_max1(X2, X3).

gen_cost_diff0(X3, X2) :-
    gen_diff0(X3, X1),
    call(X1 #= X2).

gen_diff0([], 0) :- !.
gen_diff0([X1|X2], X3+X4) :-
    X3 #<=> X1 #\= 0,
    gen_diff0(X2, X4).

gen_cost_max_abs(X3, X1) :-
    gen_abs(X3, X2),
    call(maximum(X1, X2)).

gen_abs([], []) :- !.
gen_abs([X1|X2], [X3|X4]) :-
    X3 #= abs(X1),
    gen_abs(X2, X4).

atoms_concat([X2|X3], X1) :-
    atoms_concat(X3, X2, X1).

atoms_concat([], X1, X1) :- !.
atoms_concat([X2|X5], X3, X1) :-
    atom_concat(X3, X2, X4),
    atoms_concat(X5, X4, X1).

atom_proper_suffix_add_underscore(X5, X4) :-
    atom_codes('_', X6),
    atom_codes(X5, X3),
    atom_codes(X4, X2),
    append(X6, X2, X1),
    proper_suffix(X3, X1).

add_key(X2, X1) :-
    add_key(X2, 1, X1).

add_key([], _, []) :- !.
add_key([X|X3], X4, [X4-X|X5]) :-
    X1 is X4+1,
    add_key(X3, X1, X5).

prodlist(X1, X2) :-
(   foreach(X,X1),
    fromto(1,X3,X5,X2)
do  X5 is X3*X
).

gen_occ_vars(X1, X2, _, []) :-
    X1 > X2, !.
gen_occ_vars(X4, X5, X1, [X4-X2|X6]) :-
    X4 =< X5,
    X2 in 1..X1,
    X3 is X4+1,
    gen_occ_vars(X3, X5, X1, X6).

gen_occ_vars(X1, X2, _, [], []) :-
    X1 > X2, !.
gen_occ_vars(X4, X5, X1, [X4-X2|X6], [X2|X7]) :-
    X4 =< X5,
    X2 in 1..X1,
    X3 is X4+1,
    gen_occ_vars(X3, X5, X1, X6, X7).

compute_max_abs([], [], []) :- !.
compute_max_abs([X2|X4], [X3|X5], [X1|X6]) :-
    X1 is max(abs(X2),abs(X3)),
    compute_max_abs(X4, X5, X6).

split_list_wrt_smallest_length([], [], []) :- !.
split_list_wrt_smallest_length([X2|X3], [X2|X4], X5) :-
    arg(1, X2, X6),
    length(X6, X1),
    split_list_wrt_smallest_length(X3, X1, X4, X5).

split_list_wrt_smallest_length([], _, [], []) :- !.
split_list_wrt_smallest_length([X2|X3], X1, [X2|X4], X5) :-
    arg(1, X2, X6),
    length(X6, X1),
    !,
    split_list_wrt_smallest_length(X3, X1, X4, X5).
split_list_wrt_smallest_length(X1, _, [], X1).

cartesian_product_without_sort(X3, X4, X1) :-
    findall(X2, (member(X5, X3), member(X6, X4), append([X5], X6, X2)), X1).

cartesian_product_with_sort(X5, X6, X2) :-
    findall(X3, (member(X7, X5),
                  member(X8, X6),
                  ((is_list(X7), is_list(X8)) -> append(X7, X8,   X4) ;
                    is_list(X7)               -> append(X7, [X8], X4) ;
                                                 append([X7], X8, X4) ),
                  sort(X4, X3)),                                        X1),
    sort(X1, X2).

sort_wrt_list_length(X4, X2) :-
    add_len_key(X4, X3),
    keysort(X3, X1),
    add_len_key(X2, X1).

add_len_key([], []) :- !.
add_len_key([X1|X2], [X3-X1|X4]) :-
    length(X1, X3),
    add_len_key(X2, X4).

listify([], []) :- !.
listify([X1|X2], [[X1]|X3]) :-
    listify(X2, X3).

build_continuation_list([], [], []) :- !.
build_continuation_list([X2|X3], [X1|X4], [[X2|X1]|X5]) :-
    build_continuation_list(X3, X4, X5).

create_list_of_empty_lists(0, []) :- !.
create_list_of_empty_lists(X2, [[]|X3]) :-
    X2 > 0,
    X1 is X2-1,
    create_list_of_empty_lists(X1, X3).

remove_first_last_elements([], _, _, []) :- !.
remove_first_last_elements([X3|X5], [X1|X6], [X2|X7], [X4|X8]) :-
    remove_first_last_elements1(X3, X1, X2, X4),
    remove_first_last_elements(X5, X6, X7, X8).

remove_first_last_elements1([], _, _, []) :- !.
remove_first_last_elements1([X1|X3], X1, X2, X4) :-
    !,
    remove_last_element(X3, X2, X4).
remove_first_last_elements1([X2|X3], _, X1, [X2|X5]) :-
    remove_last_element(X3, X1, X5).

remove_last_element([], _, []) :- !.
remove_last_element([X1], X1, []) :- !.
remove_last_element([X1], _, [X1]) :- !.
remove_last_element([X2|X3], X1, [X2|X4]) :-
    remove_last_element(X3, X1, X4).


remove_first_last_elements([],  []) :- !.
remove_first_last_elements([_], []) :- !.
remove_first_last_elements([_|X3], X4) :-
    length(X3, X5),
    X1 is X5-1,
    prefix_length(X3, X4, X1).

complement_elements([], [], []) :- !.
complement_elements([X1|X3], [X2|X4], [X5|X6]) :-
    complement_elements1(X1, X2, X5),
    complement_elements(X3, X4, X6).

complement_elements1(X1, [], X1) :- !.
complement_elements1([], _, []) :- !.
complement_elements1([X1|X2], [X3|X4], [X1|X5]) :-
    X1 < X3,
    !,
    complement_elements1(X2, [X3|X4], X5).
complement_elements1([X1|X2], [X1|X3], X4) :-
    !,
    complement_elements1(X2, X3, X4).
complement_elements1([X1|X2], [_|X4], X5) :-
    complement_elements1([X1|X2], X4, X5).

intersect_elements([], [], []) :- !.
intersect_elements([X1|X3], [X2|X4], [X5|X6]) :-
    intersect_elements1(X1, X2, X5),
    intersect_elements(X3, X4, X6).

intersect_elements1(_, [], []) :- !.
intersect_elements1([], _, []) :- !.
intersect_elements1([X1|X2], [X3|X4], X5) :-
    X1 < X3,
    !,
    intersect_elements1(X2, [X3|X4], X5).
intersect_elements1([X1|X2], [X1|X3], [X1|X4]) :-
    !,
    intersect_elements1(X2, X3, X4).
intersect_elements1([X1|X2], [_|X4], X5) :-
    intersect_elements1([X1|X2], X4, X5).

more_than_one_unique_value([])  :- !, false.
more_than_one_unique_value([_]) :- !, false.
more_than_one_unique_value([X1|X2]) :-
   more_than_one_unique_value1(X2, X1).

more_than_one_unique_value1([X|_], X3) :-
   X =\= X3, !.
more_than_one_unique_value1([X|X2], _) :-
   more_than_one_unique_value1(X2, X).

write_list([]) :- !.
write_list([X1|X2]) :-
    write(X1), nl,
    write_list(X2).

write_list([], _) :- !.
write_list([X2|X3], X1) :-
    format(X1,'~w.~n',[X2]),
    write_list(X3, X1).

write_spaces(0) :- !.
write_spaces(X2) :-
    X2 > 0,
    write(' '),
    X1 is X2-1,
    write_spaces(X1).

binary_term_calculation(X1, X3, X4, X5, X6) :-
    (X1 = mfloor -> tab_get_min(X5,X2), X6 is (X3 // max(X4 - X2, 1)) ;
     X1 = plus   -> X6 is X3 + X4                                                ;
     X1 = minus  -> X6 is X3 - X4                                                ;
     X1 = prod   -> X6 is X3 * X4                                                ;
     X1 = abs    -> X6 is abs(X3 - X4)                                           ;
     X1 = min    -> X6 is min(X3, X4)                                            ;
     X1 = max    -> X6 is max(X3, X4)                                            ;
     X1 = floor  -> X4 =\= 0, X6 is X3 // X4                                   ;
     X1 = ceil   -> X4 =\= 0, X6 is (X3 + X4 - 1) // X4                      ;
     X1 = mod    -> X4 =\= 0, X6 is X3 mod X4                                  ;
     X1 = cmod   -> X3 =\= 0, X6 is X3 - (X4 mod X3)                         ;
     X1 = dmod   -> X4 =\= 0, X6 is X3 - (X3 mod X4)                         ;
     X1 = fmod   -> X4 =\= 0, X7 is X3 mod X4, (X7 = 0 -> X6 = X4 ; X6 = X7)   ;
                            false                                                             ).

intersect_lists([], _, []) :- !.
intersect_lists(_, [], []) :- !.
intersect_lists([X|X2], [X|X3], [X|X4]) :- !,intersect_lists(X2,X3,X4).
intersect_lists([X|X2], [X3|X4], X5) :-
    ((X @< X3) -> intersect_lists(X2, [X3|X4], X5) ; intersect_lists([X|X2], X4, X5)).

remove_elements_from_unsorted_list(X1, X2, X3) :-
    sort(X1, X4),
    sort(X2, X5),
    remove_elements_from_list(X4, X5, X3).

remove_elements_from_list([], _, []) :- !.
remove_elements_from_list(X1, [], X1)  :- !.
remove_elements_from_list([X|X2], [X|X3], X4) :- !,
    remove_elements_from_list(X2, X3, X4).
remove_elements_from_list([X|X2], [X3|X4], [X|X5]) :-
    X @< X3, !,
    remove_elements_from_list(X2, [X3|X4], X5).
remove_elements_from_list(X1, [_|X3], X4) :-
    remove_elements_from_list(X1, X3, X4).

del(X1, [X1|X2], X2).
del(X1, [X2|X3], [X2|X4]) :-
    del(X1, X3, X4).

gen_all_element_subset_pairs(X3, X1) :-
    length(X3, X10),
    keys_and_values(X3,X6,_),
    X9 is X10-1,
    findall([X4]-X7,
            (del(X4, X6, X8),
             sublist_max_card(X8,X9,X7),
             (X7 = [X12] ->
                
                memberchk(X4-X2, X3),
                memberchk(      X12-X5      , X3),
                (X2 < X5 ->
                    true
                ;
                 (X2 = X5, X4 < X12) ->
                    true
                ;
                    false)
             ;
                true
             )), X1).

combine_lists([], [], []) :- !.
combine_lists([], X1, X1) :- !.
combine_lists(X1, [], X1) :- !.
combine_lists([X|X2], [X|X3], [X|X4]) :-
    !,
    combine_lists(X2,X3,X4).
combine_lists([X|X2], [X3|X4], [X|X5]) :-
    X @< X3,
    !,
    combine_lists(X2,[X3|X4],X5).
combine_lists(X1, [X2|X3], [X2|X4]) :-
    combine_lists(X1,X3,X4).

combine_lists_exclusive([], [], []) :- !.
combine_lists_exclusive([], X1, X1) :- !.
combine_lists_exclusive(X1, [], X1) :- !.
combine_lists_exclusive([X|X2], [X3|X4], [X|X5]) :-
    X @< X3,
    !,
    combine_lists_exclusive(X2,[X3|X4],X5).
combine_lists_exclusive([X|X2], [X3|X4], [X3|X5]) :-
    X @> X3,
    !,
    combine_lists_exclusive([X|X2],X4,X5).
combine_lists_exclusive([_|X2], [_|X3], X4) :-
    combine_lists_exclusive(X2,X3,X4).

call_with_time_out(X1) :- 
    time_out(X1, 3000, X2),
    (X2 = success -> true ; write(time_out(X1)), nl, false). 

check_goal(X1, _) :-
    integer(X1), !.

check_goal(X3, X1) :-
    var(X3), !,
    fd_min(X3, X4),
    fd_max(X3, X5),
    (memberchk(X4, [inf,sup]) -> write('1: '), write(X1), nl, write(X3), nl, halt ;
     memberchk(X5, [inf,sup]) -> write('2: '), write(X1), nl, write(X3), nl, halt ;
                                  true                                                        ),
    X2 is X5-X4,
    (X2 > 200 -> write('3: '), write(X1), nl, write(X3), nl, halt ; true).

check_goal(X4, X1) :-
    functor(X4, X2, X3),
    (X2 = element -> X5 is X3 - 1 ; X5 = X3),
    check_goal(X5, X4, X1).

check_goal(0, _, _) :- !.
check_goal(X5, X2, X1) :-
    X5 > 0,
    arg(X5, X2, X3),
    check_goal(X3, X1),
    X4 is X5-1,
    check_goal(X4, X2, X1).

group_same_keys([], []) :- !.
group_same_keys([X2-X3|X4], [X2-[X3|X5]|X6]) :-
    group_same_keys1(X4, X2, X5, X1),
    group_same_keys(X1, X6).

group_same_keys1([X1-X2|X3], X1, [X2|X4], X5) :- !,
    group_same_keys1(X3, X1, X4, X5).
group_same_keys1(X1, _, [], X1).

merge_lists([], X1, X1) :- !.
merge_lists([X3|X4], X1, X2) :-
    merge_lists(X4, [X3|X1], X2).

length_prefix([X3|X4], X3, X5, X1) :- !,
    X2 is X5+1,
    length_prefix(X4, X3, X2, X1).
length_prefix(_, _, X1, X1). 

remove_first_elem([X1|X2], X1, X3) :- !,
    remove_first_elem(X2, X1, X3).
remove_first_elem(X1, _, X1).

sum_squares(X2, X1) :-
    sum_squares(X2, 0, X1).

sum_squares([], X1, X1) :- !.
sum_squares([X4|X5], X1, X3) :-
    X2 is X1 + X4*X4,
    sum_squares(X5, X2, X3).

get_non_zero_exponents([], _, []) :- !.
get_non_zero_exponents([X3|X4], X5, X1) :-
    X2 is X5+1,
    (X3 = 0 -> get_non_zero_exponents(X4, X2, X1)             ;
              get_non_zero_exponents(X4, X2, X6), X1 = [X5-X3|X6]).

count_distinct_vals([], X1, X2) :-
    !,
    (foreach(X3, X1), foreach(X3-0,X2)
    do
     true
    ).
count_distinct_vals([X4|X8], X3, X1) :-
    count_distinct_vals(X8, X3, X2),
    (foreach(X7-X5, X2), foreach(X7-X6, X1), param(X4)
    do
     (X7 = X4 ->
         X6 is X5 + 1
     ;
         X6 is X5
     )
    ).

unify_variables([], _, _, _) :- !.
unify_variables([X5|X6], X7, X1, X2) :-
    arg(X5, X1, X3),
    arg(X7, X2,    X3),
    X4 is X7+1,
    unify_variables(X6, X4, X1, X2).

collect_temporal_attrs(X1, X2, _, _, _, _, _, _, []) :-
    X1 > X2, !.
collect_temporal_attrs(X11, X12, X13, X14, X1, X5, X3, X7, X2) :-
    X11 =< X12,                                                       
    arg(X11, X5,  X8),                                         
    arg(X11, X3, X6),                                        
    arg(X11, X7,   X9),    
    X10 is X11+1,
    (X11 = X13 ->                                                     
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
     X11 = X14 ->                                                     
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
     X8 = set ->                                                
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
     X8 = cst ->                                                
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
     X6 > 0 ->                                                 
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
     memberchk(within(col(X1,X11),col(X1,_)), X9) -> 
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X2)
    ;
        collect_temporal_attrs(X10,X12,X13,X14,X1,X5,X3,X7,X4),
        X2 = [X11|X4]                                    
    ).                                                            
