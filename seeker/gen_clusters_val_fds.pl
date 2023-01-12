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
% Purpose: Utilities required for generation of sequences of Conditional Functional Dependencies and Prefix Trees of CFDs
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_clusters_val_fds,[gen_clusters_val_fds/5,
                                collect_cluster_zero/2,
                                build_tree_wrt_common_prefix/2]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).
:- use_module(bool_cond_utility).

gen_clusters_val_fds(X5, X6, X2, X1, X4) :-
    gen_model1(X5, X6, X2, X1, X7),
    group_fd_with_val1(X7, X3),
    sort(X3, X4).

build_tree_wrt_common_prefix([], []) :- !.
build_tree_wrt_common_prefix(X2, [X5|X3]) :-
    X2 = [[X8-X6|_]|_],
    split_wrt_common_prefix(X2, X8-X6, X1, X7),
    X5 = t(X8,X6,_,X4),
    build_tree_wrt_common_prefix(X1, X4),
    build_tree_wrt_common_prefix(X7, X3).

split_wrt_common_prefix([[[]-X1]|X2], []-X1, [], X2) :- !.
split_wrt_common_prefix([[X3-X1|X4]|X5], X3-X1, [X4|X6], X2) :-
    !,
    split_wrt_common_prefix(X5, X3-X1, X6, X2).
split_wrt_common_prefix(X1, _, [], X1).

group_fd_with_val1([], []) :- !.
group_fd_with_val1([X3|X5], [X1|X6]) :-
    arg(1, X3, X4),
    arg(2, X3, X2),
    group_fd_with_val(X4, X2, X1),
    group_fd_with_val1(X5, X6).

group_fd_with_val([], [X1], [[]-X1]) :- !.
group_fd_with_val([X2|X3], [X1|X4], [X2-X1|X5]) :-
    group_fd_with_val(X3, X4, X5).

collect_cluster_zero([],       []       ) :- !.
collect_cluster_zero([t(_,  X2, _, X1)|_], [X2|X4]) :-
    collect_cluster_zero(X1, X4).

gen_model1(X12, X13, X3, X1, X16) :-

    
    
    length(X3, X17),
    length(X5, X17),
    list_to_fdset(X3, X14),
    declare_domains1(X5, X14),
    all_distinct(X5),    

    
    
    X15 is X17-1,
    declare_domains0(X15, X2, X14),

    
    
    length(X11, X15),
    declare_domains_fdvars(X11, X15, X1),

    
    
    gen_table_ctr(X15, X5, X2, X11, X1),

    
    
    
    gen_incompatible_value_ctrs(1, X15, X5, X2),

    
    
    length(X6, X13),
    domain(X6, 0, 1),
    reverse(X11, X7),
    link_used_attrs_to_used_fds(X6, 1, X7, X1),

    
    
    append(X5, X11, X9),   
    gen_sum_term(X6, var, X10), 
    X18 in 1..X13,                       
    call(X18 #= X10),                  
    get_min_nb_of_attributes_for_a_solution(X18, X9, X8),
    X18 #= X8,                      
    findall(t(X4, X5),
            (labeling([], X9),        
             get_selected_fd(X11, X15, X12, X1, X4)),
            X16).

get_min_nb_of_attributes_for_a_solution(X1, X2, _) :-
    once(labeling([], [X1|X2])),
    assert(min_nb_of_attributes_for_a_solution(X1)),
    false.
get_min_nb_of_attributes_for_a_solution(_, _, X1) :-
    min_nb_of_attributes_for_a_solution(X1),
    retractall(min_nb_of_attributes_for_a_solution(_)).

declare_domains1([], _) :- !.
declare_domains1([X2|X3], X1) :-
    X2 in_set X1,
    declare_domains1(X3, X1).

declare_domains0(0, [], _) :- !.
declare_domains0(X4, [X1|X5], X2) :-
    X4 > 0,
    !,
    length(X1, X4),
    declare_domains1(X1, X2),
    X3 is X4-1,
    declare_domains0(X3, X5, X2).

declare_domains_fdvars([], _, _) :- !.
declare_domains_fdvars([X5|X12], X3, X6) :-
    arg(X3, X6, X4-_),  
    functor(X4, cfd_val, X7), 
    findall(X9, (X14 in 1..X7,     
                  indomain(X14),
                  arg(X14,X4,X8),
                  member(t(_,_,X11), X8),
                  length(X11,X9)),
            X2),
    sumlist(X2, X10),         
    X5 in 1..X10,                 
    X1 is X3-1,
    declare_domains_fdvars(X12, X1, X6).

gen_table_ctr(0, [_], [], [], _) :- !.
gen_table_ctr(X10, [X4|X11], [X3|X12], [X6|X13], X2) :-
    X10 > 0,
    X7 = [X6,X4|X3],
    arg(X10, X2, X1-_),
    collect_functor_args(X1, X8),
    gen_table_tuples_cur_level(X8, 1, X5, []),
    table([X7], X5),
    X9 is X10-1,
    gen_table_ctr(X9, X11, X12, X13, X2).

collect_functor_args(X1, X3) :-
    functor(X1, _, X2),
    collect_functor_args(1, X2, X1, X3).

collect_functor_args(X1, X2, _, []) :-
    X1 > X2,
    !.
collect_functor_args(X4, X5, X1, [X2|X6]) :-
    X4 =< X5,
    arg(X4, X1, X2),
    X3 is X4+1,
    collect_functor_args(X3, X5, X1, X6).

gen_table_tuples_cur_level([], _, X1, X1) :- !.
gen_table_tuples_cur_level([X6|X7], X5, X1, X4) :-
    gen_table_tuples_cur_level1(X6, X5, X2, X1, X3),
    gen_table_tuples_cur_level(X7, X2, X3, X4).

gen_table_tuples_cur_level1([], X2, X2, X1, X1) :- !.
gen_table_tuples_cur_level1([t([X10],X8,X6)|X11], X9, X1, X2, X7) :-
    length(X6, X3),
    X4 is X9+X3,
    collect_new_tuples(X9, X4, X10, X8, X2, X5),
    gen_table_tuples_cur_level1(X11, X4, X1, X5, X7).

collect_new_tuples(X3, X1, _, _, X2, X2) :-
    X3 = X1, !.
collect_new_tuples(X6, X1, X8, X7, X2, X4) :-
    X6 < X1,
    X2 = [[X6,X8|X7]|X3],
    X5 is X6 + 1,
    collect_new_tuples(X5, X1, X8, X7, X3, X4).

gen_incompatible_value_ctrs(X1, X2, _, _) :-
    X1 > X2,
    !.
gen_incompatible_value_ctrs(X4, X5, [X2|X6], [_|X1]) :-
    X4 =< X5,
    gen_incompatible_value_ctrs1(X1, X2),
    X3 is X4+1,
    gen_incompatible_value_ctrs(X3, X5, X6, X1).

gen_incompatible_value_ctrs1([], _) :- !.
gen_incompatible_value_ctrs1([X1|X3], X2) :-
    gen_incompatible_value_ctrs2(X1, X2),
    gen_incompatible_value_ctrs1(X3, X2).

gen_incompatible_value_ctrs2([], _) :- !.
gen_incompatible_value_ctrs2([X1|X3], X2) :-
    X2 #\= X1,
    gen_incompatible_value_ctrs2(X3, X2).

get_selected_fd([], _, _, _, []) :- !.
get_selected_fd([X7|X9], X10, X6, X1, [X2|X11]) :-
    arg(X10, X1, _-X3),
    findall(col(X6,X5), (member(X5-X4, X3),
                                   memberchk(X7, X4)),                X2),
    X8 is X10-1,
    get_selected_fd(X9, X8, X6, X1, X11).

link_used_attrs_to_used_fds([], _, _, _) :- !.
link_used_attrs_to_used_fds([X2|X6], X7, X3, X1) :-
    link_used_attrs_to_used_fds1(X3, 1, X1, X2, X7, X4),
    call(X2 #<=> X4),
    X5 is X7+1,
    link_used_attrs_to_used_fds(X6, X5, X3, X1).

link_used_attrs_to_used_fds1([], _, _, _, _, 0) :-
    !.
link_used_attrs_to_used_fds1([X6|X8], X9, X1, X3, X10, X6 in_set X5 #\/ X11) :-
    arg(X9, X1, _-X2),
    memberchk(X10-X4, X2),
    !,
    list_to_fdset(X4, X5),
    X7 is X9+1,
    link_used_attrs_to_used_fds1(X8, X7, X1, X3, X10, X11).
link_used_attrs_to_used_fds1([_|X5], X6, X1, X2, X7, X8) :-
    X3 is X6+1,
    link_used_attrs_to_used_fds1(X5, X3, X1, X2, X7, X8).
