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
% Purpose: GENERATE THE METADATA ASSOCIATED WITH THE DIFFERENT TABLES (use the file tables.pl to get the names of the tables)
% Authors : Nicolas Beldiceanu, IMT Atlantique
%           Ramiz Gindullin,    IMT Atlantique (primary & foreign keys)


:- use_module(library(timeout)).
:- use_module(library(lists)).
:- use_module(library(samsort)).
:- use_module(library(clpfd)).
:- use_module(utility).
:- use_module(tables).
:- use_module(table_access).
:- use_module(gen_candidate_tables).
:- use_module(rank_fd).
:- use_module(gen_clusters_val_fds).

top(0) :- 
    top(model_seeker,0), top(model_seeker,-1).


top(X5, X1) :- 
    X1 >= 0,
    get_tables(X5, _, _, _, X9), 
    sort(X9, X2),                           
    member(X8, X2),
    retractall(prev_table_meta_data(_)),                  
    (X1 > 0 ->                                 
        X10 in 2..X1,
        indomain(X10)
    ;                                                     
        X10 = 0
    ),
    number_codes(X10, X6),                        
    atom_codes(X7, X6),                      
    atoms_concat(['data/',X5,'/data',X7,'/'],
                 X3),
    get_metadata_attributes(X4),
    gen_metadata(X5, X8, X10, X4, X3, X1), 
    false.

top(X1, -1) :- !,                    
    get_tables(X1, _, _, _, X2), 
    read_all_data_and_meta_data_files(X2, X1), 
    gen_all_fks(X2, X1, X2). 
top(_, _).                                  

gen_metadata(X8, X10, X13, X5, X6, X2) :- 
    atom_concat(X6, X10, X1),
    atom_concat(X1, '.pl', X4),
    max_size_combi(X8, X11),                    
    (X13 = X11 -> write(X4), nl ; true),     
    consult(X4),
    statistics(runtime, [X17|_]),
    build_meta_data(X8, X13, X2, X5, X10, X3),          
    (X13 = X11 -> statistics(runtime, [X18|_]), X14 is X18-X17, write(time(X14)), nl ; true), 
    atom_concat(X1, '_metadata.pl', X7),
    get_metadata_arity(X12),
    write_metadata_file(X7, X12, X3),
    signature(X10, _, X15),
    functor(X15, t, X9),
    functor(X16, X10, X9),
    retractall(signature(_,_,_)),
    retractall(X16).

write_metadata_file(X2, X5, X1) :- 
    open(X2, write, X6),
    number_codes(X5, X3),                     
    atom_codes(X4, X3),                   
    format(X6,':- multifile table_metadata/~a.~n',[X4]),
    format(X6,':- dynamic table_metadata/~a.~n~n',[X4]),
    format(X6,'~w.~n',[X1]),
    close(X6).

build_meta_data(X21, X61, X6, X15, X22, X7) :- 
    signature(X22, X61, X62),
    functor(X62,     t,      X23),
    get_table_size(X22, X23, X47),
    functor(X30,       name,           X23),
    functor(X55,          kind,           X23),
    functor(X48,         inout,          X23),
    functor(X63,           min,            X23),
    functor(X64,           max,            X23),
    functor(X56,          types,          X23),
    functor(X57,          nval,           X23),
    functor(X36,        median,         X23),
    functor(X65,           gcd,            X23),
    functor(X66,           sum,            X23),
    functor(X58,          mean,           X23),
    functor(X49,         equal,          X23),
    functor(X69,            fd,             X23),
    functor(X59,          nb_fd,          X23),
    functor(X67,           cmp,            X23),
    functor(X50,         nb_cmp,         X23),
    functor(X68,           ctr,            X23),
    functor(X37,        maxocc,         X23),
    functor(X16,     maxoccval,      X23),
    functor(X17,     affinity,       X23),
    functor(X10,   distinct_vals,  X23),
    functor(X38,        vals_fds,       X23),
    functor(X4, monotonicities, X23), 
    X2 = 4,                                
    get_nb_primary_and_input(1, X23, X62, 0, X5), 
    gen_col_names(1, X23, X62, X30),
    gen_kinds(1, X23, X62, X55),
    gen_inouts(1, X23, X62, X48),
    gen_mins(1, X23, X22, X63),
    gen_maxs(1, X23, X22, X64),
    gen_types(1, X23, X22, X63, X64, X56), 
    gen_nvals(1, X23, X22, X56, X2, X57, X10), 
    gen_medians_maxoccs_maxoccvals(1, X23, X22, X56, X36, X37, X16), 
    gen_gcds(1, X23, X22, X56, X65), 
    gen_sums(1, X23, X22, X56, X66), 
    gen_means(1, X23, X47, X56, X66, X58), 
    gen_equals(1, X23, X22, X56, X66, X49), 
    gen_fds(X21, X61, X15, X23, X22, X55, X48, X56, X49, X5, X10, X69, X38), 
    gen_nb_fds(1, X23, X22, X69, X59),
    gen_cmps(X23, X22, X56, X49, X67), 
    gen_nb_cmps(1, X23, X22, X67, X50),
    gen_ctrs(1, X23, X61, X22, X55, X56, X49, X67, X68), 
    (X61 = 0 -> 
        get_table(X21, 0, _, X39, X22), 
        ((memberchk(no_pk, X39) ; memberchk(pk([]), X39)) -> X70 = []                            ;
          memberchk(pk(X72), X39)                              -> X70 = [1-X72]                        ;
                                                                     gen_pks(X22,
                                                                             X47, X23, X56, 
                                                                             X63, X64,
                                                                             X57, X49, X37, X70))
    ;
        true
    ),
    (X61 = 0 ->  
        true      
    ;             
        X70 = [], 
        X71 = []  
    ),
    gen_affinities(1, X23, X47, X55, X56, X49, X22, X17),
    gen_monotonicities(1, X23, X22, X21, X61, X6, X55, X4), 
    gen_inf_sup(X63, X64, X51),
    (X61 = 0 -> true ; X24 = []), 
    get_metadata_arity(X60),
    functor(X7, table_metadata, X60),
    memberchk(X11-table_name,          X15), arg(X11,      X7, X22),
    memberchk(X40-max_n,                    X15), arg(X40,           X7, X61),
    memberchk(X12-nb_columns,          X15), arg(X12,      X7, X23),
    memberchk(X25-nb_rows,                X15), arg(X25,         X7, X47),
    memberchk(X14-col_names,            X15), arg(X14,       X7, X30),
    memberchk(X31-kinds,                   X15), arg(X31,          X7, X55),
    memberchk(X26-in_outs,                X15), arg(X26,         X7, X48),
    memberchk(X41-mins,                     X15), arg(X41,           X7, X63),
    memberchk(X42-maxs,                     X15), arg(X42,           X7, X64),
    memberchk(X32-types,                   X15), arg(X32,          X7, X56),
    memberchk(X33-nvals,                   X15), arg(X33,          X7, X57),
    memberchk(X18-medians,               X15), arg(X18,        X7, X36),
    memberchk(X43-gcds,                     X15), arg(X43,           X7, X65),
    memberchk(X44-sums,                     X15), arg(X44,           X7, X66),
    memberchk(X34-means,                   X15), arg(X34,          X7, X58),
    memberchk(X27-equals,                 X15), arg(X27,         X7, X49),
    memberchk(X52-fds,                       X15), arg(X52,            X7, X69),
    memberchk(X35-nb_fds,                  X15), arg(X35,          X7, X59),
    memberchk(X45-cmps,                     X15), arg(X45,           X7, X67),
    memberchk(X28-nb_cmps,                X15), arg(X28,         X7, X50),
    memberchk(X46-ctrs,                     X15), arg(X46,           X7, X68),
    memberchk(X19-maxoccs,               X15), arg(X19,        X7, X37),
    memberchk(X8-maxoccvals,         X15), arg(X8,     X7, X16),
    memberchk(X53-pks,                       X15), arg(X53,            X7, X70),
    memberchk(X54-fks,                       X15), arg(X54,            X7, X71),
    memberchk(X9-affinities,         X15), arg(X9,     X7, X17),
    memberchk(X29-inf_sup,                X15), arg(X29,         X7, X51),
    memberchk(X13-ranked_fds,          X15), arg(X13,      X7, X24),
    memberchk(X3-distinct_vals,    X15), arg(X3,   X7, X10),
    memberchk(X20-vals_fds,              X15), arg(X20,        X7, X38),
    memberchk(X1-monotonicities, X15), arg(X1, X7, X4), 
    retractall(prev_table_meta_data(_)),
    assert(prev_table_meta_data(X7)),
    !.
build_meta_data(_, X2, _, _, X1, _) :- 
    write('could not build metadata for table '), write(X1), write(' for MaxN='), write(X2), halt.

get_nb_primary_and_input(X2, X3, _, X1, X1) :-
    X2 > X3, !.
get_nb_primary_and_input(X6, X7, X1, X3, X4) :-
    X6 =< X7,
    (arg(X6, X1, t(_,primary,input)) -> X2 is X3+1 ; X2 = X3),
    X5 is X6+1,
    get_nb_primary_and_input(X5, X7, X1, X2, X4).

get_table_size(X1, X6, X2) :-
    findall(X5, (functor(X3,X1,X6), call(X3), arg(1, X3, X5)), X4),
    length(X4, X2).

gen_col_names(X1, X2, _, _) :-
    X1 > X2, !.
gen_col_names(X5, X6, X2, X1) :-
    X5 =< X6,
    arg(X5, X2, t(X3,_,_)),
    arg(X5, X1, X3),
    X4 is X5+1,
    gen_col_names(X4, X6, X2, X1).

gen_kinds(X1, X2, _, _) :-
    X1 > X2, !.
gen_kinds(X5, X6, X2, X1) :-
    X5 =< X6,
    arg(X5, X2, t(_,X3,_)),
    arg(X5, X1, X3),
    X4 is X5+1,
    gen_kinds(X4, X6, X2, X1).

gen_inouts(X1, X2, _, _) :-
    X1 > X2, !.
gen_inouts(X5, X6, X3, X1) :-
    X5 =< X6,
    arg(X5, X3, t(_,_,X2)),
    arg(X5, X1, X2),
    X4 is X5+1,
    gen_inouts(X4, X6, X3, X1).

gen_mins(X1, X2, _, _) :-
    X1 > X2, !.
gen_mins(X9, X10, X1, X2) :-
    X9 =< X10,                         
    findall(X6, (functor(X3,X1,X10), call(X3), arg(X9, X3, X4), get_mins_value(X4, X6)), X5), 
    min_member(X7, X5),
    arg(X9, X2, X7),
    X8 is X9+1,
    gen_mins(X8, X10, X1, X2).

get_mins_value(X1, X1) :-    
    integer(X1), !.
get_mins_value(X1-_, X1) :-  
    integer(X1), !.
get_mins_value(X2, X3) :-   
    is_list(X2), !,
    X2 = [X1|_],
    (integer(X1) -> X3 = X1                      ;
     X1 = X4-_  -> X3 = X4                        ;
                       write(get_mins_value1), nl, halt).
get_mins_value(_, _) :-
    write(get_mins_value2), nl, halt.

gen_maxs(X1, X2, _, _) :-
    X1 > X2, !.
gen_maxs(X9, X10, X1, X2) :-
    X9 =< X10,                         
    findall(X6, (functor(X3,X1,X10), call(X3), arg(X9, X3, X4), get_maxs_value(X4, X6)), X5), 
    max_member(X7, X5),
    arg(X9, X2, X7),
    X8 is X9+1,
    gen_maxs(X8, X10, X1, X2).

get_maxs_value(X1, X1) :-    
    integer(X1), !.
get_maxs_value(_-X1, X1) :-  
    integer(X1), !.
get_maxs_value(X1, X3) :-   
    is_list(X1), !,
    last(X1, X2),
    (integer(X2) -> X3 = X2                      ;
     X2 = _-X4   -> X3 = X4                        ;
                      write(get_maxs_value1), nl, halt).
get_maxs_value(_, _) :-
    write(get_maxs_value2), nl, halt.

gen_types(X1, X2, _, _, _, _) :- 
    X1 > X2, !.
gen_types(X9, X10, X1, X3, X4, X2) :- 
    X9 =< X10,
    (check_if_set(X1, X10, X9) -> 
        X5 = set
    ;
        arg(X9, X3, X6),
        arg(X9, X4, X7),
        X11 is X7-X6,
        (X11 = 0              -> X5 = cst  ;
         (X6 = 0, X7 = 1) -> X5 = bool ;
                               X5 = int  )
    ),
    arg(X9, X2, X5),
    X8 is X9+1,
    gen_types(X8, X10, X1, X3, X4, X2). 

check_if_set(X1, X4, X5) :-    
    functor(X2, X1, X4),    
    call(X2),                     
    arg(X5, X2, X3),              
    (is_list(X3) -> true ;         
     X3 = _-_    -> true ;         
                     false),        
    !.                              

gen_nvals(X1, X2, _, _, _, _, _) :-   
    X1 > X2, !.
gen_nvals(X14, X15, X5, X6, X2, X7, X3) :-
    X14 =< X15,
    arg(X14, X6, X8),            
    (X8 = set ->                  
        arg(X14, X7, none),        
        arg(X14, X3, [])    
    ;
        findall(X12, (functor(X9,X5,X15), call(X9), arg(X14, X9, X12)), X10),
        sort(X10, X4),
        length(X4, X11),
        arg(X14, X7, X11),
        (X11 =< X2 ->
            count_distinct_vals(X10, X4, X1),
            arg(X14, X3, X1)
        ;
            arg(X14, X3, [])
        )
    ),
    X13 is X14+1,
    gen_nvals(X13, X15, X5, X6, X2, X7, X3).

gen_medians_maxoccs_maxoccvals(X1, X2, _, _, _, _, _) :- 
    X1 > X2, !.
gen_medians_maxoccs_maxoccvals(X19, X20, X3, X10, X5, X6, X1) :-
    X19 =< X20,
    arg(X19, X10, X11),                                 
    (X11 = set ->                                       
        X7 = none, X8 = none, X4 = none   
    ;
        findall(X14, (functor(X12,X3,X20), call(X12), arg(X19, X12, X14)), X13),
        samsort(X13, X2),
        length(X2, X21),
        X22 is X21 // 2 + 1,
        suffix_length(X2, X9, X22),
        X15 is X21 mod 2,
        (X15 = 1 ->
            X9 = [X7|_]
        ;
            X9 = [X16,X17|_], X7 is (X16+X17) / 2
        ),
        gen_maxoccs_maxoccvals(X2, X8, X4)
    ),
    arg(X19, X5,    X7),
    arg(X19, X6,    X8),
    arg(X19, X1, X4),
    X18 is X19+1,
    gen_medians_maxoccs_maxoccvals(X18, X20, X3, X10, X5, X6, X1).

gen_maxoccs_maxoccvals([], 0, _) :- !.
gen_maxoccs_maxoccvals([X3|X4], X2, X1) :-
    gen_maxoccs_maxoccvals1(X4, 1, X3, 1, X3, X2, X1).

gen_maxoccs_maxoccvals1([], _, _, X2, X1, X2, X1) :- !.
gen_maxoccs_maxoccvals1([X10|X11], X7, X8, X4, X3, X9, X5) :-
    (X10 = X8 ->
        X6 is X7+1,
        (X6 > X4 ->
            X2    = X6,
            X1 = X10
        ;
            X2    = X4,
            X1 = X3
        ),
        gen_maxoccs_maxoccvals1(X11, X6, X8, X2, X1, X9, X5)
    ;
        gen_maxoccs_maxoccvals1(X11, 1, X10, X4, X3, X9, X5)
    ).

gen_gcds(X1, X2, _, _, _) :- 
    X1 > X2, !.
gen_gcds(X11, X12, X1, X4, X5) :- 
    X11 =< X12,
    arg(X11, X4, X6),                                 
    (X6 = set ->                                       
        X8 = none                                       
    ;
        findall(X3, (functor(X7,X1,X12), call(X7), arg(X11, X7, X9), X3 is abs(X9)), X2),
        gcd(X2, X8)
    ),
    arg(X11, X5, X8),
    X10 is X11+1,
    gen_gcds(X10, X12, X1, X4, X5). 

gen_sums(X1, X2, _, _, _) :- 
    X1 > X2, !.
gen_sums(X10, X11, X1, X2, X3) :- 
    X10 =< X11,
    arg(X10, X2, X4),                                 
    (X4 = set ->                                       
        X7 = none                                       
    ;
        findall(X8, (functor(X5,X1,X11), call(X5), arg(X10, X5, X8)), X6),
        sumlist(X6, X7)
    ),
    arg(X10, X3, X7),
    X9 is X10+1,
    gen_sums(X9, X11, X1, X2, X3). 

gen_means(X1, X2, _, _, _, _) :- 
    X1 > X2, !.
gen_means(X9, X10, X1, X2, X4, X3) :- 
    X9 =< X10,
    arg(X9, X2, X5),                                 
    (X5 = set ->                                       
        X6 = none                                      
    ;
        arg(X9, X4, X7),
        X6 is X7 / X1
    ),
    arg(X9, X3, X6),
    X8 is X9+1,
    gen_means(X8, X10, X1, X2, X4, X3). 

gen_equals(X1, X2, _, _, _, _) :- 
    X1 > X2, !.
gen_equals(X7, X8, X1, X3, X4, X2) :- 
    (X7 = 1 ->
        arg(X7, X2, 0)
    ;
     arg(X7, X3, set) ->  
        arg(X7, X2, 0)   
    ;
        X7 =< X8,
        X9 is X7-1,
        arg(X7, X4, X5),
        gen_equals1(X9, X7, X8, X1, X4, X5, 0, X2)
    ),
    X6 is X7+1,
    gen_equals(X6, X8, X1, X3, X4, X2). 

gen_equals1(0, X2, _, _, _, _, _, X1) :- !,
    arg(X2, X1, 0).
gen_equals1(X14, X15, X16, X1, X8, X9, X4, X3) :-
    X14 >= 1,
    X13 is X14-1,
    arg(X14, X8, X10),
    (X9 = X10 ->
        (X4 = 0 ->
            findall(X11, (functor(X5,X1,X16), call(X5), arg(X15,X5,X11)), X2)
        ;
            X2 = X4
        ),
        findall(X12, (functor(X6,X1,X16), call(X6), arg(X14,X6,X12)), X7),
        (X2 = X7 -> arg(X15, X3, X14) ; gen_equals1(X13, X15, X16, X1, X8, X9, X2, X3))
    ;
        gen_equals1(X13, X15, X16, X1, X8, X9, X2, X3)
    ).

gen_fds(X9, X20, X7, X10, X11, X18, X15, X19, X16, X2, X5, X21, X13) :- 
    ((X20 > 2, prev_table_meta_data(_)) ->
        prev_table_meta_data(X1),
        memberchk(X6-nb_columns, X7), arg(X6, X1, X3),
        memberchk(X12-equals,        X7), arg(X12,    X1, X8),
        memberchk(X17-fds,              X7), arg(X17,       X1, X14),
        ((X10 = X3, X16 = X8) -> X4 = 1 ; X4 = 0)
    ;
        X4 = 0
    ),
    gen_fds1(1, X10, X9, X11, X18, X15, X19, X16, X2, X20, X4, X14, X5, X21, X13). 

gen_fds1(X1, X2, _, _, _, _, _, _, _, _, _, _, _, _, _) :- 
    X1 > X2, !.
gen_fds1(X35, X36, X11, X12, X25, X21, X26, X22, X5, X29, X6, X17, X7, X32, X18) :- 
    X35 =< X36,
    arg(X35, X25,  X30),
    arg(X35, X21, X27),
    arg(X35, X26,  X31),
    arg(X35, X22, X28),
    ( X31  = set                     -> arg(X35, X32, []), arg(X35, X18, []) ;
     (X30  = primary, X27 = input) -> arg(X35, X32, []), arg(X35, X18, []) ;
     (X30  = variable)               -> arg(X35, X32, []), arg(X35, X18, []) ;
      X31  = cst                     -> arg(X35, X32, []), arg(X35, X18, []) ;
      X28 > 0                       -> arg(X35, X32, []), arg(X35, X18, []) ;
        (X11 \== model_seeker ->
            findall(X37, (X37 in 1..X36, X37 #\= X35, indomain(X37), arg(X37,X25,primary),   arg(X37,X22,0)), X14),
            findall(X37, (X37 in 1..X36, X37 #\= X35, indomain(X37), arg(X37,X25,secondary), arg(X37,X22,0)), X15),
            X19 is min(X5+1,10),
            (X5 >= 5 -> X16 = 3 ; X16 = 4)
        ;
            findall(X37, (X37 in 1..X36, X37 #\= X35, indomain(X37), arg(X37,X21,input), arg(X37,X22,0)), X14),
            X15 = [],
            X19 is 5,
            X16 is 5
        ),
        (X6 = 1 ->                                 
            arg(X35, X17, X10),
            select_previous_fd(X10, X4),  
            (search_functional_dependencies(X4, X35, X36, X29, X12, []-[], X10, _) ->
                arg(X35, X32, X10)                       
            ;                                                 
                findall(X33, sublist_max_card(X14,X15,X16,X19,X33), X8),
                search_functional_dependencies(X8, X35, X36, X29, X12, []-[], X23, _),
                arg(X35, X32, X23)
            )
        ;                                                     
            findall(X33, sublist_max_card(X14,X15,X16,X19,X33), X8),
            search_functional_dependencies(X8, X35, X36, X29, X12, []-[], X23, _),
            arg(X35, X32, X23)
        ),
        arg(X35, X7, X3),
        (X3 = [_,_,_|_] ->                      
            keys_and_values(X3,X9,_),
            gen_all_element_subset_pairs(X3, X1),
            gen_fds2(X1, X14, X15, X16, X19, X35, X36, X29, X12, X13),
            two_levels_grouping_fds2(X13, X9, X2),
            (gen_clusters_val_fds(X12, X36, X9, X2, X24) ->
                true
            ;
                write(gen_clusters_val_fds(X12)), nl, halt
            ),
            arg(X35, X18, X24),
            max_size_combi(X11, X20), 
            (X29 = X20 ->                  
                write('generate cluster facts for column '), write(X35), write(' of table '), write(X12), nl
            ;
                true
            )
        ;
            arg(X35, X18, [])
        )
    ),
    X34 is X35+1,
    gen_fds1(X34, X36, X11, X12, X25, X21, X26, X22, X5, X29, X6, X17, X7, X32, X18). 

two_levels_grouping_fds2(X4, X3, X1) :-
    gen_keys_for_grouping(X4, X2),
    length(X3, X5),
    X6 is X5-1,
    functor(X1, cfd, X6),
    two_levels_grouping_fds2a(1, X6, X5, X3, X1, X2).

two_levels_grouping_fds2a(X1, X2, _, _, _, _) :-
    X1 > X2,
    !.
two_levels_grouping_fds2a(X12, X13, X14, X5, X1, X3) :-
    X12 =< X13,
    findall(key(X12,X8)-t(X9,X10,X6), member(key(X12,X8)-t(X9,X10,X6), X3), X2),
    functor(X7, cfd_val, X14),
    arg(X12, X1, X7-X4),
    two_levels_grouping_fds2b(X5, 1, X7, X2),
    two_levels_grouping_fds2c(X14, X7, X4),
    X11 is X12+1,
    two_levels_grouping_fds2a(X11, X13, X14, X5, X1, X3).

two_levels_grouping_fds2b([], _, _, _) :-
    !.
two_levels_grouping_fds2b([X5|X9], X10, X3, X1) :-
    findall(t(X6,X7,X4), member(key(_,X5)-t(X6,X7,X4), X1), X2),
    arg(X10, X3, X2),
    X8 is X10+1,
    two_levels_grouping_fds2b(X9, X8, X3, X1).

two_levels_grouping_fds2c(X5, X4, X2) :-
    two_levels_grouping_fds2c(1, X5, 1, X4, X3),
    sort(X3, X1),
    group_same_keys(X1, X2).

two_levels_grouping_fds2c(X1, X2, _, _, []) :-
    X1 > X2,
    !.
two_levels_grouping_fds2c(X9, X10, X5, X6, X3) :-
    X9 =< X10,
    arg(X9, X6, X7),
    two_levels_grouping_fds2d(X7, X5, X4, X2),
    X8 is X9+1,
    two_levels_grouping_fds2c(X8, X10, X4, X6, X1),
    append(X2, X1, X3).
    
two_levels_grouping_fds2d([], X1, X1, []) :- !.
two_levels_grouping_fds2d([t(_,_,X7)|X9], X5, X4, X1) :-
    two_levels_grouping_fds2e(X7, X5, X6, X2),
    two_levels_grouping_fds2d(X9, X6, X4, X3),
    append(X2, X3, X1).

two_levels_grouping_fds2e([], X1, X1, []) :- !.
two_levels_grouping_fds2e([X7|X8], X5, X4, X1) :-
    two_levels_grouping_fds2f(X7, X5, X2),
    X6 is X5+1,
    two_levels_grouping_fds2e(X8, X6, X4, X3),
    append(X2, X3, X1).

two_levels_grouping_fds2f([], _, []) :- !.
two_levels_grouping_fds2f([col(_,X2)|X4], X1, [X2-X1|X5]) :-
    two_levels_grouping_fds2f(X4, X1, X5).

gen_keys_for_grouping([], []) :- !.
gen_keys_for_grouping([t(X2,X3,X1)|X6], [key(X4,X5)-t(X2,X3,X1)|X7]) :-
    length(X3,X4),               
    X2 = [X5],                   
    gen_keys_for_grouping(X6, X7).

gen_fds2([], _, _, _, _, _, _, _, _, []) :- !.
gen_fds2([X10-X11|X12], X3, X4, X5, X6, X13, X14, X8, X2, [t(X10,X11,X7)|X15]) :-
    findall(X9, sublist_max_card(X3,X4,X5,X6,X9), X1),
    search_functional_dependencies(X1, X13, X14, X8, X2, X10-X11, X7, _),
    gen_fds2(X12, X3, X4, X5, X6, X13, X14, X8, X2, X15).

select_previous_fd([], []) :- !.
select_previous_fd([X2|X3], [X1|X4]) :-
    select_previous_fd1(X2, X1),
    select_previous_fd(X3, X4).

select_previous_fd1([], []) :- !.
select_previous_fd1([col(_,X1)|X3], [X1|X4]) :-
    select_previous_fd1(X3, X4).

search_functional_dependencies([], _, _, _, _, _, [], _) :- !.
search_functional_dependencies([X14|X16], X5, X17, X11, X1, X8-X9, X6, X10) :-
    (is_not_a_functional_dependency(X14, X5, X17, X1, X8-X9) ->
        X12 = X16,
        X6 = X3
    ;
        findall(X4, (member(X13,X14),functor(X4,col,2),arg(1,X4,X1),arg(2,X4,X13)), X7),
        X6 = [X7|X3],
        (integer(X10) -> X15 = X16                                              ;  
                           length(X7, X2),                             
                           (X11 = 0 ->                                           
                               X10 is X2+3                               
                           ;                                                      
                               X10 is X2+1                               
                           ),
                           remove_list_whose_length_exceeds_limit(X16, X10, X15)), 
        remove_dominated_sets(X15, X14, X12)
    ),
    search_functional_dependencies(X12, X5, X17, X11, X1, X8-X9, X3, X10).

is_not_a_functional_dependency(X7, X4, X8, X2, X5-X6) :- 
    fd_project(X7, X4, X8, X2, X5-X6, X3),
    sort(X3, X1),
    fd_same_key(X1).

fd_project(X10, X7, X11, X2, X8-X9, X3) :-
    length(X10, X12),
    findall(X6-X4,
            (functor(X1, X2, X11),
             functor(X6, t, X12),
             unify_variables(X10, 1, X1, X6),
             call(X1),
             arg(X7,X1,X5),
             ((X8 = [], X9 = [])    -> X4 = X5 ;
              memberchk(X5, X8) -> X4 = 1         ;
              memberchk(X5, X9) -> X4 = 0         ;
                                             false                 )
             ),
            X3).

fd_same_key([X1-_,X1-_|_]) :- !.
fd_same_key([_|X2]) :-
    fd_same_key(X2).

remove_list_whose_length_exceeds_limit([], _, []) :- !.
remove_list_whose_length_exceeds_limit([X2|X4], X1, [X2|X5]) :-
    length(X2, X3),
    X3 =< X1,
    !,
    remove_list_whose_length_exceeds_limit(X4, X1, X5).
remove_list_whose_length_exceeds_limit([_|X3], X1, X4) :-
    remove_list_whose_length_exceeds_limit(X3, X1, X4).

remove_dominated_sets([], _, []) :- !.
remove_dominated_sets([X1|X3], X2, X4) :-
    set_is_include(X2, X1),
    !,
    remove_dominated_sets(X3, X2, X4).
remove_dominated_sets([X1|X3], X2, [X1|X4]) :-
    remove_dominated_sets(X3, X2, X4).

set_is_include([], _) :- !.
set_is_include([X1|X3], X2) :-
    memberchk(X1, X2),
    set_is_include(X3, X2).

gen_nb_fds(X1, X2, _, _, _) :-
    X1 > X2, !.
gen_nb_fds(X7, X8, X1, X4, X2) :-
    X7 =< X8,
    arg(X7, X4, X5),
    length(X5, X3),
    arg(X7, X2, X3),
    X6 is X7+1,
    gen_nb_fds(X6, X8, X1, X4, X2).

gen_cmps(X14, X1, X3, X2, X7) :- 
    functor(X8, X1, X14),
    findall(X8, call(X8), X4),
    findall(t(X12,X11,X13), (X15 in 1..X14, X16 in 1..X14, X15 #< X16,
                           indomain(X15), arg(X15, X2, 0), arg(X15, X3, X5),
                           indomain(X16), arg(X16, X2, 0), arg(X16, X3, X6),
                           ((X5 \= set, X6 \= set) -> X12 = X15, X13 = X16, X9 = init   ;  
                            (X5 \= set, X6  = set) -> X12 = X15, X13 = X16, X9 = within ;  
                            (X5 =  set, X6 \= set) -> X12 = X16, X13 = X15, X9 = within ;  
                                                            false                         ), 
                           extract_comp_ctr(X9, X4, X12, X13, X11)),           X10),
    gen_cmps1(1, X14, X1, X10, X7).

gen_cmps1(X1, X2, _, _, _) :-
    X1 > X2, !.
gen_cmps1(X12, X13, X1, X8, X9) :-
    X12 =< X13,
    findall(X5,
            (member(t(X12,X10,X14), X8),
             functor(X5, X10, 2),
             arg(1, X5, col(X1, X12)),
             arg(2, X5, col(X1, X14))),
            X2),
    findall(X6,
            (member(t(X14,X10,X12), X8),
             invert_cmp(X10, X3),
             functor(X6, X3, 2),
             arg(1, X6, col(X1, X12)),
             arg(2, X6, col(X1, X14))),
            X4),
    append(X2, X4, X7),
    arg(X12, X9, X7),
    X11 is X12+1,
    gen_cmps1(X11, X13, X1, X8, X9).

invert_cmp(geq,    leq).
invert_cmp(gt,     lt).
invert_cmp(leq,    geq).
invert_cmp(lt,     gt).
invert_cmp(eq,     eq).
invert_cmp(neq,    neq).
invert_cmp(within, contain). 

extract_comp_ctr(init,   [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(lt,  X5, X6, X7, X2).
extract_comp_ctr(init,   [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(eq,  X5, X6, X7, X2).
extract_comp_ctr(init,   [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(gt,  X5, X6, X7, X2).
extract_comp_ctr(lt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(lt,  X5, X6, X7, X2).
extract_comp_ctr(lt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(leq, X5, X6, X7, X2).
extract_comp_ctr(lt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(neq, X5, X6, X7, X2).
extract_comp_ctr(eq,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(leq, X5, X6, X7, X2).
extract_comp_ctr(eq,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(eq,  X5, X6, X7, X2).
extract_comp_ctr(eq,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(geq, X5, X6, X7, X2).
extract_comp_ctr(gt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(neq, X5, X6, X7, X2).
extract_comp_ctr(gt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(geq, X5, X6, X7, X2).
extract_comp_ctr(gt,     [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(gt,  X5, X6, X7, X2).
extract_comp_ctr(leq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(leq, X5, X6, X7, X2).
extract_comp_ctr(leq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(leq, X5, X6, X7, X2).
extract_comp_ctr(neq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 < X4, !, extract_comp_ctr(neq, X5, X6, X7, X2).
extract_comp_ctr(neq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(neq, X5, X6, X7, X2).
extract_comp_ctr(geq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !, extract_comp_ctr(geq, X5, X6, X7, X2).
extract_comp_ctr(geq,    [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 > X4, !, extract_comp_ctr(geq, X5, X6, X7, X2).
extract_comp_ctr(within, [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), is_list(X4), !, memberchk(X3,X4),
                                                 extract_comp_ctr(within, X5, X6, X7, X2). 
extract_comp_ctr(within, [X1|X7], X8, X9, X2) :- arg(X8, X1, X4), arg(X9, X1, X5), X5 = X3-X6, !, X3 =< X4, X4 =< X6,
                                                 extract_comp_ctr(within, X7, X8, X9, X2). 
extract_comp_ctr(within, [X1|X5], X6, X7, X2) :- arg(X6, X1, X3), arg(X7, X1, X4), X3 = X4, !,
                                                 extract_comp_ctr(within, X5, X6, X7, X2). 
extract_comp_ctr(X1,    [],       _, _, X1) :- X1 \= init. 

gen_nb_cmps(X1, X2, _, _, _) :-
    X1 > X2, !.
gen_nb_cmps(X7, X8, X1, X4, X2) :-
    X7 =< X8,
    arg(X7, X4, X5),
    length(X5, X3),
    arg(X7, X2, X3),
    X6 is X7+1,
    gen_nb_cmps(X6, X8, X1, X4, X2).

gen_ctrs(X1, X2, _, _, _, _, _, _, _) :-
    X1 > X2, !.
gen_ctrs(X24, X25, X13, X2, X5, X6, X4, X14, X15) :-
    X24 =< X25,
    arg(X24, X6,  X16),
    arg(X24, X4, X7),
    (X16  = set -> arg(X24, X15, []) ; 
     X16  = cst -> arg(X24, X15, []) ;
     X7 > 0   -> arg(X24, X15, []) ;
        findall(X20, (functor(X17,X2,X25), call(X17), arg(X24, X17, X20)), X18),
        length(X18, X26),
        sort(X18, X1),
        length(X1, X19),
        (X26 = X19 ->
            X18 = [X21|_],
            last(X18, X22),
            X8 is X22-X21+1,
            ((X21 = 1, X22 = X19) -> X9 = [permutation]                     ;
             X8 = X26             -> X9 = [alldifferent_consecutive_values] ;
                                      X9 = [alldifferent]                    ;
                                      X9 = []                                ),
            gen_inclusion_except_default_value_ctrs(1, X25, X13, X24, X1, X2, X5, X6, X4, X14, X10)
        ;
            count_zeros(X18, 0, X28),
            X11 is X28+X19-1,        
            ((X28>0, X11 = X26) -> X9 = [alldifferent_except_0] ;
                                 X9 = []                      ),
            X10 = []
        ),
        (increasing_values(X18) ->
            (strictly_increasing_values(X18) -> X12 = [strictly_increasing] ; X12 = [increasing])
        ;
            (decreasing_values(X18) ->
                (strictly_decreasing_values(X18) -> X12 = [strictly_decreasing] ; X12 = [decreasing])
            ;
                X12 = []
            )
        ),
        ((ground(X9), ground(X10), ground(X12)) -> true ; write(gen_ctrs(X9,X10,X12)), nl, halt),
        append([X9,X10,X12], X3),
        arg(X24, X15, X3)
    ),
    X23 is X24+1,
    gen_ctrs(X23, X25, X13, X2, X5, X6, X4, X14, X15).

gen_inclusion_except_default_value_ctrs(X1, X2, _, _, _, _, _, _, _, _, []) :-
    X1 > X2, !.
gen_inclusion_except_default_value_ctrs(X20, X21, X14, X22, X9, X3, X10, X11, X7, X15, X5) :-
    X20 =< X21,
    (X20 = X22 ->
        X5 = X16
    ;
        arg(X20, X11,  X12),
        arg(X20, X7, X8),
        (X12 = cst -> X5 = X16 ;
         X8 > 0  -> X5 = X16 ;
                        findall(X17, (functor(X18,X3,X21), call(X18), arg(X20, X18, X17)), X13),
                        (X12 = set -> flatten(X13, X4) ; X4 = X13),
                        sort(X4, X2),
                        (include_except_default_value(X2, X9, X6) -> 
                            ((X14=0,                                                 
                              integer(X6),                                       
                              check_if_no_cycle(X21, X22, X20, X3, X6)) ->      
                                (check_if_temporal_ctrs(X21, X22, X20, X3, X10, X11, X7, X15, X6,X1) ->
                                    X5 = [include_except_default_value_no_cycle(X22, X20, X6, X1)|X16],
                                    write(include_except_default_value_no_cycle(X22, X20, X6, X1)),nl
                                ;
                                    X5 = [include_except_default_value_no_cycle(X22, X20, X6, [])|X16],
                                    write(include_except_default_value_no_cycle(X22, X20, X6, [])),nl
                                )
                            ;
                                X5 = [include_value(X22, X20)|X16]
                            )
                        ;
                            X5 = X16
                        )
        )
    ),
    X19 is X20+1,
    gen_inclusion_except_default_value_ctrs(X19, X21, X14, X22, X9, X3, X10, X11, X7, X15, X16).

include_except_default_value(X1, X3, X2) :-
    include_except_default_value(X1, X3, X3, X2).

include_except_default_value([], _, _, _) :- !.
include_except_default_value([X2], [], _, X1) :-
    integer(X2),  
    !,
    X2 = X1. 
include_except_default_value([X3|X5], [X4|X6], X2, X1) :-
    integer(X3),  
    X3 < X4,    
    !,
    X3 = X1, 
    include_except_default_value(X5, [X4|X6], X2, X1).
include_except_default_value([X3|X5], [X4|X6], X2, X1) :-
    integer(X3),  
    X3 = X4,    
    !,
    include_except_default_value(X5, X6, X2, X1).
include_except_default_value([X3|X5], [X4|X6], X2, X1) :-
    integer(X3),  
    X3 > X4,    
    !,              
    include_except_default_value([X3|X5], X6, X2, X1).
include_except_default_value([X3-X4|X5], _, X2, X1) :-
    include_except_default_value1([X3-X4|X5], X2, X1).

include_except_default_value1([], _, _) :- !.
include_except_default_value1([X2-X3], [], X1) :- !,
    X2 = X3,
    X2 = X1.
include_except_default_value1([X3-X5|X6], [X4|X7], X1) :-
    X3 < X4,    
    !,
    X3 = X1, 
    (X3 = X5 ->
        include_except_default_value1(X6, [X4|X7], X1)
    ;
        X2 is X3 + 1,
        include_except_default_value1([X2-X5|X6], [X4|X7], X1)
    ).
include_except_default_value1([X3-X5|X6], [X4|X7], X1) :-
    X3 = X4,    
    !,
    (X3 = X5 ->
        include_except_default_value1(X6, X7, X1)
    ;
        X2 is X3 + 1,
        include_except_default_value1([X2-X5|X6], X7, X1)
    ).
include_except_default_value1([X2-X4|X5], [X3|X6], X1) :-
    X2 > X3,    
    !,
    include_except_default_value1([X2-X4|X5], X6, X1).

check_if_no_cycle(X12, X13, X14, X2, X3) :-
    findall(X11, (functor(X5,X2,X12),
                  call(X5),
                  arg(X13, X5, X11)), X6),              
    length(X6, X15),
    length(X7, X15),                                      
    domain(X7, 1, X15),                                   
    keys_and_values(X4, X6, X7),                 
    findall(X8-X1, (functor(X5,X2,X12), 
                               call(X5),                
                               arg(X13, X5, X8),        
                               arg(X14, X5, X9),        
                               clean_succ(X9, X3, X1)), X10),
    check_if_no_cycle(X10, X4).

clean_succ(X3, X2, X1) :-
    (integer(X3) ->
        X3 \= X2,
        X1 = [X3]                 
    ;
     is_list(X3) ->
        delete(X3, X2, X1),  
        X1 \= []
    ;
        X1 = false
    ).

check_if_no_cycle([], _) :- !.
check_if_no_cycle([false|_], _) :- !,                   
    false.                                              
check_if_no_cycle([X4-X2|X5], X1) :-
    memberchk(X4-X3, X1),                     
    check_if_no_cycle(X2, X3, X1),           
    check_if_no_cycle(X5, X1).

check_if_no_cycle([], _, _) :- !.
check_if_no_cycle([X4|X5], X2, X1) :- !,       
    memberchk(X4-X3, X1),                     
    X2 #< X3,                                     
    check_if_no_cycle(X5, X2, X1).

check_if_temporal_ctrs(X37, X38, X39, X14, X27, X28, X23, X31, X19, X32) :-
    collect_temporal_attrs(1, X37, X38, X39, X14, X28, X23, X31, X15),       
    length(X15, X40),
    X40 > 0,
    create_bools(X15, X27, X16,  X4,  X5), 
    create_bools(X15, X27, X12, X3, X5), 
    append([X16, X12], X29),                                              
    gen_sum_term(X4,  var, X2),
    gen_sum_term(X3, var, X1),
    call(X2  #> 0),                                                   
    call(X1 #> 0),                                                   
    common_output_if_single(X4,                                          
                            X3,                                         
                            X2,                                       
                            X1),                                     
                                                                                         

    common_output_if_single(X3,                                         
                            X4,                                          
                            X1,                                      
                            X2),                                      
                                                                                         


    gen_sum_term(X16,  var, X9),
    gen_sum_term(X12, var, X8),
    call(X9  #=< 2),                                                           
    call(X8 #=< 2),                                                           
    findall(X33, (functor(X33,X14,X37), call(X33)), X18),                    
    findall(X33, (functor(X33,X14,X37),                                            
                   call(X33),
                   arg(X39, X33, X34),
                   clean_succ(X34, X19, _)), X24),
    length(X5, X36),                                                      
    length(X10, X36),                                                            
    length(X11, X36),                                                            
    post_temporal_ctrs(X24, X18,
                       X37, X38, X39, X14,                                               
                       X15, X16, X12,                                 
                       X5, X4, X3,      
                       X10, X11,                                       
                       X19, X30, []),
    at_least_one_common_output_ordered(X4,                               
                                       X3,                              
                                       X10,                                     
                                       X11,                                     
                                       X25),                                          
    call((X1 #> 1 #/\ X2 #> 1) #=> X25),       
    X20 in 0..100000,
    X21 in 0..100000,
    X20 #=< X21,
    minimum(X20, X30),                                                             
    maximum(X21, X30),                                                             
    X35 #= X20+X21,                                                             
    X35 #>= 2*X20,
    X22 = 60000,                                                                     
    time_out(label_prec(X35, X29, X30), X22, X26),                           
    (X26 \== time_out ->
        extract_selected_attribute_names(X16,  X15, X14, X17 ),
        extract_selected_attribute_names(X12, X15, X14, X13),
        (X20 = X21 ->                                                            
            X32 = [precedence(X17,X20,=,X13)]                          
        ;
            count_distances(X30, X20, X21, 0, 0, X7, X6),
            (X7 = X6 ->
                X32 = [precedence(X17, X20, =<, X13),                      
                        precedence(X17, X21, >=, X13)]
            ;
            X7 >= X6 ->                                     
                X32 = [precedence(X17, X20, =<, X13)]                  
            ;                                                                            
                X32 = [precedence(X17, X21, >=, X13)]                  
            )
        )
    ).

common_output_if_single([], [], _, _) :- !.
common_output_if_single([X3|X5], [X4|X6], X1, X2) :-
    call((X1 #= 1 #/\ X2 #> 1 #/\ X3 #= 1) #=> X4 #= 1),
    common_output_if_single(X5, X6, X1, X2).

extract_selected_attribute_names([], [], _, []) :- !.
extract_selected_attribute_names([1|X3], [X1|X4], X2, [col(X2,X1)|X5]) :-
    extract_selected_attribute_names(X3, X4, X2, X5).
extract_selected_attribute_names([0|X2], [_|X4], X1, X5) :-
    extract_selected_attribute_names(X2, X4, X1, X5).

count_distances([], _, _, X1, X2, X1, X2) :- !.
count_distances([X9|X12], X7, X8, X3, X4, X5, X6) :-
    X10 is X8 - X9,          
    X11 is X9 - X7,          
    (X10 < X11 -> X1 is X3  , X2 is X4+1 ;
     X10 > X11 -> X1 is X3+1, X2 is X4   ;
                  X1 is X3  , X2 is X4   ),
    count_distances(X12, X7, X8, X1, X2, X5, X6).

post_temporal_ctrs([], _, _, _, _, _, _, _, _, _, _, _, X1, X2, _, X3, X3) :- !,
    force_non_ground_to_1(X1),
    force_non_ground_to_1(X2).
post_temporal_ctrs([X18|X19], X15, X20, X21, X22, X10,
                   X11, X12, X7,
                   X2, X3, X1,
                   X5, X6,
                   X14, X16, X8) :-
    extract_attrs(X11, X18, X13),                                      
    get_jth_terms(X20, X21, X22, X10, X14, X18, X15, X17),               
    post_temporal_ctr(X17, X11, X12, X7,                     
                      X13, X16, X9),
    extract_attrs(X2, X18, X4),
    update_secondary_leq_geq(X17, X2,                            
                             X4, X5, X6),       
    post_temporal_ctrs(X19, X15, X20, X21, X22, X10,
                       X11, X12, X7,
                       X2, X3, X1,
                       X5, X6,
                       X14, X9, X8).

post_temporal_ctr([], _, _, _, _, X1, X1) :- !.
post_temporal_ctr([X11|X13], X5, X6, X1, X7, X10, X2) :-
    extract_attrs(X5, X11, X3),
    gen_linear_sum(X7,  X6,  X9),
    gen_linear_sum(X3, X1, X8),
    X12 in 0..100000,
    call(X9 + X12 #= X8),
    X10 = [X12|X4],
    post_temporal_ctr(X13, X5, X6, X1, X7, X4, X2).

update_secondary_leq_geq([], _, _, _, _) :- !.    
update_secondary_leq_geq([X6|X7], X2, X3, X4, X5) :-
    extract_attrs(X2, X6, X1),
    update_secondary_leq_geq(X3, X1, X4, X5),
    update_secondary_leq_geq(X7, X2, X3, X4, X5).

update_secondary_leq_geq([], [], [], []) :- !.
update_secondary_leq_geq([X2|X5], [X1|X6], [X3|X7], [X4|X8]) :-
    (X2 > X1 -> X3 = 0 ;
     X2 < X1 -> X4 = 0 ;
                                               true    ),
    update_secondary_leq_geq(X5, X6, X7, X8).

at_least_one_common_output_ordered([], [], [], [], 0) :- !.
at_least_one_common_output_ordered([X2|X5],
                                   [X1|X6],
                                   [X3|X7],
                                   [X4|X8],
                                   (X2  #= 1 #/\
                                    X1 #= 1 #/\
                                    (X3 #= 1 #\/ X4 #= 1)) #\/ X9) :-
    at_least_one_common_output_ordered(X5, X6, X7, X8, X9).

force_non_ground_to_1([]) :- !.
force_non_ground_to_1([X1|X2]) :-
    integer(X1),
    !,
    force_non_ground_to_1(X2).
force_non_ground_to_1([1|X1]) :-
    force_non_ground_to_1(X1).

label_prec(X2, X1, X3) :-
    indomain(X2),
    minimize((labeling([],X1),
              once(labeling([], X3))), X2),
    !.

create_bools([], _, [], [], []) :- !.
create_bools([X3|X4], X1, [X5|X6], [X5|X7], [X3|X8]) :-
    arg(X3, X1, X2),
    X2 \== primary,
    !,
    X5 in 0..1,
    create_bools(X4, X1, X6, X7, X8).
create_bools([_|X3], X1, [X4|X5], X6, X7) :-
    X4 in 0..1,
    create_bools(X3, X1, X5, X6, X7).

get_jth_terms(X8, X9, X10, X2, X3, X6, X4, X5) :-
    arg(X10, X6, X7),
    clean_succ(X7, X3, X1),                      
    get_jth_terms(X1, X8, X9, X2, X4, X5).

get_jth_terms([], _, _, _, _, []) :- !.
get_jth_terms([X4|X5], X6, X7, X1, X2, [X3|X8]) :-
    functor(X3, X1, X6), 
    arg(X7, X3, X4),          
    memberchk(X3, X2),     
    get_jth_terms(X5, X6, X7, X1, X2, X8).

extract_attrs([], _, []) :- !.
extract_attrs([X1|X4], X3, [X2|X5]) :-
    arg(X1, X3, X2),
    extract_attrs(X4, X3, X5).

count_zeros([], X1, X1) :- !.
count_zeros([X2|X3], X4, X5) :-
    (X2 = 0 -> X1 is X4+1 ; X1 = X4),
    count_zeros(X3, X1, X5).

increasing_values([_]) :- !.
increasing_values([X1,X2|X3]) :-
    X1 =< X2,
    increasing_values([X2|X3]).

strictly_increasing_values([_]) :- !.
strictly_increasing_values([X1,X2|X3]) :-
    X1 < X2,
    strictly_increasing_values([X2|X3]).

decreasing_values([_]) :- !.
decreasing_values([X1,X2|X3]) :-
    X1 >= X2,
    decreasing_values([X2|X3]).

strictly_decreasing_values([_]) :- !.
strictly_decreasing_values([X1,X2|X3]) :-
    X1 > X2,
    strictly_decreasing_values([X2|X3]).

gen_pks(X4, X10, X5, X12, X14, X15, X13, X11, X8, X18) :- 
    findall(X19,                               
            (X19 in 1..X5, indomain(X19), 
             arg(X19, X12, X16),            
             X16 \= set,                    
             arg(X19, X13, X17), X17 > 1,
             arg(X19, X11, 0)),
            X1),
    X2 is min(3, X5),         
    findall(X6, sublist_max_card(X1,X2,X6), X3),
    check_if_pks(X3, X4, X10, X5, X13, X8, X7),
    gen_cost_pks(X7, X14, X15, X9),
    keysort(X9, X18).

gen_cost_pks([], _, _, []) :- !.
gen_cost_pks([X5|X6], X2, X3, [X4-X5|X7]) :-
    length(X5, X1),
    cost_pks(X5, X1, X2, X3, 1, X4),
    gen_cost_pks(X6, X2, X3, X7).

cost_pks([], X1, _, _, X3, X2) :- !, X2 is X3 + X1.
cost_pks([X7|X11], X1, X3, X4, X8, X5) :-
    arg(X7, X3, X9),
    arg(X7, X4, X10),
    X2 is X10-X9+1,
    X6 is X8*X2,
    cost_pks(X11, X1, X3, X4, X6, X5).

check_if_pks([], _, _, _, _, _, []) :- !.
check_if_pks([X1|X8], X2, X5, X3, X6, X4, [X1|X9]) :-
    checked_that_is_pks(X1, X2, X5, X3, X6, X4), !,
    restrict_pks_candidates(X8, X1, X7),                         
    check_if_pks(X7, X2, X5, X3, X6, X4, X9). 
check_if_pks([_|X7], X1, X4, X2, X5, X3, X8) :-  
    check_if_pks(X7, X1, X4, X2, X5, X3, X8) .

restrict_pks_candidates([], _, []) :- !.
restrict_pks_candidates([X1|X3], X2, X4) :-
    subseq0(X1, X2),
    !,
    restrict_pks_candidates(X3, X2, X4).
restrict_pks_candidates([X1|X3], X2, [X1|X4]) :-
    restrict_pks_candidates(X3, X2, X4).

checked_that_is_pks(X1, X2, X5, X3, X6, X4) :- 
    check_wrt_nvals(X1, 1, X6, X5),                               
    (length(X1, 1) ->                                                    
        true                                                                    
    ;                                                                           
        (check_that_is_pks1(X1, X2, X5, X3, X6, X4) ->
            true
        ;
            false
        )
    ).

check_wrt_nvals([X6|X7], X2, X4, X3) :-
    arg(X6, X4, X5),
    X1 is X2*X5,
    (X1 >= X3 -> true ; check_wrt_nvals(X7, X1, X4, X3)).

check_that_is_pks1(X5, X6, X12, X7, X14, X11) :-
    findall(X13-X17, (nth1(_,X5,X17),arg(X17,X11,X13)), X8),
    keysort(X8, X2),
    reverse(X2, X1),
    keys_and_values(X1, _, X3),
    findall([X18|X15]-X16, partition_list(X3,[X18|X15],X16), X10),
                                                             
                                                             
    check_pairs_condition(X10, X12, X14, X11), 
    pk_project(X5, X7, X6, X9),  
    sort(X9, X4),                        
    same_length(X9, X4).                 

pk_project(X5, X6, X2, X3) :-
    length(X5, X7),
    findall(X4,
            (functor(X1, X2, X6),
             functor(X4, t, X7),
             unify_variables(X5, 1, X1, X4),
             call(X1)),
            X3).

check_pairs_condition([], _, _, _) :- !.
check_pairs_condition([X10-X11|X16], X7, X9, X6) :-
    findall(X8, (nth1(_,X10,X14),arg(X14,X6,X8)), X3),
    sumlist(X3, X4),              
    length(X10, X12),
    X2 is X4 - (X12-1)*X7,
    (X2 =< 0 ->
        true
    ;
        findall(X13, (nth1(_,X11,X14),arg(X14,X9,X13)), X5),
        prodlist(X5, X1),       
        X2 =< X1
    ),
    check_pairs_condition(X16, X7, X9, X6).

partition_list([], [], []) :- !.   
partition_list([X|X2], X3, [X|X4]) :- 
    partition_list(X2, X3, X4).       
partition_list([X|X2], [X|X3], X4) :-
    partition_list(X2, X3, X4).

gen_all_fks([], _, _) :- !.  
gen_all_fks([X2|X10], X3, X7) :- 
    get_table(X3, 0, _, X6, X2), 
    (memberchk(no_fk, X6) ->
        X1 = []
    ;                                             
        gen_fks(X7, X2, X1)
    ),
    tab_get_arity(col(X2,_),   X4),
    tab_get_maxn(col(X2,_),    X9),
    tab_get_nb_rows(col(X2,_), X8),
    functor(X5, ranked_fd, X4),
    gen_ranked_fds(1, X4, X9, X8, X2, X1, X5),
    record_fks_ranked_fds_in_metadata_fact_and_metadata_file(X3, X2, X1, X5), 
    gen_all_fks(X10, X3, X7).         

gen_fks([], _, []) :- !.                       
gen_fks([X1|X3], X1, X2) :-    
    !,
    gen_fks(X3, X1, X2).               
gen_fks([X1|X6], X2, X4) :-   
    gen_fk(X1, X2, X3),
    gen_fks(X6, X2, X5),
    (X3 = [] ->                          
        X4 = X5                              
    ;
        X4 = [X3|X5]
    ).

gen_fk(X4, X5, X2) :-               
   tab_get_pks(col(X4,_), X6),                   
   gen_fk1(X6, X4, X5, X7),        
   findall(X8-X9, (member(X9, X7),                       
                     X9 = ind(X8,_,_)),
           X3),
   keysort(X3, X1),                    
   findall(X9, member(_-X9,X1), X2). 

gen_fk1([], _, _, []) :- !.
gen_fk1([_-X4|X7], X1, X3, X5) :- 
    gen_fk2(X1, X3, X4,                
            X5, X2),                           
    gen_fk1(X7, X1, X3, X2).

gen_fk2(_, _, [], X1, X1) :- !. 
gen_fk2(X5, X7, X9, X110, X6) :-
    
    
    get_fk_column_candidates(X9, X5, X7, X11),
    
    
    findall(X, (list_cartesian_product(X11,X), 
                sort(X,X11),                                 
                same_length(X,X11)                           
               ), X3),
    
    
    
    tab_get_arity(col(X5,_), X4),
    pk_project(X9, X4, X5, X8),
    sort(X8, X2),
    check_all_fk_candidates(X3, X5, X7, X2, X9, X110, X6). 

get_fk_column_candidates([], _, _, []) :- !.
get_fk_column_candidates([X2|X16], X3, X5, [X1|X17]) :-
    tab_get_arity(col(X5,_), X7),
    findall(X19, (X19 in 1..X7, indomain(X19),
                tab_get_type(col(X5,X19), X13),
                X13 \= set,
                tab_get_min(col(X3, X2), X8),
                tab_get_max(col(X3, X2), X9),
                tab_get_nval(col(X3,X2), X6),
                tab_get_min(col(X5,X19), X11), X11 >= X8, (X11 > X8 -> X14 = 1 ; X14 = 0),
                tab_get_max(col(X5,X19), X12), X12 =< X9, (X12 < X9 -> X15 = 1 ; X15 = 0),
                X4 is (X6 - X14 - X15),
                tab_get_nval(col(X5,X19), X10), X10 > 1, X10 =< X4
               ), X1),
    get_fk_column_candidates(X16, X3, X5, X17).

check_all_fk_candidates([], _, _, _, _, X1, X1) :- !.
check_all_fk_candidates([X6|X14], X7, X9, X1, X11, X12, X4) :-
    X12 = [ind(X13, pk(X7,X11), fk(X6))|X8],
    tab_get_arity(col(X9,_), X3),
    pk_project(X6, X3, X9,  X10), 
    sort(X10, X2),                                
    sort_included(X2, X1),
    !,
    length(X2, X16),                                      
    tab_get_nb_rows(col(X7,_), X5),               
    X13 is X5 / X16,                                        
    check_all_fk_candidates(X14, X7, X9, X1, X11, X8, X4).
check_all_fk_candidates([_|X8], X3, X4, X1, X5, X6, X2) :-
                                                                     
    check_all_fk_candidates(X8, X3, X4, X1, X5, X6, X2).

list_cartesian_product([], []).
list_cartesian_product([X1|X3], [X2|X4]) :-
    nth1(_, X1, X2),
    list_cartesian_product(X3, X4).

sort_included([], _) :- !.
sort_included([X|X2], [X|X3]) :- !,
    sort_included(X2, X3).
sort_included([X|X2], [X3|X4]) :-
    X @> X3,                    
    sort_included([X|X2], X4).

read_all_data_and_meta_data_files([], _) :- !.             
read_all_data_and_meta_data_files([X2|X3], X1) :- 
    read_data_and_meta_data_files(X1, X2),       
    read_all_data_and_meta_data_files(X3, X1).       

read_data_and_meta_data_files(X2, X5) :-                                    
    atoms_concat(['data/',X2,'/data'], X4),                               
    gen_table_and_metadata_file_names(X4, 0, X5, X3, X1),    
    consult(X3),    
    consult(X1). 

record_fks_ranked_fds_in_metadata_fact_and_metadata_file(X7, X11, X9, X8) :-
    get_metadata_arity(X12),                                
    get_metadata_attributes(X5),                      
    memberchk(X3-table_name, X5),           
    memberchk(X10-fks,              X5),           
    memberchk(X4-ranked_fds, X5),           
    functor(X2, table_metadata, X12),            
    arg(X3, X2, X11),                  
    call(X2),                                      
    arg(X10, X2, X9),                      
    arg(X4, X2, X8),              
    functor(X1, table_metadata, X12),     
    arg(X3, X1, X11),           
    retractall(X1),                         
    assert(X2),                                    
    atoms_concat(['data/',X7,'/data0/',  
                  X11,                        
                  '_metadata.pl'], X6), 
    write_metadata_file(X6, X12, X2).    

gen_affinities(X1, X2, _, _, _, _, _, _) :-
    X1 > X2, !.
gen_affinities(X15, X16, X5, X7, X8, X6, X3, X2) :-
    X15 =< X16,                                                   
    arg(X15, X7,  X11),
    arg(X15, X8,  X12),
    arg(X15, X6, X9),                                    
    (X12  = set     -> arg(X15, X2, none) ;    
     X11  = primary -> arg(X15, X2, none) ;            
     X12  = cst     -> arg(X15, X2, none) ;            
     X9 > 0       -> arg(X15, X2, none) ;            
        findall(X17, (X17 in 1..X16, indomain(X17),                   
                    arg(X17,X7,primary),
                    arg(X17,X8,X10),
                    X10 \= cst,
                    X10 \= set, 
                    arg(X17,X6,0)), X1),          
        gen_affinity(X1, X15, X16, X5, X3, t(0,0,0,0,0,_), X4),
        (X4 = t(0,0,0,0,0,_) ->                         
            arg(X15, X2, none)                          
        ;                                                     
            check_if_can_complete_affinity_with_a_single_cst(X15, X16, X3, X4),
            X4 = t(_,_,_,_,_,X13),                      
            (var(X13) -> X4 = t(_,_,_,_,_,none) ; true),
            arg(X15, X2, X4)                      
        )
    ),
    X14 is X15+1,                                                
    gen_affinities(X14, X16, X5, X7, X8, X6, X3, X2).

gen_affinity([], _, _, _, _, X1, X1) :- !.
gen_affinity([X12|X13], X14, X15, X11, X5, X1, X2) :-
    X1 = t(X7,_,_,_,_,_),                     
    X6 is X7+1,
    X8 is X11//2,
    X9 is max(X6,X8),                        
    gen_affinity1(X14, X12, X15, X11, X5,                 
                  X9, X3),                      
    X3  = t(X10,_,_,_,_,_),                      
    (integer(X10), X10 > X7 -> X4 = X3 ; X4 = X1),
    gen_affinity(X13, X14, X15, X11, X5, X4, X2).

gen_affinity1(X16, X17, X18, X5, X1, X4, X2) :-
    X2 = t(X10, X6, X7, X8, X17, _),           
    X6 in  1..3,                                             
    X7 in -3..3,
    X8 in -3..3,
    X7 #\= 0,
    X6 #= abs(X7) #/\ abs(X7) #> 1 #=> X8 #\= 0,
    X6 #= abs(X7) #/\ X6 #= abs(X8) #=> X6 #= 1,
    X10 in X4..X5,                                    
    findall(X14-X15, (functor(X12,X1,X18), call(X12),      
                    arg(X16, X12, X14), arg(X17, X12, X15)), X9),
    gen_affinity2(X9, X6, X7, X8, X3),        
    call(X10 #= X3),                                     
    X13 = [X6,X7,X8],                                 
    labeling([maximize(X10),time_out(1000,_)], X13),          
    !.
gen_affinity1(_, _, _, _, _, _, _).                             

gen_affinity2([], _, _, _, 0) :- !.
gen_affinity2([X5-X6|X7], X1, X2, X3, X4+X8) :-
    X4 in 0..1,
    X5*X1 + X6*X2 + X3 #= 0 #<=> X4,                 
    gen_affinity2(X7, X1, X2, X3, X8).

check_if_can_complete_affinity_with_a_single_cst(X12, X13, X1, X2) :-
    X2 = t(_, X4, X5, X6, X14, X9),      
    findall(X10-X11, (functor(X8,X1,X13), call(X8), 
                    arg(X12, X8, X10),                      
                    arg(X14, X8, X11)), X7),             
    check_if_can_complete_affinity_with_a_single_cst1(X7, X4, X5, X6, X9),
    !.                                                     
check_if_can_complete_affinity_with_a_single_cst(_, _, _, t(_, _, _, _, _, none)).

check_if_can_complete_affinity_with_a_single_cst1([], _, _, _, _) :- !.
check_if_can_complete_affinity_with_a_single_cst1([X5-X6|X7], X1, X2, X3, X4) :-
    X8 is X5*X1 + X6*X2 + X3,
    (X8 = 0 -> true ; X5 = X4),
    check_if_can_complete_affinity_with_a_single_cst1(X7, X1, X2, X3, X4).

gen_monotonicities(X1, X2, _, _, _, _, _, _) :-                   
    X1 > X2, !.
gen_monotonicities(X18, X19, X8, X9, X15, X5, X12, X2) :-   
    X18 =< X19,                                                     
    (X15 < X5 ->                                    
        X6 = []                                       
    ;
     X9 = model_seeker ->                                
        X6 = []                                       
    ;                                                           
     arg(X18, X12, primary) ->
        findall(X20, (X20 in 1..X19, indomain(X20), X20 \== X18, arg(X20, X12, primary)),                          X3),
        findall(X20, (X20 in 1..X19, indomain(X20), X20 \== X18, arg(X20, X12, X13), memberchk(X13,[low,up])), [X10]    ),
        findall(X4-t(X1,X11),    
                (functor(X16, X8, X19),                   
                 call(X16),                                    
                 args(X3, X16, X4),
                 arg(X18,               X16, X1),
                 arg(X10,        X16, X11)),
                X14),
    sort(X14, X7),                                   
    check_monotonicity(X7, undetermined, X6) 
    ;                                                           
        X6 = []                                       
    ),
    arg(X18, X2, X6),                       
    X17 is X18+1,                                                  
    gen_monotonicities(X17, X19, X8, X9, X15, X5, X12, X2).

gen_inf_sup(X3, X4, X5-X6) :-
    functor(X3,_,X10), 
    findall(X7, (X11 in 1..X10, indomain(X11), arg(X11, X3, X7)), X1),
    findall(X8, (X11 in 1..X10, indomain(X11), arg(X11, X4, X8)), X2),
    min_member(X5, X1),
    max_member(X6, X2).

gen_ranked_fds(X1, X2, _, _, _, _, _) :-
    X1 > X2, !.
gen_ranked_fds(X29, X30, X16, X14, X9, X22, X10) :-
    X29 =< X30,
    (X16 = 0 ->                                           
        tab_get_fd(col(X9,X29), X26),
        
        
        (X26 = [] ->                                        
            arg(X29, X10, [])                          
        ;
            tab_get_inputs(X9, X15),             
            tab_get_pks(col(X9, _), X23),           
            (X23 = [] ->                                   
                X27 = []                                    
             ;                                             
                X23 = [_-X27|_]                             
            ),
            findall(X17,
                    (member(X18, X15),
                     tab_get_ctr(X18, X19), 
                     member(X24,X19),
                     X24 = include_except_default_value_no_cycle(_, X17, _, _)),
                    X1), 
            
            findall(X17,
                    (member(X18, X15),
                     tab_get_cmp(X18, X20), 
                     member(within(col(_,X17),_),X20)),
                    X4),
            
            get_fk_columns(X22, X11),
            append([X27, X1, X4, X11, [X29]],
                   X6),      
            findall(col(X9,X25), (member(col(X9,X25), X15),
                                         nonmember(X25, X6),
                                         tab_get_type(col(X9,X25), X21),
                                         nonmember(X21, [set,cst])),
                    X2),
            filter_fds(X26, X2, X7),
            X8 = 1,
            add_extra_input_cols_to_fd(X8, X2, X7, X5),
            rank_fds(X9, X30, X14, X29, X5, X13),
            arg(X29, X10, X13)
        )
    ;                                                      
        arg(X29, X10, [])
    ),
    
    
    X28 is X29+1,
    gen_ranked_fds(X28, X30, X16, X14, X9, X22, X10).

add_extra_input_cols_to_fd(X6, X3, X7, X5) :-
    findall(X11, (member(X12, X7),
                    findall(X9, (member(X9, X3), nonmember(X9, X12)), X1),
                    sublist_max_card(X1, X6, X8),
                    append(X12, X8, X4),
                    sort(X4, X11)),       X10),
    append(X7, X10, X2),
    sort(X2, X5).

filter_fds(X5, X2, X4) :-
    (X5 = [] ->
        X4 = []
    ;
        findall(X1, (member(X3,X5),
                                    sort(X3, X1),                   
                                    subseq0(X2,X1)), X4)
    ).
