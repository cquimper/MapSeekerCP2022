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
% Purpose: GENERATE A PARAMETERISED CANDIDATE POLYNOMIAL FORMULA WRT SOME GIVEN OPTIONS,
%          AND ON BACTRACKING PRODUCE THE NEXT CANDIDATE FORMULA
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_poly_formula,[gen_possible_combinations_of_attr/3,
                            extend_functor_unary/7,
                            extend_functor_binaryt/3,
                            get_break_sym_in_unaryt_binaryt/7,
                            get_break_sym_in_unaryf/3,
                            get_break_sym_in_binaryf/3,
                            formula_gen_attr_ctrs/10,
                            formula_gen_polynoms/10,
                            restrict_attr_wrt_binary_functions/4,
                            gen_source_target_templates/4,
                            formula_pattern_gen_additional_ctr/2]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(gen_cond_formula).
:- use_module(utility).
:- use_module(table_access).
:- use_module(instrument_code).

gen_possible_combinations_of_attr([], _, []) :- !.
gen_possible_combinations_of_attr([X2|X4], X1, [X3|X5]) :-
    gen_possible_combination_of_attr(X1, X2, X3),
    gen_possible_combinations_of_attr(X4, X1, X5).

gen_possible_combination_of_attr([], _, []) :- !.
gen_possible_combination_of_attr([X2|X3], X1, [X4|X5]) :-
    (memberchk(X2, X1) -> X4 = 1 ; X4 = 0),
    gen_possible_combination_of_attr(X3, X1, X5).

extend_functor_unary([], [], _, _, _, [], []) :- !.
extend_functor_unary([X11|X12], [X13|X14], X3, X1, X2, X7, X4) :-
    functor(X11, X15, X16),
    ((memberchk(X15, X1), X16 = 2) ->
        arg(1, X11, X5),                                  
        arg(2, X11, X6),                                  
        X5 =< X6,                                   
        functor(X13, X15, 1),                                   
        arg(1, X13, X8),                                     
        (X3 = 1 -> X8 in X5..X6 ;             
         X15 = floor   -> X8 in 2..X6      ;             
                        X8 in X5..X6 ),
        X7 = [X8|X17],                                     
        X4 = X18
    ;                                                       
                                                            
     X11 = in                           -> functor(X13, in, 2), arg(1, X13, X9), arg(2, X13, X10),
                                         X9 in 0..5, X10 in 0..9, X9 #=< X10, X10 #=< X9 + 5, X7 = X17, X4 = [X9,X10|X18] ;
    (X11 = power(X19), integer(X19), X19 > 1) -> X13 = X11, X7 = X17, X4 = X18                                                        ;
    memberchk(X11, X2)       -> X13 = X11, X7 = X17, X4 = X18                                                        ;
                                         write(extend_functor_unary), nl, halt                                              ),
    extend_functor_unary(X12, X14, X3, X1, X2, X17, X18).

extend_functor_binaryt([], [], []) :- !.
extend_functor_binaryt([X3|X4], [X5|X6], X1) :-
    (memberchk(X3, [min,max,prod]) ->
        functor(X5, X3, 1),                                   
        arg(1, X5, 0),                                       
        X1 = X7                                          
    ;
    memberchk(X3, [floor,mfloor,ceil,mod,cmod,dmod,fmod]) ->
        functor(X5, X3, 1),                                   
        arg(1, X5, X2),                                   
        X2 in 0..1,
        X1 = [X2|X7]
    ;
        write(extend_functor_binaryt), nl, halt
    ),
    extend_functor_binaryt(X4, X6, X7).

get_break_sym_in_unaryt_binaryt(1, X1, [power(_)], _, _, _, power_prod(X1)) :- !.
get_break_sym_in_unaryt_binaryt(_, _, _, 1, X1, [prod], power_prod(X1)) :- !.
get_break_sym_in_unaryt_binaryt(_, _, _, _, _, _, none).

get_break_sym_in_unaryf(2, [X2], X1) :-    
    !,                                                              
    (functor(X2, in, 2) ->                               
        arg(1, X2, X3),                                 
        arg(2, X2, X5),                                  
                                                                    
        X1 = in(X3, 0, 5, X5, 0, 9)                  
                                                                    
    ;
     functor(X2, mod, 1) ->                              
        arg(1, X2, X4),                                 
        X1 = mod(X4)                                 
   ;
     functor(X2, power, 1) ->                            
        X1 = power                                    
    ;                                                               
        X1 = none                                     
    ).
get_break_sym_in_unaryf(_, _, none).                                

get_break_sym_in_binaryf(3, [prod], prod) :- !. 
get_break_sym_in_binaryf(_, _, none).           

formula_gen_attr_ctrs(X2, X18, X19, X20, X7, X1, X12, X16, X4, X5) :-
    formula_pattern(np(X23),         X2),      
    formula_pattern(nu(X24),         X2),      
    formula_pattern(nb(X25),         X2),      
    formula_pattern(unary(X17),   X2),      
    formula_pattern(binary(X13), X2),      
    X21 is X24+X25,                                         
    X22 is X20+X21,                                      
    gen_lists_dvars(X24, X20, 0, 1, X14),              
    gen_lists_dvars(X25, X20, 0, 1, X15),              
    gen_lists_dvars(X23, X22,  0, 1, X12),              
                                                          
                                                          
    gen_lists_dvars(1,  X20, 0, 1, [X16]),             
    remove_equal_col_attributes(X7, X16),        
    (X5 = [_|_] ->                                
        call(table([X16], X5))    
    ;
        true
    ),
    length(X3, X1),               
    domain(X3, 1, 1),                           
    prefix_length(X16, X3, X1), 
    gen_count_ctrs(X14, 1, eq(1)),                     
    gen_count_ctrs(X15, 1, eq(2)),                     
    gen_count_ctrs(X12, 1, geq(1)),                    
    append([X12,X14,X15], X9),             
    prefixes_length(X9, X8, X20),           
    transpose(X8, X6),                     
    gen_or_ctrs(X6, var, X16),                  
    gen_count_ctrs([X16], 1, in(X18,X19)),            
    (X21 > 0 ->                                           
        suffixes_length(X12, X11, X21),            
        transpose(X11, X10),                     
        gen_count_ctrs(X10, 1, geq(1))               
    ;
        true
    ),
    flatten(X9, X4),                       
    formula_pattern(attributes_use([p(X12),u(X14),  
                                    b(X15),a(X16)]),
                                    X2),
    restrict_attr_wrt_unary_terms(X14, X17,          
                                  X7),
    restrict_attr_wrt_binary_terms(X15, X13, X20,  
                                   X7).

remove_equal_col_attributes([], []) :- !.                 
remove_equal_col_attributes([X1|X3], [X4|X5]) :-       
    tab_get_equal(X1, X2),                          
    (X2 > 0 -> X4 = 0 ; true),
    remove_equal_col_attributes(X3, X5).

formula_gen_polynoms(X2, X1, _, _, _, _, _, [], [], []) :- X2 > X1, !.
formula_gen_polynoms(X18, X16, X4, X9, X1, X3, X2, [X12|X19], [X6|X20], [X13|X21]) :-
    X18 =< X16,
    arg(X18, X4, X5),                                                                       
    (memberchk(degree(X14,X15),     X5) -> true ; write(formula_gen_polynoms1), nl, halt),    
    (memberchk(coef(X7,X8), X5) -> true ; write(formula_gen_polynoms2), nl, halt),    
    (memberchk(cst(X10,X11),    X5) -> true ; write(formula_gen_polynoms3), nl, halt),    
    (X14 >  0                                  -> true ; write(formula_gen_polynoms4), nl, halt),    
    (X14 =< X15                               -> true ; write(formula_gen_polynoms5), nl, halt),    
    gen_polynom(X9, X1, X3, X2,                  
                t(X14,X15,X7,X8,X10,X11), X5, X12, X6, X13),
    X17 is X18+1,
    formula_gen_polynoms(X17, X16, X4, X9, X1, X3, X2, X19, X20, X21).

gen_polynom(X18, X1, X5, X3, X19, X11, X20, X14, X21) :-
    X19 = t(X22,X23,_,_,_,_),
    length(X18, X17),                                                
    all_options(unary_boolean, X2),                      
    get_max_degree_params(X18, X2, X23, X9), 
    length(X7, X17),                                         
    gen_list_dvars_min_maxs(X7, 0, X9),                  
    gen_sum_term(X7, var, X10),                           
    X8 in 0..X23,                                                
    call(X10 #= X8),                         
    findall(t(X8,X7,_),                                
            (labeling([down],[X8]),                               
             labeling([],X7)), X14),
    gen_polynom_set_domain_coefs(X14, X5, X19, X21), 
    gen_polynom_min_max_degree_ctr(X14, X22, X23),                    
    gen_polynom_non_zeros_ctr(X14, X11),                           
    gen_polynom_param_use_ctr(X14, X11, X17, X20),
    (X1 = power_prod(X4) ->              
        enforce_single_monome_coefs_to_be_null(X14, X4)  
    ;
        true
    ),
    (X5 = power ->                                            
        enforce_first_non_zero_monome_coef_to_be_positive(X21)            
    ;
        true
    ),
    (X3 = prod ->                                            
        gen_polynom_count_non_zero_monomes(X14, X6),        
        X6 #> 1
    ;
        true
    ).

enforce_single_monome_coefs_to_be_null([], _) :- !.
enforce_single_monome_coefs_to_be_null([t(_,X2,X3)|X5], X1) :-
    (all_zero_except_ith_position(X2, X1) -> X3 = 0 ; true),
    enforce_single_monome_coefs_to_be_null(X5, X1).

all_zero_except_ith_position([], _) :- !.
all_zero_except_ith_position([X2|X3], X4) :-
    (X4 = 1 -> true ; X2 = 0),
    X1 is X4-1,
    all_zero_except_ith_position(X3, X1).

enforce_first_non_zero_monome_coef_to_be_positive(X2) :-                 
    gen_signature(X2, X1),                                        
    automaton(X1, _, X1,                                      
              [source(s),sink(r)],                                          
              [arc(s, 1, s),  
               arc(s, 2, r),  
               arc(r, 0, r),  
               arc(r, 1, r),  
               arc(r, 2, r)], 
               [], [], []).

gen_polynom_set_domain_coefs([], _, _, []) :- !.
gen_polynom_set_domain_coefs([t(X2,_,X12)|X17], X1, X5, [X12|X18]) :-
    X5 = t(_,_,X3,X4,                      
                    X6,X7),                      
    (X2 = 0 ->                                 
        X12 in X6..X7,                          
        (X1 = in(X13,X8,X9,        
                               X15,X10,X11   ) ->     
            X12 #> 0 #=> X13 #= X8 #\/ X15 #= X10, 
                                                         
            X12 #< 0 #=> X13 #= X9 #\/ X15 #= X11  
        ;                                                
            true
        )
    ;
        X12 in X3..X4
    ),
    (X1 = mod(X14) ->                      
        X12 #>= 0,                                      
        X12 #< X14                                      
    ;
        true
    ),
    gen_polynom_set_domain_coefs(X17, X1, X5, X18).

gen_polynom_count_non_zero_monomes(X3, X1) :- 
    get_monomes_coefs(X3, X4),
    gen_sum_term(X4, var_neq(0), X2),
    call(X1 #= X2).

get_monomes_coefs([], []) :- !.
get_monomes_coefs([t(_,_,X1)|X3], [X1|X4]) :-
    get_monomes_coefs(X3, X4).

gen_polynom_min_max_degree_ctr(X1, X3, X4) :-
    gen_polynom_min_max_degree_ctr1(X1, X3, X4, X2), 
    (X2 = [] ->                                               
        false                                                    
    ;                                                            
        gen_or_term(X2, var_neq(0), X5),                    
        call(X5)
    ).

gen_polynom_min_max_degree_ctr1([], _, _, []) :- !.
gen_polynom_min_max_degree_ctr1([t(X1,_,X2)|X6], X3, X4, [X2|X7]) :-
    X3 =< X1,
    X4 >= X1,
    !,
    gen_polynom_min_max_degree_ctr1(X6, X3, X4, X7).
gen_polynom_min_max_degree_ctr1([_|X4], X1, X2, X5) :-
    gen_polynom_min_max_degree_ctr1(X4, X1, X2, X5).

gen_polynom_non_zeros_ctr(X3, X2) :-
    findall(non_zero(X6,X7,X4,X5),                   
            member(non_zero(X6,X7,X4,X5), X2),
            X1),
    gen_polynom_non_zeros_ctr1(X1, X3).    

gen_polynom_non_zeros_ctr1([], _) :- !.
gen_polynom_non_zeros_ctr1([non_zero(X5,X6,X2,X3)|X8], X1) :- 
    gen_polynom_non_zeros_ctr2(X1, X5, X6, X4),           
    gen_sum_term(X4, var_neq(0), X7),                            
    call(X7 #>= X2),                               
    call(X7 #=< X3),                               
    gen_polynom_non_zeros_ctr1(X8, X1).

gen_polynom_non_zeros_ctr2([], _, _, []) :- !.
gen_polynom_non_zeros_ctr2([t(X1,_,X2)|X6], X3, X4, [X2|X7]) :-
    X1 >= X3, X1 =< X4, !,
    gen_polynom_non_zeros_ctr2(X6, X3, X4, X7).
gen_polynom_non_zeros_ctr2([_|X4], X1, X2, X5) :-
    gen_polynom_non_zeros_ctr2(X4, X1, X2, X5).

gen_polynom_param_use_ctr(X3, X2, X4, X5) :-
    gen_polynom_param_use_ctr1(1, X4, X3, X5, X1), 
    (memberchk(param(X6), X2) ->                               
        call(X1 #=< X6)                         
    ;
        true
    ).

gen_polynom_param_use_ctr1(X1, X2, _, [], 0) :-
    X1 > X2, !.                                                               
gen_polynom_param_use_ctr1(X6, X7, X1, [X4|X8], X4+X9) :-    
    X6 =< X7,                                                     
    gen_polynom_param_use_ctr2(X1, X6, X2),              
    gen_or_term(X2, var_neq(0), X3),                       
    call(X3 #= X4),                            
    X5 is X6+1,                                                  
    gen_polynom_param_use_ctr1(X5, X7, X1, X8, X9).

gen_polynom_param_use_ctr2([], _, []) :- !.
gen_polynom_param_use_ctr2([t(_,X1,X3)|X5], X6, [X3|X7]) :-
    nth1(X6,X1,X2),
    X2 > 0,
    !,
    gen_polynom_param_use_ctr2(X5, X6, X7).
gen_polynom_param_use_ctr2([_|X2], X3, X4) :-
    gen_polynom_param_use_ctr2(X2, X3, X4).

get_max_degree_params([], _, _, []) :- !.
get_max_degree_params([X3|X8], X1, X5, [X4|X9]) :-
    functor(X3, X2, _),
    (X3 = col(_,_)                          -> tab_get_min_max(X3, X6, X7) ;
     memberchk(X2, X1) -> X6 = 0, X7 = 1                 ;
                                                  X6 = 2                          ),
    ((X6 =  0, X7 = 1) -> X4 = 1   ;
     (X6 = -1, X7 = 1) -> X4 = 2   ;
                            X4 = X5),
    get_max_degree_params(X8, X1, X5, X9).

restrict_attr_wrt_unary_terms([], _, _) :- !.               
restrict_attr_wrt_unary_terms(X13, X14, X6) :-
    tab_get_mins_attr_names(X6, X9),
    tab_get_maxs_attr_names(X6, X10),
    tab_get_indices_in_range_attr_names(X6,  0,       1, 1, X11),
    tab_get_indices_in_range_attr_names(X6, -1,       1, 1, X12),
    tab_get_indices_neg_min_attr_names(X6,               1, X5),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 0, [min,max],    X3),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 0, [floor,ceil], X1),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 0, [mod],        X7),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 0, [geq],        X8),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 0, [power],      X4),
    select_unary_or_binary_terms_wrt_function_list(X14, X13, 1, [sum_consec], X2),
    restrict_min_max_wrt_unary_term(X3, X9, X10),
    restrict_floor_ceil_wrt_unary_term(X1, X9, X10),
    restrict_mod_wrt_unary_term(X7, X10),
    restrict_geq_wrt_unary_term(X8, X9, X10),
    restrict_power_wrt_unary_term(X4, X11, X12),
    restrict_sum_consec_wrt_unary_term(X2, X5).

restrict_min_max_wrt_unary_term([], _, _) :- !.
restrict_min_max_wrt_unary_term([[X4|X3]|X7], X1, X2) :-
    get_value_selected_attribute(X3, X1, X5),
    get_value_selected_attribute(X3, X2, X6),
    X4 #> X5,
    X4 #< X6,
    restrict_min_max_wrt_unary_term(X7, X1, X2).

restrict_floor_ceil_wrt_unary_term([], _, _) :- !.
restrict_floor_ceil_wrt_unary_term(X1, X3, X4) :-
    compute_max_abs(X3, X4, X2),
    restrict_floor_ceil_wrt_unary_term(X1, X2).

restrict_floor_ceil_wrt_unary_term([], _) :- !.
restrict_floor_ceil_wrt_unary_term([[X4|X3]|X5], X1) :-
    get_value_selected_attribute(X3, X1, X2),
    abs(X4) #=< X2,
    X4 #\= 0,
    restrict_floor_ceil_wrt_unary_term(X5, X1).

restrict_mod_wrt_unary_term([], _) :- !.
restrict_mod_wrt_unary_term([[X3|X2]|X5], X1) :-
    get_value_selected_attribute(X2, X1, X4),
    X3 #> 1,
    X3 #=< X4,
    restrict_mod_wrt_unary_term(X5, X1).

restrict_geq_wrt_unary_term([], _, _) :- !.
restrict_geq_wrt_unary_term([[X4|X3]|X7], X1, X2) :-
    get_value_selected_attribute(X3, X1, X5),
    get_value_selected_attribute(X3, X2, X6),
    X4 #>= X5,                                            
    X4 #=< X6,                                            
    restrict_geq_wrt_unary_term(X7, X1, X2).

restrict_power_wrt_unary_term([], _, _) :- !.
restrict_power_wrt_unary_term([[X3|X4]|X5],
                              X1,                  
                              X2) :-               
    nths1(X1, X4, 0),                           
    (X3 > 2 -> nths1(X2, X4, 0) ; true),    
    restrict_power_wrt_unary_term(X5, X1, X2).

restrict_sum_consec_wrt_unary_term([], _) :- !.
restrict_sum_consec_wrt_unary_term([X2|X3], X1) :-
    nths1(X1, X2, 0),
    restrict_sum_consec_wrt_unary_term(X3, X1).

get_value_selected_attribute(X3, X2, X1) :-
    automaton(X2, X4, X3, 
              [source(s),sink(r)],
              [arc(s, 0, s       ),
               arc(s, 1, r, [X4]),
               arc(r, 0, r       )],
               [_], [1000000], [X1]).


restrict_attr_wrt_binary_terms([], _, _, _) :- !.                                       
restrict_attr_wrt_binary_terms(X9, X10, X11, X7) :-
    select_unary_or_binary_terms_wrt_function_list(X10, X9, 1, [min,max],         X4),
    select_unary_or_binary_terms_wrt_function_list(X10, X9, 0, [floor,ceil],      X3), 
    select_unary_or_binary_terms_wrt_function_list(X10, X9, 0, [cmod],            X5),
    select_unary_or_binary_terms_wrt_function_list(X10, X9, 0, [mod,dmod,fmod],   X2),
    append(X3, X2, X1),
    ((X4 = [], X1 = [], X5 = []) -> true ;
        build_table_attr_wrt_cmp(X11, X7, geq_gt, X6),                  
        (X6 = [_|_] ->                                                          
            restrict_attr_wrt_binary_term(X4,               X6, X11, 0), 
            restrict_attr_wrt_binary_term(X1, X6, X11, 1), 
            restrict_attr_wrt_binary_term(X5,                 X6, X11, 2)  
        ;
            true
        )
    ),
    ((X2 = [], X5 = []) -> true ;                                                           
        build_table_attr_wrt_cmp(X11, X7, gt0, X8),                                                  
        ((X8 = [_|_], X2 = [_|_]) -> restrict_attr_wrt_table(X2, 1, X8) ; true),
        ((X8 = [_|_], X5        = [_|_]) -> restrict_attr_wrt_table(X5,    0, X8) ; true)
    ).

select_unary_or_binary_terms_wrt_function_list([], [], _, _, []) :- !.
select_unary_or_binary_terms_wrt_function_list([X6|X7], [X4|X8], X2, X1, X3) :-
    functor(X6, X5, _),
    (memberchk(X5, X1) ->
        (X2 = 1 -> X3 = [X4|X10] ; arg(1, X6, X11), X3 = [[X11|X4]|X10])
    ;
        X3 = X10
    ),
    select_unary_or_binary_terms_wrt_function_list(X7, X8, X2, X1, X10).

build_table_attr_wrt_cmp(X10, X5, X12, X9) :-
    (X12 = geq_gt ->                                                                            
        findall([X13,X14],                                                                          
                (X13 in 1..X10,
                 indomain(X13),                                                                   
                 nth1(X13, X5, X6),                                                 
                 tab_get_cmp(X6, X8),                                              
                 findall(X3, member(geq(X6,X3), X8), X1), 
                 findall(X4, member(gt(X6, X4), X8), X2), 
                 lists_member([X1,X2], X7),                            
                 nth1(X14, X5, X7)),                                                
                X9)
    ;
     X12 = gt0 ->                                                                               
        findall([X13],                                                                            
                (X13 in 1..X10,
                indomain(X13),                                                                    
                nth1(X13, X5, X6),                                                  
                tab_get_min(X6, X11),                                                   
                X11 > 0),                                                                      
               X9)
    ;
        write(build_table_attr_wrt_cmp), nl, halt
    ).

restrict_attr_wrt_binary_term([], _, _, _) :- !.
restrict_attr_wrt_binary_term(X2, X1, X4, X5) :-
    build_geq_gt_table_wrt_lena(X1, X5, X4, X3), 
    (X2 = [X6] ->
        call(#\table([X6], X3))
    ;
        write(build_geq_gt_table_wrt_lena), halt
    ).

build_geq_gt_table_wrt_lena([], _, _, []) :- !.
build_geq_gt_table_wrt_lena([[X5,X6]|X7], X1, X4, [X2|X8]) :-
    length(X3, X4),
    build_geq_gt_table_wrt_lena1(X3, 1, X5, X6), 
    ( X1 = 0         -> X2 = X3                          ; 
                                                                               
     (X1 = 1, X5 < X6) -> X2 = [1|X3]                      ; 
     (X1 = 1, X5 > X6) -> X2 = [0|X3]                      ; 
                                                                               
     (X1 = 2, X5 < X6) -> X2 = [0|X3]                      ; 
     (X1 = 2, X5 > X6) -> X2 = [1|X3]                      ; 
                                 write(build_geq_gt_table_wrt_lena), nl, halt),
    build_geq_gt_table_wrt_lena(X7, X1, X4, X8).

build_geq_gt_table_wrt_lena1([], _, _, _) :- !.
build_geq_gt_table_wrt_lena1([X3|X4], X2, X5, X6) :-
    (X2 = X5 -> X3 = 1 ; X2 = X6 -> X3 = 1 ; X3 = 0),
    X1 is X2+1,
    build_geq_gt_table_wrt_lena1(X4, X1, X5, X6).

restrict_attr_wrt_table([], _, _) :- !.
restrict_attr_wrt_table([[X3|X4]|X6], X2, X5) :-
    get_attribute_index_binary_term(X3, X4, X2, X1),
    call(table([[X1]], X5)),
    restrict_attr_wrt_table(X6, X2, X5).

get_attribute_index_binary_term(X5, X6, X2, X1) :-
    gen_signature_attribute_index_binary_term(X6, X5, X2, 1, X3, X4),
    automaton(X3, X7, X4, 
              [source(s),sink(f)],
              [arc(s,0,s    ), arc(s,1,s    ), arc(s,2,r    ), arc(s,3,r,[X7]),
               arc(r,0,r    ), arc(r,1,r    ), arc(r,2,f,[X7]), arc(r,3,f    ),
               arc(f,0,f    ), arc(f,1,f    )],
               [_], [1], [X1]).

gen_signature_attribute_index_binary_term([], _, _, _, [], []) :- !.
gen_signature_attribute_index_binary_term([X4|X6], X2, X1, X7, [X7|X8], [X3|X9]) :-
    X4 #= 0 #/\ X2 #= 0 #<=> X3 #= 0,
    X4 #= 0 #/\ X2 #= 1 #<=> X3 #= 1,
    (X1 = 1 ->
        X4 #= 1 #/\ X2 #= 0 #<=> X3 #= 2,
        X4 #= 1 #/\ X2 #= 1 #<=> X3 #= 3
    ;
        X4 #= 1 #/\ X2 #= 1 #<=> X3 #= 2,
        X4 #= 1 #/\ X2 #= 0 #<=> X3 #= 3
    ),
    X5 is X7+1,
    gen_signature_attribute_index_binary_term(X6, X2, X1, X5, X8, X9).

restrict_attr_wrt_binary_functions(3, X1, X10, X11) :- !,
    X1 = [X2],                                 
    (memberchk(X2, [min,max]) ->                               
        X10 = [X5,X6],                                           
        length(X5, X13),                                              
        length(X6, X14),
        (X13 = X14 ->                                                    
            X7 = [op(#<)],                                             
            lex_chain(X10, X7)
        ;
            true
        )
    ;
     memberchk(X2,[ceil,floor]) -> 
        append(X10, X3),                                          
        get_max_abs_dvars(X3, X8),
        X9 = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97],
        findall(X12, (member(X12, X9), X12 =< X8), X4),
        gcd_eq_one_ctr(X4, X3)                                 
                                                                           
                                                                           
                                                                           
    ;
        true
    ),
    count(1, X11, #>, 1).                                                
restrict_attr_wrt_binary_functions(_, _, _, _).

gen_source_target_templates(formula, X2, X7, X8) :-                
    length(X3, X8),                                                        
    formula_pattern(tattributes(X3), X2),                        
    gen_unary_templates(X2, X8, X3, X6),              
    gen_binary_templates(X2, X7, X8, X3, X5), 
    append([X3, X6, X5], X1),       
    gen_polynom_templates(X2, X1, X4),     
    gen_unaryf_template(X2, X4),                                 
    gen_binaryf_template(X2, X4).                                

gen_unary_templates(X1, X9, X3, X5) :-
    formula_pattern(attributes_use(X4), X1),                     
    formula_pattern(unary(X6), X1),                                 
    formula_pattern(mandatory_optional_attributes_names(X7), X1),    
    memberchk(u(X8), X4),                                                
    gen_unary_templates1(X6, X8, X7, X9, X3,            
                         X2, X5),
    formula_pattern(tunary(X2), X1).                            

gen_unary_templates1([], [], _, _, _, [], []) :- !.
gen_unary_templates1([X3|X8], [X6|X9], X4, X7, X1, [X2|X10], [X5|X11]) :-
    gen_unary_template(X3, X6, X4, X7, X1, X2, X5),
    gen_unary_templates1(X8, X9, X4, X7, X1, X10, X11).

gen_unary_template(X6, X16, X7, X20, X1, X2, X11) :-
    X2 = t(X3,                                    
                      X4,                                    
                      X5),                                   
    length(X8, X20),                                          
    gen_linear_sum(X1, X8, X12),                 
    functor(X6, X24, _),                                        
    (memberchk(X24, [min,max,floor,ceil,mod]) ->                       
                                                                     
                                                                     
        append([[X11], X1, X8, [X13]], X3),
        arg(1, X6, X21),                                      
        append(X16, [X21], X5),                            
        functor(X4, #=, 2),                                  
        arg(1, X4, X11),
        arg(2, X4, X17),
        (memberchk(X24, [floor,ceil]) ->                               
            functor(X17, div, 2),                                  
            (X24 = floor ->                                            
                arg(1, X17, X12),
                arg(2, X17, X13)
            ;
                arg(1, X17, (X12+X13-1)),                    
                arg(2, X17, X13)
            )
        ;
            functor(X17, X24, 2),
            arg(1, X17, X12),
            arg(2, X17, X13)
        )                                                          ;
     X24 = geq ->                                                      
        element(X26, X16, 1),                                        
        tab_get_mins_attr_names(X7, X9),                
        tab_get_maxs_attr_names(X7, X10),                
        element(X26, X9, X14),                                
        element(X26, X10, X18),                                 
        arg(1, X6, X21),                                      
        X21 #> X14,                                               
        X21 #< X18,                                                
                                                                     
                                                                     
                                                                     
                                                                     
        append([[X11], X1, X8, [X13]], X3),
        append(X16, [X21], X5),                            
        functor(X4, #<=>, 2),                                
        arg(1, X4, X11),
        arg(2, X4, X17),
        functor(X17, #>=, 2),
        arg(1, X17, X12),
        arg(2, X17, X13)                                      ;
     X24 = in ->                                                       
        element(X26, X16, 1),                                        
        tab_get_mins_attr_names(X7, X9),                
        tab_get_maxs_attr_names(X7, X10),                
        element(X26, X9, X14),                                
        element(X26, X10, X18),                                 
        X22 #>= X14,                                              
        X23  #=< X18,                                               
        X22 #> X14 #\/ X23 #< X18,                               
        append([[X11], X1, X8, [X15,X19]],  
               X3),                                          
        arg(1, X6, X22),                                      
        arg(2, X6, X23),                                       
        append(X16, [X22,X23], X5),                         
        functor(X4, #<=>, 2),                                
        arg(1, X4, X11),                                  
        arg(2, X4, (X15#=<X12 #/\ X12#=<X19))   ;
     X24 = power ->
        append([[X11], X1, X8], X3),     
        X5 = X16,                                          
        arg(1, X6, X27),                                        
        functor(X4, #=, 2),                                  
        arg(1, X4, X11),
        arg(2, X4, X17),
        gen_power_template(X27, X12, X17)                       ; 
     X24 = sum_consec ->
        append([[X11], X1, X8], X3),     
        X5 = X16,                                          
        functor(X4, #=, 2),                                  
        arg(1, X4, X11),
        arg(2, X4, X17),
        X17 = ((X12 * (X12 + 1)) div 2)                    ; 
        write(gen_unary_template), nl, halt
    ).

gen_binary_templates(X2, X7, X9, X3, X5) :-
    formula_pattern(attributes_use(X4), X2), 
    formula_pattern(binary(X6), X2),           
    memberchk(b(X8), X4),                            
    gen_binary_templates1(X6, X8, X7, X9, X3, 
                          X1, X5),
    formula_pattern(tbinary(X1), X2).      

gen_binary_templates1([], [], _, _, _, [], []) :- !.
gen_binary_templates1([X3|X8], [X6|X9], X4, X7, X2, [X1|X10], [X5|X11]) :-
    gen_binary_template(X3, X6, X4, X7, X2, X1, X5),
    gen_binary_templates1(X8, X9, X4, X7, X2, X10, X11).

gen_binary_template(X5, X20, X9, X24, X2, X1, X19) :-
    arg(1, X5, X21),                                               
    gen_integer_list_from_low_to_up(1, X24, X10),
    automaton(X10, X30, X20,                                          
              [source(s),sink(f)],                                           
              [arc(s,0,s), arc(s,1,r, [X30,X31]),                              
               arc(r,0,r), arc(r,1,f, [X32,X30]),
               arc(f,0,f)],
               [X32,X31], [0,0], [X25,X26]),
    X25 #< X26,                                                            
    X1 = t(X6,                                           
                       X7,                                           
                       X8),                                          
                                                                             
    functor(X5, X34, 1),                                               
    X27 = element(X17, X2, X11),                        
    X28 = element(X18, X2, X12),                        
    (X34 = mfloor ->                                                           
        tab_get_mins_attr_names(X9, X13),
        element(X25, X13, X14),
        element(X26, X13, X15),
        X21 #= 0 #=> X15 #> 0,                                        
        X21 #= 1 #=> X14 #> 0                                         
    ;
        true
    ),
    (memberchk(X34, [min,max,prod]) ->                                         
                                                                             
                                                                             
        append([[X19],X2,[X11,X12,X17,X18]], X6),
        X8 = [X25,X26],                                            
        functor(X29, #=, 2),                                                
        arg(1, X29, X19),                                                
        (X34 = prod ->
            arg(2, X29, (X11 * X12))                              
        ;
            functor(X22, X34, 2),                                            
            arg(1, X22, X11),                                         
            arg(2, X22, X12),
            arg(2, X29, X22)                                              
        )
    ;                                                                        
                                                                             
                                                                             
        (X34 = cmod ->                                                         
            append([[X19],X2,[X11,X12,X17,X18,X16]], X6),
            X8 = [X25,X26,X21],                                  
            
            ((integer(X21), X21=1) ->                                    
                true                                                         
            ;
                X22 = (X11 - (X12 mod X11))                 
            ),
            ((integer(X21), X21=0) ->                                    
                true                                                         
            ;
                X23 = (X12 - (X11 mod X12))                 
            )
        ;
         X34 = dmod ->                                                         
            append([[X19],X2,[X11,X12,X17,X18,X16]], X6),
            X8 = [X25,X26,X21],                                  
            ((integer(X21), X21=1) ->                                    
                true                                                         
            ;
                X22 = (X11 - (X11 mod X12))                 
            ),
            ((integer(X21), X21=0) ->                                    
                true                                                         
            ;
                X23 = (X12 - (X12 mod X11))                 
            )
        ;
         X34 = fmod ->                                                         
            append([[X19],X2,[X11,X12,X17,X18,X16]], X6),
            X8 = [X25,X26,X21],                                  
                                                                             
            ((integer(X21), X21=1) ->                                    
                true                                                         
            ;                                                                
                X22 = (X11 mod X12 #= 0)*X12 + (X11 mod X12 #> 0)*(X11 mod X12)
                
            ),
            ((integer(X21), X21=0) ->                                    
                true                                                         
            ;                                                                
                X23 = (X12 mod X11 #= 0)*X11 + (X12 mod X11 #> 0)*(X12 mod X11)
            )
        ;
            (memberchk(X34, [floor,ceil,mfloor]) -> X33 = div ; X33 = X34),        
            (X34 = mfloor ->
                append([[X19],X2,[X11,X12,X17,X18,X3,X4,X16]], X6),
                X8 = [X25,X26,X14,X15,X21]             
            ;
                append([[X19],X2,[X11,X12,X17,X18,X16]], X6),
                X8 = [X25,X26,X21]                               
           ),
            ((integer(X21), X21=1) ->                                    
                true                                                         
            ;
                functor(X22, X33, 2),                                       
                (X34 = ceil   -> arg(1, X22, (X11+X12-1))       ;  
                               arg(1, X22,  X11)                   ), 
                (X34 = mfloor -> arg(2, X22, max(X12-X4,1)) ;  
                               arg(2, X22, X12)                    )
            ),
            ((integer(X21), X21=0) ->                                    
                true                                                         
            ;
                functor(X23, X33, 2),                                       
                (X34 = ceil   -> arg(1, X23, (X12+X11-1))       ;  
                               arg(1, X23,  X12)                   ), 
                (X34 = mfloor -> arg(2, X23, max(X11-X3,1)) ;  
                               arg(2, X23, X11)                    )
            )
        ),
        functor(X29, #=, 2),                                                
        arg(1, X29, X19),                                                
        ((integer(X21), X21=1) ->                                        
            arg(1, X29, X23)
        ;
         (integer(X21), X21=0) ->                                        
            arg(1, X29, X22)
        ;                                                                    
                                                                             
                                                                             
            arg(2, X29, (((1-X16) * X22) + (X16 * X23)))
        )
    ),
    X7 = [X27,X28,X29].                                           

gen_polynom_templates(X3, X1, X4) :-
    formula_pattern(polynoms(X5), X3),                                         
    gen_polynom_templates1(X5, X1, X2, X4), 
    formula_pattern(tpolynom(X2), X3).                                 

gen_polynom_templates1([], _, [], []) :- !.
gen_polynom_templates1([X3|X5], X1, [X2|X6], [X4|X7]) :-
    gen_polynom_template(X3, X1, X2, X4), 
    gen_polynom_templates1(X5, X1, X6, X7).

gen_polynom_template(X9, X1, X3, X10) :-
    X3 = t(X5,
                        X6,
                        X7),
    length(X9, X8),                                                    
    length(X4, X8),                                             
    append([[X10], X1, X4], X5),      
    gen_sum_monomes_source_term(X9, X4, X1, 
                                X2, X7),
    functor(X6, #=, 2),                                                    
    arg(1, X6, X10),
    arg(2, X6, X2).

gen_sum_monomes_source_term([], [], _, 0, []) :- !.
gen_sum_monomes_source_term([t(_,X3,X5)|X7],                         
                        [X4|X8],                                       
                        X1,                          
                        (X4*X2)+X9,                            
                        [X5|X10]) :-                                       
    gen_monome_source_term(X3, X1, X2), 
    gen_sum_monomes_source_term(X7, X8, X1, X9, X10).     

gen_monome_source_term([], [], 1) :- !.                                    
gen_monome_source_term([0|X1], [_|X3], X4) :- !,                              
    gen_monome_source_term(X1, X3, X4).                                       
gen_monome_source_term([X3|X4], [X1|X5], X2*X6) :-
    X3 > 0,                                                                 
    gen_power_template(X3, X1, X2),              
    gen_monome_source_term(X4, X5, X6).                                       

gen_unaryf_template(X1, X3) :-
    formula_pattern(f(X23), X1),
    (X23 = 2 ->                                                        
        formula_pattern(unaryf([X4]), X1),    
        functor(X4, X9, _),
        X2 = [t(X5,
                            X6,
                            X7)],
        X3 = [X8],                                
        (memberchk(X9, [min,max,floor,mod]) ->
            arg(1, X4, X20),                              
            functor(X18, #=, 2),                                    
            arg(1, X18, X11),                                    
            arg(2, X18, X15),
            (X9 = mod ->
                X15 = (X8 mod X12)
            ;
                (X9 = floor -> X16 = div ; X16 = X9),
                functor(X15, X16, 2),                            
                arg(1, X15, X8),
                arg(2, X15, X12)                                   
            ),                                                       
            append([[X11], X3, [X12]], X5), 
            X7 = [X20],                                      
            X6 = [X18]                                    ;
         X9 = geq0 ->
            functor(X18, #<=>, 2),                                  
            arg(1, X18, X11),                                    
            arg(2, X18, X15),
            functor(X15, #>=, 2),
            arg(1, X15, X8),                               
            arg(2, X15, 0),
            append([X11], X3, X5),             
            X7 = [],
            X6 = [X18]                                    ;
         X9 = in ->
            arg(1, X4, X21),                              
            arg(2, X4, X22),                               
            functor(X18, #<=>, 2),                                  
            arg(1, X18, X11),                                    
            arg(2, X18, (X13#=<X8 #/\ X8#=<X17)),
                                                                     
            append([[X11],X3,[X13,X17]], X5),
            X7 = [X21,X22],                                   
            X6 = [X18]                                    ;
         X9 = power ->
            arg(1, X4, X14),                           
            gen_power_template(X14, X8, X10),
            functor(X18, #=, 2),                                    
            arg(1, X18, X11),                                    
            arg(2, X18, X10),
            append([[X11],X3],X5),             
            X7 = [],
            X6 = [X18]                                    ;
         X9 = sum_consec ->
            functor(X18, #=, 2),                                    
            arg(1, X18, X11),                                    
            arg(2, X18, X15),
            X15 = ((X8 * (X8 + 1)) div 2),         
            functor(X19, #>=, 2),                                   
            arg(1, X19, X8),
            arg(2, X19, 0),
            append([X11], X3, X5),             
            X7 = [],
            X6 = [X18,X19]                               ;
            write(gen_unaryf_template), nl, halt                   )
    ;
        X2 = []
    ),
    formula_pattern(tunaryf(X2), X1).        

gen_power_template(1, X1, X1) :- !.
gen_power_template(X3, X1, X1*X4) :-
    X3 > 1,
    X2 is X3-1,
    gen_power_template(X2, X1, X4).

gen_binaryf_template(X2, X4) :-
    formula_pattern(f(X17), X2),
    (X17 = 3 ->                                                       
        formula_pattern(binaryf([X3]), X2), 
        functor(X3, X10, _),
        X1 = [t(X7,
                             X8,
                             X9)],
        append([X11], X4, X7),                
        X9 = [],                                            
        X4 = [X5,X6],                  
        functor(X14, #=, 2),                                       
        arg(1, X14, X11),                                       
        arg(2, X14, X12),
        (memberchk(X10,[ceil,floor]) -> X13 = div      ;    
         memberchk(X10, [cmod,dmod]) -> X13 = mod      ;
                                              X13 = X10),   
        (X10 = ceil -> X12 = ((X5 + X6 - 1) div X6) ; 
         X10 = cmod -> X12 = (X5 - (X6 mod X5))     ;
         X10 = dmod -> X12 = (X5 - (X5 mod X6))     ;
         X10 = prod -> X12 = (X5*X6)                         ;
                             functor(X12, X13, 2),              
                             arg(1, X12, X5),
                             arg(2, X12, X6)                                ),
        (memberchk(X10,[ceil,floor]) ->                       
            functor(X15, #>, 2),                                   
            arg(1, X15, X6),
            arg(2, X15, 0),
            X8 = [X14,X15]            ;                   
         X10 = prod ->                                        
           functor(X15, #>=, 2),                                   
           arg(1, X15, X5),
           arg(2, X15, 0),
           X8 = [X14,X15]             ;                   
         memberchk(X10, [mod,dmod]) ->                        
            functor(X15, #>, 2),                                   
            arg(1, X15, X6),
            arg(2, X15, 1),
            functor(X16, #>=, 2),                                  
            arg(1, X16, X5),
            arg(2, X16, 0),
            X8 = [X14,X15,X16]        ;                  
         X10 = cmod ->                                        
            functor(X15, #>, 2),                                   
            arg(1, X15, X5),
            arg(2, X15, 1),
            functor(X16, #>=, 2),                                  
            arg(1, X16, X6),
            arg(2, X16, 0),
            X8 = [X14,X15,X16]        ;                  
         memberchk(X10, [min,max]) ->                         
            X8 = [X14]                  ;                  
            write(gen_binaryf_template), nl, halt)
    ;
        X1 = []
    ),
    formula_pattern(tbinaryf(X1), X2).     

formula_pattern_gen_additional_ctr(X1, X2) :-
    formula_pattern(f(1),  X1),                                            
    formula_pattern(nu(0), X1),                                            
    formula_pattern(nb(0), X1),                                            
    !,
    formula_pattern(polynoms([X4]), X1),                              
    tab_get_gcd(X2, X3),
    get_polynom_coefs(X4, X8),
    (X3 = 0 ->
        get_max_abs_dvars(X8, X6),
        X7 = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97],
        findall(X9, (member(X9, X7), X9 =< X6), X5),
        gcd_eq_one_ctr(X5, X8),
        set_first_coef_diff_from_zero_to_positive(X8)
    ;
        true
    ).
formula_pattern_gen_additional_ctr(_, _).

get_polynom_coefs([], []) :- !.
get_polynom_coefs([t(_,_,X1)|X3], [X1|X4]) :-
    get_polynom_coefs(X3, X4).

gcd_eq_one_ctr([], _) :- !.
gcd_eq_one_ctr([X2|X3], X4) :- gcd_eq_one_ctr(X4, X2, X1), call(X1), gcd_eq_one_ctr(X3, X4).

gcd_eq_one_ctr([], _, 0) :- !.
gcd_eq_one_ctr([X1|X2], X3, X1 mod X3 #> 0 #\/ X4) :- gcd_eq_one_ctr(X2, X3, X4).

set_first_coef_diff_from_zero_to_positive(X5) :-                     
    reverse(X5, X3),                                           
    X3 = [X4|X1],                                  
    append(X1, [X4], X2),                      
    set_first_coef_diff_from_zero_to_positive1(X2, X6),     
    call(X6).                                           

set_first_coef_diff_from_zero_to_positive1([X1], X1 #>= 0) :- !.
set_first_coef_diff_from_zero_to_positive1([X1,X2|X3], (X1 #> 0 #\/ (X1 #= 0 #/\ X4))) :-
    set_first_coef_diff_from_zero_to_positive1([X2|X3], X4).
