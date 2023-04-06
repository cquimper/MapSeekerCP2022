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
% Purpose: GENERATE A PARAMETERISED CANDIDATE FORMULA WRT SOME GIVEN OPTIONS,
%          AND ON BACTRACKING PRODUCE THE NEXT CANDIDATE FORMULA
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_formula,[is_boolean_formula/1,                              
                       is_unconditional_formula/1,                        
                       get_cond_cost_vars/2,                              
                       get_then_cost_vars/2,                              
                       get_else_cost_vars/2,                              
                       get_nber_of_used_unary_binary_functions/2,         
                       formula_generator/11,                              
                       clear_type_found_formula/0,                        
                       record_type_found_formula/3,                       
                       keep_conditional_formula/2,                        
                       search_a_single_formula_for_all_table_entries/3]). 

:- use_module(library(timeout)).
:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(gen_poly_formula).
:- use_module(gen_bool_formula).
:- use_module(gen_cond_formula).
:- use_module(utility).
:- use_module(table_access).
:- use_module(instrument_code).




max_main_formula(3). 

                                                                                          
                                                                                          
                                                                                          
default_option(cond,            [attr_eq_coef,attr_eq_attr,attr_leq_coef,attr_leq_attr]). 
default_option(then,            [cst,attr]).                                              
default_option(else,            [cst,attr]).                                              

                                                                          
default_option(mandatory_attr,  []).                                      
default_option(optional_attr,   []).                                      
default_option(min_attr,        [0]).                                     
default_option(max_attr,        [9]).                                     
default_option(table_attr,      []).                                      
default_option(nb_polynom,      [0,1,2]).                                 
default_option(nb_unary,        [0,1]).                                   
default_option(nb_binary,       [0,1]).                                   
default_option(main_formula,    [0-t,                                     
                                 1-t([degree(1,1)]),                      
                                 2-t([degree(1,1)]),                      
                                 3-t([degree(1,1)],[degree(1,1)])]).      
default_option(unary,           [min,max,floor,ceil,mod,                  
                                 in,geq,power(2),sum_consec]).
default_option(binary,          [min,max,floor,mfloor,mod,prod,ceil,      
                                 cmod,dmod,fmod]).
default_option(unary_function,  [in,geq0,power(2),sum_consec]).           
default_option(binary_function, [min,max,floor,mod,prod,cmod,dmod]).      

get_option(X3, X1, X2) :-                                   
    functor(X4, X3, 1),                                                
    arg(1, X4, X2),                                                   
    (memberchk(X4, X1) -> true ; default_option(X3, X2)).

is_boolean_formula(X1) :-
    formula_pattern(op(_), X1).                               

is_unconditional_formula(X1) :-
    formula_pattern(f(_), X1).                                

get_cond_cost_vars(X1, X2) :-
    formula_pattern(cond(_, _, _, _, _, _, X2, _, _, _, _, _), X1).

get_then_cost_vars(X1, X2) :-
    formula_pattern(then(_, _, _, _, _,    X2, _, _, _, _, _), X1).

get_else_cost_vars(X1, X2) :-
    formula_pattern(else(_, _, _, _, _,    X2, _, _, _, _, _), X1).

get_nber_of_used_unary_binary_functions(X2, X1) :-
    formula_pattern(then(X7, _, _, _, _, _, _, _, _, _, _), X2),
    functor(X7, X3, _),
    (memberchk(X3, [unary_term,binary_term]) ->
        X5 = 1
    ;
        X5 = 0
    ),
    formula_pattern(else(X8, _, _, _, _, _, _, _, _, _, _), X2),
    functor(X8, X4, _),
    (memberchk(X4, [unary_term,binary_term]) ->
        X6 = 1
    ;
        X6 = 0
    ),
    X1 is X5+X6.

formula_pattern_create(bool, [mandatory_attr(_),       
                              neg(_),                  
                              shift(_),                
                              op(_),                   
                              nb_terms(_),             
                              conds(_),                
                              combined_row_ctrs(_,   
                                                _,
                                                _,
                                                _)]).


formula_pattern_create(cond, [mandatory_attr(_),       
                              cond(_,             
                                                       
                                                       
                                   _,            
                                   _,            
                                   _,            
                                   _,              
                                   _,             
                                   _,         
                                   _,  
                                   _, 
                                   _, 
                                   _,       
                                   _),      
                              then(_,             
                                   _,            
                                   _,            
                                   _,              
                                   _,             
                                   _,         
                                   _,  
                                   _, 
                                   _, 
                                   _,       
                                   _),      
                              else(_,             
                                   _,            
                                   _,            
                                   _,              
                                   _,             
                                   _,         
                                   _,  
                                   _, 
                                   _, 
                                   _,       
                                   _)]).    

formula_pattern_create(formula, [np(_),                                    
                                 nu(_),                                    
                                 nb(_),                                    
                                 f(_),                                     
                                 cst(_),                                   
                                 unary(_),                                 
                                 binary(_),                                
                                 unaryf(_),                                
                                 binaryf(_),                               
                                 attributes_use(_),                        
                                 polynoms(_),                              
                                 tattributes(_),                           
                                                                           
                                 tunary(_),                                
                                                                           
                                 tbinary(_),                               
                                                                           
                                 tpolynom(_),                              
                                                                           
                                 tunaryf(_),                               
                                                                           
                                 tbinaryf(_),                              
                                                                           
                                 mandatory_optional_attributes_names(_)]). 
                                                                           

formula_generator(X7, X6, X3, X5, X11, X10, X13, X4, X1,
                  X12, X9) :-
    member(X8, X6),                 
    (memberchk(bool(_), X8) -> 
        X2 = bool
    ;
     memberchk(cond(_), X8) ->
        keep_conditional_formula(X11, X13),   
        X2 = cond
    ;
        keep_unconditional_formula(X11, X13), 
        X2 = formula                
    ),
    formula_generator1(X2, X7, X8, X3, X5, X10, X13, X4, X1, 
                       X12, X9).

keep_conditional_formula(X1, X3) :-
    ((X1 = secondary, type_found_formula(X3, boolean, X2), X2 =< 3) -> false ; true).

keep_cluster_formula(X1, X3) :-
    ((X1 = secondary, type_found_formula(X3, conditional, X2), X2 =< 3) -> false ;
                                                                                  true  ).

keep_unconditional_formula(X1, X3) :-
    ((X1 = secondary, type_found_formula(X3, boolean, _))                   -> false ;
     (X1 = secondary, type_found_formula(X3, conditional, X2), X2 =< 3) -> false ;
     (X1 = secondary, type_found_formula(X3, cluster,     X2), X2 =< 5) -> false ;
                                                                                  true  ).

clear_type_found_formula :-
    retractall(type_found_formula(_,_,_)).

record_type_found_formula(X1, X3, X2) :-
    retractall(type_found_formula(X3,_,_)),
    (is_boolean_formula(X1)       -> assert(type_found_formula(X3,boolean,X2))       ;
     is_unconditional_formula(X1) -> assert(type_found_formula(X3,unconditional,X2)) ;
                                                 assert(type_found_formula(X3,conditional,X2))   ).





formula_generator1(bool, X50, X51, X30, X37, X57, X66, X34, X15, 
                   X63, X56) :- !,
    X31            = [],                                        
    X1 = [],                                        
    X38              = [],                                        
    get_option(mandatory_attr, X51, X22),                 
    get_option(bool,           X51, X23),                 
    X35 = [mandatory_attr(X22)|X23],         
    formula_generator_bool_conds(X35, X30,               
                                 X37,                             
                                 t(X52,X44,X39,X2),
                                 X12),
    formula_pattern_create(bool, X12),
    (get_option(cluster,           X51, [[X58],X59]) ->         
        X15 = [cluster([X58],X59)|X12]       
    ;                                                                   
     get_option(then_else,         X51, X45) ->                
        X15 = [then_else(X45)|X12]          
    ;
        X15 = X12
    ),
    memberchk(conds(X60), X15),
    pos_bool_cond_entry(lcondattr,      X25),
    pos_bool_cond_entry(lcondextravars, X10),
    get_entries_of_all_boolean_conditions(X60, X25,      X40),
    get_entries_of_all_boolean_conditions(X60, X10, X16),
    flatten(X40, X24),                                  
    flatten(X16, X9),                        
    append(X24, X9, X46),                
    length(X22, X64),
    X61 is X64+1,
    length(X60, X68),                                                   
    (X2 = 1 ->                                       
        X17 = 1                                              
    ;
        (get_option(cluster, X51, _) ->                             
            X17 is min(X68,2)                                  
        ;                                                               
            X17 is min(X68,3)                                  
        )
    ),
    gen_occ_vars(2, X61, X17, X53, X26),      
    length(X24, X11),
    X54 is X11-X64,
    X65 in 0..X54,                                                 
    global_cardinality(X24, [1-X65|X53]),                
    gen_sum_term(X26, var, X36),                        
    call(X36 #= X52 + 2*X44 + 3*X39),             


    instrument_code(instrument_in_formula_generator, X50),
    search_a_single_formula_for_all_table_entries(X50, X15, col(X57,X66)),
    X55 = 12000000,                                                   
    (get_option(then_else,         X51, X45) ->                
        X45 = [then(X32, X47, X41, X18, _,
                    _, _, _, _),
                    else(X33, X48, X42, X20, _,
                    _, _, _, _)],
        formula_pattern(op(X62),                 X15),
        avoid_simplifiable_conditional(X60, X22, X62,
                                        X32, X33,
                                        X41,   X42,
                                        X47,    X48),
        append([X31,X41,X42],       X27),
        append([X46,X18,X20],X43),
        (user:max_cost(X67) -> X63 in 0..X67 ; X67 = X34, X63 in 0..X67),
        get_bool_cost_vars(X15, X28),                   
        get_option(cost_then_else, X51, X29),
        X49 in 0..X67,
        gen_cost_sum_abs(X28, X49),
        X63 #= X29 + X49,
        time_out(minimize(label(X27, X1,
                                X43, X38), X63, [all]), X55, X56)
    ;
        (user:max_cost(X67) -> X63 in 0..X67 ; X67 = X34, X63 in 0..X67),
        get_bool_cost_vars(X15, X28),                   
        gen_cost_sum_abs(X28, X63),
        time_out(minimize(label(X31, X1, X46, X38), X63, [all]), X55, X56)
    ).

formula_generator1(cond, X52, X53, X26, _, X61, X69, X32, X12,
                   X64, X60) :- !,
    X27            = [],                                        
    X1 = [],                                        
    X34              = [],                                        
    get_option(mandatory_attr, X53, X22),                 
    get_option(cond,           X53, X65),                          
    get_option(then,           X53, X66),                          
    get_option(else,           X53, X67),                          
    length(X22, X68),                                        
    formula_generator_condition(X68, X22, X26, X65, X28, X35, X13, X23, X36, X37, X38,
                                X54, X45, X9, X3, X4, X14, X15),
    formula_generator_then_else(X68, X22, X66, X29, X39, X16, X24, X40, X41,
                                X55, X46, X10, X5, X6, X17, X18),
    formula_generator_then_else(X68, X22, X67, X30, X42, X19, X25, X43, X44,
                                X56, X47, X11, X7, X8, X20, X21),
    avoid_same_condattr_in_then(X22, X28, X35, X39, X45),
    avoid_same_condattr_in_else(X22, X28, X35, X42, X45),
    avoid_same_func_in_cond_and_then(X28, X36, X37, 
                                     X29, X40, X41),
    avoid_same_func_in_cond_and_then(X28, X36, X37, 
                                     X30, X43, X44),
    avoid_simplifiable_conditional(X22,
                                   X28, X29, X30,
                                   X35,   X39,   X42,
                                   X45,    X46,    X47),
    append([X35,X39,X42], X62),                     
    append([X13,X16,X19], X33), 
    append(X62, X33, X48),                                
    length(X62, X63),                                               
    gen_occ_vars(1, X68, X63, X57),                              
    global_cardinality(X62, X57),                                 
    X12 = [mandatory_attr(X22),                    
                      cond(X28, X36, X37, X38, X54, X45, X23,
                           X9, X3, X4, X14, X15),
                      then(X29, X40, X41,            X55, X46, X24,
                           X10, X5, X6, X17, X18),
                      else(X30, X43, X44,            X56, X47, X25,
                           X11, X7, X8, X20, X21)],
    formula_pattern_create(cond, X12),


    instrument_code(instrument_in_formula_generator, X52),

    search_a_single_formula_for_all_table_entries(X52, X12, col(X61,X69)),
    (user:max_cost(X70) -> X64 in 0..X70 ; X70 = X32, X64 in 0..X70),
    get_nber_of_used_unary_binary_functions(X12, X2),
    (X2 = 2 -> X58 = 3 ; X58 = X2),
    X49 in 0..X70,
    X50 in 0..X70,
    X51 in 0..X70,
    gen_cost_sum_abs(X23,      X49),                     
    gen_cost_sum_abs_max1(X24, X50),                     
    gen_cost_sum_abs_max1(X25, X51),                     
    X64 #= X49 + max(X50,X51) + X58 + 1,            
    X64 #>= 2,                                                         
    X59 = 1000,                                                     
    time_out(minimize(label(X27, X1, X48, X34), X64, [all]), X59, X60).


formula_generator1(formula, X42, X43, _, _, X52, X64, X20, X10,
                   X58, X47) :-


    get_option(mandatory_attr,  X43, X11),                
    get_option(optional_attr,   X43, X14),                 
    get_option(min_attr,        X43, X44),                      
    get_option(max_attr,        X43, X45),                      
    get_option(table_attr,      X43, X23),                    
    get_option(nb_polynom,      X43, X24),                    
    get_option(nb_unary,        X43, X25),                    
    get_option(nb_binary,       X43, X26),                    
    get_option(main_formula,    X43, X33),                     
    get_option(unary,           X43, X34),                     
    get_option(binary,          X43, X35),                     
    get_option(unary_function,  X43, X27),                    
    get_option(binary_function, X43, X28),                    
    length(X11, X6),                            
    length(X14,  X9),                             
    X59 is X6 + X9,                         
    X60 is max(X44,X6),                              
    X61 is min(X45,X59),                                          
    (X60 > X61 -> write(error(formula_generator1)), nl, halt ;        
     X59 > 20   -> write(error(formula_generator2)), nl, halt ;        
                    true                                       ),
    append(X11, X14, X29),                     
    gen_possible_combinations_of_attr(X23, X29,             
                                      X21),                      
    max_member(X53, X24),                                       
    max_member(X54, X25),                                       
    max_member(X55, X26),                                       
    max_main_formula(X62),                                             
    X69 in 0..X53,                                                     
    X70 in 0..X54,                                                     
    X71 in 0..X55,                                                     
    X72  in 0..X62,                                                      
    (X45 = 0 -> X69 #= 0 ; true),                                    
    (X44 > 1 -> X69 #> 0 ; true),                                    
    X70+X71 #=< 1,                                                        
    X69 #= 0 #=> X70 #= 0,                                                
    X69 #= 0 #=> X71 #= 0,                                                
    X69 #= 0 #=> X72 #= 0,                                                 
    X69 #= 1 #=> X72 #= 1 #\/ X72 #= 2,                                      
    X69 #= 2 #=> X72 #= 3,                                                 
    member(X69, X24),                                              
    member(X70, X25),                                              
    member(X71, X26),                                              
    member(X30,  X33),                                       
    X30 = X72-X36,
    (X72 = 2 -> X65 = 1 ; X65 = 0),                                       
    (X72 = 3 -> X66 = 1 ; X66 = 0),                                       
    length(X31,          X70),                                     
    length(X22,         X71),                                     
    length(X4,  X65),                                    
    length(X3, X66),                                    
    members(X31,          X34),                              
    members(X22,         X35),                              
    members(X4,  X27),                             
    members(X3, X28),                             


    instrument_code(instrument_in_formula_generator, X42),
    extend_functor_unary(X31, X15, 1,                    
                         [min,max,floor,ceil,mod,geq],
                         [sum_consec],X48,X37),
    extend_functor_unary(X4, X7, 0,        
                         [min,max,floor,mod],
                         [geq0,sum_consec], X49,X38),
    append(X37, X38, X32),
    extend_functor_binaryt(X22, X12, X39),        
    append([X39,X48, X49], X1),
    formula_pattern_create(formula, X10),                    
    (X72 = 0 ->                                                           
        X67 in inf..sup,                                                
        formula_pattern(cst(X67), X10)                       
    ;                                                                   
        formula_pattern(cst(0), X10)                         
    ),
    formula_pattern(np(X69),                      X10),       
    formula_pattern(nu(X70),                      X10),       
    formula_pattern(nb(X71),                      X10),       
    formula_pattern(f(X72),                        X10),       
    formula_pattern(unary(X15),         X10),       
    formula_pattern(binary(X12),       X10),       
    formula_pattern(unaryf(X7),    X10),       
    formula_pattern(binaryf(X3), X10),       
    formula_gen_attr_ctrs(X10, X60, X61, X59, X29,  
                          X6, X50, X56, X17, 
                          X21),
    append([X11,X14,                                 
            X31,                                                  
            X22], X51),                                       
    X18  is X59+1,                                             
    X16 is X59+X70+1,                                          
    get_break_sym_in_unaryt_binaryt(X70, X18,  X31,        
                                    X71, X16, X22,       
                                    X2),            
    get_break_sym_in_unaryf(X72, X7,                        
                            X8),                          
    get_break_sym_in_binaryf(X72, X3,                     
                             X5),                        
    formula_gen_polynoms(1, X69, X36, X51,                       
                         X2, X8,      
                         X5, X50, X40, X57),
    restrict_attr_wrt_binary_functions(X72, X3,           
                                       X57, X56),
    append(X57, X41),                                            
    formula_pattern(polynoms(X40), X10),                
    formula_pattern(mandatory_optional_attributes_names(X29),     
                    X10),                                    
    gen_source_target_templates(formula, X10,                
                                X29, X59),
    search_a_single_formula_for_all_table_entries(X42, X10, col(X52,X64)),
    (user:max_cost(X68) -> X58 in 0..X68 ; X68 = X20, X58 in 0..X68),
    append([X1, X41], X63),                   
    gen_cost_sum_abs(X63, X32, X58),
    X46 = 10000,                                                    
    time_out(minimize(label(X17, X1, X41, X32), X58, [all]), X46, X47).

label(X3, X1, X6, X5) :-
    split_list_vars(X6, X7, X4, X2),
    labeling([ffc],  X3),
    labeling([ffc],  X1),
    labeling([down], X7),
    labelpos(X2),
    labelcoefs(X4),
    once(labeling([], X5)).

split_list_vars([], [], [], []) :- !.
split_list_vars([X1|X2], X3, X4, X5) :-
    integer(X1), !,
    split_list_vars(X2, X3, X4, X5).
split_list_vars([X1|X2], [X3|X4], X5, X6) :-
    nonvar(X1),
    functor(X1, condb, 1), !,
    arg(1, X1, X3),
    split_list_vars(X2, X4, X5, X6).
split_list_vars([X1|X4], X5, [X2|X6], X7) :-
    nonvar(X1),
    functor(X1, coef, 2), !,
    arg(1, X1, X3),
    arg(2, X1, X8),
    functor(X2, X3, 1),
    arg(1, X2, X8),
    split_list_vars(X4, X5, X6, X7).
split_list_vars([X1|X2], X3, X4, [X1|X5]) :-
    split_list_vars(X2, X3, X4, X5).

labelpos([]) :- !.
labelpos([X1|X2]) :-
    integer(X1),
    !,
    labelneg(X2).
labelpos([X1|X2]) :-
    X1 #> 0,
    labeling([up,bisect], [X1]),
    labelneg(X2).
labelpos([0|X1]) :-
    labelneg(X1).
labelpos([X1|X2]) :-
    X1 #< 0,
    labeling([down,bisect], [X1]),
    labelneg(X2).

labelneg([]) :- !.
labelneg([X1|X2]) :-
    integer(X1),
    !,
    labelpos(X2).
labelneg([X1|X2]) :-
    X1 #< 0,
    labeling([down,bisect], [X1]),
    labelpos(X2).
labelneg([0|X1]) :-
    labelpos(X1).
labelneg([X1|X2]) :-
    X1 #> 0,
    labeling([up,bisect], [X1]),
    labelpos(X2).

labelcoefs([]) :- !.
labelcoefs([eq(X2)|X3]) :- !,
    fd_min(X2, X1),
    X2 = X1,
    labelcoefs(X3).
labelcoefs([leq(X2)|X3]) :- !,
    fd_min(X2, X1),
    X2 = X1,
    labelcoefs(X3).
labelcoefs([geq(X2)|X3]) :-
    fd_max(X2, X1),
    X2 = X1,
    labelcoefs(X3).

search_a_single_formula_for_all_table_entries(X2, X1, X3) :-
    (formula_pattern(f(_), X1) ->
        search_a_single_formula_for_all_table_entries_formula(X2, X1, X3) 
    ;
     formula_pattern(op(_), X1) ->
        search_a_single_formula_for_all_table_entries_bool(X2, X1, X3)    
    ;
        search_a_single_formula_for_all_table_entries_cond(X2, X1, X3)    
    ),
    !.
search_a_single_formula_for_all_table_entries(X1, _, _) :-
    instrument_code(instrument_fail_without_time_out, X1),
    false.

search_a_single_formula_for_all_table_entries_bool(_, X6, X20) :-
    formula_pattern(mandatory_attr(X13),          X6),      
    formula_pattern(neg(X18),                       X6),      
                                                                              
    formula_pattern(shift(X14),                   X6),      
                                                                              
    formula_pattern(op(X21),                          X6),      
    formula_pattern(nb_terms(X19),                  X6),      
    formula_pattern(conds(X22),                       X6),      
    formula_pattern(combined_row_ctrs(X5,                        
                                      X3,
                                      X4,
                                      X10),      X6),
    X20 = col(X23,_),                                                    
    tab_get_arity(col(X23,_), X24),                                       
    append(X13, [X20], X8),                                
    length(X8, X15),                                          
    length(X11, X15),                                            
    functor(X12, X23, X24),                                        
    build_source_target_extraction_terms(X8, X12, X11),
    (formula_pattern(cluster(X25,X26), X6) ->                 
        findall(X2, (call(user:X12),                    
                                    update_table_entry_cluster(X11,    
                                                               X25,         
                                                               X26,         
                                                               X2)),
                                   X9)
    ;                                                                         
        findall(X11, call(user:X12),                            
                            X9)                                     
    ),
    sort(X9,X7),
    (formula_pattern(then_else(X17), X6) ->
        true
    ;
        X17 = []
    ),
    post_bool_on_all_table_entries(X7, X13, X18, X14, X21, X19, X22, 
                                   combined_row_ctrs(X5, X3, X4, X10),
                                   X17, X1),
    (formula_pattern(then_else(_), X6) ->
        minimum(0, X1),                                
        count(1,X1,#>,0)                               
                                                                                  
                                                                                  
     ;
        true).

post_bool_on_all_table_entries([], _, _, _, _, _, _, _, _, []) :- !.
post_bool_on_all_table_entries([X30|X65], X52, X59, X53, X62, X60, X63,
                               combined_row_ctrs(X21,X19,X20,X40),
                               X57, X2) :-
    (X57 = [] ->                                                             
        update_table_entry(X30, X59, X53, X62, X60, X41, X15),
        post_bool_on_one_table_entry(X63, X52, X62, X60, X15, X54),
        append(X21, X19,  X42),
        append([[X41],X54,X20], X43),
        copy_term(X42-X40, X43-X44),
        post_ctrs(X44),
        X2 = []
    ;                                                                              
        X57 = [then(_, _, _, _, _,
                    X16, X9, X10, X25),
                    else(_, _, _, _, _,
                    X17, X11, X12, X27)],
        remove_last_elem(X30, X6, X58),         
        length(X6, X64),       
        length(X16, X7),                       
        X4 is X7-X64,                   
        length(X13, X4),                    
        append(X16, X9, X36),            
                                                                                   
        append([X13, X6, X10], X37),
        X16  = [X47|_],
        X13 = [X33|_],
        copy_term(X36-X25, X37-X28),
        post_ctrs(X28),
        length(X17, X8),                       
        X5 is X8-X64,                   
        length(X14, X5),                    
        append(X17, X11, X38),            
        
        append([X14, X6, X12], X39),
        X17  = [X48|_],
        X14 = [X34|_],
        copy_term(X38-X27, X39-X29),
        post_ctrs(X29),
        X21 = [X49|_],
        
        remove_last_elem(X18, X6, X35),   
        post_bool_on_one_table_entry(X63, X52, X62, X60, X18, X54),
        
        append(X21, X19,  X42),
        append([[X35],X54,X20], X43),
        copy_term(X42-X40, X43-X44),
        post_ctrs(X44),
        
        X50 = [  X49 #=> (X61 #= X47),
                      #\X49 #=> (X61 #= X48)],
        copy_term([X61,  X47,  X48,  X49  ]-X50,
                  [X58,X33,X34,X35]-X51),
        post_ctrs(X51),
     
        X3 in 0..2,
        X33 #=  X34 #=> X3 #= 2,                 
        X33 #\= X34 #=> X3 #= X35,
        X2 = [X3|X1]
    ),
    post_bool_on_all_table_entries(X65, X52, X59, X53, X62, X60, X63,
                                   combined_row_ctrs(X21, X19, X20, X40),
                                   X57, X1).

update_table_entry_cluster([X4], X2, X3, [X1]) :-
    !,
    (memberchk(X4, X2) -> X1 = 1 ;
     memberchk(X4, X3) -> X1 = 0 ;
                              false          ).
update_table_entry_cluster([X1|X4], X2, X3, [X1|X5]) :-
    update_table_entry_cluster(X4, X2, X3, X5).

update_table_entry(X1, 0, 0, _, _, X2, X1) :-
    !, last(X1, X2).
update_table_entry(X2, X5, X4, X7, X6, X3, X1) :-
    update_table_entry0(X2, X5, X4, X7, X6, X3, X1).

update_table_entry0([X7], X4, X3, X6, X5, X2, X1) :-
    !,
    (X4 = 1 ->                                                   
        (X6 = sum ->
            X2 is X5-(X7-X3)
        ;
            X2 is 1-(X7-X3)
        )
    ;
     X3 = 0 ->
        X2 is X7
    ;
        X2 is X7-X3
    ),
    X1 = [X2].
update_table_entry0([X1|X7], X4, X3, X6, X5, X2, [X1|X8]) :-
    update_table_entry0(X7, X4, X3, X6, X5, X2, X8).

post_bool_on_one_table_entry([], _, _, _, _, []) :- !.
post_bool_on_one_table_entry([X26|X27], X18, X25, X23, X8, [X21|X28]) :-
    X26 = cond(_, _, X19, _, _, _, _, _, _, _,
                X4, X1, X2, X14, _),
    X21 in 0..1,
    append(X4, X1, X15),    
    length(X19, X10),
    length(X6, X10),
    append([[X21],X6,X8,X2], X16),
    copy_term(X15-X14, X16-X17),
    post_ctrs(X17),
    post_bool_on_one_table_entry(X27, X18, X25, X23, X8, X28).

search_a_single_formula_for_all_table_entries_cond(_, X13, X41) :-
                                                                              
    formula_pattern(mandatory_attr(X31), X13),
    formula_pattern(cond(_,_,_,_,_,_,_,X10,X4,X5,
                         X14,X15), X13),
    formula_pattern(then(X36,_,_,_,_,_,  X11,X6,X7,
                         X16,X17), X13),
    formula_pattern(else(X37,_,_,_,_,_,  X12,X8,X9,
                         X18,X19), X13),
    functor(X36, X32, _),                                          
    (memberchk(X32, [unary_term,                                        
                           binary_term]) ->                                   
        X1 = 1
    ;
        X1 = 0
    ),
    functor(X37, X33, _),                                          
    (memberchk(X33, [unary_term,                                        
                           binary_term]) ->                                   
        X2 = 1
    ;
        X2 = 0
    ),
    X41 = col(X42,_),                                                    
    tab_get_arity(col(X42,_), X43),                                       
    append(X31, [X41], X24),                                
    length(X24, X34),                                          
    length(X26, X34),                                            
    functor(X27, X42, X43),                                        
    build_source_target_extraction_terms(X24, X27, X26),
    findall(X26, call(user:X27),                                
                        X25),                                        
    post_cond_on_all_table_entries(X25,
                                   X10, X4, X5, X14, X15,
                                   X11, X6, X7, X16, X17,
                                   X12, X8, X9, X18, X19,
                                   X3, X28, X29, X30,
                                   X38, X39, X40),
    minimum(0, X3),                                
    count(1,X3,#>,0),                              
                                                                              
                                                                              
    (X15 = 1 ->
        minimum(0, X28),
        maximum(2, X28)
    ;
        true
    ),
    (X17 > 0 ->                                                    
        gen_then_else_min_max_ctr(X29, 1, 0, X20),          
        call(X20),
        gen_then_else_min_max_ctr(X29, 1, 2, X21),
        call(X21)
    ;
        true
    ),
    (X19 > 0 ->                                                    
        gen_then_else_min_max_ctr(X30, 0, 0, X22),          
        call(X22),
        gen_then_else_min_max_ctr(X30, 0, 2, X23),
        call(X23)
    ;
        true
    ),
    (X1 = 1 ->
        no_unique_value_for_res_then_or_res_else(X38, X39, 1)
    ;
        true
    ),
    (X2 = 1 ->
        no_unique_value_for_res_then_or_res_else(X38, X40, 0)
    ;
        true
    ).

post_cond_on_all_table_entries([], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, [], [], [], [], [], [], []) :- !.
post_cond_on_all_table_entries([X30|X48], 
                               X18, X9, X10, X21, X22,
                               X19, X11, X12, X23, X24,
                               X20, X13, X14, X25, X26,
                               [X1|X49], X37, X38, X39,
                               [X43|X], [X44|X51], [X45|X52]) :-
    remove_last_elem(X30, X5, X46),           
    length(X5, X47),                                     
    length(X18, X6),                       
    X2 is X6-X47,                   
    length(X15, X2),                    
    append(X18, X9, X31),            
                                                                               
    append([X15, X5, X10], X32),
    copy_term(X31-X21, X32-X27),
    post_ctrs(X27),
    length(X19, X7),                       
    X3 is X7-X47,                   
    length(X16, X3),                    
    append(X19, X11, X33),            
                                                                               
    append([X16, X5, X12], X34),
    copy_term(X33-X23, X34-X28),
    post_ctrs(X28),
    length(X20, X8),                       
    X4 is X8-X47,                   
    length(X17, X4),                    
    append(X20, X13, X35),            
                                                                               
    append([X17, X5, X14], X36),
    copy_term(X35-X25, X36-X29),
    post_ctrs(X29),
    X15 = [X43|_],                                       
    X16 = [X44|_],                                        
    X17 = [X45|_],                                        
    X46 #= X43*X44 + (1-X43)*X45,
    X44 #\= X46 #=> X43 #= 0,
    X45 #\= X46 #=> X43 #= 1,
    X1 in 0..2,
    X44 #=  X45 #=> X1 #= 2,                 
    X44 #\= X45 #=> X1 #= X43,
    (X22 > 0 ->                                                     
        nth1(X22, X15, X40),                 
        X37 = [X40|X54]                                             
    ;                                                                          
        X37 = []
    ),
    (X24 > 0 ->                                                     
        nth1(X24, X16, X41),                 
        X38 = [X43-X41|X55]                                    
    ;                                                                          
        X38 = []
    ),
    (X26 > 0 ->                                                     
        nth1(X26, X17, X42),                 
        X39 = [X43-X42|X56]                                    
    ;                                                                          
        X39 = []
    ),
    post_cond_on_all_table_entries(X48,
                                   X18, X9, X10, X21, X22,
                                   X19, X11, X12, X23, X24,
                                   X20, X13, X14, X25, X26,
                                   X49, X54, X55, X56, X, X51, X52).

remove_last_elem([X1], [], X1) :- !.
remove_last_elem([X,X3|X4], [X|X5], X1) :-
    remove_last_elem([X3|X4], X5, X1).

post_ctrs([]) :- !.
post_ctrs([X1|X2]) :-
    call(X1),
    post_ctrs(X2).

search_a_single_formula_for_all_table_entries_formula(_, X7, X23) :-
    formula_pattern(f(X30),                                           X7), 
    formula_pattern(mandatory_optional_attributes_names(X17), X7), 
    formula_pattern(tunary(X8),                         X7), 
    formula_pattern(tbinary(X4),                       X7), 
    formula_pattern(tpolynom(X1),                     X7), 
    formula_pattern(tunaryf(X9),                        X7), 
    formula_pattern(tbinaryf(X5),                      X7), 
    X23 = col(X24,X27),                                               
    tab_get_type(col(X24,X27), X26),                                    
    ((X30 = 2, X26 \= bool) ->                                              
        formula_pattern(unaryf([X11]), X7),          
        functor(X11, X18, _),                              
        (memberchk(X18, [geq0,in]) -> false ; true)
    ;
        true
    ),
    formula_pattern_gen_additional_ctr(X7, X23),            
    tab_get_arity(col(X24,_), X25),                                    
    tab_get_inf_sup(col(X24,_), X28, X29),                               
    append(X17, [X23], X12),                             
    length(X12, X19),                                       
    length(X14, X19),                                         
    functor(X15, X24, X25),                                     
    build_source_target_extraction_terms(X12, X15, X14),
    findall(X14, call(user:X15),                             
                        X13),                                     
    (X30 = 2 ->                                                              
        formula_pattern(unaryf([X11]), X7),          
        functor(X11, X18, _),
        (memberchk(X18, [min,max,floor,mod]) ->                      
            X6 = 1                                            
        ;                                                                  
            X6 = 0
        )
    ;
        X6 = 0
    ),
    (X30 = 3 ->                                                              
        formula_pattern(binaryf([X10]), X7),        
        functor(X10, X20, _),
        (memberchk(X20, [min,max,floor,mod,cmod,dmod]) ->            
            X2 = 1                                           
        ;                                                                  
            X2 = 0
        )
    ;
        X2 = 0
    ),
    post_on_all_table_entries(X13, X28, X29, X30,
                              t(X1, X8, X4, X9, X5),
                              X6, X2, X21, X16),
    (X6 = 1 ->                                                
        arg(1, X11, X3),                           
        set_lt_gt_ctr_for_at_least_one_table_entry_for_ufunction(X21, X3, X18)
    ;
        true
    ),
    (X2 = 1 ->                                               
        set_lt_gt_ctr_for_at_least_one_table_entry_for_bfunction(X16, X20)
    ;
        true
    ).

build_source_target_extraction_terms([], _, []) :- !.
build_source_target_extraction_terms([col(_,X4)|X5], X1, [X2|X6]) :-
    arg(X4, X1, X2),
    build_source_target_extraction_terms(X5, X1, X6).

post_on_all_table_entries([], _, _, _, _, _, _, [], []) :- !.
post_on_all_table_entries([X27|X40], X36, X37, X41, X29, X20, X18, X30, X28) :-
    X29 = t(X19, X23, X21, X24, X22),
    length(X27, X38),
    X31 is X38-1,
    last(X27, X32),                                         
    prefix_length(X27, X33, X31),                        
    post_unary(X23, X33, X13),              
    post_binary(X21, X36, X37, X33, X4), 
    (X41 = 1 ->
        X19 = [t(X14,X15,X16)],
        append([[X32], X33, X13, X4, X16], X3), 
        copy_term(X14-X15, X3-X17),
        call(X17),
        X30  = X26,                           
        X28 = X25                           
    ;
     X41 = 2 ->
        X19 = [t(X14,X15,X16)],
        append([[X39], X33, X13, X4, X16], X3), 
        
        X39 in -10000..10000,
        copy_term(X14-X15, X3-X17),
        call(X17),
        
        X32 in -10000..10000,
        post_unaryf(X24, [X32,X39]),
        (X20 = 1 ->                               
            X30 = [X39|X26]                   
        ;
            X30 = X26
        ),
        X28 = X25                            

        
        
        
        
        
        
        
        
        
        
    ;
     X41 = 3 ->                                                 
        X19 = [t(X5,X6,X7),
                            t(X8,X9,X10)],
        append([[X34], X33, X13, X4, X7], X1),
        append([[X35], X33, X13, X4, X10], X2),
        
        
        
        X34 in -10000..10000,
        X35 in -10000..10000,
        copy_term(X5-X6, X1-X11),
        copy_term(X8-X9, X2-X12),
        call(X11),
        call(X12),
        
        X32 in -10000..10000,
        post_binaryf(X22, [X32,X34,X35]),
        (X18 = 1 ->                              
            X28 = [X34-X35|X25]           
        ;
            X28 = X25
        ),
        X30 = X26                             
    ;
        write(post_on_all_table_entries), nl, halt
    ),
    post_on_all_table_entries(X40, X36, X37, X41, X29, X20, X18, X26, X25).

set_lt_gt_ctr_for_at_least_one_table_entry_for_ufunction(X1, X4, X2) :-
    gen_all_cmp_signatures(X1, X4, X2, X3),
    (memberchk(X2, [min,max]) -> minimum(0, X3), maximum(2, X3) ; 
     X2 = floor               -> maximum(1, X3)                     ; 
     X2 = mod                 -> maximum(1, X3)                     ; 
                                        write(set_lt_gt_ctr_for_at_least_one_table_entry_for_ufunction), nl, halt).

set_lt_gt_ctr_for_at_least_one_table_entry_for_bfunction(X1, X2) :-
    gen_all_cmp_signatures(X1, X2, X3),
    (memberchk(X2, [min,max])       -> minimum(0, X3), maximum(2, X3) ; 
     X2 = floor                     -> maximum(1, X3)                     ; 
     memberchk(X2, [mod,cmod,dmod]) -> maximum(1, X3)                     ; 
                                              write(set_lt_gt_ctr_for_at_least_one_table_entry_for_bfunction), nl, halt).

gen_all_cmp_signatures([], _, _, []) :- !.
gen_all_cmp_signatures([X2|X5], X3, X1, [X4|X6]) :-
    (X1 = floor ->
        X4 in 0..1,
        call(X2 #=< X3 #<=> X4 #= 0),
        call(X2 #>  X3 #<=> X4 #= 1)  
    ;
     X1 = mod ->
        X4 in 0..1,
        call(X2 #<  X3 #<=> X4 #= 0),
        call(X2 #>= X3 #<=> X4 #= 1)  
    ;
        X4 in 0..2,                     
        call(X2 #< X3 #<=> X4 #= 0),  
        call(X2 #= X3 #<=> X4 #= 1),
        call(X2 #> X3 #<=> X4 #= 2)   
    ),
    gen_all_cmp_signatures(X5, X3, X1, X6).

gen_all_cmp_signatures([], _, []) :- !.
gen_all_cmp_signatures([X2-X3|X5], X1, [X4|X6]) :-
    (X1 = floor ->
        X4 in 0..1,
        call(X2 #=< X3 #<=> X4 #= 0),
        call(X2 #>  X3 #<=> X4 #= 1)  
    ;
     memberchk(X1, [mod,dmod]) ->
        X4 in 0..1,
        call(X2 #<  X3 #<=> X4 #= 0),
        call(X2 #>= X3 #<=> X4 #= 1)  
    ;
     X1 = cmod ->
        X4 in 0..1,
        call(X3 #<  X2 #<=> X4 #= 0),
        call(X3 #>= X2 #<=> X4 #= 1)  
    ;
        X4 in 0..2,                       
        call(X2 #< X3 #<=> X4 #= 0),  
        call(X2 #= X3 #<=> X4 #= 1),
        call(X2 #> X3 #<=> X4 #= 2)   
    ),
    gen_all_cmp_signatures(X5, X1, X6).

post_unary([], _, []) :- !.
post_unary([X7|X9], X8, [X2|X10]) :-
    X7 = t(X3,X4,X5),
    append([[X2], X8, X5], X1),
    copy_term(X3-X4, X1-X6),
    call(X6),
    post_unary(X9, X8, X10).

post_binary([], _, _, _, []) :- !.
post_binary([X7|X13], X11, X12, X8, [X2|X14]) :-
    X7 = t(X3,X4,X5),
    
    
    
    X9 in -10000..10000,
    X10 in -10000..10000,
    append([[X2], X8, [X9,X10], X5], X1),
    copy_term(X3-X4, X1-X6),
    post_unaries_or_binaries(X6),
    post_binary(X13, X11, X12, X8, X14).

post_binaryf(X6, X7) :-
    X6 = [t(X2,X3,X4)],
    append(X7, X4, X1),
    copy_term(X2-X3, X1-X5),
    post_unaries_or_binaries(X5).

post_unaryf(X6, [X7,X8]) :-
    X6 = [t(X2,X3,X4)],
    append([[X7,X8], X4], X1),
    copy_term(X2-X3, X1-X5),
    post_unaries_or_binaries(X5).

post_unaries_or_binaries([]) :- !.
post_unaries_or_binaries([X1|X2]) :-
    call(X1),
    post_unaries_or_binaries(X2).
