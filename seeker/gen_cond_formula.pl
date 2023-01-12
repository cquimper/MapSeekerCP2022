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
% Purpose: UTILITIES USED TO GENERATE A PARAMETERISED CONDITIONAL CANDIDATE FORMULA WRT SOME GIVEN OPTIONS,
%          AND ON BACTRACKING PRODUCE THE NEXT CANDIDATE FORMULA
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_cond_formula,[all_options/2,                              
                            formula_generator_condition/18,             
                            formula_generator_then_else/16,             
                            avoid_same_func_in_cond_and_then/6,         
                            avoid_same_condattr_in_then/5,              
                            avoid_same_condattr_in_else/5,              
                            avoid_simplifiable_conditional/10,
                            no_unique_value_for_res_then_or_res_else/3,
                            gen_then_else_min_max_ctr/4               ]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).
:- use_module(bool_cond_utility).
:- use_module(table_access).
                                                                          
all_options(cond,            [attr_eq_coef,   attr_eq_attr,   unary_term_eq_coef,  binary_term_eq_coef,
                              attr_leq_coef,  attr_leq_attr,  unary_term_leq_coef, binary_term_leq_coef,
                              attr_leq_unary, unary_leq_attr, attr_in_interval,
                              linear_eq_coef, sum_leq_attr,   minus_mod_eq0]).
all_options(then,            [cst, attr, unary_term, binary_term]).
all_options(else,            [cst, attr, unary_term, binary_term]).


all_options(unary_boolean,   [in,geq]).                                   
all_options(unary,           [plus,minus,prod,min,max,max_min,            
                              floor,ceil,floor_min,mod,                   
                              in,geq,power,sum_consec]).                  
all_options(binary,          [plus,minus,linear,abs,min,max,plus_min,     
                              prod,floor,mfloor,ceil,plus_floor,          
                              minus_floor,mod,cmod,dmod,fmod]).           
all_options(unary_function,  [in,geq0,power,sum_consec]).                 
all_options(binary_function, [min,max,floor,mod,prod,cmod,dmod]).         

formula_generator_condition(X55, X9, X18, X56, X19, X33, X6, X10, X34, X35, X36,
                            X52, X39, X3, X1, X2, X28, X7) :-
    (compound(X56) -> true ;
     atom(X56)     -> true ; write(formula_generator_condition1), nl, halt),                
    functor(X56, X40, X37),                                                      
    length(X11, X55),                                                             

    
    
    
    ((memberchk(X40, [attr_eq_attr,attr_leq_attr]), X37 = 0) ->                   
        X33      = [X34,X35],                                              
        X36      = 0,                                                                  
        X6 = [],                                                                 
        domain(X33, 1, X55),                                                          
        X39 = 0,                                                                        
        X52  = 0,                                                                        

        
        
        
        X57 = element(X14, X11, X41),                               
        X58 = element(X15, X11, X42),                               
        (X40 = attr_eq_attr ->                                                          
            X34 #< X35,                                                          
            X12 = [eq,lt,gt,neq],                                                  
            X59 = (X20 #<=> (X41 #= X42))                                 
        ;                                                                                    
            X34 #\= X35,                                                         
            X12 = [leq,eq,lt,gt],                                                  
            X59 = (X20 #<=> (X41 #=< X42))                                
        ),
        gen_table_ctr_wrt_forbidden_cmp(X55, X9, X12, 0, X33),
        append([X20,X41,X42], X11, X3),
        X1 = [X14,X15],
        X2 = [X34,X35],
        X28       = [X57,X58,X59],                                                 
        X19      = X40,
        X10    = [],
        X7   = 0
    ;

    
    
    
     (memberchk(X40, [attr_eq_coef,attr_leq_coef]), X37 = 1) ->                   
        ((arg(1, X56, coef(X21,X22)),                                       
          integer(X21), integer(X22), X21 =< X22) ->         
            X39 in X21..X22                                             
        ;
            write(formula_generator_condition2), nl, halt
        ),
        X33      = [X34],                                                        
        X6 = [X39],                                                         
        X34 in 1..X55,                                                                
        X35 = 0,                                                                       
        X36 = 0,                                                                       
        X52   = 0,                                                                       
        get_set_of_values_for_each_mandatory_attribute(X9, 0, allequal, 0,
                                                       X40, X18,
                                                       X21, X22,
                                                       [_|X8]),                  
                                                                                             
        table([[X34,X39]],X8),                                        
        X57 = element(X14, X11, X41),                               
        (X40 = attr_eq_coef ->                                                          
            forbid_cols_that_cant_intersect_min_max(X55, X9,                     
                                                    X21, X22, X34),    
            X58 = (X20 #<=> (X41 #= X23)),
            X28 = [X57,X58],                                                        
            append([X20,X41], X11, X3)
        ;                                                                                    
            forbid_cols_where_min_gt_up_or_max_leq_low(X55, X9,                  
                                                       X21, X22, X34), 
            X58 = (X20      #<=> (X41 #=< X23)),                       
                                                                                             
            
                                                                                             
                                                                                             
            X28 = [X57,X58],
            
            append([X20,X41], X11, X3)
        ),
        X1 = [X14,X23],
        X2 = [X34,X39],
        X19      = X40,
        X10    = [],
        X7   = 0
    ;

    
    
     (X40 = attr_in_interval, X37 = 2) ->
        arg(1, X56, X24),                                                           
        arg(2, X56, X25),                                                           
        ((integer(X24),
          integer(X25),
          X24 < X25) ->
            X52  in X24..X25,                                            
            X39 in X24..X25,                                            
            X52 #< X39,                                                             
                                                                                             
            X33      = [X34],                                                    
            X6 = [X52,X39],                                             
            X34 in 1..X55,                                                            
            X35 = 0,                                                                   
            X36 = 0,                                                                   
            get_set_of_values_for_each_mandatory_attribute(X9, 0, allequal, 0,
                                                           attr_leq_coef, X18,
                                                           X24, X25,
                                                           [_|X8]),              
                                                                                             
            table([[X34,X52]], X8),                                    
            table([[X34,X39]],X8),                                    
            X57 = element(X14, X11, X41),                           
            
            
            
            
            X60 = (X20 #<=> (X29 #=< X41 #/\ X41 #=< X23)),
            
            X28 = [X57,X60],                                                        
            append([X20,X41], X11, X3),
            X1 = [X14,X29,X23],                        
            X2 = [X34,X52,X39],                                 
            X19      = X40,                                                     
            X10    = [X39],                                                   
            X7   = 0
        ;
            write(formula_generator_condition3), nl, halt
        )
    ;

    
    
    
     (memberchk(X40,[attr_leq_unary,                                                    
                          unary_leq_attr]), X37 = 1) ->                                
        arg(1, X56, X30),                                                            
        X33      = [X34,X35],                                              
        X36      = 0,                                                                  
        X6 = [X52],                                                          
        domain(X33, 1, X55),                                                          
        X34 #\= X35,                                                             
        (X40 = attr_leq_unary ->
            X12 = [leq,eq,lt]                                                      
        ;
            X12 = [geq,eq,gt]                                                      
        ),
        gen_table_ctr_wrt_forbidden_cmp(X55, X9, X12, 0, X33),
        X39 = 0,                                                                        
        (is_list(X30) ->                                                              
            member(X38, X30),                                                   
            ((compound(X38),                                                           
              functor(X38, X53, 2),                                                  
              memberchk(X53, [prod]),                                                      
              arg(1, X38, X31),                                                 
              arg(2, X38, X32),                                                 
              integer(X31), integer(X32), X31 =< X32) ->         
                X52 in X31..X32,                                           
                X52 #> 1,
                get_set_of_unaryf_values_for_each_pair_of_mandatory_attributes(X9, 0, X40, prod,
                                                                               X18, X31, X32,
                                                                               [_|X13]),
                                                                                             
                                                                                             
                X13 = [_|_],
                table([[X34,X35,X52]],X13),                        
                X57 = element(X14, X11, X41),                       
                X58 = element(X15, X11, X42),                       
                (X40 = attr_leq_unary ->
                    X59 = (X20      #<=> (X41 #=< X42 * X29)),
                    
                    X19 = attr_leq_unary(prod)
                ;
                    X59 = (X20      #<=> (X41 * X29 #=< X42)),
                    
                    X19 = unary_leq_attr(prod)
                ),
                append([X20,X41,X42], X11, X3),
                X28 = [X57,X58,X59],
                X7 = 0,
                X1 = [X14, X15, X29],
                X2 = [   X34,    X35,    X52],
                X10    = []
            ;
                write(formula_generator_condition4), nl, halt
            )
        ;
            write(formula_generator_condition5), nl, halt
        )
    ;

    
    
    
     (memberchk(X40,[unary_term_eq_coef,unary_term_leq_coef]), X37 = 2) ->        
        arg(1, X56, X30),                                                            
        ((arg(2, X56, coef(X21,X22)),                                       
          integer(X21), integer(X22), X21 =< X22) ->         
            X39 in X21..X22                                             
        ;
            write(formula_generator_condition6), nl, halt
        ),
        X33      = [X34],                                                        
        X6 = [X39,X52],                                                 
        X34 in 1..X55,                                                                
        X35 = 0,                                                                       
        X36 = 0,                                                                       
        (is_list(X30) ->                                                              
            member(X38, X30),                                                   
            ((compound(X38),                                                           
              functor(X38, X53, 2),                                                  
              X53 = mod,                                                                   
              arg(1, X38, X31),                                                 
              arg(2, X38, X32),                                                 
              integer(X31), integer(X32), X31 =< X32) ->         
                X52 in X31..X32,                                           
                tab_get_mins_attr_names(X9, X43),                            
                tab_get_maxs_attr_names(X9, X44),                            
                element(X34, X43, X45),                                      
                element(X34, X44, X46),                                      
                X52 #> 1,
                X52 #=< X46 - X45,                                             
                get_set_of_unary_term_values_for_each_mandatory_attribute(X9, 0,
                                                                          allequal, 0,
                                                                          X40, X38,
                                                                          X18,
                                                                          X31, X32,
                                                                          X21, X22,
                                                                          [_|X8]),
                                                                                             
                                                                                             
                table([[X34,X52,X39]],X8),                        
                X57 = element(X14, X11, X41),                       
                (X40 = unary_term_eq_coef ->
                    X58 = (X20 #<=> ((X41 mod X29) #=  X23)),
                    append([X20,X41], X11, X3),
                    X28 = [X57,X58],
                    X19 = unary_term_eq_coef(mod)
                ;
                    X58 = (X20      #<=> ((X41 mod X29) #=< X23)),
                    
                    append([X20,X41], X11, X3),
                    X28 = [X57,X58],
                    X19 = unary_term_leq_coef(mod)
                ),
                X7 = 0,
                X1 = [X14,X29,X23],
                X2 = [X34,X52,X39],
                X10    = [X52]
            ;
                write(formula_generator_condition7), nl, halt
            )
        ;
            write(formula_generator_condition8), nl, halt
        )
    ;

    
    
    
     (memberchk(X40,[binary_term_eq_coef,binary_term_leq_coef]), X37 = 2) ->      
        arg(1, X56, X26),                                                           
        ((arg(2, X56, coef(X21,X22)),                                       
          integer(X21), integer(X22), X21 =< X22) ->         
            X39 in X21..X22                                             
        ;
            write(formula_generator_condition9), nl, halt
        ),         
        X33      = [X34,X35],                                              
        X36      = 0,                                                                  
        X6 = [X39],                                                         
        domain(X33, 1, X55),                                                          
        X52 = 0,                                                                         
        (is_list(X26) ->                                                             
            member(X54, X26),                                                      
            ((all_options(binary, X4),                                          
              memberchk(X54, X4)) ->                                          
                (memberchk(X54, [plus,abs,min,max,prod]) ->                                
                    X34 #<  X35                                                  
                ;                                                                            
                    X34 #\= X35                                                  
                ),
                (memberchk(X54, [floor,mfloor,ceil,mod,dmod,fmod]) ->                      
                    forbid_cols_which_can_be_leq0(X55, X9, 0, X35)
                ;
                 X54 = cmod ->                                                             
                    forbid_cols_which_can_be_leq0(X55, X9, 0, X34)
                ;
                    true                                                                     
                ),
                X57 = element(X14, X11, X41),
                X58 = element(X15, X11, X42),
                (X54 = plus ->
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, plus,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                             
                                                                                             
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> (X41+X42 #= X23)),
                        X19 = binary_term_eq_coef(plus)
                    ;
                        X59 = (X20      #<=> (X41+X42 #=< X23)),
                        
                        X19 = binary_term_leq_coef(plus)
                    )
                ;
                 X54 = minus ->
                    gen_table_ctr_wrt_authorised_cmp(X55, 2, X9, [geq,gt], 0, X33), 
                    X39 #> 0,                                                                 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, minus,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            



                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> (X41-X42 #= X23)),
                        X19 = binary_term_eq_coef(minus)
                    ;
                        X59 = (X20      #<=> (X41-X42 #=< X23)),
                        
                        X19 = binary_term_leq_coef(minus)
                    )
                ;
                 X54 = abs ->
                    X39 #> 0,                                                                          
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt,eq,geq,gt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, abs,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> (abs(X41-X42) #= X23)),
                        X19 = binary_term_eq_coef(minus)
                    ;
                        X59 = (X20      #<=> (abs(X41-X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(abs)
                    )
                ;
                 X54 = min ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X34, X43, X45),
                    element(X35, X43, X47),
                    element(X34, X44, X46),
                    element(X35, X44, X48),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt,eq,geq,gt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, min,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X39 #>= max(X45,X47),
                        X39 #=< min(X46,X48),
                        X59 = (X20 #<=> (min(X41,X42) #=  X23)),
                        X19 = binary_term_eq_coef(min)
                    ;
                        X39 #>  max(X45,X47),
                        X39 #<  min(X46,X48),
                        X59 = (X20      #<=> (min(X41,X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(min)
                    )
                ;
                 X54 = max ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X34, X43, X45),
                    element(X35, X43, X47),
                    element(X34, X44, X46),
                    element(X35, X44, X48),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt,eq,geq,gt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, max,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X39 #>= max(X45,X47),
                        X39 #=< min(X46,X48),
                        X59 = (X20 #<=> (max(X41,X42) #=  X23)),
                        X19 = binary_term_eq_coef(max)
                    ;
                        X39 #>  max(X45,X47),
                        X39 #<  min(X46,X48),
                        X59 = (X20      #<=> (max(X41,X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(max)
                    )
                ;
                 X54 = floor ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X35, X43, X47),
                    element(X35, X44, X48),
                    (X47 #> 0 #\/ X48 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, floor,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 div X42) #=  X23)),
                        X19 = binary_term_eq_coef(floor)
                    ;
                        X59 = (X20      #<=> ((X41 div X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(floor)
                    )
                ;
                 X54 = mfloor ->
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                                                                                                  
                    tab_get_mins_attr_names(X9, X43), 
                    element(X35, X43, X47),
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, mfloor,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 div max(X42-X27,1)) #=  X23)),
                        X19 = binary_term_eq_coef(mfloor,X47)
                    ;
                        X59 = (X20      #<=> ((X41 div max(X42-X27,1)) #=< X23)),
                        
                        X19 = binary_term_leq_coef(mfloor,X47)
                    )
                ;
                 X54 = mod ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X35, X43, X47),
                    element(X35, X44, X48),
                    (X47 #> 0 #\/ X48 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, mod,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 mod X42) #=  X23)),
                        X19 = binary_term_eq_coef(mod)
                    ;
                        X59 = (X20      #<=> ((X41 mod X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(mod)
                    )
                ;
                 X54 = prod ->
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, prod,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 * X42) #=  X23)),
                        X19 = binary_term_eq_coef(prod)
                    ;
                        X59 = (X20      #<=> ((X41 * X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(prod)
                    )
                ;
                 X54 = ceil ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X35, X43, X47),
                    element(X35, X44, X48),
                    (X47 #> 0 #\/ X48 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, ceil,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> (((X41+X42-1) div X42) #=  X23)),
                        X19 = binary_term_eq_coef(ceil)
                    ;
                        X59 = (X20      #<=> (((X41+X42-1) div X42) #=< X23)),
                        
                        X19 = binary_term_leq_coef(ceil)
                    )
                ;
                 X54 = cmod ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X34, X43, X45),
                    element(X34, X44, X46),
                    (X45 #> 0 #\/ X46 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [geq,gt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, cmod,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 - (X42 mod X41)) #=  X23)),
                        X19 = binary_term_eq_coef(cmod)
                    ;
                        X59 = (X20      #<=> ((X41 - (X42 mod X41)) #=< X23)),
                        
                        X19 = binary_term_leq_coef(cmod)
                    )
                ;
                 X54 = dmod ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X35, X43, X47),
                    element(X35, X44, X48),
                    (X47 #> 0 #\/ X48 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, dmod,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 - (X41 mod X42)) #=  X23)),
                        X19 = binary_term_eq_coef(dmod)
                    ;
                        X59 = (X20      #<=> ((X41 - (X41 mod X42)) #=< X23)),
                        
                        X19 = binary_term_leq_coef(dmod)
                    )
                ;
                 X54 = fmod ->
                    tab_get_mins_attr_names(X9, X43), 
                    tab_get_maxs_attr_names(X9, X44), 
                    element(X35, X43, X47),
                    element(X35, X44, X48),
                    (X47 #> 0 #\/ X48 #< 0),
                    gen_table_ctr_wrt_forbidden_cmp(X55, X9, [leq,lt], 0, X33), 
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X9, 0,
                                                                                        allequal, 0,
                                                                                        X40, fmod,
                                                                                        X18,
                                                                                        X21, X22,
                                                                                        [_|X5]),
                                                                                            
                                                                                            
                    X5 = [_|_],
                    table([[X34,X35,X39]],X5),
                    (X40 = binary_term_eq_coef ->
                        X59 = (X20 #<=> ((X41 mod X42 #= 0)*X42 +
                                                  (X41 mod X42 #> 0)*(X41 mod X42) #=  X23)),
                        X19 = binary_term_eq_coef(fmod)
                    ;
                        X59 = (X20      #<=> ((X41 mod X42 #= 0)*X42 +
                                                       (X41 mod X42 #> 0)*(X41 mod X42) #=< X23)),
                        
                        
                        X19 = binary_term_leq_coef(fmod)
                    )
                ;
                    true
                ),
                (X54 = mfloor ->
                    X1 = [X14,X15,X23,X27],
                    X2 = [X34,X35,X39,X47]
                ;
                    X1 = [X14,X15,X23],
                    X2 = [X34,X35,X39]
                ),
                (X40 = binary_term_eq_coef ->
                    append([X20,X41,X42], X11, X3),
                    X28 = [X57,X58,X59]
                ;
                    append([X20,X41,X42], X11, X3),
                    X28 = [X57,X58,X59]
                ),
                X10 = [],
                X7 = 0
            ;
                write(formula_generator_condition10), nl, halt
            )
        ;
            write(formula_generator_condition11), nl, halt
        )
    ;

    
    
     (X40 = linear_eq_coef,                                                             
      functor(X56, linear_eq_coef, 2),
      arg(1, X56, cst(X31,X32)),
      arg(2, X56, coef(X21,X22)),
      integer(X31),                                                                   
      integer(X32),
      integer(X21),                                                                  
      integer(X22),
      X31  =< X32,
      X21 =< X22) ->
        X52  in X31..X32,                                                  
        X39 in X21..X22,                                                
        X52 #\= 0,                                                                       
        X33 = [X34,X35,X36],                                         
        X6 = [X52,X39],                                                 
        domain(X33, 1, X55),                                                          
        X35 #< X36,                                                              
        all_distinct(X33),                                                             
        X57 = element(X14, X11, X41),
        X58 = element(X15, X11, X42),
        X59 = element(X16, X11, X49),
        X61 = (X20 #<=> (X29*X41+X42+X49) #= X23),
        X1 = [X14,X15,X16,X29,X23],
        X2 = [   X34,   X35,   X36,   X52,   X39],
        append([X20,    X41,   X42,    X49], X11, X3),
        X28     = [X57,X58,X59,X61],
        X19    = linear_eq_coef,
        X10  = [X52,X39],
        X7 = 0
    ;

    
    
    
     (memberchk(X40,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]),
      X37 = 0                                  ) ->
        X33      = [X34,X35,X36],                                    
        X6 = [],                                                                 
        domain(X33, 1, X55),                                                          
        X39 = 0,                                                                        
        X52  = 0,                                                                        
        
        (X40 = ceil_leq_floor ->
             gen_table_ctr_wrt_authorised_cmp(X55, 3,                                       
                                              X9,                                 
                                              [geq,gt],                                      
                                              1,                                             
                                              X33)                                     
        ;
             gen_table_ctr_wrt_authorised_cmp(X55, 3,                                       
                                              X9,                                 
                                              [leq,lt],                                      
                                              1,                                             
                                              X33)                                     
        ),
        get_set_of_ternary_triplets_of_mandatory_attributes(X9, 0, X40, X18, X17),
        table([X33],X17),
        X57 = element(X14, X11, X41),
        X58 = element(X15, X11, X42),
        X59 = element(X16, X11, X49),
        (X40 = sum_leq_attr ->
            X61 = (X20 #<=> (X41+X42) #=< X49)
        ;
         X40 = minus_mod_eq0 ->
            tab_get_mins_attr_names(X9, X43), 
            tab_get_maxs_attr_names(X9, X44), 
            element(X35, [0|X43], X47),
            element(X35, [0|X44], X48),
            (X47 #=< 0 #/\ X48 #>= 0),
            X61 = (X20 #<=> ((X49-X41) mod X42 #= 0))
        ;
            tab_get_mins_attr_names(X9, X43), 
            tab_get_maxs_attr_names(X9, X44), 
            element(X35, [0|X43], X47),
            element(X35, [0|X44], X48),
            (X47 #=< 0 #/\ X48 #>= 0),
            element(X36, [0|X43], X50),
            element(X36, [0|X44], X51),
            (X50 #=< 0 #/\ X51 #>= 0),
            X61 = (X20 #<=> (((X41 - X49 + X42 - 1) / X42) #=< ((X41 - X42)/ X49)))
        ),
        X1 = [X14,X15,X16],
        X2 = [   X34,   X35,   X36],
        append([X20,    X41,   X42,    X49], X11, X3),
        X28     = [X57,X58,X59,X61],
        X19    = X40,
        X10  = [],
        X7 = 0
    ;

        write(formula_generator_condition12), nl, halt
    ).

formula_generator_then_else(X45, X6, X46, X13, X25, X4, X7, X26, X27, 
                            X40, X30, X3, X1, X2, X20, X5) :-
    (compound(X46) -> true ;
     atom(X46)     -> true ; write(formula_generator_then_else1), nl, halt),        
    functor(X46, X31, X28),                                              
    length(X8, X45),                                                     

    
    
    ((X31 = coef, X28 = 2) ->                                             
        X25      = [],                                                         
        X4 = [X30],                                                 
        X26 = 0,                                                               
        X27 = 0,                                                               
        X40   = 0,                                                               
        ((X46 = coef(X14,X15),                                      
          integer(X14), integer(X15), X14 =< X15) -> 
            X30 in X14..X15,                                    
            X47 = (X41 #= X16),
            append([X41], X8, X3),
            X1 = [X16],
            X2 = [X30],
            X20 = [X47],
            X13 = X31,
            X7 = [X30],                                              
            X5 = 0
        ;
            write(formula_generator_then_else2), nl, halt
        )
    ;

    
    
     (X31 = attr, X28 = 0) ->                                             
        X25      = [X26],                                                
        X4 = [],                                                         
        X26 in 1..X45,                                                        
        X27 = 0,                                                               
        X40   = 0,                                                               
        X30  = 0,                                                               
        X47 = element(X9, X8, X32),                       
        append([X32], X8, X3),
        X1 = [X9],
        X2 = [X26],
        X20 = [X47],                                                         
        X13 = X31,
        X7 = [1],                                                         
        X5 = 0
    ;

    
    
     (X31 = unary_term, X28 = 1) ->                                       
        X25      = [X26],                                                
        X4 = [X40],                                                  
        X26 in 1..X45,                                                        
        X27 = 0,                                                               
        X30  = 0,                                                               
        arg(1, X46, X21),                                                    
        (is_list(X21) ->                                                      
            member(X29, X21),                                           
            ((compound(X29),                                                   
              functor(X29, X43, 2),                                          
              arg(1, X29, X22),                                         
              arg(2, X29, X23),                                         
              integer(X22), integer(X23), X22 =< X23) -> 
                X40 in X22..X23,                                   
                (memberchk(X43, [prod])                            -> X40 #> 1 ;
                 memberchk(X43, [plus,minus,floor,ceil,floor_min]) -> X40 #> 0 ;
                 memberchk(X43, [min,max]) ->
                    tab_get_mins_attr_names(X6,X33),
                    tab_get_maxs_attr_names(X6,X34),
                    element(X26, X33, X35),
                    element(X26, X34, X36),
                    X40 #< X36,                                             
                    X40 #> X35                                              
                ;
                    memberchk(X43, [mod]) ->
                    tab_get_mins_attr_names(X6,X33),
                    tab_get_maxs_attr_names(X6,X34),
                    element(X26, X33, X35),
                    element(X26, X34, X36),
                    X40 #>= 2,
                    X40 #=< (X36 - X35)                                
                ;
                    true
                ),
                (memberchk(X43, [min_min,max_min]) ->
                    tab_get_mins_attr_names(X6,X33),
                    tab_get_maxs_attr_names(X6,X34),
                    element(X26, X33, X35),
                    element(X26, X34, X36),
                    X40 #< X36 - X35,                                   
                    X40 #> 0                                                      
                ;
                    true),
                (memberchk(X43, [max_min,floor_min,min_min]) ->
                    tab_get_mins_attr_names(X6,X33),
                    element(X26, X33, X35),                          
                    X35 #> 0
                ;
                    true
                ),
                X47 = element(X9, X8, X32),               
                (X43 = plus      -> X48 = (X41 #= X32+X24)                          ;
                 X43 = minus     -> X48 = (X41 #= X32-X24)                          ;
                 X43 = prod      -> X48 = (X41 #= X32*X24)                          ;
                 X43 = min       -> X48 = (X41 #= min(X32,X24))                     ;
                 X43 = min_min   -> X48 = (X41 #= min(X32-X17,X24))         ;
                 X43 = max       -> X48 = (X41 #= max(X32,X24))                     ;
                 X43 = max_min   -> X48 = (X41 #= max(X32-X17,X24))         ;
                 X43 = floor     -> X48 = (X41 #= (X32 div X24))                    ;
                 X43 = floor_min -> X48 = (X41 #= ((X32 - X17) div X24))    ;
                 X43 = ceil      -> X48 = (X41 #= ((X32 + X24 - 1) div X24)) ;
                 X43 = mod       -> X48 = (X41 #= (X32 mod X24))                    ;
                    write(formula_generator_then_else3), nl, halt                    
                ),
                (memberchk(X43, [min,max]) ->
                    X49 = (X10 #= 0 #<=> X32 #< X24),
                    X50 = (X10 #= 1 #<=> X32 #= X24),          
                    X51 = (X10 #= 2 #<=> X32 #> X24),          
                    append([X41,X10,X32], X8, X3),
                    X20 = [X47,X48,X49,X50,X51],
                    X5 = 2                                               
                ;
                 memberchk(X43, [min_min,max_min]) ->
                    X49 = (X10 #= 0 #<=> X32-X17 #< X24),
                    X50 = (X10 #= 1 #<=> X32-X17 #= X24),
                    X51 = (X10 #= 2 #<=> X32-X17 #> X24),
                    append([X41,X10,X32], X8, X3),
                    X20 = [X47,X48,X49,X50,X51],
                    X5 = 2                                               
                ;
                    append([X41,X32], X8, X3),
                    X20 = [X47,X48],
                    X5 = 0
                ),
                (memberchk(X43, [max_min,min_min,floor_min]) ->
                    X1 = [X9,X24,X17],
                    X2 = [X26,X40,X35],
                    X13 = unary_term(X43,X35)
                ;
                    X1 = [X9,X24],
                    X2 = [X26,X40],
                    X13 = unary_term(X43)
                ),
                X7 = [X40]                                            
            ;
                write(formula_generator_then_else4), nl, halt
            )
        ;
            write(formula_generator_then_else5), nl, halt
        )
    ;

    
    
     (X31 = binary_term, X28 = 1) ->                                      
        X25 = [X26,X27],                                           
        domain(X25, 1, X45),                                                  
        arg(1, X46,  X18),                                                  
        (is_list(X18) ->                                                     
            member(X44, X18),                                              
            (memberchk(X44, [plus,minus,abs,min,max,prod,floor,mfloor,ceil,mod,cmod,dmod,fmod]) ->
                X40  = 0,                                                        
                X30 = 0,                                                        
                X4 = []                                                  
            ;
             (functor(X44, X42, 2),                                             
              memberchk(X42, [linear,plus_min,plus_floor]),                       
              arg(1, X44, X22),                                             
              arg(2, X44, X23),                                             
              integer(X22), integer(X23), X22 =< X23) -> 
                X40 in X22..X23,
                X30 = 0,                                                        
                X4 = [X40],                                          
                (X44 = linear(_,_) ->
                    X40 #\= -1, X40 #\= 0, X40 #\= 1                     
                ;
                 X44 = plus_min(_,_) ->
                    tab_get_mins_attr_names(X6,X33),
                    tab_get_maxs_attr_names(X6,X34),
                    element(X27, X33, X37),                          
                    element(X27, X34, X38),                          
                    X40 #> 0,                                                    
                    X40 #> X37,                                             
                    X40 #< X38                                              
                ;
                 X44 = plus_floor(_,_) ->                                          
                    X40 #\= -1, X40 #\= 0,
                    tab_get_mins_attr_names(X6, X33), 
                    tab_get_maxs_attr_names(X6, X34), 
                    element(X27, X33, X37),
                    element(X27, X34, X38),
                    (X37 #> 0 #\/ X38 #< 0)
                ;
                 memberchk(X44, [floor, ceil, mod, dmod, fmod]) ->
                    tab_get_mins_attr_names(X6, X33), 
                    tab_get_maxs_attr_names(X6, X34), 
                    element(X27, X33, X37),
                    element(X27, X34, X38),
                    (X37 #> 0 #\/ X38 #< 0)
                ;
                 X44 = cmod ->
                    tab_get_mins_attr_names(X6, X33), 
                    tab_get_maxs_attr_names(X6, X34), 
                    element(X26, X33, X35),
                    element(X26, X34, X36),
                    (X35 #> 0 #\/ X36 #< 0)
                ;
                    true
                )
            ;
             (functor(X44, X42, 4),                                             
              X42 = minus_floor,
              arg(1, X44, X22),                                             
              arg(2, X44, X23),                                             
              arg(3, X44, X14),                                            
              arg(4, X44, X15),                                            
              integer(X22),
              integer(X23),
              X22 =< X23,                                              
              integer(X14),
              integer(X15),
              X14 =< X15) ->                                         
                X11 is max(X14,2),
                X40  in   X22..X23,                                
                X30 in X11..X15,                               
                X4 = [X30,X40]                                  
            ;
                write(formula_generator_then_else6), nl, halt
            ),
            (memberchk(X44, [plus,abs,min,max,prod]) ->                            
                X26 #<  X27                                              
            ;                                                                        
                X26 #\= X27                                              
            ),
            (memberchk(X44, [floor,mfloor,ceil,mod,dmod,fmod]) ->                  
                forbid_cols_which_can_be_leq0(X45, X6, 0, X27)
            ;
            X44 = cmod ->                                                          
                forbid_cols_which_can_be_leq0(X45, X6, 0, X26)
            ;
                true                                                                 
            ),
            (memberchk(X44, [abs,min,max]) ->                                      
                gen_table_ctr_wrt_forbidden_cmp(X45, X6, [leq,lt,eq,geq,gt], 0, X25)
            ;
             memberchk(X44, [floor,mfloor,ceil, 
                               minus_floor,mod,dmod,fmod]) ->                        
                gen_table_ctr_wrt_forbidden_cmp(X45, X6, [leq,lt], 0, X25)
            ;
             X44 = cmod ->                                                         
                gen_table_ctr_wrt_forbidden_cmp(X45, X6, [geq,gt], 0, X25)
            ;
             X44 = minus ->                                                        
                gen_table_ctr_wrt_forbidden_cmp(X45, X6, [gt], 0, X25)
            ;
                true
            ),
            X47 = element(X9, X8, X32),                   
            X48 = element(X12, X8, X39),                   
            (X44 = plus                 -> X49 = (X41 #= X32+X39)                                      ;
             X44 = minus                -> X49 = (X41 #= X32-X39)                                      ;
             X44 = linear(_,_)          -> X49 = (X41 #= (X32+X24*X39))                         ;
             X44 = abs                  -> X49 = (X41 #= abs(X32-X39))                                 ;
             X44 = min                  -> X49 = (X41 #= min(X32,X39))                                 ;
             X44 = max                  -> X49 = (X41 #= max(X32,X39))                                 ;
             X44 = plus_min(_,_)        -> X49 = (X41 #= min(X32+X39-X24,X32))             ;
             X44 = prod                 -> X49 = (X41 #= (X32 * X39))                                  ;
             X44 = floor                -> X49 = (X41 #= (X32 div X39))                                ;
             X44 = mfloor               -> tab_get_mins_attr_names(X6,X33),
                                             element(X27, X33, X37),         
                                             X49 = (X41 #= (X32 div max(X39-X19,1)))             ;
             X44 = ceil                 -> X49 = (X41 #= ((X32+X39-1) div X39))                   ;
             X44 = plus_floor(_,_)      -> X49 = (X41 #= ((X32+X39+X24) div X32))          ;
             X44 = minus_floor(_,_,_,_) -> X49 = (X41 #= ((X32-X39+X24) div X16))       ; 
             X44 = mod                  -> X49 = (X41 #= (X32 mod X39))                                ;
             X44 = cmod                 -> X49 = (X41 #= (X32 - (X39 mod X32)))                   ;
             X44 = dmod                 -> X49 = (X41 #= (X32 - (X32 mod X39)))                   ;
             X44 = fmod                 -> X49 = (X41 #= ((X32 mod X39 #= 0)*X39 +
                                                                (X32 mod X39 #> 0)*(X32 mod X39))) ;
                                             true
            ),
            append([X41,X32,X39], X8, X3),      
            (X44 = mfloor ->
                X1 = [X9,X12,X19],
                X2 = [X26,X27,X37],
                X13      = binary_term(X44,X37),
                X7    = [1]                                               
            ;
             memberchk(X44,[linear(_,_),plus_min(_,_),plus_floor(_,_)]) ->
                X1 = [X9,X12,X24],
                X2 = [X26,X27,X40],
                X7    = [X40],                                        
                (X44 = linear(_,_)     -> X13 = binary_term(linear)     ;
                 X44 = plus_min(_,_)   -> X13 = binary_term(plus_min)   ;
                                            X13 = binary_term(plus_floor) )
            ;
             X44 = minus_floor(_,_,_,_) ->                                         
                X1 = [X9,X12,X24,X16],
                X2 = [   X26,   X27,   X40,   X30],  
                X7    = [X40, X30],                              
                X13 = binary_term(minus_floor)
            ;
                X1 = [X9,X12],
                X2 = [X26,X27],
                X13      = binary_term(X44),
                (memberchk(X44, [cmod,dmod,fmod]) ->
                    X7 = [2]                                              
                ;
                    X7 = [1]                                              
                )
            ),
            X20 = [X47,X48,X49],                                           
            X5 = 0
        ;
            write(formula_generator_then_else7), nl, halt
        )
    ;
        write(formula_generator_then_else8(X46)), nl, halt
    ).

avoid_same_func_in_cond_and_then(X1, X3, X4, X2, X5, X6) :-
    functor(X1, X7, _),
    functor(X2, X8, _),
    ((X7 = unary_term_eq_coef, X8 = unary_term) ->
        arg(1, X1, X9),
        arg(1, X2, X10),
        (X9 = X10 ->
            X3 #\= X5
        ;
            true
        )
    ;
     (X7 = binary_term_eq_coef, X8 = binary_term) ->
        arg(1, X1, X9),
        arg(1, X2, X10),
        (X9 = X10 ->
            X3 #\= X5 #\/ X4 #\= X6
        ;
            true
        )
        
    ;
        true
    ).

avoid_same_condattr_in_then(X1, X2, X3, X4, X7) :-
    (X2 = attr_eq_attr -> 
        X3 = [_,X8],
        (foreach(X9,X4), param(X8) do X8 #\= X9)
    ;
     X2 = attr_eq_coef -> 
        X3 = [X8],
        (foreach(X9,X4), param(X8) do X8 #\= X9)
    ;
     X2 = binary_term_eq_coef(plus) -> 
        X3 = [X5, X6],
        tab_get_mins_attr_names(X1,X10),
        tab_get_maxs_attr_names(X1,X11),
        element(X5, X10, X12),
        element(X6, X10, X13),
        element(X5, X11, X14),
        element(X6, X11, X15),
        (foreach(X9,X4), param(X5), param(X6),
         param(X12), param(X13), param(X14), param(X15), param(X7) do
                (X7 #= (X12 + X13)) #=> ((X5 #\= X9) #/\ (X6 #\= X9)),
                (X7 #= (X14 + X15)) #=> ((X5 #\= X9) #/\ (X6 #\= X9))
        )
    ;
     X2 = binary_term_eq_coef(prod) -> 
        X3 = [X5, X6],
        tab_get_mins_attr_names(X1,X10),
        tab_get_maxs_attr_names(X1,X11),
        element(X5, X10, X12),
        element(X6, X10, X13),
        element(X5, X11, X14),
        element(X6, X11, X15),
        (foreach(X9,X4), param(X5), param(X6),
         param(X12), param(X13), param(X14), param(X15), param(X7) do
                (X7 #= (X12 * X13)) #=> ((X5 #\= X9) #/\ (X6 #\= X9)),
                (X7 #= (X14 * X15)) #=> ((X5 #\= X9) #/\ (X6 #\= X9))
        )
    ;
        true
    ).

avoid_same_condattr_in_else(X1, X2, X3, X4, X5) :-
    (X2 = attr_leq_coef -> 
        X3 = [X6],
        tab_get_maxs_attr_names(X1, X7),                           
        element(X6, X7, X8),                                      
        (foreach(X9,X4), param(X6), param(X8), param(X5) do
                (X8 #= X5 + 1) #=> X6 #\= X9
        )
    ;
     X2 = attr_geq_coef -> 
        X3 = [X6],
        tab_get_mins_attr_names(X1, X10),                           
        element(X6, X10, X11),                                      
        (foreach(X9,X4), param(X6), param(X11), param(X5) do
                (X11 #= X5 - 1) #=> X6 #\= X9
        )
    ;
        true
    ).

avoid_simplifiable_conditional(_,
                               X2, X3, X4,
                               X6,  _,   X7,
                               X9,    X10,   _) :-
    ((X2 = binary_term_eq_coef(mod),
      X3 = coef,
      X4 = binary_term(fmod)) ->
        X6 = [X11, X12],
        X7 = [X13, X14],
        ((X11 #= X13) #/\ (X12 #= X14)) #=> (X9 #\= X10)
    ;
        true).


forbid_cols_that_cant_intersect_min_max(X6, X1, X3, X4, X9) :-
    findall(X10,
            (X10 in 1..X6,
             indomain(X10),                            
             nth1(X10, X1, X2),          
             tab_get_min_max(X2, X7, X8), 
             (X8 < X3 -> true ;                
              X7 > X4 -> true ;
                               false)),
            X5),
    var_diff_from_values(X5, X9).                

forbid_cols_where_min_gt_up_or_max_leq_low(X4, X1, X7, X9, X8) :-
    findall(X10,
            (X10 in 1..X4,
             indomain(X10),                            
             nth1(X10, X1, X2),          
             tab_get_min_max(X2, X5, X6), 
             (X5  > X9  -> true ;                  
              X6 =< X7 -> true ;
                             false)),
            X3),
    var_diff_from_values(X3, X8).                

no_unique_value_for_res_then_or_res_else(X2, X1, X3) :-
        X4 is 1-X3,
        automaton(X1, X5, X2,
                  [source(r), sink(t)],
                  [arc(r, X4, r, [X6]),
                   arc(r, X3, s, [X5]),
                   arc(s, X4, s, [X6]),
                   arc(s, X3, s, (X5 #=  X6 -> [X6])),
                   arc(s, X3, t, (X5 #\= X6 -> [X6])),
                   arc(t, X4, t, [X6]),
                   arc(t, X3, t, [X6])],
                   [X6], [0], [_]).

gen_then_else_min_max_ctr([], _, _, 0) :- !.
gen_then_else_min_max_ctr([X1-X2|X5], X3, X4, (X1 #= X3 #/\ X2 #= X4) #\/ X6) :-
    gen_then_else_min_max_ctr(X5, X3, X4, X6).
