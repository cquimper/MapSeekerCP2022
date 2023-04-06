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
% Purpose: UTILITIES USED TO GENERATE A PARAMETERISED BOOLEAN CANDIDATE FORMULA WRT SOME GIVEN OPTIONS,
%          AND ON BACTRACKING ON THE MAIN OPERATOR OF THE FORMULA PRODUCE THE NEXT CANDIDATE FORMULA
% Authors: Nicolas Beldiceanu, Ramiz Gindullin, IMT Atlantique

:- module(gen_bool_formula,[formula_generator_bool_conds/5,            
                            pos_bool_cond_entry/2,                     
                            get_bool_cost_vars/2,                      
                            get_entries_of_all_boolean_conditions/3,
                            avoid_simplifiable_conditional/9]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).
:- use_module(table_access).
:- use_module(bool_cond_utility).

all_bool_options(binary, [plus,minus,abs,min,max,                      
                          prod,floor,mfloor,ceil,mod,
                          cmod,dmod,fmod]).

all_mod_conds([minus_mod_eq0,                                          
               unary_term_eq_coef(mod),
               unary_term_geq_coef(mod),
               unary_term_leq_coef(mod),
               binary_term_eq_coef(mod),
               binary_term_eq_coef(cmod),
               binary_term_eq_coef(dmod),
               binary_term_eq_coef(fmod),
               binary_term_leq_coef(mod),
               binary_term_leq_coef(cmod),
               binary_term_leq_coef(dmod),
               binary_term_leq_coef(fmod),
               binary_term_geq_coef(mod),
               binary_term_geq_coef(cmod),
               binary_term_geq_coef(dmod),
               binary_term_geq_coef(fmod)]).

pos_bool_cond_entry(condb,          1) :- !.
pos_bool_cond_entry(newcondtype,    2) :- !.
pos_bool_cond_entry(lcondattr,      3) :- !.
pos_bool_cond_entry(lcondextravars, 4) :- !.
pos_bool_cond_entry(condcostvars  , 5) :- !.
pos_bool_cond_entry(lcondcst,       9) :- !.
pos_bool_cond_entry(lcondcoef,      10):- !.

formula_generator_bool_conds(X16, X15, X19, t(X31,X26,X20,X2), X21) :-
    (memberchk(mandatory_attr(X10), X16) -> true ; write(formula_generator_bool_conds1), nl, halt),
    (memberchk(neg(X32),                  X16) -> true ; write(formula_generator_bool_conds2), nl, halt),
    (memberchk(op(X38),                    X16) -> true ; write(formula_generator_bool_conds3), nl, halt),
    (memberchk(nb_terms(X33,X34),     X16) -> true ; write(formula_generator_bool_conds4), nl, halt),
    (memberchk(conds(X39),                 X16) -> true ; write(formula_generator_bool_conds5), nl, halt),
    (foreach(X44,X38)
        do (memberchk(X44,[and,or,sum,allequal,xor,voting,card1]) -> true ; write(formula_generator_bool_conds6(X44)), nl, halt)
    ),                                                
    (memberchk(use_mods(X35),             X16) -> true ; write(formula_generator_bool_conds6a), nl, halt),
    pos_bool_cond_entry(condb,       X27),
    pos_bool_cond_entry(newcondtype, X8),
    pos_bool_cond_entry(lcondattr,   X12),
    ((integer(X33), integer(X34), X33 > 0, X33 =< X34) -> true ; write(formula_generator_bool_conds7), nl, halt),
    X36 in X33..X34,
    indomain(X36),                                
    length(X10, X37),                   
    gen_compatible_unary_and_binary_and_ternary(      
                                    X36, X37, 
                                    X1),
    (X1 = [] -> false ; true),  
    member(X42, X38),                            

    
    
    
    tab_get_mins_attr_names(X10, X28), 
    tab_get_maxs_attr_names(X10, X29), 
    get_shifted_bool_attributes(X28, X29, 2, X4),
    (length(X4, X37) ->             
        (X36 = 1 -> X32 = 0 ; true),          
        X30 = 1,
        X3 is min(X36,X37),
        X17 = [t(cond(attr_eq_coef(coef(0,1))), no_negation,    X3),
                      t(cond(attr_eq_attr),            no_restriction, X3)],
        duplicate_bool_conds(X17, X36, X22)
    ;                                                 
        X30 = 0,
        duplicate_bool_conds(X39, X36, X22)
    ),

    X21 = [                                     
                 mandatory_attr(X10),       
                 neg(X32),                        
                 shift(X19),                    
                 op(X42),                           
                 nb_terms(X36),                   
                 conds(X43),                        
                 combined_row_ctrs(X7,   
                                   X5,  
                                   X6,
                                   X18)],

                                                      
                                                      
    formula_generator_bool_conds1(X22, X42, X32, X36, X10, X30, X35, X28, X29, X4,
                                  X15, X40, X43, X41, X23, X13),
    restrict_nb_unary_nb_binary_nb_ternary(X43,     
                                           X1,
                                           X36, X37,
                                           t(X31,X26,X20,X2)),

    break_symmetry_between_duplicated_conds(X43,    
                                            X27, X8, X12),

    (X35 = 1 ->                                   
        all_mod_conds(X14),                  
        collect_condb_for_mods(X43, X14, X27, X8, X24),
        count(0, X24, #=, X9),      
        count(1, X24, #=, X11 ),      
        X11 + X9 #>= 1          
    ;
        true
    ),
    length(X43, X45),                                 
    X25 is X45 - X36,                         
    count(-1, X41, #=, X25),                 
                                                      
                                                      
    formula_generator_bool_extra_ctr(X42, X36, X40, X41, X23, X13,
                                     X7, X5, X6, X18).

collect_condb_for_mods([], _, _, _, []) :- !.         
collect_condb_for_mods([X5|X7], X2, X3, X1, [X4|X8]) :- 
    arg(X1, X5, X6),
    memberchk(X6, X2), !,
    arg(X3, X5, X4),
    collect_condb_for_mods(X7, X2, X3, X1, X8).
collect_condb_for_mods([_|X6], X2, X4, X1, X3) :-
    collect_condb_for_mods(X6, X2, X4, X1, X3).

duplicate_bool_conds([], _, []) :- !.
duplicate_bool_conds([t(cond(X5),X1,X3)|X6], X4, [t(cond(X5),X1,1)|X7]) :-
    (X3 = 1 ->                             
        duplicate_bool_conds(X6, X4, X7)        
    ;                                              
        X2 is min(X4,X3)-1,  
        (X2  = 0 ->
            duplicate_bool_conds(X6, X4, X7)
        ;
            duplicate_bool_conds([t(cond(X5),X1,X2)|X6], X4, X7)
        )
    ).

get_shifted_bool_attributes([], [], _, []) :- !.
get_shifted_bool_attributes([X6|X4], [X7|X5], X2, [X2|X3]) :-
    X6 = 0, 
    X7 = 1,
    !,
    X1 is X2+1,
    get_shifted_bool_attributes(X4, X5, X1, X3).
get_shifted_bool_attributes([_|X4], [_|X5], X2, X3) :-
    X1 is X2+1,
    get_shifted_bool_attributes(X4, X5, X1, X3).

get_bool_cost_vars(X2, X5) :-
    pos_bool_cond_entry(condcostvars, X1),
    memberchk(conds(X6), X2),
    get_bool_cost_vars(X6, X1, X3),
    flatten(X3, X4),
    memberchk(op(X7), X2),    
    (memberchk(X7,[card1,xor,voting]) ->  
        X5 = [2|X4]          
    ;
        X5 = X4
    ).

get_bool_cost_vars([], _, []) :- !.
get_bool_cost_vars([X3|X4], X1, [X2|X5]) :-
    arg(X1, X3, X2),
    get_bool_cost_vars(X4, X1, X5).

get_entries_of_all_boolean_conditions([], _, []) :- !.
get_entries_of_all_boolean_conditions([X3|X4], X1, [X2|X5]) :-
    arg(X1, X3, X2),
    get_entries_of_all_boolean_conditions(X4, X1, X5).

formula_generator_bool_conds1([], _, _, _, _, _, _, _, _, _, _, _, [], [], [], []) :- !.
formula_generator_bool_conds1([t(cond(X21),X2,1)|X22], X19, X14, X15, X3, X10, X16, X11, X12, X1,
                              X6, X17, X4, X18, X9, X5) :-
    (formula_generator_bool_cond1(X19, X14, X15, X3, X10, X16, X11, X12, X1,
                                  X6, X21, X2, X17, X7, X20, X13, X8) ->
        X4 = [X7|X23],
        X18       = [X20|X24],
        X9    = [X13|X25],
        X5 = [X8|X26]
    ;
        X4 = X23,
        X18       = X24,
        X9    = X25,
        X5 = X26
    ),
    formula_generator_bool_conds1(X22, X19, X14, X15, X3, X10, X16, X11, X12, X1, X6, X17, X23, X24, X25, X26).

formula_generator_bool_cond1(X75, X67, X68, X15, X50, X69, X51, X52, X4,
                             X25, X79, X7, X74, X26, X76, X53, X27) :-
    
    ((X68 = 1, X67 = 1)       -> X76 in -1..1, X76 #\= 0                                    ; 
     X7 = no_negation    -> X76 in -1..1, X76 #\= 0                                    ;
     X7 = no_restriction -> X76 in -1..1                                                 ;
                                         write(formula_generator_bool_cond1a(X7)), nl, halt),
    X26 = cond(X76,                            
                       X28,                      
                       X44,                        
                       X11,                   
                       X16,                    
                       X45, X46, X47,  
                       X70, X54,                
                       X8,                  
                       X5,                 
                       X6,                 
                       X37,                       
                       X12),                  
                                                         
                                                         
    
    (compound(X79) -> true ;
     atom(X79)     -> true ; write(formula_generator_bool_cond1b), nl, halt),               
    functor(X79, X55, X48),                                                      
    length(X15, X80),                                                             
    length(X17, X80),                                                             
    X77 is X80+1,
    append([0], X17, X13),                                              

    
    
    X56 is (X68-1)*3+1,                                                             
    X57 is X56+1,                                                                  
    (X56 < X80 -> X3   = 1 ;                                       
                        X3   = 0 ),                                      
    (X57 < X80 -> X2  = 1 ;                                       
     X80     < 2    -> X2  = 1 ;                                       
                        X2  = 0 ),                                      
    (X80     < 3    -> X1 = 1 ;                                       
                        X1 = 0 ),                                      

    
    
    
    ((memberchk(X55, [attr_eq_attr,attr_leq_attr]), X48 = 0, X80 = 1) ->
        false
    ;
     (memberchk(X55, [attr_eq_attr,attr_leq_attr]), X2 = 1) ->
        false
    ;
     (memberchk(X55, [attr_eq_attr,attr_leq_attr]), X48 = 0, X80 > 1) ->         
        X44      = [X45,X46],                                              
        X47      = 0,                                                                  
        X11 = [condb(X76)],                                                     
        domain(X44, 1, X77),                                                         
        X76 #= -1 #<=> X45 #= 1,                                                     
        X76 #= -1 #<=> X46 #= 1,                                                     
        X54 = 0,                                                                        
        X70  = 0,                                                                        

        
        
        
        X81 = element(X20, X13, X58),                              
        X82 = element(X21, X13, X59),                              
        (X55 = attr_eq_attr ->                                                          
            X45 #=< X46,
            X45 #= 1 #\/ X45 #< X46,                                       
            X18 = [eq,lt,gt,neq],                                                  
            X83 = (X27 #<=> (X58 #= X59)),                                
            (X50 = 1 ->                                                                 
                X84 in 0..2,
                X76 #= -1 #=> X84 #= 0,
                X76 #>= 0 #=> X84 #= 2-X76,
                X16 = [X84]
            ;                                                                                
                X16 = []
            )
        ;                                                                                    
            X45 #= 1 #\/ X45 #\= X46,                                      
            X18 = [leq,eq,lt,gt],                                                  
            X83 = (X27 #<=> (X58 #=< X59)),                               
            X84 in 0..1, X76 #= -1 #=> X84 #= 0, X76 #> -1 #=> X84 #= 1,              
            X16 = [X84]
        ),
        gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
        append([X81,X82,X83], X85, X37),                                          
        gen_table_ctr_wrt_forbidden_cmp(X80, X15, X18, 1, X44),   
        append([[X27,X58,X59], X17, [X74]], X8),
        X5 = [X53,X20,X21],
        X6 = [X76,X45,X46],
        X28      = X55,
        X12   = 0
    ;

    
    
    
    
     (memberchk(X55, [attr_eq_coef,attr_leq_coef,attr_geq_coef]), X3 = 1) ->
        false
    ;
     (memberchk(X55, [attr_eq_coef,attr_leq_coef,attr_geq_coef]), X48 = 1) ->     
        ((arg(1, X79, coef(X29,X30)),                                       
          integer(X29), integer(X30), X29 =< X30) ->         
            X54 in X29..X30                                             
        ;
            write(formula_generator_bool_cond1c), nl, halt
        ),
        (X55 = attr_eq_coef  -> X11 = [condb(X76),coef(eq, X54)] ;    
         X55 = attr_leq_coef -> X11 = [condb(X76),coef(leq,X54)] ;
                                     X11 = [condb(X76),coef(geq,X54)] ),
        X44      = [X45],                                                        
        X45 in 1..X77,                                                               
        X76 #= -1 #<=> X45 #= 1,                                                     
        X76 #= -1 #=> X54 #= X29,                                             
        X46 = 0,                                                                       
        X47 = 0,                                                                       
        X70   = 0,                                                                       
                                                                                             
                                                                                             
                                                                                             
        get_set_of_values_for_each_mandatory_attribute(X15, 1, X75, X67, X55, X25,
                                                       X29, X30, X14),
        X14 = [_,_|_],
        table([[X45,X54]], X14),                                       
                                                                                             
                                                                                             
        (X50 = 1 ->                                                                     
            X84 in 0..1,
            X76 #= -1 #=> X84 #= 0,
            X76 #> -1 #=> X84 #= 1 - X54,
            X16 = [X84]                                                           
        ;                                                                                    
            X71 is min(0,X29),                                                   
            X72 is max(0,X30)+1,
            X84 in X71..X72,
            X76 #= -1 #=> X84 #= 0,
            (X55 = attr_eq_coef -> X76 #> -1 #=> X84 #= X54 ; X76 #> -1 #=> X84 #= X54 + 1),
            X16 = [X84]
        ),
        X81 = element(X20, X13, X58),                              
        (X55 = attr_eq_coef ->                                                          
            X82 = (X27 #<=> (X58 #= X31))
        ;
         X55 = attr_leq_coef ->                                                         
            X82 = (X27 #<=> (X58 #=< X31))
        ;
            X82 = (X27 #<=> (X58 #>= X31))
        ),
        append([[X27,X58], X17, [X74]], X8),
        gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
        append([X81,X82], X85, X37),                                               
        X5 = [X53,X20,X31],
        X6 = [X76,X45,X54],
        X28      = X55,
        X12   = 0
    ;

    
    
    (X55 = attr_in_interval, X3 = 1) ->
        false
    ;
    (X55 = attr_in_interval, X48 = 2) ->                                          
        arg(1, X79, X32),                                                           
        arg(2, X79, X33),                                                           
        ((integer(X32),
          integer(X33),
          X32 < X33) ->
            X70  in X32..X33,                                            
            X54 in X32..X33,                                            
            X44      = [X45],                                                    
            X11 = [condb(X76),coef(geq,X70),coef(leq,X54)],            
            X45 in 1..X77,                                                           
            X46 = 0,                                                                   
            X47 = 0,                                                                   
            X76 #= -1 #<=> X45 #= 1,                                                 
            X76 #= -1 #=>  X70   #= X32,                                       
            X76 #= -1 #=>  X54  #= X32,                                       
            X76 #> -1 #<=> X70   #< X54,                                          
            get_set_of_values_for_each_mandatory_attribute(X15, 1, X75, X67, attr_leq_coef, X25,
                                                           X32, X33, X14),
            X14 = [_,_|_],
            table([[X45,X70]], X14),                                    
            table([[X45,X54]], X14),                                   
            element(X45, [X32|X51], X60),                            
            element(X45, [X32|X52], X61),                            
            X76 #> -1 #=> X70  #> X60,                                            
            X76 #> -1 #=> X54 #< X61,                                            
            X71 is min(0,X32),                                                   
            X72 is max(0,X33+2),                                                 
            X84 in X71..X72,                                                        
            X76 #= -1 #=> X84 #= 0,                                                       
            X76 #> -1 #=> X84 #= abs(X54) + 1 + (X76 #= 0),                        
                                                                                             
            X81 = element(X20, X13, X58),                          
            X82 = (X27 #<=> (X38 #=< X58 #/\ X58 #=< X31)),
            append([[X27,                                                            
                     X58], X17, [X74]], X8),
            gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
            append([X81,X82], X85, X37),                                           
            X5 = [X53,X20,X38,X31],               
            X6 = [X76,X45,X70,X54],                           
            X28      = X55,                                                     
            X16    = [X84],
            X12   = 0
        ;
            write(formula_generator_bool_cond1d), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X55,[attr_eq_unary,attr_leq_unary,unary_leq_attr]), X48 = 1, X80 = 1) ->
        false
    ;
    (memberchk(X55,[attr_eq_unary,attr_leq_unary,unary_leq_attr]), X2 = 1) ->
        false
    ;
    (memberchk(X55,[attr_eq_unary,                                                      
                        attr_leq_unary,unary_leq_attr]), X48 = 1, X80 > 1) ->         
        arg(1, X79, X39),                                                            
        X44      = [X45,X46],                                              
        X47      = 0,                                                                  
        X11 = [condb(X76),X70],                                             
        domain(X44, 1, X77),                                                         
        X76 #= -1 #<=> X45 #= 1,                                                     
        X76 #= -1 #<=> X46 #= 1,                                                     
        X76 #> -1 #<=> X45 #\= X46,                                            
        X54 = 0,                                                                        
        (memberchk(X55, [attr_eq_unary,attr_leq_unary]) ->
            X18 = [leq,eq,lt]                                                      
        ;
            X18 = [geq,eq,gt]                                                      
        ),
        gen_table_ctr_wrt_forbidden_cmp(X80, X15, X18, 1, X44),   
        (X39 = [X49]  ->                                                        
            ((compound(X49),                                                           
              functor(X49, X78, 2),                                                  
              memberchk(X78, [prod]),                                                      
              arg(1, X49, X40),                                                 
              arg(2, X49, X41),                                                 
              integer(X40), integer(X41), X40 =< X41) ->         
                X42 is max(2,X40),                                             
                X70 in X42..X41,                                           
                X76 #= -1 #=> X70 #= X42,                                       
                X76 #> -1 #=> X70 #\= 1,                                               
                X71 is min(0,X42),                                                
                X72 is max(0,X41+1),                                              
                X84 in X71..X72,                                                    
                X76 #= -1 #=> X84 #= 0,                                                   
                (X73 = attr_eq_unary ->
                    X76 #> -1 #=> X84 #= X70                                          
                ;
                    X76 #> -1 #=> X84 #= X70 + 1                                      
                ),
                X81 = element(X20, X13, X58),                      
                X82 = element(X21, X13, X59),                      
                get_set_of_unaryf_values_for_each_pair_of_mandatory_attributes(X15, 1, X55, prod, X25,
                                                                               X40, X41, X19),
                X19 = [_,_|_],
                table([[X45,X46,X70]], X19),                       
                (X55 = attr_leq_unary ->
                    X83 = (X27 #<=> (X58 #=< X59 * X38)),
                    X28 = attr_leq_unary(prod)
                ;
                 X55 = unary_leq_attr ->
                    X83 = (X27 #<=> (X58 * X38 #=< X59)),
                    X28 = unary_leq_attr(prod)
                ;
                 X73 = attr_eq_unary ->
                    X83 = (X27 #<=> (X58 #= X59 * X38)),
                    X28 = attr_eq_unary(prod)
                ;
                    write(formula_generator_bool_cond1e), nl, halt
                ),
                gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
                append([[X27,X58,X59], X17, [X74]], X8),
                append([X81,X82,X83], X85, X37),                                  
                X5 = [X53, X20, X21, X38],       
                X6 = [   X76,    X45,    X46,    X70],       
                X16    = [X84],
                X12   = 0
            ;
                write(formula_generator_bool_cond1f), nl, halt
            )
        ;
            write(formula_generator_bool_cond1g), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X55, [unary_term_eq_coef,unary_term_leq_coef,unary_term_geq_coef]), X3 = 1) ->
        false
    ;
    (memberchk(X55,[unary_term_eq_coef,unary_term_leq_coef,unary_term_geq_coef]),
     X48 = 2                                                                   ) ->    
        arg(1, X79, X39),                                                            
        ((arg(2, X79, coef(X29,X30)),                                       
          integer(X29), integer(X30), X29 =< X30) ->         
            X54 in X29..X30                                             
        ;
            write(formula_generator_bool_cond1h), nl, halt
        ),                                                                                   
        (X55 = unary_term_eq_coef  -> X11 = [condb(X76),coef(eq, X54),X70] ;
         X55 = unary_term_leq_coef -> X11 = [condb(X76),coef(leq,X54),X70] ;
                                           X11 = [condb(X76),coef(geq,X54),X70] ),
        X44      = [X45],                                                        
        X45 in 1..X77,                                                               
        X46 = 0,                                                                       
        X47 = 0,                                                                       
        X76 #= -1 #<=> X45 #= 1,                                                     
        (X39 = [X49] ->                                                         
            ((compound(X49),                                                           
              functor(X49, X78, 2),                                                  
              (X78 = mod ->                                                                
                true
              ;
                write(formula_generator_bool_cond1i), nl, halt
              ),
              X76 #= -1 #=> X54 #= X29,                                       
              arg(1, X49, X40),                                                 
              arg(2, X49, X41),                                                 
              integer(X40), integer(X41), X40 =< X41) ->         
                X70 in X40..X41,                                           
                X76 #= -1 #=> X70 #= X40,                                       
                X71 is min(0,X40),
                (X55 = unary_term_eq_coef ->                                            
                    X72 is max(0,X41+X30+1)
                ;
                    X72 is max(0,X41+X30+2)
                ),                                                                           
                X84 in X71..X72,                                                    
                X76 #= -1 #=> X84 #= 0,                                                   
                (X55 = unary_term_eq_coef ->
                    X76 #> -1 #=> X84 #= X70+X54+1                               
                ;
                    X76 #> -1 #=> X84 #= X70+X54+2                               
                ),
                element(X45, [X40|X51], X60),                         
                element(X45, [X40|X52], X61),                         
                X76 #> -1 #=> X70 #> 1,
                X76 #> -1 #=> X70 #=< (X61 - X60),                           
                                                                                             
                                                                                             
                                                                                             
                                                                                             
                                                                                             
                get_set_of_unary_term_values_for_each_mandatory_attribute(X15, 1, X75, X67, X55, mod, X25,    
                                                          X40, X41, X29, X30, X14),
                table([[X45,X70,X54]], X14),                       
                gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
                X81 = element(X20, X13, X58),                      
                (X55 = unary_term_eq_coef ->
                    X76 #> -1 #=> X54 #<  X70,
                    X82 = (X27 #<=> ((X58 mod X38) #=  X31)),
                    X28 = unary_term_eq_coef(mod)
                ;
                 X55 = unary_term_leq_coef ->
                    X76 #> -1 #=> X54 #<  X70 - 1,                                
                    X82 = (X27 #<=> ((X58 mod X38) #=< X31)),
                    X28 = unary_term_leq_coef(mod)
                ;
                    X76 #> -1 #=> X54 #<  X70 - 1,                                
                    X82 = (X27 #<=> ((X58 mod X38) #>= X31)),
                    X28 = unary_term_geq_coef(mod)
                ),
                X12 = 0,
                append([[X27,X58], X17, [X74]], X8),
                append([X81,X82], X85, X37),                                       
                X5 = [X53, X20, X38, X31],
                X6 = [   X76,    X45,    X70,    X54],
                X16    = [X84]
            ;
                write(formula_generator_bool_cond1j), nl, halt
            )
        ;
            write(formula_generator_bool_cond1k), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X55,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X48 = 2, X80 = 1) ->
        false
    ;
    (memberchk(X55,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X2 = 1) ->
        false
    ;                                                                                        
    (memberchk(X55,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X48 = 2, X80 > 1) ->
        arg(1, X79, X34),                                                           
        (X55 = binary_term_eq_coef  -> X11 = [condb(X76),coef(eq, X54)] ; 
         X55 = binary_term_leq_coef -> X11 = [condb(X76),coef(leq,X54)] ;
                                            X11 = [condb(X76),coef(geq,X54)] ),
        X44      = [X45, X46],                                             
        X45 in 1..X77,                                                               
        X46 in 1..X77,                                                               
        X47 = 0,                                                                       
        X70 = 0,
        X76 #= -1 #<=> X45 #= 1,                                                     
        X76 #= -1 #<=> X46 #= 1,                                                     
        ((arg(2, X79, coef(X29,X30)),                                       
          integer(X29), integer(X30), X29 =< X30) ->         
            X54 in X29..X30                                             
        ;
            write(formula_generator_bool_cond1l), nl, halt
        ),         
        (X34 = [X43] ->                                                       
            ((all_bool_options(binary, X9),                                     
              memberchk(X43, X9)) ->                                     
                (memberchk(X43, [plus,abs,min,max,prod]) ->                           
                    X76 #> -1 #=> X45 #<  X46                                  
                ;                                                                            
                    X76 #> -1 #=> X45 #\= X46                                  
                ),
                (memberchk(X43, [floor,mfloor,ceil,mod,dmod,fmod]) ->                 
                    forbid_cols_which_can_be_leq0(X80, X15, 1, X46)
                ;
                 X43 = cmod ->                                                        
                    forbid_cols_which_can_be_leq0(X80, X15, 1, X45)
                ;
                    true                                                                     
                ),
                X76 #= -1 #=> X54 #= X29,                                     
                X71 is min(0,X29),
                (X43 = plus   -> X35 = 0 ;
                 X43 = minus  -> X35 = 1 ;
                 X43 = abs    -> X35 = 5 ;
                 X43 = min    -> X35 = 5 ;
                 X43 = max    -> X35 = 5 ;
                 X43 = prod   -> X35 = 6 ;
                 X43 = floor  -> X35 = 7 ;
                 X43 = mfloor -> X35 = 8 ;
                 X43 = ceil   -> X35 = 7 ;
                 X43 = mod    -> X35 = 5 ;
                 X43 = cmod   -> X35 = 6 ;
                 X43 = dmod   -> X35 = 6 ;
                 X43 = fmod   -> X35 = 6 ;
                                        true            ),
                (X55 = binary_term_eq_coef ->                                           
                    X72 is max(0,X30+2+X35)
                ;
                    X72 is max(0,X30+3+X35)
                ),
                X84 in X71..X72,                                                    
                X76 #= -1 #=> X84 #= 0,                                                   
                (X55 = binary_term_eq_coef ->
                    X76 #> -1 #=> X84 #= abs(X54) + 2 + X35                  
                ;
                    X76 #> -1 #=> X84 #= abs(X54) + 3 + X35                  
                ),
                gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
                X81 = element(X20, X13, X58),
                X82 = element(X21, X13, X59),
                (X43 = plus ->
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            plus, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> (X58+X59 #= X31)),
                        X28 = binary_term_eq_coef(plus)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> (X58+X59 #=< X31)),
                        X28 = binary_term_leq_coef(plus)
                    ;
                        X83 = (X27 #<=> (X58+X59 #>= X31)),
                        X28 = binary_term_geq_coef(plus)
                    )
                ;
                 X43 = minus ->
                    X76 #> -1 #=> X54 #> 0,                                                  
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            minus, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->                                              
                        X83 = (X27 #<=> (X58-X59 #=  X31)),
                        X28 = binary_term_eq_coef(minus)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> (X58-X59 #=< X31)),
                        X28 = binary_term_leq_coef(minus)
                    ;
                        X83 = (X27 #<=> (X58-X59 #>= X31)),
                        X28 = binary_term_geq_coef(minus)
                    )
                ;
                 X43 = abs ->                                                                
                    X76 #> -1 #=> X54 #> 0,                                                  
                                                                                                    
                                                                                                    
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            abs, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt,eq,geq,gt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> (abs(X58-X59) #=  X31)),
                        X28 = binary_term_eq_coef(abs)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> (abs(X58-X59) #=< X31)),
                        X28 = binary_term_leq_coef(abs)
                    ;
                        X76 #> -1 #=> X54 #> 1,
                        X83 = (X27 #<=> (abs(X58-X59) #>= X31)),
                        X28 = binary_term_geq_coef(abs)
                    )
                ;
                 X43 = min ->                                                                 
                    element(X45, [0|X51], X60),
                    element(X46, [0|X51], X62),
                    element(X45, [0|X52], X61),
                    element(X46, [0|X52], X63),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt,eq,geq,gt], 1, X44),
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            min, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->
                        X76 #> -1 #=> X54 #>= max(X60,X62),                      
                        X76 #> -1 #=> X54 #=< min(X61,X63),                      
                        X83 = (X27 #<=> (min(X58,X59) #=  X31)),
                        X28 = binary_term_eq_coef(min)
                    ;
                     X55 = binary_term_leq_coef ->
                        X76 #> -1 #=> X54 #>  max(X60,X62),                      
                        X76 #> -1 #=> X54 #<  min(X61,X63),                      
                        X83 = (X27 #<=> (min(X58,X59) #=< X31)),
                        X28 = binary_term_leq_coef(min)
                    ;
                        X76 #> -1 #=> X54 #>  max(X60,X62),                      
                        X76 #> -1 #=> X54 #<  min(X61,X63),                      
                        X83 = (X27 #<=> (min(X58,X59) #>= X31)),
                        X28 = binary_term_geq_coef(min)
                    )
                ;
                 X43 = max ->                                                                  
                    element(X45, [0|X51], X60),
                    element(X46, [0|X51], X62),
                    element(X45, [0|X52], X61),
                    element(X46, [0|X52], X63),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt,eq,geq,gt], 1, X44),
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            max, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->
                        X76 #> -1 #=> X54 #>= max(X60,X62),                      
                        X76 #> -1 #=> X54 #=< min(X61,X63),                      
                        X83 = (X27 #<=> (max(X58,X59) #=  X31)),
                        X28 = binary_term_eq_coef(max)
                    ;
                     X55 = binary_term_leq_coef ->
                        X76 #> -1 #=> X54 #>  max(X60,X62),                      
                        X76 #> -1 #=> X54 #<  min(X61,X63),                      
                        X83 = (X27 #<=> (max(X58,X59) #=< X31)),
                        X28 = binary_term_leq_coef(max)
                    ;
                        X76 #> -1 #=> X54 #>  max(X60,X62),                      
                        X76 #> -1 #=> X54 #<  min(X61,X63),                      
                        X83 = (X27 #<=> (max(X58,X59) #>= X31)),
                        X28 = binary_term_geq_coef(max)
                    )
                ;
                 X43 = floor ->                                                            
                    element(X46, [0|X51], X62),
                    element(X46, [0|X52], X63),
                    (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                          
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            floor, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 div X59) #=  X31)),
                        X28 = binary_term_eq_coef(floor)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 div X59) #=< X31)),
                        X28 = binary_term_leq_coef(floor)
                    ;
                        X83 = (X27 #<=> ((X58 div X59) #>= X31)),
                        X28 = binary_term_geq_coef(floor)
                    )
                ;
                 X43 = mfloor ->
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44), 
                                                                                                  
                    element(X46, [0|X51], X62),
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        mfloor, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 div max(X59-X36,1)) #=  X31)),
                        X28 = binary_term_eq_coef(mfloor,X62)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 div max(X59-X36,1)) #=< X31)),
                        X28 = binary_term_leq_coef(mfloor,X62)
                    ;
                        X83 = (X27 #<=> ((X58 div max(X59-X36,1)) #>= X31)),
                        X28 = binary_term_geq_coef(mfloor,X62)
                    )
                ;
                 X43 = mod ->                                                              
                    element(X46, [0|X51], X62),
                    element(X46, [0|X52], X63),
                    (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                          
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                            mod, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 mod X59) #=  X31)),
                        X28 = binary_term_eq_coef(mod)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 mod X59) #=< X31)),
                        X28 = binary_term_leq_coef(mod)
                    ;
                        X83 = (X27 #<=> ((X58 mod X59) #>= X31)),
                        X28 = binary_term_geq_coef(mod)
                    )
                ;
                 X43 = prod ->
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        prod, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 * X59) #=  X31)),
                        X28 = binary_term_eq_coef(prod)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 * X59) #=< X31)),
                        X28 = binary_term_leq_coef(prod)
                    ;
                        X83 = (X27 #<=> ((X58 * X59) #>= X31)),
                        X28 = binary_term_geq_coef(prod)
                    )
                ;
                 X43 = ceil ->                                                             
                    element(X46, [0|X51], X62),
                    element(X46, [0|X52], X63),
                    (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                          
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        ceil, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> (((X58+X59-1) div X59) #=  X31)),
                        X28 = binary_term_eq_coef(ceil)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> (((X58+X59-1) div X59) #=< X31)),
                        X28 = binary_term_leq_coef(ceil)
                    ;
                        X83 = (X27 #<=> (((X58+X59-1) div X59) #>= X31)),
                        X28 = binary_term_geq_coef(ceil)
                    )
                ;
                 X43 = cmod ->                                                             
                    element(X45, [0|X51], X60),
                    element(X45, [0|X52], X61),
                    (X60 #=< 0 #/\ X61 #>= 0) #=> X76 #= -1,                          
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        cmod, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [geq,gt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 - (X59 mod X58)) #=  X31)),
                        X28 = binary_term_eq_coef(cmod)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 - (X59 mod X58)) #=< X31)),
                        X28 = binary_term_leq_coef(cmod)
                    ;
                        X83 = (X27 #<=> ((X58 - (X59 mod X58)) #>= X31)),
                        X28 = binary_term_geq_coef(cmod)
                    )
                ;
                 X43 = dmod ->                                                             
                    element(X46, [0|X51], X62),
                    element(X46, [0|X52], X63),
                    (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                          
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        dmod, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> ((X58 - (X58 mod X59)) #=  X31)),
                        X28 = binary_term_eq_coef(dmod)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> ((X58 - (X58 mod X59)) #=< X31)),
                        X28 = binary_term_leq_coef(dmod)
                    ;
                        X83 = (X27 #<=> ((X58 - (X58 mod X59)) #>= X31)),
                        X28 = binary_term_geq_coef(dmod)
                    )
                ;
                 X43 = fmod ->                                                               
                    element(X46, [0|X51], X62),
                    element(X46, [0|X52], X63),
                    (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                            
                    get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X15, 1, X75, X67, X55,
                                                                                        fmod, X25, X29, X30, X10),
                    X10 = [_,_|_],
                    table([[X45,X46,X54]], X10),
                    gen_table_ctr_wrt_forbidden_cmp(X80, X15, [leq,lt], 1, X44),
                    (X55 = binary_term_eq_coef ->
                        X83 = (X27 #<=> (((X58 mod X59 #= 0) * X59 +
                                                   (X58 mod X59 #> 0) * (X58 mod X59)) #=  X31)),
                        X28 = binary_term_eq_coef(fmod)
                    ;
                     X55 = binary_term_leq_coef ->
                        X83 = (X27 #<=> (((X58 mod X59 #= 0) * X59 +
                                                   (X58 mod X59 #> 0) * (X58 mod X59)) #=< X31)),
                        X28 = binary_term_leq_coef(fmod)
                    ;
                        X83 = (X27 #<=> (((X58 mod X59 #= 0) * X59 +
                                                   (X58 mod X59 #> 0) * (X58 mod X59)) #>= X31)),
                        X28 = binary_term_geq_coef(fmod)
                    )
                ;
                    true
                ),
                (X43 = mfloor ->
                    X5 = [X53, X20,X21,X31,X36],
                    X6 = [   X76,    X45,   X46,   X54,   X62]
                ;
                    X5 = [X53, X20,X21,X31],
                    X6 = [   X76,    X45,   X46,   X54]
                ),
                append([[X27,X58,X59], X17, [X74]], X8),
                append([X81,X82,X83], X85, X37),                                  
                X16 = [X84],
                X12 = 0
            ;
                write(formula_generator_bool_cond1m), nl, halt
            )
        ;
            write(formula_generator_bool_cond1n), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X55,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X48 = 0, X80 < 3) ->
        false
    ;
    (memberchk(X55,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X1 = 1) ->
        false
    ;
    (memberchk(X55,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X48 = 0, X80 >= 3) ->
        X44      = [X45,X46,X47],                                    
        X11 = [condb(X76)],                                                     
        domain(X44, 1, X77),                                                         
                                                                                             
                                                                                             
                                                                                             
        (X55 = ceil_leq_floor ->
             gen_table_ctr_wrt_authorised_cmp(X80, 3,                                       
                                              X15,                                 
                                              [geq,gt],                                      
                                              1,                                             
                                              X44)                                     
        ;
             gen_table_ctr_wrt_authorised_cmp(X80, 3,                                       
                                              X15,                                 
                                              [leq,lt],                                      
                                              1,                                             
                                              X44)                                     
        ),
        X76 #= -1 #<=> X45 #= 1,                                                     
        X76 #= -1 #<=> X46 #= 1,                                                     
        X76 #= -1 #<=> X47 #= 1,                                                     
        X54 = 0,                                                                        
        X70  = 0,                                                                        
        X84 in 0..2,                                                                        
        X76 #= -1 #<=> X84 #= 0,
        X76 #> -1 #<=> X84 #= 2,
        get_set_of_ternary_triplets_of_mandatory_attributes(X15, 1, X55, X25, X22),
        X22 = [_,_|_],
        table([X44], X22),
        X81 = element(X20, X13, X58),
        X82 = element(X21, X13, X59),
        X83 = element(X23, X13, X64),
        (X55 = sum_leq_attr ->
            X86 = (X27 #<=> (X58+X59 #=< X64))
        ;
         X55 = minus_mod_eq0 ->
            X86 = (X27 #<=> ((X64-X58) mod X59 #= 0))
        ;
            element(X46, [0|X51], X62),
            element(X46, [0|X52], X63),
            (X62 #=< 0 #/\ X63 #>= 0) #=> X76 #= -1,                             
            element(X47, [0|X51], X65),
            element(X47, [0|X52], X66),
            (X65 #=< 0 #/\ X66 #>= 0) #=> X76 #= -1,                             
            X86 = (X27 #<=> (((X58 - X64 + X59 - 1) / X59) #=< ((X58 - X59) / X64)))
        ),
        gen_table_constraint_for_a_condition(X75, X68, X74, X53, X27, X85),
        append([X81,X82,X83,X86], X85, X37),                                     
        append([[X27,X58,X59,X64], X17, [X74]], X8),
        X5 = [X53,X20,X21,X23],
        X6 = [X76,X45,X46,X47],
        X28      = X55,
        X16    = [X84],
        X12   = 0
    ;
        write(formula_generator_bool_cond1o(X55,X48)), nl, halt
    ),
    (X69 = 0 ->                                                                          
        all_mod_conds(X24),                                                         
        nonmember(X28, X24)                                                 
    ;
        true
    ),
    (is_list(X44) ->
        (memberchk(X55,[attr_eq_attr,attr_eq_coef]) ->                                  
            true                                                                             
        ;                                                                                    
            filter_boolean_attrs(X44, X4)                                
        )                                                                                    
    ;
        write(formula_generator_bool_cond1p(X55,X48)), nl, halt
    ).

filter_boolean_attrs([], _) :- !.
filter_boolean_attrs([X2|X3], X1) :-
    filter_boolean_attr(X1, X2),
    filter_boolean_attrs(X3, X1).

filter_boolean_attr([], _) :- !.
filter_boolean_attr([X2|X3], X1) :-
    X1 #\= X2,
    filter_boolean_attr(X3, X1).

gen_table_constraint_for_a_condition(and,    _, X4, X3, X1,
                                            [(X4 #= 1 #=> table([[X3,X1]], [[-1,0],[-1,1],[0,0],[1,1]]))]) :- !.
gen_table_constraint_for_a_condition(or,     _, X4, X3, X1,
                                            [(X4 #= 0 #=> table([[X3,X1]], [[-1,0],[-1,1],[0,1],[1,0]]))]) :- !.
gen_table_constraint_for_a_condition(sum,    X3, X4, X2, X1,
                                            [(X4 #= X3 #=> table([[X2,X1]], [[-1,0],[-1,1],[0,0],[1,1]]))]) :- !.
gen_table_constraint_for_a_condition(X5, _, _, _, _, []) :-
    memberchk(X5, [allequal, xor, voting, card1]), !.
gen_table_constraint_for_a_condition(X1, _, _, _, _, _) :- write(gen_table_constraint_for_a_condition(X1)), nl, halt.

formula_generator_bool_extra_ctr(X16,
                                 X9,
                                 X13,
                                 X14,
                                 X8,
                                 X4,
                                 X3,
                                 X1,
                                 X2,
                                 X5) :-
    (X16 = and  ->
        build_additional_term_for_and(X8, X4, X10),
        X5 = [(X13 #= 0 #=> X10)]
    ;
     X16 = or ->
        build_additional_term_for_or(X8, X4, X15),
        X5 = [(X13 #= 1 #=> X15)]
    ;
     X16 = sum ->
        build_additional_term_for_sum(X8, X4, X11),
        X5 = [(X13 #= X11)]
    ;
     X16 = allequal ->
        build_additional_terms_for_allequal(X8, X4, X6, X7),
        X17 = (X13 #= 0 #=>  X6 #< X9),
        X18 = (X13 #= 0 #=>  X7 #< X9),
        X19 = (X13 #= 1 #=> (X6 #= X9) #\/ (X7 #= X9)),
        X5 = [X17,X18,X19]
    ;
     X16 = xor ->
        build_additional_term_for_sum(X8, X4, X11),
        X5 = [(X13 #= X11 mod 2)]
    ;
     X16 = voting ->
        build_additional_term_for_sum(X8, X4, X11),
        X12 is (X9+1) // 2,
        X5 = [(X13 #= (X11 #>= X12))]
    ;
     X16 = card1 ->
        build_additional_term_for_sum(X8, X4, X11),
        X5 = [(X13 #= (X11 #= 1))]
    ;
        write(formula_generator_bool_extra_ctr(X16)), nl, halt
    ),
    append([X13], X4, X3),
    X1 = X8,
    X2 = X14.

build_additional_term_for_and([X2],   [X1],   (X2 #= (#\ X1))) :- !.
build_additional_term_for_and([X2|X3], [X1|X4], (X2 #= (#\ X1)) #\/ X5) :-
    build_additional_term_for_and(X3, X4, X5).

build_additional_term_for_or([X2],   [X1],   (X2 #= X1)) :- !.
build_additional_term_for_or([X2|X3], [X1|X4], (X2 #= X1) #\/ X5) :-
    build_additional_term_for_or(X3, X4, X5).

build_additional_term_for_sum([X2],   [X1],   (X2 #= X1)) :- !.
build_additional_term_for_sum([X2|X3], [X1|X4], (X2 #= X1) + X5) :-
    build_additional_term_for_sum(X3, X4, X5).

build_additional_terms_for_allequal([X2],   [X1],   (X2 #= X1),   (X2 #= (#\ X1))) :- !.
build_additional_terms_for_allequal([X2|X3], [X1|X4], (X2 #= X1)+X5, (X2 #= (#\ X1))+X6) :-
    build_additional_terms_for_allequal(X3, X4, X5, X6).

restrict_nb_unary_nb_binary_nb_ternary(X14, X1, X10, X11, t(X12,X8,X6,X2)) :-
    pos_bool_cond_entry(condb,     X9),
    pos_bool_cond_entry(lcondattr, X3),
    get_nb_unary_nb_binary_nb_ternary(X14, X9, X3, X7, X5, X4),
    X12   in 0..X10,
    X8  in 0..X10,
    X6 in 0..X10,
    call(X12   #= X7),                      
    call(X8  #= X5),                     
    call(X6 #= X4),                    
    table([[X12,X8,X6]], X1),
    ((X11 > 1, integer(X12), integer(X8), integer(X6)) ->
        X13 is X12 + 2*X8 + 3*X6, 
        (X13 = X11 ->                          
            X2 = 1                  
        ;
            X2 = 0                  
        )
    ;
        X2 = 0                      
    ).

get_nb_unary_nb_binary_nb_ternary([], _, _, 0, 0, 0) :- !.
get_nb_unary_nb_binary_nb_ternary([X4|X5], X2, X1, (X3 #>= 0)+X6, X7, X8) :-
    arg(X1, X4, [_]),                                                              
    !,
    arg(X2, X4, X3),
    get_nb_unary_nb_binary_nb_ternary(X5, X2, X1, X6, X7, X8).
get_nb_unary_nb_binary_nb_ternary([X4|X5], X2, X1, X6, (X3 #>= 0)+X7, X8) :-
    arg(X1, X4, [_,_]),                                                            
    !,
    arg(X2, X4, X3),
    get_nb_unary_nb_binary_nb_ternary(X5, X2, X1, X6, X7, X8).
get_nb_unary_nb_binary_nb_ternary([X4|X5], X2, X1, X6, X7, (X3 #>= 0)+X8) :-
    arg(X1, X4, [_,_,_]),                                                          
    !,
    arg(X2, X4, X3),
    get_nb_unary_nb_binary_nb_ternary(X5, X2, X1, X6, X7, X8).
get_nb_unary_nb_binary_nb_ternary([X1|_], _, _, _, _, _) :-
    write(get_nb_unary_nb_binary_nb_ternary(X1)), nl, halt.

break_symmetry_between_duplicated_conds([], _, _, _) :- !.
break_symmetry_between_duplicated_conds([_], _, _, _) :- !.
break_symmetry_between_duplicated_conds([X10,X11|X14], X5, X1, X2) :-
    arg(X5,       X10, X8),     
    arg(X1, X10, X12),
    arg(X2,   X10, X3),
    arg(X5,       X11, X9),     
    arg(X1, X11, X13),
    arg(X2,   X11, X4),
    (X12 = X13 ->                       
        X6 = [X8|X3],      
        X7 = [X9|X4],      
        gen_bool_cond_symmetry_breaking_automaton(X6, X7)
    ;
        true
    ),
    break_symmetry_between_duplicated_conds([X11|X14], X5, X1, X2).

gen_bool_cond_symmetry_breaking_automaton(X2, X3) :-
    gen_signature_bool_cond_symmetry_breaking_automaton(X2, X3, X1),
    automaton(X1, _, X1, 
              [source(r),sink(s),sink(t),sink(x)],
              [arc(r,0,s),
               arc(r,1,t),
               arc(r,2,v),
               arc(r,3,w),
               arc(r,4,w),
               arc(s,4,s),
               arc(t,5,t),
               arc(v,6,v),
               arc(w,6,w),
               arc(v,7,x),
               arc(v,8,x),
               arc(w,7,x),
               arc(x,6,x),
               arc(x,7,x),
               arc(x,8,x)],
               [], [], []).

gen_signature_bool_cond_symmetry_breaking_automaton([], [], []) :- !.
gen_signature_bool_cond_symmetry_breaking_automaton([X1|X2], [X3|X4], [X5|X6]) :-
    X5 in 0..7,
    X1 #= -1 #/\ X3 #= -1                 #<=> X5 #= 0, 
   (X1 #=  0 #\/ X1 #=  1) #/\ X3 #= -1   #<=> X5 #= 1, 
    X1 #=  1 #/\ X3 #=  0                 #<=> X5 #= 2, 
    X1 #=  0 #/\ X3 #=  0                 #<=> X5 #= 3, 
    X1 #=  1 #/\ X3 #=  1                 #<=> X5 #= 4, 
                                                       
    X1 #>  1 #/\ X3 #=  1                 #<=> X5 #= 5, 
                                                       
    X1 #>  1 #/\ X3 #>  1  #/\ X1 #= X3   #<=> X5 #= 6, 
    X1 #>  1 #/\ X3 #>  1  #/\ X1 #> X3   #<=> X5 #= 7, 
    X1 #>  1 #/\ X3 #>  1  #/\ X1 #< X3   #<=> X5 #= 8, 
    gen_signature_bool_cond_symmetry_breaking_automaton(X2, X4, X6).

forbid_specific_combinations_of_conds([], _, _, _, _, _, _, _, _, _, _) :- !.
forbid_specific_combinations_of_conds([X13|X15], X12, X10, X2, X11,  X7, X8, X4, X9, X1, X3) :-
    arg(X1, X13, X14),
    pos_bool_cond_entry(lcondcst,       X6),
    pos_bool_cond_entry(lcondcoef,      X5),
    forbid_specific_combinations_of_conds(X15, X13-X14, X12, X10, X2, X11,
                                          X7, X8, X4, X9, X1, X3, X5, X6),
    forbid_specific_combinations_of_conds(X15, X12, X10, X2, X11,  X7, X8,X4, X9, X1, X3).

avoid_simplifiable_conditional([],_,_,_,_,_,_,_,_) :- !.
avoid_simplifiable_conditional([X24|X25], X2,  X22,
                               X4, X5,
                               X8,   X9,
                               X11,    X12) :-
    pos_bool_cond_entry(condb,             X13),
    pos_bool_cond_entry(lcondattr,     X3),
    pos_bool_cond_entry(lcondcoef,      X6),
    pos_bool_cond_entry(newcondtype, X1),
    arg(X13,       X24, X23),
    arg(X3,   X24, X10),
    arg(X6,    X24, X14),
    arg(X1, X24, X7),
    ((X22 = and, X7 = attr_eq_attr) -> 
        X10 = [_,X15],
        (foreach(X16,X8), param([X15,X23])
        do
         (X23 #= 1) #=> (X15 #\= X16)
        )
    ;
     (X22 = and, X7 = attr_eq_coef) -> 
        X10 = [X15],
        (foreach(X16,X8), param([X15,X23])
        do
         (X23 #= 1) #=> (X15 #\= X16)
        )
    ;
     (X22 = and, X7 = attr_leq_coef) -> 
        X10 = [X15],
        tab_get_maxs_attr_names(X2, X17),                           
        element(X15, X17, X18),                                      
        (foreach(X19,X9), param([X23,X15,X18,X14])
        do
         ((X23 #= 1)#/\(X18 #= X14 + 1)) #=> (X15 #\= X19)
        )
    ;
     (X22 = and, X7 = attr_geq_coef) -> 
        X10 = [X15],
        tab_get_mins_attr_names(X2, X20),                           
        element(X15, X20, X21),                                      
        (foreach(X19,X9), param([X23,X15,X21,X14])
        do
         ((X23 #= 1)#/\(X21 #= (X14 - 1))) #=> (X15 #\= X19)
        )
    ;
        true
    ),
    avoid_simplifiable_conditional(X25, X2, X22,
                                   X4, X5,
                                   X8,   X9,
                                   X11,    X12).

restrict_specific_combinations_of_conds(X7, X5, X2, X8, X4, X1) :-
    (X5 > X2 ->
        get_all_condb_in_a_given_set_of_types(X7, X8, X4, X1, X6),
        (X6 = [_|_] ->
            X3 is X5-X2,
            count(-1, X6, #>=, X3)
        ;
            true
        )
    ;
        true
    ).

get_all_condb_in_a_given_set_of_types([], _, _, _, []) :- !.
get_all_condb_in_a_given_set_of_types([X6|X7], X4, X3, X1, [X5|X8]) :-
    arg(X1, X6, X2),
    memberchk(X2, X4),
    !,
    arg(X3, X6, X5),
    get_all_condb_in_a_given_set_of_types(X7, X4, X3, X1, X8).
get_all_condb_in_a_given_set_of_types([_|X5], X3, X2, X1, X6) :-
    get_all_condb_in_a_given_set_of_types(X5, X3, X2, X1, X6).

incompatible_families(X7, X2, X4, X1) :-
    length(X2, X8),
    length(X5,  X8),
    incompatible_families(X7, X2, X4, X1, X5),
    unused_families(X5, X6),
    X3 is X8-1,
    count(-1, X6, #>=, X3).

unused_families([], []) :- !.
unused_families([X1|X2], [X3|X4]) :-
    X3 in -1..1,
    (X1 = [_|_] ->
        maximum(X3, X1)
    ;
        X3 = -1
    ),
    unused_families(X2, X4).

incompatible_families([], _, _, _, X1) :- !,
    set_to_empty_list(X1).
incompatible_families([X6|X7], X3, X4, X1, X5) :-
    find_cond_family(X3, X6, X4, X1, X5, X2),
    incompatible_families(X7, X3, X4, X1, X2).

find_cond_family([], _, _, _, X2, X2) :- !.
find_cond_family([X6|_], X8, X4, X1, [X5|X10], [X2|X10]) :-
    arg(X1, X8, X3),
    memberchk(X3, X6),
    !,
    arg(X4, X8, X7),
    X5 = [X7|X2].
find_cond_family([_|X6], X4, X2, X1, [X3|X7], [X3|X8]) :-
    find_cond_family(X6, X4, X2, X1, X7, X8).

set_to_empty_list([]) :- !.
set_to_empty_list([[]|X1]) :-
    set_to_empty_list(X1).

