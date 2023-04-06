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

formula_generator_bool_conds(X15, X14, X19, t(_,_,_,_), X21) :- 
    (memberchk(mandatory_attr(X10), X15) -> true ; write(formula_generator_bool_conds1), nl, halt),
    (memberchk(neg(X31),                  X15) -> true ; write(formula_generator_bool_conds2), nl, halt),
    (memberchk(op(X37),                    X15) -> true ; write(formula_generator_bool_conds3), nl, halt),
    (memberchk(nb_terms(X32,X33),     X15) -> true ; write(formula_generator_bool_conds4), nl, halt),
    (memberchk(conds(X38),                 X15) -> true ; write(formula_generator_bool_conds5), nl, halt),
    (foreach(X43,X37)
        do (memberchk(X43,[and,or,sum,allequal,xor,voting,card1]) -> true ; write(formula_generator_bool_conds6(X43)), nl, halt)
    ),                                                
    (memberchk(use_mods(X34),             X15) -> true ; write(formula_generator_bool_conds6a), nl, halt),
    pos_bool_cond_entry(condb,       X27),
    pos_bool_cond_entry(newcondtype, X8),
    
    ((integer(X32), integer(X33), X32 > 0, X32 =< X33) -> true ; write(formula_generator_bool_conds7), nl, halt),
    X35 in X32..X33,
    indomain(X35),                                
    length(X10, X36),                   
    gen_compatible_unary_and_binary_and_ternary(      
                                    X35, X36, 
                                    X1),
    (X1 = [] -> false ; true),  
    member(X41, X37),                            

    
    
    
    tab_get_mins_attr_names(X10, X28), 
    tab_get_maxs_attr_names(X10, X29), 
    get_shifted_bool_attributes(X28, X29, 2, X4),
    (length(X4, X36) ->             
        (X35 = 1 -> X31 = 0 ; true),          
        X30 = 1,
        X3 is min(X35,X36),
        X17 = [t(cond(attr_eq_coef(coef(0,1))), no_negation,    X3),
                      t(cond(attr_eq_attr),            no_restriction, X3)],
        duplicate_bool_conds(X17, X35, X22)
    ;                                                 
        X30 = 0,
        duplicate_bool_conds(X38, X35, X22)
    ),

    X21 = [                                     
                 mandatory_attr(X10),       
                 neg(X31),                        
                 shift(X19),                    
                 op(X41),                           
                 nb_terms(X35),                   
                 conds(X42),                        
                 combined_row_ctrs(X7,   
                                   X5,  
                                   X6,
                                   X18)],

                                                      
                                                      
    formula_generator_bool_conds1(X22, X41, X31, X35, X10, X30, X34, X28, X29, X4,
                                  X14, X39, X42, X40, X23, X12),


    (X34 = 1 ->                                   
        all_mod_conds(X13),                  
        collect_condb_for_mods(X42, X13, X27, X8, X24),
        count(0, X24, #=, X9),      
        count(1, X24, #=, X11 ),      
        X11 + X9 #>= 1          
    ;
        true
    ),
    length(X42, X44),                                 
    X25 is X44 - X35,                         
    count(-1, X40, #=, X25),                 
                                                      
                                                      
    formula_generator_bool_extra_ctr(X41, X35, X39, X40, X23, X12,
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

formula_generator_bool_cond1(X71, X63, X64, X13, X46, X65, X47, X48, X4,
                             _, X75, X7, X70, X22, X72, X49, X23) :-
    
    ((X64 = 1, X63 = 1)       -> X72 in -1..1, X72 #\= 0                                    ; 
     X7 = no_negation    -> X72 in -1..1, X72 #\= 0                                    ;
     X7 = no_restriction -> X72 in -1..1                                                 ;
                                         write(formula_generator_bool_cond1a(X7)), nl, halt),
    X22 = cond(X72,                            
                       X24,                      
                       X40,                        
                       X10,                   
                       X14,                    
                       X41, X42, X43,  
                       X66, X50,                
                       X8,                  
                       X5,                 
                       X6,                 
                       X33,                       
                       X11),                  
                                                         
                                                         
    
    (compound(X75) -> true ;
     atom(X75)     -> true ; write(formula_generator_bool_cond1b), nl, halt),               
    functor(X75, X51, X44),                                                      
    length(X13, X76),                                                             
    length(X15, X76),                                                             
    X73 is X76+1,
    append([0], X15, X12),                                              

    
    
    X52 is (X64-1)*3+1,                                                             
    X53 is X52+1,                                                                  
    (X52 < X76 -> X3   = 1 ;                                       
                        X3   = 0 ),                                      
    (X53 < X76 -> X2  = 1 ;                                       
     X76     < 2    -> X2  = 1 ;                                       
                        X2  = 0 ),                                      
    (X76     < 3    -> X1 = 1 ;                                       
                        X1 = 0 ),                                      

    
    
    
    ((memberchk(X51, [attr_eq_attr,attr_leq_attr]), X44 = 0, X76 = 1) ->
        false
    ;
     (memberchk(X51, [attr_eq_attr,attr_leq_attr]), X2 = 1) ->
        false
    ;
     (memberchk(X51, [attr_eq_attr,attr_leq_attr]), X44 = 0, X76 > 1) ->         
        X40      = [X41,X42],                                              
        X43      = 0,                                                                  
        X10 = [condb(X72)],                                                     
        domain(X40, 1, X73),                                                         
        X72 #= -1 #<=> X41 #= 1,                                                     
        X72 #= -1 #<=> X42 #= 1,                                                     
        X50 = 0,                                                                        
        X66  = 0,                                                                        

        
        
        
        X77 = element(X18, X12, X54),                              
        X78 = element(X19, X12, X55),                              
        (X51 = attr_eq_attr ->                                                          
            X41 #=< X42,
            X41 #= 1 #\/ X41 #< X42,                                       
            X16 = [eq,lt,gt,neq],                                                  
            X79 = (X23 #<=> (X54 #= X55)),                                
            (X46 = 1 ->                                                                 
                X80 in 0..2,
                X72 #= -1 #=> X80 #= 0,
                X72 #>= 0 #=> X80 #= 2-X72,
                X14 = [X80]
            ;                                                                                
                X14 = []
            )
        ;                                                                                    
            X41 #= 1 #\/ X41 #\= X42,                                      
            X16 = [leq,eq,lt,gt],                                                  
            X79 = (X23 #<=> (X54 #=< X55)),                               
            X80 in 0..1, X72 #= -1 #=> X80 #= 0, X72 #> -1 #=> X80 #= 1,              
            X14 = [X80]
        ),
        gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
        append([X77,X78,X79], X81, X33),                                          
        gen_table_ctr_wrt_forbidden_cmp(X76, X13, X16, 1, X40),   
        append([[X23,X54,X55], X15, [X70]], X8),
        X5 = [X49,X18,X19],
        X6 = [X72,X41,X42],
        X24      = X51,
        X11   = 0
    ;

    
    
    
    
     (memberchk(X51, [attr_eq_coef,attr_leq_coef,attr_geq_coef]), X3 = 1) ->
        false
    ;
     (memberchk(X51, [attr_eq_coef,attr_leq_coef,attr_geq_coef]), X44 = 1) ->     
        ((arg(1, X75, coef(X25,X26)),                                       
          integer(X25), integer(X26), X25 =< X26) ->         
            X50 in X25..X26                                             
        ;
            write(formula_generator_bool_cond1c), nl, halt
        ),
        (X51 = attr_eq_coef  -> X10 = [condb(X72),coef(eq, X50)] ;    
         X51 = attr_leq_coef -> X10 = [condb(X72),coef(leq,X50)] ;
                                     X10 = [condb(X72),coef(geq,X50)] ),
        X40      = [X41],                                                        
        X41 in 1..X73,                                                               
        X72 #= -1 #<=> X41 #= 1,                                                     
        X72 #= -1 #=> X50 #= X25,                                             
        X42 = 0,                                                                       
        X43 = 0,                                                                       
        X66   = 0,                                                                       
                                                                                             
                                                                                             
                                                                                             

        
        
                                                                                             
                                                                                             
        (X46 = 1 ->                                                                     
            X80 in 0..1,
            X72 #= -1 #=> X80 #= 0,
            X72 #> -1 #=> X80 #= 1 - X50,
            X14 = [X80]                                                           
        ;                                                                                    
            X67 is min(0,X25),                                                   
            X68 is max(0,X26)+1,
            X80 in X67..X68,
            X72 #= -1 #=> X80 #= 0,
            (X51 = attr_eq_coef -> X72 #> -1 #=> X80 #= X50 ; X72 #> -1 #=> X80 #= X50 + 1),
            X14 = [X80]
        ),
        X77 = element(X18, X12, X54),                              
        (X51 = attr_eq_coef ->                                                          
            X78 = (X23 #<=> (X54 #= X27))
        ;
         X51 = attr_leq_coef ->                                                         
            X78 = (X23 #<=> (X54 #=< X27))
        ;
            X78 = (X23 #<=> (X54 #>= X27))
        ),
        append([[X23,X54], X15, [X70]], X8),
        gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
        append([X77,X78], X81, X33),                                               
        X5 = [X49,X18,X27],
        X6 = [X72,X41,X50],
        X24      = X51,
        X11   = 0
    ;

    
    
    (X51 = attr_in_interval, X3 = 1) ->
        false
    ;
    (X51 = attr_in_interval, X44 = 2) ->                                          
        arg(1, X75, X28),                                                           
        arg(2, X75, X29),                                                           
        ((integer(X28),
          integer(X29),
          X28 < X29) ->
            X66  in X28..X29,                                            
            X50 in X28..X29,                                            
            X40      = [X41],                                                    
            X10 = [condb(X72),coef(geq,X66),coef(leq,X50)],            
            X41 in 1..X73,                                                           
            X42 = 0,                                                                   
            X43 = 0,                                                                   
            X72 #= -1 #<=> X41 #= 1,                                                 
            X72 #= -1 #=>  X66   #= X28,                                       
            X72 #= -1 #=>  X50  #= X28,                                       
            X72 #> -1 #<=> X66   #< X50,                                          
            element(X41, [X28|X47], X56),                            
            element(X41, [X28|X48], X57),                            
            X72 #> -1 #=> X66  #> X56,                                            
            X72 #> -1 #=> X50 #< X57,                                            
            X67 is min(0,X28),                                                   
            X68 is max(0,X29+2),                                                 
            X80 in X67..X68,                                                        
            X72 #= -1 #=> X80 #= 0,                                                       
            X72 #> -1 #=> X80 #= abs(X50) + 1 + (X72 #= 0),                        
                                                                                             
            X77 = element(X18, X12, X54),                          
            X78 = (X23 #<=> (X34 #=< X54 #/\ X54 #=< X27)),
            append([[X23,                                                            
                     X54], X15, [X70]], X8),
            gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
            append([X77,X78], X81, X33),                                           
            X5 = [X49,X18,X34,X27],               
            X6 = [X72,X41,X66,X50],                           
            X24      = X51,                                                     
            X14    = [X80],
            X11   = 0
        ;
            write(formula_generator_bool_cond1d), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X51,[attr_eq_unary,attr_leq_unary,unary_leq_attr]), X44 = 1, X76 = 1) ->
        false
    ;
    (memberchk(X51,[attr_eq_unary,attr_leq_unary,unary_leq_attr]), X2 = 1) ->
        false
    ;
    (memberchk(X51,[attr_eq_unary,                                                      
                        attr_leq_unary,unary_leq_attr]), X44 = 1, X76 > 1) ->         
        arg(1, X75, X35),                                                            
        X40      = [X41,X42],                                              
        X43      = 0,                                                                  
        X10 = [condb(X72),X66],                                             
        domain(X40, 1, X73),                                                         
        X72 #= -1 #<=> X41 #= 1,                                                     
        X72 #= -1 #<=> X42 #= 1,                                                     
        X72 #> -1 #<=> X41 #\= X42,                                            
        X50 = 0,                                                                        
        (memberchk(X51, [attr_eq_unary,attr_leq_unary]) ->
            X16 = [leq,eq,lt]                                                      
        ;
            X16 = [geq,eq,gt]                                                      
        ),
        gen_table_ctr_wrt_forbidden_cmp(X76, X13, X16, 1, X40),   
        (X35 = [X45]  ->                                                        
            ((compound(X45),                                                           
              functor(X45, X74, 2),                                                  
              memberchk(X74, [prod]),                                                      
              arg(1, X45, X36),                                                 
              arg(2, X45, X37),                                                 
              integer(X36), integer(X37), X36 =< X37) ->         
                X38 is max(2,X36),                                             
                X66 in X38..X37,                                           
                X72 #= -1 #=> X66 #= X38,                                       
                X72 #> -1 #=> X66 #\= 1,                                               
                X67 is min(0,X38),                                                
                X68 is max(0,X37+1),                                              
                X80 in X67..X68,                                                    
                X72 #= -1 #=> X80 #= 0,                                                   
                (X69 = attr_eq_unary ->
                    X72 #> -1 #=> X80 #= X66                                          
                ;
                    X72 #> -1 #=> X80 #= X66 + 1                                      
                ),
                X77 = element(X18, X12, X54),                      
                X78 = element(X19, X12, X55),                      
                (X51 = attr_leq_unary ->
                    X79 = (X23 #<=> (X54 #=< X55 * X34)),
                    X24 = attr_leq_unary(prod)
                ;
                 X51 = unary_leq_attr ->
                    X79 = (X23 #<=> (X54 * X34 #=< X55)),
                    X24 = unary_leq_attr(prod)
                ;
                 X69 = attr_eq_unary ->
                    X79 = (X23 #<=> (X54 #= X55 * X34)),
                    X24 = attr_eq_unary(prod)
                ;
                    write(formula_generator_bool_cond1e), nl, halt
                ),
                gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
                append([[X23,X54,X55], X15, [X70]], X8),
                append([X77,X78,X79], X81, X33),                                  
                X5 = [X49, X18, X19, X34],       
                X6 = [   X72,    X41,    X42,    X66],       
                X14    = [X80],
                X11   = 0
            ;
                write(formula_generator_bool_cond1f), nl, halt
            )
        ;
            write(formula_generator_bool_cond1g), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X51, [unary_term_eq_coef,unary_term_leq_coef,unary_term_geq_coef]), X3 = 1) ->
        false
    ;
    (memberchk(X51,[unary_term_eq_coef,unary_term_leq_coef,unary_term_geq_coef]),
     X44 = 2                                                                   ) ->    
        arg(1, X75, X35),                                                            
        ((arg(2, X75, coef(X25,X26)),                                       
          integer(X25), integer(X26), X25 =< X26) ->         
            X50 in X25..X26                                             
        ;
            write(formula_generator_bool_cond1h), nl, halt
        ),                                                                                   
        (X51 = unary_term_eq_coef  -> X10 = [condb(X72),coef(eq, X50),X66] ;
         X51 = unary_term_leq_coef -> X10 = [condb(X72),coef(leq,X50),X66] ;
                                           X10 = [condb(X72),coef(geq,X50),X66] ),
        X40      = [X41],                                                        
        X41 in 1..X73,                                                               
        X42 = 0,                                                                       
        X43 = 0,                                                                       
        X72 #= -1 #<=> X41 #= 1,                                                     
        (X35 = [X45] ->                                                         
            ((compound(X45),                                                           
              functor(X45, X74, 2),                                                  
              (X74 = mod ->                                                                
                true
              ;
                write(formula_generator_bool_cond1i), nl, halt
              ),
              X72 #= -1 #=> X50 #= X25,                                       
              arg(1, X45, X36),                                                 
              arg(2, X45, X37),                                                 
              integer(X36), integer(X37), X36 =< X37) ->         
                X66 in X36..X37,                                           
                X72 #= -1 #=> X66 #= X36,                                       
                X67 is min(0,X36),
                (X51 = unary_term_eq_coef ->                                            
                    X68 is max(0,X37+X26+1)
                ;
                    X68 is max(0,X37+X26+2)
                ),                                                                           
                X80 in X67..X68,                                                    
                X72 #= -1 #=> X80 #= 0,                                                   
                (X51 = unary_term_eq_coef ->
                    X72 #> -1 #=> X80 #= X66+X50+1                               
                ;
                    X72 #> -1 #=> X80 #= X66+X50+2                               
                ),
                element(X41, [X36|X47], X56),                         
                element(X41, [X36|X48], X57),                         
                X72 #> -1 #=> X66 #> 1,
                X72 #> -1 #=> X66 #=< (X57 - X56),                           
                                                                                             
                                                                                             
                                                                                             
                                                                                             
                                                                                             
                
                gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
                X77 = element(X18, X12, X54),                      
                (X51 = unary_term_eq_coef ->
                    X72 #> -1 #=> X50 #<  X66,
                    X78 = (X23 #<=> ((X54 mod X34) #=  X27)),
                    X24 = unary_term_eq_coef(mod)
                ;
                 X51 = unary_term_leq_coef ->
                    X72 #> -1 #=> X50 #<  X66 - 1,                                
                    X78 = (X23 #<=> ((X54 mod X34) #=< X27)),
                    X24 = unary_term_leq_coef(mod)
                ;
                    X72 #> -1 #=> X50 #<  X66 - 1,                                
                    X78 = (X23 #<=> ((X54 mod X34) #>= X27)),
                    X24 = unary_term_geq_coef(mod)
                ),
                X11 = 0,
                append([[X23,X54], X15, [X70]], X8),
                append([X77,X78], X81, X33),                                       
                X5 = [X49, X18, X34, X27],
                X6 = [   X72,    X41,    X66,    X50],
                X14    = [X80]
            ;
                write(formula_generator_bool_cond1j), nl, halt
            )
        ;
            write(formula_generator_bool_cond1k), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X51,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X44 = 2, X76 = 1) ->
        false
    ;
    (memberchk(X51,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X2 = 1) ->
        false
    ;                                                                                        
    (memberchk(X51,[binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]), X44 = 2, X76 > 1) ->
        arg(1, X75, X30),                                                           
        (X51 = binary_term_eq_coef  -> X10 = [condb(X72),coef(eq, X50)] ; 
         X51 = binary_term_leq_coef -> X10 = [condb(X72),coef(leq,X50)] ;
                                            X10 = [condb(X72),coef(geq,X50)] ),
        X40      = [X41, X42],                                             
        X41 in 1..X73,                                                               
        X42 in 1..X73,                                                               
        X43 = 0,                                                                       
        X66 = 0,
        X72 #= -1 #<=> X41 #= 1,                                                     
        X72 #= -1 #<=> X42 #= 1,                                                     
        ((arg(2, X75, coef(X25,X26)),                                       
          integer(X25), integer(X26), X25 =< X26) ->         
            X50 in X25..X26                                             
        ;
            write(formula_generator_bool_cond1l), nl, halt
        ),         
        (X30 = [X39] ->                                                       
            ((all_bool_options(binary, X9),                                     
              memberchk(X39, X9)) ->                                     
                (memberchk(X39, [plus,abs,min,max,prod]) ->                           
                    X72 #> -1 #=> X41 #<  X42                                  
                ;                                                                            
                    X72 #> -1 #=> X41 #\= X42                                  
                ),
                (memberchk(X39, [floor,mfloor,ceil,mod,dmod,fmod]) ->                 
                    forbid_cols_which_can_be_leq0(X76, X13, 1, X42)
                ;
                 X39 = cmod ->                                                        
                    forbid_cols_which_can_be_leq0(X76, X13, 1, X41)
                ;
                    true                                                                     
                ),
                X72 #= -1 #=> X50 #= X25,                                     
                X67 is min(0,X25),
                (X39 = plus   -> X31 = 0 ;
                 X39 = minus  -> X31 = 1 ;
                 X39 = abs    -> X31 = 5 ;
                 X39 = min    -> X31 = 5 ;
                 X39 = max    -> X31 = 5 ;
                 X39 = prod   -> X31 = 6 ;
                 X39 = floor  -> X31 = 7 ;
                 X39 = mfloor -> X31 = 8 ;
                 X39 = ceil   -> X31 = 7 ;
                 X39 = mod    -> X31 = 5 ;
                 X39 = cmod   -> X31 = 6 ;
                 X39 = dmod   -> X31 = 6 ;
                 X39 = fmod   -> X31 = 6 ;
                                        true            ),
                (X51 = binary_term_eq_coef ->                                           
                    X68 is max(0,X26+2+X31)
                ;
                    X68 is max(0,X26+3+X31)
                ),
                X80 in X67..X68,                                                    
                X72 #= -1 #=> X80 #= 0,                                                   
                (X51 = binary_term_eq_coef ->
                    X72 #> -1 #=> X80 #= abs(X50) + 2 + X31                  
                ;
                    X72 #> -1 #=> X80 #= abs(X50) + 3 + X31                  
                ),
                gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
                X77 = element(X18, X12, X54),
                X78 = element(X19, X12, X55),
                (X39 = plus ->
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> (X54+X55 #= X27)),
                        X24 = binary_term_eq_coef(plus)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> (X54+X55 #=< X27)),
                        X24 = binary_term_leq_coef(plus)
                    ;
                        X79 = (X23 #<=> (X54+X55 #>= X27)),
                        X24 = binary_term_geq_coef(plus)
                    )
                ;
                 X39 = minus ->
                    X72 #> -1 #=> X50 #> 0,                                                  
                    (X51 = binary_term_eq_coef ->                                              
                        X79 = (X23 #<=> (X54-X55 #=  X27)),
                        X24 = binary_term_eq_coef(minus)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> (X54-X55 #=< X27)),
                        X24 = binary_term_leq_coef(minus)
                    ;
                        X79 = (X23 #<=> (X54-X55 #>= X27)),
                        X24 = binary_term_geq_coef(minus)
                    )
                ;
                 X39 = abs ->                                                                
                    X72 #> -1 #=> X50 #> 0,                                                  
                                                                                                    
                                                                                                    
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt,eq,geq,gt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> (abs(X54-X55) #=  X27)),
                        X24 = binary_term_eq_coef(abs)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> (abs(X54-X55) #=< X27)),
                        X24 = binary_term_leq_coef(abs)
                    ;
                        X72 #> -1 #=> X50 #> 1,
                        X79 = (X23 #<=> (abs(X54-X55) #>= X27)),
                        X24 = binary_term_geq_coef(abs)
                    )
                ;
                 X39 = min ->                                                                 
                    element(X41, [0|X47], X56),
                    element(X42, [0|X47], X58),
                    element(X41, [0|X48], X57),
                    element(X42, [0|X48], X59),
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt,eq,geq,gt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X72 #> -1 #=> X50 #>= max(X56,X58),                      
                        X72 #> -1 #=> X50 #=< min(X57,X59),                      
                        X79 = (X23 #<=> (min(X54,X55) #=  X27)),
                        X24 = binary_term_eq_coef(min)
                    ;
                     X51 = binary_term_leq_coef ->
                        X72 #> -1 #=> X50 #>  max(X56,X58),                      
                        X72 #> -1 #=> X50 #<  min(X57,X59),                      
                        X79 = (X23 #<=> (min(X54,X55) #=< X27)),
                        X24 = binary_term_leq_coef(min)
                    ;
                        X72 #> -1 #=> X50 #>  max(X56,X58),                      
                        X72 #> -1 #=> X50 #<  min(X57,X59),                      
                        X79 = (X23 #<=> (min(X54,X55) #>= X27)),
                        X24 = binary_term_geq_coef(min)
                    )
                ;
                 X39 = max ->                                                                  
                    element(X41, [0|X47], X56),
                    element(X42, [0|X47], X58),
                    element(X41, [0|X48], X57),
                    element(X42, [0|X48], X59),
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt,eq,geq,gt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X72 #> -1 #=> X50 #>= max(X56,X58),                      
                        X72 #> -1 #=> X50 #=< min(X57,X59),                      
                        X79 = (X23 #<=> (max(X54,X55) #=  X27)),
                        X24 = binary_term_eq_coef(max)
                    ;
                     X51 = binary_term_leq_coef ->
                        X72 #> -1 #=> X50 #>  max(X56,X58),                      
                        X72 #> -1 #=> X50 #<  min(X57,X59),                      
                        X79 = (X23 #<=> (max(X54,X55) #=< X27)),
                        X24 = binary_term_leq_coef(max)
                    ;
                        X72 #> -1 #=> X50 #>  max(X56,X58),                      
                        X72 #> -1 #=> X50 #<  min(X57,X59),                      
                        X79 = (X23 #<=> (max(X54,X55) #>= X27)),
                        X24 = binary_term_geq_coef(max)
                    )
                ;
                 X39 = floor ->                                                            
                    element(X42, [0|X47], X58),
                    element(X42, [0|X48], X59),
                    (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                          
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 div X55) #=  X27)),
                        X24 = binary_term_eq_coef(floor)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 div X55) #=< X27)),
                        X24 = binary_term_leq_coef(floor)
                    ;
                        X79 = (X23 #<=> ((X54 div X55) #>= X27)),
                        X24 = binary_term_geq_coef(floor)
                    )
                ;
                 X39 = mfloor ->
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40), 
                                                                                                  
                    element(X42, [0|X47], X58),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 div max(X55-X32,1)) #=  X27)),
                        X24 = binary_term_eq_coef(mfloor,X58)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 div max(X55-X32,1)) #=< X27)),
                        X24 = binary_term_leq_coef(mfloor,X58)
                    ;
                        X79 = (X23 #<=> ((X54 div max(X55-X32,1)) #>= X27)),
                        X24 = binary_term_geq_coef(mfloor,X58)
                    )
                ;
                 X39 = mod ->                                                              
                    element(X42, [0|X47], X58),
                    element(X42, [0|X48], X59),
                    (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                          
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 mod X55) #=  X27)),
                        X24 = binary_term_eq_coef(mod)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 mod X55) #=< X27)),
                        X24 = binary_term_leq_coef(mod)
                    ;
                        X79 = (X23 #<=> ((X54 mod X55) #>= X27)),
                        X24 = binary_term_geq_coef(mod)
                    )
                ;
                 X39 = prod ->
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 * X55) #=  X27)),
                        X24 = binary_term_eq_coef(prod)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 * X55) #=< X27)),
                        X24 = binary_term_leq_coef(prod)
                    ;
                        X79 = (X23 #<=> ((X54 * X55) #>= X27)),
                        X24 = binary_term_geq_coef(prod)
                    )
                ;
                 X39 = ceil ->                                                             
                    element(X42, [0|X47], X58),
                    element(X42, [0|X48], X59),
                    (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                          
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> (((X54+X55-1) div X55) #=  X27)),
                        X24 = binary_term_eq_coef(ceil)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> (((X54+X55-1) div X55) #=< X27)),
                        X24 = binary_term_leq_coef(ceil)
                    ;
                        X79 = (X23 #<=> (((X54+X55-1) div X55) #>= X27)),
                        X24 = binary_term_geq_coef(ceil)
                    )
                ;
                 X39 = cmod ->                                                             
                    element(X41, [0|X47], X56),
                    element(X41, [0|X48], X57),
                    (X56 #=< 0 #/\ X57 #>= 0) #=> X72 #= -1,                          
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [geq,gt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 - (X55 mod X54)) #=  X27)),
                        X24 = binary_term_eq_coef(cmod)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 - (X55 mod X54)) #=< X27)),
                        X24 = binary_term_leq_coef(cmod)
                    ;
                        X79 = (X23 #<=> ((X54 - (X55 mod X54)) #>= X27)),
                        X24 = binary_term_geq_coef(cmod)
                    )
                ;
                 X39 = dmod ->                                                             
                    element(X42, [0|X47], X58),
                    element(X42, [0|X48], X59),
                    (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                          
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> ((X54 - (X54 mod X55)) #=  X27)),
                        X24 = binary_term_eq_coef(dmod)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> ((X54 - (X54 mod X55)) #=< X27)),
                        X24 = binary_term_leq_coef(dmod)
                    ;
                        X79 = (X23 #<=> ((X54 - (X54 mod X55)) #>= X27)),
                        X24 = binary_term_geq_coef(dmod)
                    )
                ;
                 X39 = fmod ->                                                               
                    element(X42, [0|X47], X58),
                    element(X42, [0|X48], X59),
                    (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                            
                    gen_table_ctr_wrt_forbidden_cmp(X76, X13, [leq,lt], 1, X40),
                    (X51 = binary_term_eq_coef ->
                        X79 = (X23 #<=> (((X54 mod X55 #= 0) * X55 +
                                                   (X54 mod X55 #> 0) * (X54 mod X55)) #=  X27)),
                        X24 = binary_term_eq_coef(fmod)
                    ;
                     X51 = binary_term_leq_coef ->
                        X79 = (X23 #<=> (((X54 mod X55 #= 0) * X55 +
                                                   (X54 mod X55 #> 0) * (X54 mod X55)) #=< X27)),
                        X24 = binary_term_leq_coef(fmod)
                    ;
                        X79 = (X23 #<=> (((X54 mod X55 #= 0) * X55 +
                                                   (X54 mod X55 #> 0) * (X54 mod X55)) #>= X27)),
                        X24 = binary_term_geq_coef(fmod)
                    )
                ;
                    true
                ),
                (X39 = mfloor ->
                    X5 = [X49, X18,X19,X27,X32],
                    X6 = [   X72,    X41,   X42,   X50,   X58]
                ;
                    X5 = [X49, X18,X19,X27],
                    X6 = [   X72,    X41,   X42,   X50]
                ),
                append([[X23,X54,X55], X15, [X70]], X8),
                append([X77,X78,X79], X81, X33),                                  
                X14 = [X80],
                X11 = 0
            ;
                write(formula_generator_bool_cond1m), nl, halt
            )
        ;
            write(formula_generator_bool_cond1n), nl, halt
        )
    ;

    
    
    
    
    (memberchk(X51,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X44 = 0, X76 < 3) ->
        false
    ;
    (memberchk(X51,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X1 = 1) ->
        false
    ;
    (memberchk(X51,[sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), X44 = 0, X76 >= 3) ->
        X40      = [X41,X42,X43],                                    
        X10 = [condb(X72)],                                                     
        domain(X40, 1, X73),                                                         
                                                                                             
                                                                                             
                                                                                             
        (X51 = ceil_leq_floor ->
             gen_table_ctr_wrt_authorised_cmp(X76, 3,                                       
                                              X13,                                 
                                              [geq,gt],                                      
                                              1,                                             
                                              X40)                                     
        ;
             gen_table_ctr_wrt_authorised_cmp(X76, 3,                                       
                                              X13,                                 
                                              [leq,lt],                                      
                                              1,                                             
                                              X40)                                     
        ),
        X72 #= -1 #<=> X41 #= 1,                                                     
        X72 #= -1 #<=> X42 #= 1,                                                     
        X72 #= -1 #<=> X43 #= 1,                                                     
        X50 = 0,                                                                        
        X66  = 0,                                                                        
        X80 in 0..2,                                                                        
        X72 #= -1 #<=> X80 #= 0,
        X72 #> -1 #<=> X80 #= 2,
        X77 = element(X18, X12, X54),
        X78 = element(X19, X12, X55),
        X79 = element(X20, X12, X60),
        (X51 = sum_leq_attr ->
            X82 = (X23 #<=> (X54+X55 #=< X60))
        ;
         X51 = minus_mod_eq0 ->
            X82 = (X23 #<=> ((X60-X54) mod X55 #= 0))
        ;
            element(X42, [0|X47], X58),
            element(X42, [0|X48], X59),
            (X58 #=< 0 #/\ X59 #>= 0) #=> X72 #= -1,                             
            element(X43, [0|X47], X61),
            element(X43, [0|X48], X62),
            (X61 #=< 0 #/\ X62 #>= 0) #=> X72 #= -1,                             
            X82 = (X23 #<=> (((X54 - X60 + X55 - 1) / X55) #=< ((X54 - X55) / X60)))
        ),
        gen_table_constraint_for_a_condition(X71, X64, X70, X49, X23, X81),
        append([X77,X78,X79,X82], X81, X33),                                     
        append([[X23,X54,X55,X60], X15, [X70]], X8),
        X5 = [X49,X18,X19,X20],
        X6 = [X72,X41,X42,X43],
        X24      = X51,
        X14    = [X80],
        X11   = 0
    ;
        write(formula_generator_bool_cond1o(X51,X44)), nl, halt
    ),
    (X65 = 0 ->                                                                          
        all_mod_conds(X21),                                                         
        nonmember(X24, X21)                                                 
    ;
        true
    ),
    (is_list(X40) ->
        (memberchk(X51,[attr_eq_attr,attr_eq_coef]) ->                                  
            true                                                                             
        ;                                                                                    
            filter_boolean_attrs(X40, X4)                                
        )                                                                                    
    ;
        write(formula_generator_bool_cond1p(X51,X44)), nl, halt
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

