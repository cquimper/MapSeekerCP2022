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
% Purpose: A set of utility predicates required for creation of additional performance constraints for gen_bool_formulae.pl and gen_cond_formulae.pl
% Author : Nicolas Beldiceanu, Ramiz Gindullin, IMT Atlantique

:- module(bool_cond_utility,[tab_get_unaryf_values/7,
                             tab_get_unary_term_values/7,
                             tab_get_binary_term_values/7,
                             tab_get_attribute_values/6,
                             tab_get_ternary_values/6,
                             gen_compatible_unary_and_binary_and_ternary/3,
                             generate_oplus_lists_from_val_target_pairs/5,
                             split_value_target_pairs/4,
                             get_set_of_values_for_each_mandatory_attribute/9,
                             get_set_of_unaryf_values_for_each_pair_of_mandatory_attributes/8,
                             get_set_of_unary_term_values_for_each_mandatory_attribute/12,
                             get_set_of_ternary_triplets_of_mandatory_attributes/5,
                             get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes/10]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(table_access).
:- use_module(utility).

tab_get_attribute_values([], _, _, _, _, []) :- !.
tab_get_attribute_values([col(X29, X30)|X33], col(X29, X18), X14, X10, X26, X1) :- 
    tab_get_arity(col(X29,_), X35),
    ((X14 = [], X10 = []) ->
        tab_get_min(col(X29, X18), X19),
        tab_get_max(col(X29, X18), X20),
        X11 is X20 - X19
    ;
        X19   = 0,
        X11 = 1
    ),
    findall(X31-X28, (functor(X32, X29, X35),             
                         call(user:X32),                     
                         arg(X18, X32, X27),       
                         ((X14 = [], X10 = []) ->
                             X28 is X27 - X19   
                         ;
                             (memberchk(X27, X14 ) -> X28 is 1 ;
                              memberchk(X27, X10) -> X28 is 0 ;
                                                                 false       )
                         ),
                         arg(X30, X32, X31)), X21),
    sort(X21, X2),                        

    
    
    
    
    
    (X11 = 1 ->
        generate_oplus_lists_from_val_target_pairs(X2, X11, 0, X26,
                                                   [X22,       X15,
                                                    X25,        X23,
                                                    X4,  X3,
                                                    X7,    X5,
                                                    X12,     X8]),
        X1 = [attr_eq([ and,      0, col(X29, X30), X22]),
                            attr_neq([and,      0, col(X29, X30), X15]),
                            attr_eq([ or,       0, col(X29, X30), X25]),
                            attr_neq([or,       0, col(X29, X30), X23]),
                            attr_eq([ allequal, 0, col(X29, X30), X4]),
                            attr_neq([allequal, 0, col(X29, X30), X3]),
                            attr_eq([ and,      1, col(X29, X30), X7]),
                            attr_neq([and,      1, col(X29, X30), X5]),
                            attr_eq([ or,       1, col(X29, X30), X12]),
                            attr_neq([or,       1, col(X29, X30), X8]),
                            attr_eq([ allequal, 1, col(X29, X30), X4]),
                            attr_neq([allequal, 1, col(X29, X30), X3])|X36]
    ;
        generate_oplus_lists_from_val_target_pairs(X2, X11, 0, X26,
                                                   [X24,    X16,
                                                    X9, X6,
                                                    X17,   X13]),
        X1 = [attr_eq([ sum,       0, col(X29, X30), X24]),
                            attr_neq([sum,       0, col(X29, X30), X16]),
                            attr_eq([ sum,       1, col(X29, X30), X9]),
                            attr_neq([sum,       1, col(X29, X30), X6]),
                            attr_eq([ and,       0, col(X29, X30), X17]),
                            attr_neq([and,       0, col(X29, X30), X13]),
                            attr_eq([ and,       1, col(X29, X30), X17]),
                            attr_neq([and,       1, col(X29, X30), X13]),
                            attr_eq([ or,        0, col(X29, X30), X17]),
                            attr_neq([or,        0, col(X29, X30), X13]),
                            attr_eq([ or,        1, col(X29, X30), X17]),
                            attr_neq([or,        1, col(X29, X30), X13]),
                            attr_eq([ allequal,  0, col(X29, X30), X17]),
                            attr_neq([allequal,  0, col(X29, X30), X13]),
                            attr_eq([ allequal,  1, col(X29, X30), X17]),
                            attr_neq([allequal,  1, col(X29, X30), X13])|X36]
    ),
    tab_get_attribute_values(X33, col(X29, X18), X14, X10, X26, X36).



tab_get_binary_term_values([X8|X4], X5, X2, X1, X3, X10, X11) :- !,
    (memberchk(X3, [plus,abs,min,max,prod]) ->                       
        findall(X12-X13, (member(X12,[X8|X4]), X12 = col(_,X14),
                            member(X13,[X8|X4]), X13 = col(_,X15),
                            X15 > X14), X9)
    ;
     memberchk(X3, [minus,floor,ceil,mfloor,mod,cmod,dmod,fmod]) ->  
        findall(X12-X13, (member(X12,[X8|X4]), X12 = col(_,X14),
                            member(X13,[X8|X4]), X13 = col(_,X15),
                            X15 =\= X14), X9)
    ;
        write(tab_get_binary_term_values(X3)), nl, halt
    ),
    ((X2 = [], X1 = []) ->
        tab_get_min(X5, X6),
        tab_get_max(X5, X7)
    ;
        X6 = 0,
        X7 = 1
    ),
    tab_get_binary_term_values0(X9, X5, X2, X1, X3, X6-X7, X10, X11).
tab_get_binary_term_values([], _, _, _, _, _, _) :- write(tab_get_binary_term_values), nl, halt.

tab_get_binary_term_values0([], _, _, _, _, _, _, []) :- !.
tab_get_binary_term_values0([col(X30, X31)-col(X30, X32)|X37], col(X30, X19), X14, X10, X15, X20-X21, X27, X1) :- 
    tab_get_arity(col(X30,_), X39),
    X11 is X21 - X20,
    findall(X35-X29, (functor(X36, X30, X39),             
                         call(user:X36),                     
                         arg(X19, X36, X28),       
                         ((X14 = [], X10 = []) ->
                             X29 is X28 - X20   
                         ;
                             (memberchk(X28, X14 ) -> X29 is 1 ;
                              memberchk(X28, X10) -> X29 is 0 ;
                                                                 false       )
                         ),
                         arg(X31, X36, X33),
                         arg(X32, X36, X34),
                         binary_term_calculation(X15,X33,X34,col(X30, X32), X35)), X22),
    sort(X22, X2),                        

    
    
    
    
    
    (X11 = 1 ->
        generate_oplus_lists_from_val_target_pairs(X2, X11, 0, X27,
                                                   [X23,       X16,
                                                    X26,        X24,
                                                    X4,  X3,
                                                    X7,    X5,
                                                    X12,     X8]),
        X1 = [binary_eq([ X15, and,      0, col(X30, X31),col(X30, X32), X23]),
                            binary_neq([X15, and,      0, col(X30, X31),col(X30, X32), X16]),
                            binary_eq([ X15, or,       0, col(X30, X31),col(X30, X32), X26]),
                            binary_neq([X15, or,       0, col(X30, X31),col(X30, X32), X24]),
                            binary_eq([ X15, allequal, 0, col(X30, X31),col(X30, X32), X4]),
                            binary_neq([X15, allequal, 0, col(X30, X31),col(X30, X32), X3]),
                            binary_eq([ X15, and,      1, col(X30, X31),col(X30, X32), X7]),
                            binary_neq([X15, and,      1, col(X30, X31),col(X30, X32), X5]),
                            binary_eq([ X15, or,       1, col(X30, X31),col(X30, X32), X12]),
                            binary_neq([X15, or,       1, col(X30, X31),col(X30, X32), X8]),
                            binary_eq([ X15, allequal, 1, col(X30, X31),col(X30, X32), X4]),
                            binary_neq([X15, allequal, 1, col(X30, X31),col(X30, X32), X3])|X40]
    ;
        generate_oplus_lists_from_val_target_pairs(X2, X11, 0, X27,
                                                   [X25,    X17,
                                                    X9, X6,
                                                    X18,   X13]),
        X1 = [binary_eq([ X15, sum,       0, col(X30, X31),col(X30, X32), X25]),
                            binary_neq([X15, sum,       0, col(X30, X31),col(X30, X32), X17]),
                            binary_eq([ X15, sum,       1, col(X30, X31),col(X30, X32), X9]),
                            binary_neq([X15, sum,       1, col(X30, X31),col(X30, X32), X6]),
                            binary_eq([ X15, and,       0, col(X30, X31),col(X30, X32), X18]),
                            binary_eq([ X15, and,       0, col(X30, X31),col(X30, X32), X18]),
                            binary_neq([X15, and,       1, col(X30, X31),col(X30, X32), X13]),
                            binary_neq([X15, and,       1, col(X30, X31),col(X30, X32), X13]),
                            binary_eq([ X15, or,        0, col(X30, X31),col(X30, X32), X18]),
                            binary_eq([ X15, or,        0, col(X30, X31),col(X30, X32), X18]),
                            binary_neq([X15, or,        1, col(X30, X31),col(X30, X32), X13]),
                            binary_neq([X15, or,        1, col(X30, X31),col(X30, X32), X13]),
                            binary_eq([ X15, allequal,  0, col(X30, X31),col(X30, X32), X18]),
                            binary_neq([X15, allequal,  0, col(X30, X31),col(X30, X32), X13]),
                            binary_eq([ X15, allequal,  1, col(X30, X31),col(X30, X32), X18]),
                            binary_neq([X15, allequal,  1, col(X30, X31),col(X30, X32), X13])|X40]
    ),
    tab_get_binary_term_values0(X37, col(X30, X19), X14, X10, X15, X20-X21, X27, X40).

tab_get_unary_term_values([X10|X5], X6, X3, X2, X7, X11, X4) :- !,
   ((X3 = [], X2 = []) ->
        tab_get_min(X6, X8),
        tab_get_max(X6, X9)
   ;
        X8 = 1,
        X9 = 0
   ),
   (X7 = mod ->                                             
       findall(X12-X13, (member(X12, [X10|X5]),
                            X13 in 2..X11, indomain(X13)),
               X1)
   ;
       write(tab_get_unary_term_values(X7)),nl,halt
   ),                                                              
   tab_get_unary_term_values0(X1, X6, X3, X2, X7, X8-X9, X11, X4).
tab_get_unary_term_values([], _, _, _, _, _, _) :- write(tab_get_unary_term_values), nl, halt.

tab_get_unary_term_values0([], _, _, _, _, _, _, []) :- !.
tab_get_unary_term_values0([col(X30, X32)-X33|X36], col(X30, X18), X14, X10, X19, X20-X21, X27, X1) :- 
    tab_get_arity(col(X30,_), X38),
    X11 is X21 - X20,
    (X19 = mod ->
        findall(X34-X29, (functor(X35, X30, X38),            
                             call(user:X35),                    
                             arg(X18, X35, X28),      
                             ((X14 = [], X10 = []) ->
                                X29 is X28 - X20   
                             ;
                                (memberchk(X28, X14 ) -> X29 is 1 ;
                                 memberchk(X28, X10) -> X29 is 0 ;
                                                                    false       )
                             ),
                             arg(X32, X35, X31),
                             X34 is X31 mod X33),              X22)
    ;
        X22 = []
    ),
    sort(X22, X2),                           
    
    
    
    
    
    (X11 = 1 ->
        generate_oplus_lists_from_val_target_pairs(X2, X11, -X27, X27,
                                                   [X23,       X15,
                                                    X26,        X24,
                                                    X4,  X3,
                                                    X7,    X5,
                                                    X12,     X8]),
        X1 = [unary_term_eq([ X19, and,      0, col(X30, X32), X33, X23]),
                            unary_term_neq([X19, and,      0, col(X30, X32), X33, X15]),
                            unary_term_eq([ X19, or,       0, col(X30, X32), X33, X26]),
                            unary_term_neq([X19, or,       0, col(X30, X32), X33, X24]),
                            unary_term_eq([ X19, allequal, 0, col(X30, X32), X33, X4]),
                            unary_term_neq([X19, allequal, 0, col(X30, X32), X33, X3]),
                            unary_term_eq([ X19, and,      1, col(X30, X32), X33, X7]),
                            unary_term_neq([X19, and,      1, col(X30, X32), X33, X5]),
                            unary_term_eq([ X19, or,       1, col(X30, X32), X33, X12]),
                            unary_term_neq([X19, or,       1, col(X30, X32), X33, X8]),
                            unary_term_eq([ X19, allequal, 1, col(X30, X32), X33, X4]),
                            unary_term_neq([X19, allequal, 1, col(X30, X32), X33, X3])|X39]
    ;
        generate_oplus_lists_from_val_target_pairs(X2, X11, -X27, X27,
                                                   [X25,    X16,
                                                    X9, X6,
                                                    X17,   X13]),
        X1 = [unary_term_eq([ X19, sum,       0, col(X30, X32), X33, X25]),
                            unary_term_neq([X19, sum,       0, col(X30, X32), X33, X16]),
                            unary_term_eq([ X19, sum,       1, col(X30, X32), X33, X9]),
                            unary_term_neq([X19, sum,       1, col(X30, X32), X33, X6]),
                            unary_term_eq([ X19, and,       0, col(X30, X32), X33, X17]),   
                            unary_term_neq([X19, and,       0, col(X30, X32), X33, X13]),
                            unary_term_eq([ X19, and,       1, col(X30, X32), X33, X17]),
                            unary_term_neq([X19, and,       1, col(X30, X32), X33, X13]),
                            unary_term_eq([ X19, or,        0, col(X30, X32), X33, X17]),
                            unary_term_neq([X19, or,        0, col(X30, X32), X33, X13]),
                            unary_term_eq([ X19, or,        1, col(X30, X32), X33, X17]),
                            unary_term_neq([X19, or,        1, col(X30, X32), X33, X13]),
                            unary_term_eq([ X19, allequal,  0, col(X30, X32), X33, X17]),
                            unary_term_neq([X19, allequal,  0, col(X30, X32), X33, X13]),
                            unary_term_eq([ X19, allequal,  1, col(X30, X32), X33, X17]),
                            unary_term_neq([X19, allequal,  1, col(X30, X32), X33, X13])|X39]
    ),
    tab_get_unary_term_values0(X36,  col(X30, X18), X14, X10, X19, X20-X21, X27, X39).

tab_get_unaryf_values(X6, col(_, X3), X2, X1, X9, X7, X10) :- 
    (X9 = prod ->
        findall(X11-X12, (member(X11,X6), X11 = col(_,X13),
                            member(X12,X6), X12 = col(_,X14),
                            X14 =\= X13), X4)
    ;
        write(tab_get_unaryf_values(X9)), nl, halt
    ),
    append(X2, X1, X5),
    tab_get_unaryf_values0(X4, X3, X5, X9, X7, X10).

tab_get_unaryf_values0([], _, _, _, _, []) :- !.
tab_get_unaryf_values0([col(X16, X17)-col(X16, X18)|X23], X7, X9, X14, X11,[X6,X4,X5|X24]) :- 
    tab_get_arity(col(X16,_), X26),
    (X14 = prod ->
        findall(X21, (X21 in 2..X11, indomain(X21),          
                      findall(X10, (functor(X22, X16, X26), 
                                         call(user:X22),         
                                         arg(X7, X22, X15),       
                                         (X9 = [] -> true ; memberchk(X15, X9)),
                                         arg(X17, X22, X19),   
                                         arg(X18, X22, X20),
                                         X12 is X21 * X20,
                                         (X19 = X12 -> X10 = 1 ; X10 = 0)), X8),
                      memberchk(0, X8),                   
                      memberchk(1, X8)),
                X3),
        findall(X21, (X21 in 2..X11, indomain(X21),          
                      findall(X10, (functor(X22, X16, X26), 
                                         call(user:X22),         
                                         arg(X7, X22, X15),       
                                         (X9 = [] -> true ; memberchk(X15, X9)),
                                         arg(X17, X22, X19),   
                                         arg(X18, X22, X20),
                                         X12 is X21 * X20,
                                         (X19 =< X12 -> X10 = 1 ; X10 = 0)), X8),
                      memberchk(0, X8),                   
                      memberchk(1, X8)),
                X1),
        findall(X21, (X21 in 2..X11, indomain(X21),          
                      findall(X10, (functor(X22, X16, X26), 
                                         call(user:X22),         
                                         arg(X7, X22, X15),       
                                         (X9 = [] -> true ; memberchk(X15, X9)),
                                         arg(X17, X22, X19),   
                                         arg(X18, X22, X20),
                                         X13 is X21 * X19,
                                         (X13 =< X20 -> X10 = 1 ; X10 = 0)), X8),
                      memberchk(0, X8),                   
                      memberchk(1, X8)),
                X2)
    ;
        X3 = []
    ),
    X6  = unary_aequ([ X14,col(X16, X17),col(X16, X18),X3 ]),
    X4 = unary_alequ([X14,col(X16, X17),col(X16, X18),X1]),
    X5 = unary_uleqa([X14,col(X16, X17),col(X16, X18),X2]),
    tab_get_unaryf_values0(X23, X7, X9, X14, X11, X24).

tab_get_ternary_values(X7, col(_, X4), X3, X1, X2, X9) :- 
    findall([X10,X11,X12], (member(X10,X7), X10 = col(_,X13),
                               member(X11,X7), X11 = col(_,X14),
                               member(X12,X7), X12 = col(_,X15),
                               X13 =\= X14, X13 =\= X15, X14 =\= X15), X5),
    append(X3, X1, X6),
    tab_get_ternary_values0(X5, X4, X6, X2, X9).

tab_get_ternary_values0([], _, _, _, []) :- !.
tab_get_ternary_values0([[col(X10, X13),col(X10, X14),col(X10,X15)]|X21], X3, X4, X2, X6) :- 
    tab_get_arity(col(X10,_), X23),
    (X2 = sum_leq_attr ->
        findall(X5, (functor(X19, X10, X23), 
                           call(user:X19),         
                           arg(X3, X19, X7),       
                           (X4 = [] -> true ; memberchk(X7, X4)),
                           arg(X13, X19, X16),   
                           arg(X14, X19, X17),
                           arg(X15, X19, X18),
                           X11 is X16 + X17,
                           (X11 < X18 ->
                                X5 = 1
                           ;
                            X11 = X18 ->
                                X5 = 2
                           ;
                                X5 = 0
                           )
                          ), X1),
        ((memberchk(0, X1),     
          memberchk(1, X1),     
          memberchk(2, X1)) ->  
            X6 = [ternary_set([col(X10, X13), col(X10, X14), col(X10, X15)], X2)|X24]
        ;
            X6 = X24
        )
    ;
     X2 = minus_mod_eq0 ->
        
        findall(X5, (functor(X19, X10, X23), 
                           call(user:X19),         
                           arg(X3, X19, X7),       
                           (X4 = [] -> true ; memberchk(X7, X4)),
                           arg(X13, X19, X16),   
                           arg(X14, X19, X17),
                           arg(X15, X19, X18),
                           X12 is X18 - X16,
                           X17 =\= 0,
                           X20 is X12 mod X17,
                           (X20 is 0 ->
                                X5 = 1
                           ;
                                X5 = 0
                           )
                          ), X1),
        ((memberchk(0, X1),    
          memberchk(1, X1)) -> 
            X6 = [ternary_set([col(X10, X13), col(X10, X14), col(X10, X15)], X2)|X24]
        ;
            X6 = X24
        )
    ;
     X2 = ceil_leq_floor ->
        
        
        findall(X5, (functor(X19, X10, X23), 
                           call(user:X19),         
                           arg(X3, X19, X7),       
                           (X4 = [] -> true ; memberchk(X7, X4)),
                           arg(X13, X19, X16),   
                           arg(X14, X19, X17),
                           arg(X15, X19, X18),
                           X17 =\= 0, X18 =\= 0,
                           X8 is (X16 - X18 + X17 - 1) // X17,
                           X9 is (X16 - X17) // X18,
                           (X8 =< X9 ->
                                X5 = 1
                           ;
                                X5 = 0
                           )
                          ), X1),
        ((memberchk(0, X1),    
          memberchk(1, X1)) -> 
            X6 = [ternary_set([col(X10, X13), col(X10, X14), col(X10, X15)], X2)|X24]
        ;
            X6 = X24
        )
    ;
        write(tab_get_ternary_values0(X2)),nl,halt
    ),
    tab_get_ternary_values0(X21, X3, X4, X2, X24).

gen_compatible_unary_and_binary_and_ternary(X1, X2, X3) :-
    X8 in 0..X1,
    X9 in 0..X1,
    X10 in 0..X1,
    X8+X9+X10 #= X1,
    X8+2*X9+3*X10 #>= X2,            
    X4 in 0..1, X4 #= min(1,X8), 
    X5 in 0..2, X5 #= min(2,X9), 
    X6 in 0..3, X6 #= min(3,X10), 
    X7  in 0..3,
    maximum(X7, [X4,X5,X6]), 
    X7 #=< X2,                  
    !,
    findall([X8,X9,X10], labeling([], [X8,X9,X10]), X3).
gen_compatible_unary_and_binary_and_ternary(_, _, []).

generate_oplus_lists_from_val_target_pairs(X1, X20, X18, X19,
                                           [X15,                                          
                                            X14,                                         
                                            X17,                                           
                                            X16,                                          
                                            X3,                                     
                                            X2,                                    
                                            X10,                                       
                                            X5,                                      
                                            X13,                                        
                                            X11]):-                                    
    X20 = 1,
    !,

    (foreach(X-_, X1),                                                             
     foreach(X,     X6) do true),                                                    
    sort(X6,X7),                                                          
    (X7 = [_,_|_] ->                                                                 
        X12 = X7                                                            
    ;                                                                                           
        X12 = []                                                                       
    ),                                                                                          
    remove_first_last_elements(X12,                                                    
                               X8),                                                  
                                                                                                

    findall(X21, (member(X21,X12),  X21 =< X19, X21 >= X18), X3),  
    findall(X21, (member(X21,X8), X21 =< X19, X21 >= X18), X2), 

    split_value_target_pairs(X1, X20, X4, X9),           
    
    findall(X21, (member(X21,X9),                                                    
                  X21 =< X19, X21 >= X18),                                              
                                                   X15),                                  

    intersect_lists(X15,                                                                  
                    X2,                                                            
                    X14),                                                                

    remove_elements_from_list(X3,                                                   
                              X4,                                                   
                              X17),                                                        
                                                                                                
    
    remove_elements_from_list(X2,                                                  
                              X4,                                                   
                              X16),                                                       
                                                                                                

    findall(X21, (member(X21,X4),                                                   
                  X21 =< X19, X21 >= X18),                                              
                                                   X10),                               

    intersect_lists(X10,                                                               
                    X2,                                                            
                    X5),                                                             
    
    remove_elements_from_list(X3,                                                   
                              X9,                                                    
                              X13),                                                     
    
    remove_elements_from_list(X2,                                                  
                              X9,                                                    
                              X11).                                                    


generate_oplus_lists_from_val_target_pairs(X1, X17, X15, X16,
                                           [X13,                                          
                                            X10,                                         
                                            X6,                                       
                                            X2,                                      
                                            X11,                                         
                                            X9]):-                                     
    (foreach(X-_, X1),                                                             
     foreach(X,     X3) do true),                                                    
    sort(X3,X7),                                                           
                                                                                                
    remove_first_last_elements(X7,                                                    
                               X4),                                                  
                                                                                                
    findall(X18, (member(X18,X7),  X18 =< X16, X18 >= X15), X14),       
    findall(X18, (member(X18,X4), X18 =< X16, X18 >= X15), X12),      
    split_value_target_pairs(X1, X17, X5, X8),             

    X11 = X14, X9 = X12,                                           
                                                                                                

    remove_elements_from_list(X14,                                                        
                              X5,                                                    
                              X13),                                                       
                                                                                                

    remove_elements_from_list(X12,                                                       
                              X5,                                                    
                              X10),                                                      
                                                                                                
    
    remove_elements_from_list(X14,  X8, X6),                          
    remove_elements_from_list(X12, X8, X2).                         

split_value_target_pairs([], _, [], []):- !.
split_value_target_pairs([X-0|X3], X1, [X|X4], X5):- !,
    split_value_target_pairs(X3, X1, X4, X5).
split_value_target_pairs([X-X1|X3], X1, X4, [X|X5]):- !,
    split_value_target_pairs(X3, X1, X4, X5).
split_value_target_pairs([_|X3], X1, X4, X5):- !,
    split_value_target_pairs(X3, X1, X4, X5).

get_set_of_values_for_each_mandatory_attribute(X2, X8, X12, X11, X10, X3,
                                               X4, X5, [[1,X4]|X1]):-
    length(X2,X13),
    select_oplus_for_the_set_search(X12, X6),
    
    
    findall([X14,X9],(X16 in 1..X13, indomain(X16),
                              nth1(X16,X2,X15),
                              (X10 = attr_eq_coef ->
                                   memberchk(attr_eq([ X6,X11,X15,X7]), X3)
                              ;
                               memberchk(X10, [attr_leq_coef,attr_geq_coef]) ->
                                   memberchk(attr_neq([X6,X11,X15,X7]), X3)
                              ;
                                   write(get_set_of_values_for_each_mandatory_attribute(X16-X14,X6,X11)),nl,halt
                              ),
                              member(X9,X7),
                              X9 >= X4,
                              X9 =< X5,
                              X14 is X16 + X8), X1).

get_set_of_unaryf_values_for_each_pair_of_mandatory_attributes(X2, X8, X9, X4, X3,
                                                               X5, X6, [[1,1,X5]|X1]):-
    length(X2,X13),
    findall([X11,X12,X10],(X16 in 1..X13, X17 in 1..X13, indomain(X16),indomain(X17), X16 =\= X17,
                                     nth1(X16,X2,X14),
                                     nth1(X17,X2,X15),
                                     (X9 = attr_eq_unary ->
                                        memberchk(unary_aequ([X4,X14,X15,X7]),  X3)
                                     ;
                                      X9 = attr_leq_unary ->
                                        memberchk(unary_alequ([X4,X14,X15,X7]), X3)
                                     ;
                                        memberchk(unary_uleqa([X4,X14,X15,X7]), X3)
                                     ),
                                     member(X10,X7),
                                     X10 >= X5,
                                     X10 =< X6,
                                     X11 is X16 + X8,
                                     X12 is X17 + X8), X1).

get_set_of_ternary_triplets_of_mandatory_attributes(X1, X4, X5, X3,
                                                    [[1,1,1]|X2]):-
    length(X1,X9),
    findall([X6,X7,X8],(X13 in 1..X9, X14 in 1..X9, indomain(X13),indomain(X14), X13 =\= X14,
                                 nth1(X13,X1,X10),
                                 nth1(X14,X1,X11),
                                 nth1(X15,X1,X12),
                                 memberchk(ternary_set([X10,X11,X12], X5),  X3),
                                 X6 is X13 + X4,
                                 X7 is X14 + X4,
                                 X8 is X15 + X4), X2).

get_set_of_unary_term_values_for_each_mandatory_attribute(X2, X10, X16, X15, X13, X11, X3,
                                                          X7, X8, X4, X5, [[1,X7,X4]|X1]):-
    length(X2,X17),
    select_oplus_for_the_set_search(X16, X6),
    
    
    findall([X18,X14,X12],(X20 in 1..X17, indomain(X20),
                                       nth1(X20,X2,X19),
                                       X14 in X7..X8,
                                       indomain(X14),
                                       (X13 = unary_term_eq_coef ->
                                          memberchk(unary_term_eq([X11,X6,X15,X19,X14,X9]), X3)
                                       ;
                                        memberchk(X13, [unary_term_leq_coef,unary_term_geq_coef]) ->
                                          memberchk(unary_term_neq([X11,X6,X15,X19,X14,X9]), X3)
                                       ;
                                          write(get_set_of_unary_term_values_for_each_mandatory_attribute(X11,X6,X15)),nl,halt
                                       ),
                                       member(X12,X9),
                                       X12 >= X4,
                                       X12 =< X5,
                                       X18 is X20 + X10), X1).

get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X2, X9, X13, X12, X11, X7, X3,
                                                                    X4, X5, [[1,1,X4]|X1]):-
    length(X2,X16),
    select_oplus_for_the_set_search(X13, X6),
    findall([X14,X15,X10],(X19 in 1..X16, X20 in 1..X16, indomain(X19),indomain(X20), X19 =\= X20,
                                     nth1(X19,X2,X17),
                                     nth1(X20,X2,X18),
                                     (X11 = binary_term_eq_coef ->
                                        memberchk(binary_eq([ X7,X6,X12,X17,X18,X8]), X3)
                                     ;
                                      memberchk(X11, [binary_term_leq_coef,binary_term_geq_coef]) ->
                                        memberchk(binary_neq([X7,X6,X12,X17,X18,X8]), X3)
                                     ;
                                        write(get_set_of_binary_term_values_for_each_pair_of_mandatory_attributes(X11,X7,X6,X17,X18)), nl, halt
                                     ),
                                     member(X10,X8),
                                     X10 >= X4,
                                     X10 =< X5,
                                     X14 is X19 + X9,
                                     X15 is X20 + X9), X1).

select_oplus_for_the_set_search(X2, X1) :-
    (memberchk(X2, [xor,voting,card1]) -> X1 = allequal; X1 = X2).      
                                                                                                
                                                                                                
                                                                                                
                                                                                                
                                                                                                
