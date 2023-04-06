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
% Purpose: FROM A FORMULA PATTERN GENERATE A PROLOG TERM (INTERNAL FORMULA FORMAT)
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_formula_term,[formula_pattern_create_term/2]).            
:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).
:- use_module(table_access).



formula_pattern_create_term(X1, X2) :-
    (formula_pattern(f(_), X1) ->
        formula_pattern_create_term_formula(X1, X2) 
    ;
     formula_pattern(cond_ex, X1) ->
        formula_pattern_create_term_cond(X1, X2)    
    ;
     formula_pattern(op(_), X1) ->
        formula_pattern_create_term_bool(X1, X2)    
    ;
     formula_pattern(option(_,_,_), X1) ->
        formula_pattern_create_term_case(X1, X2)    
    ;
        formula_pattern_create_term_cond(X1, X2)    
    ).

formula_pattern_create_term_case(X2, X7) :-
    length(X2, X3),
    length(X8, X3),
    formula_pattern_create_term_case1(X2, X8),
    formula_pattern_create_term_case2(X8, X5, X4, X6, X1),
    X7 = t(X5, X4, X6, cases(X1)).

formula_pattern_create_term_case1([option(_,X1,X2)|X7], [X3|X8]) :-
    !,
    (integer(X2) ->
        X4 = t([],[],[],X2)
    ;
        formula_pattern_create_term(X2, X4)
    ),
    (integer(X1) ->
        X5 = t([],[],[],X1)
    ;
        formula_pattern_create_term(X1, X5)
    ),
    X3 = if_then(X4, X5),
    formula_pattern_create_term_case1(X7, X8). 
formula_pattern_create_term_case1([option(X1)], [X2]) :-
    (integer(X1) ->
        X2 = otherwise(t([],[],[],X1))
    ;
        formula_pattern_create_term(X1, X2)
    ).

formula_pattern_create_term_case2([X20|X24], X2, X1, X3, [X19|X25]) :-
    !,
    (X20 = if_then(t(X9, X4, X10, X21),
                        t(X11, X5, X12, X22)) ->
        merge_lists(X9,X11,X13),
        merge_lists(X13,X14,X2),

        merge_lists(X4,X5,X6),
        merge_lists(X6,X7,X1),

        merge_lists(X10,X12,X15),
        merge_lists(X15,X16,X3),
        
        X19 = if_then(X21, X22)
    ;
     X20 = otherwise(t(X17, X8, X18, X23)) ->
        merge_lists(X17,X14,X2),
        merge_lists(X8,X7,X1),
        merge_lists(X18,X16,X3),
        X19 = otherwise(X23)
    ;
        write(formula_pattern_create_term_case2(X20)),nl,halt
    ),
    formula_pattern_create_term_case2(X24, X14, X7, X16, X25).
formula_pattern_create_term_case2([], [], [], [], []).


formula_pattern_create_term_bool(X3, X5) :-
    formula_pattern(mandatory_attr(X7), X3),                              
    formula_pattern(neg(X9),              X3),                              
    formula_pattern(shift(X8),          X3),                              
                                                                                             
    formula_pattern(op(X13),                 X3),                              
                                                                                             
    formula_pattern(nb_terms(X10),         X3),                              
    formula_pattern(conds(X14),              X3),                              
    findall(X11, member(X11, X7),                            X2), 
    findall(X15,  (member(X16,   X7), tab_get_name(X16, X15)), X6),      
    length(X7, X4),                                                        
    length(X1, X4),                                            
    formula_pattern_create_bool_conds(X14, X12, X13, X1),
    X5 = t(X2, X6, X1, bool(X9,X8,X13,X10,X12)). 

formula_pattern_create_bool_conds([], [], _, _) :- !.
formula_pattern_create_bool_conds([X22|X24], X14, X18, X1) :-
    X22 = cond(X19, X20, _, _, _,
                X15, X16, X17, X23, X21,
                _, _, _, _, _),
    (X19 = -1 ->
        X14 = X25
    ;
        X8 is X15-1, 
        X9 is X16-1, 
        X10 is X17-1,
        formula_pattern_create_term_condition(X1, X19, X20,
                                              X8, X9, X10,
                                              X23, X21, X13),
        X14 = [X13|X25]
    ),
    formula_pattern_create_bool_conds(X24, X25, X18, X1).

formula_pattern_create_term_cond(X3, X6) :-
    formula_pattern(mandatory_attr(X8),                                          X3),
    formula_pattern(then(X24, X15, X16,         X32, X25, _, _, _, _, _, _), X3),
    formula_pattern(else(X26, X17, X18,         X33, X27, _, _, _, _, _, _), X3),
    findall(X19, member(X19, X8),                            X2), 
    findall(X34,  (member(X35,   X8), tab_get_name(X35, X34)), X7),      
    length(X8, X4),                                                        
    length(X1, X4),                                            
    (formula_pattern(cond_ex, X3) ->
        formula_pattern(neg(X13),              X3),                              
        formula_pattern(shift(X9),          X3),                              
                                                                                                 
        formula_pattern(op(X28),                 X3),                              
                                                                                                 
        formula_pattern(nb_terms(X14),         X3),                              
        formula_pattern(conds(X29),              X3),                              
        formula_pattern_create_bool_conds(X29, X20, X28, X1),
        X10 = bool(X13,X9,X28,X14,X20),
        X5 = no
    ;
        formula_pattern(cond(X30, X21, X22, X23, X36, X31, _, _, _, _, _, _), X3),
        formula_pattern_create_term_condition(X1, 1, X30, X21, X22, X23, X36, X31, X10),
        (X30 = attr_eq_coef ->         
                X5 = X21-X31  
        ;
                X5 = no
        )
    ),
    formula_pattern_create_term_then_else(X1, X24, X15, X16, X32, X25, X11, X5),
    formula_pattern_create_term_then_else(X1, X26, X17, X18, X33, X27, X12, no),
    X6 = t(X2, X7, X1, if(X10, X11, X12)).

formula_pattern_create_term_condition(X1, 0, X7, X4, X5, X6, X9, X8, X3) :- !,
    X3 = not(X2),
    formula_pattern_create_term_condition(X1, 1, X7, X4, X5, X6, X9, X8, X2).
formula_pattern_create_term_condition(X1, 1, X11, X5, X6, X7, X14, X12, X2) :-
    functor(X11, X3, _),
    (memberchk(X3, [attr_eq_coef,       attr_eq_attr,       attr_eq_unary,
                          unary_term_eq_coef, binary_term_eq_coef              ]) ->
        X2 = eq(X15,X16)
    ;
     X3 = attr_in_interval ->
        X2 = in(X15,X16,X17)
    ;
     X3 = sum_leq_attr -> 
        
        X2 = leq(sum(X15,X16),X17)
    ;
     X3 = minus_mod_eq0 -> 
        
        X2 = eq(mod(minus(X17,X15),X16),0)
    ;
     X3 = ceil_leq_floor -> 
        
        X2 = leq(ceil(minus(X15,X17),X16),floor(minus(X15,X16),X17))
    ;
     memberchk(X3, [attr_geq_coef,unary_term_geq_coef,binary_term_geq_coef]) ->
        X2 = geq(X15,X16)
    ;
        X2 = leq(X15,X16)
    ),
    (memberchk(X3, [attr_eq_attr,attr_leq_attr]) ->
        nth1(X5, X1, X15),
        nth1(X6, X1, X16)
    ;
     memberchk(X3, [attr_eq_coef,attr_leq_coef,attr_geq_coef]) ->
        nth1(X5, X1, X15),
        X16 = X12
    ;
     X3 = attr_in_interval ->
        nth1(X5, X1, X15),
        X16 = X14,
        X17 = X12
    ;
     memberchk(X3, [attr_eq_unary,attr_leq_unary]) ->
        arg(1, X11, X18),
        nth1(X5, X1, X15),
        functor(X16, X18, 2),
        nth1(X6, X1, X8),
        arg(1, X16, X8),
        arg(2, X16, X14)
    ;
     X3 = unary_leq_attr ->
        arg(1, X11, X18),
        functor(X15, X18, 2),
        nth1(X5, X1, X9),
        arg(1, X15, X9),
        arg(2, X15, X14),
        nth1(X6, X1, X16)
    ;
     memberchk(X3, [unary_term_eq_coef,unary_term_leq_coef,unary_term_geq_coef]) ->
        arg(1, X11, X18),
        functor(X15, X18, 2),
        nth1(X5, X1, X9),
        arg(1, X15, X9),
        arg(2, X15, X14),
        X16 = X12
    ;
     memberchk(X3, [binary_term_eq_coef,binary_term_leq_coef,binary_term_geq_coef]) ->
        arg(1, X11, X18),
        (X18 = mfloor -> arg(2, X11, X4), X13 = 3 ; X13 = 2),
        functor(X15, X18, X13),
        nth1(X5, X1, X9),
        arg(1, X15, X9),
        nth1(X6, X1, X8),
        arg(2, X15, X8),
        (X18 = mfloor -> arg(3, X15, X4) ; true),
        X16 = X12
    ;
     X3 = linear_eq_coef ->
        functor(X15, linear, 4),
        nth1(X5, X1, X9),
        nth1(X6, X1, X8),
        nth1(X7, X1, X10),
        arg(1, X15, X9),
        arg(2, X15, X8),
        arg(3, X15, X10),
        arg(4, X15, X14),
        X16 = X12
    ;
     memberchk(X3, [sum_leq_attr,minus_mod_eq0,ceil_leq_floor]) ->
        nth1(X5, X1, X15),
        nth1(X6, X1, X16),
        nth1(X7, X1, X17)
    ;
        write(formula_pattern_create_term_condition(X3)), nl, halt
    ).

formula_pattern_create_term_then_else(X1, X11, X7, X8, X15, X12, X3, X2) :-
    functor(X11, X4, _),
    (X4 = coef ->
        X3 = X12
    ;
     X4 = attr ->
        (X2 = X7-X13 ->                    
            X3 = X13                               
        ;                                                  
            nth1(X7, X1, X3)
        )
    ;
     X4 = unary_term ->
        arg(1, X11, X16),
        (memberchk(X16,[max_min,min_min,floor_min]) -> arg(2, X11, X5), X14 = 3 ; X14 = 2),
        functor(X3, X16, X14),
        nth1(X7, X1, X9),
        arg(1, X3, X9),
        arg(2, X3, X15),
        (X14 = 3 -> arg(3, X3, X5) ; true)
    ;
     X4 = binary_term ->
        arg(1, X11, X16),
        (memberchk(X16, [linear,plus_min,plus_floor]) ->
            nth1(X7, X1, X9),
            nth1(X8, X1, X10),
            functor(X3, X16, 3),
            arg(1, X3, X9),
            arg(2, X3, X10),
            arg(3, X3, X15)
        ;
         X16 = minus_floor ->
            nth1(X7, X1, X9),
            nth1(X8, X1, X10),
            functor(X3, X16, 4),
            arg(1, X3, X9),
            arg(2, X3, X10),
            arg(3, X3, X15),
            arg(4, X3, X12)
        ;
            (X16 = mfloor -> arg(2, X11, X6), X14 = 3 ; X14 = 2),
            functor(X3, X16, X14),
            nth1(X7, X1, X9),
            arg(1, X3, X9),
            nth1(X8, X1, X10),
            arg(2, X3, X10),
            (X16 = mfloor -> arg(3, X3, X6) ; true)
        )
    ;
        write(formula_pattern_create_term_then_else), nl, halt
    ).

formula_pattern_create_term_formula(X3, X8) :-
    formula_pattern(f(X32),                                           X3),                  
    formula_pattern(nu(X30),                                         X3),                  
    formula_pattern(unary(X23),                                   X3),                  
    formula_pattern(binary(X22),                                 X3),                  
    formula_pattern(attributes_use(X5),                  X3),                  
    formula_pattern(mandatory_optional_attributes_names(X12), X3),                  
    length(X12, X24),                                                                         
    X25 is X24 + X30,                                                                              
    X10 = t(X24, X25, X23, X22, X5),                                       
    (X32 = 0 ->                                                                                         
        formula_pattern(cst(X28), X3),                                                    
        X8 = t([],[],[],X28)                                                                 
    ;
        memberchk(a(X26), X5),                                                           
        length(X26, X6),                                                                 
        findall(X13, (X33 in 1..X6,
                            indomain(X33),
                            nth1(X33, X26, 1),
                            nth1(X33, X12, X13)), X2),                        
        findall(X27, (member(X13,X2),tab_get_name(X13,X27)), X9),
        length(X1, X6),                                                 
        (X32 = 1 ->                                                                                     
            formula_pattern(polynoms([X20]), X3),                                     
            formula_pattern_create_polynom(X20, X12,                                        
                                           X1, 0, X10, X21),            
            X11 = polynom(X21),                                                            
            X8 = t(X2, X9, X1, X11)         
        ;
        X32 = 2 ->                                                                                      
            formula_pattern(unaryf([X7]),       X3),                           
            formula_pattern(polynoms([X20]),           X3),                           
            formula_pattern_create_polynom(X20, X12,                                        
                                           X1, 0, X10, X21),            
            functor(X7, X14, _),                                                     
            (memberchk(X14, [min,max,floor,mod,power]) ->
                arg(1, X7, X28),
                functor(X11, X14, 2),
                arg(1, X11, polynom(X21)),
                arg(2, X11, X28)
            ;
             memberchk(X14, [geq0, sum_consec]) ->
                functor(X11, X14, 1),
                arg(1, X11, polynom(X21))
            ;
             X14 = in ->
                arg(1, X7, X29),
                arg(2, X7, X31),
                X11 = in(polynom(X21), X29, X31)
            ;
                write(formula_pattern_create_term(X14)), nl, halt
            ),
            X8 = t(X2, X9, X1, X11)         
        ;
         X32 = 3 ->                                                                                     
            formula_pattern(binaryf([X4]),     X3),                           
            formula_pattern(polynoms([X16,X17]), X3),
            formula_pattern_create_polynom(X16, X12,                                       
                                           X1, 0, X10, X18),           
            formula_pattern_create_polynom(X17, X12,                                       
                                           X1, 0, X10, X19),           
            functor(X4, X15, _),
            (memberchk(X15, [min,max,floor,ceil,mod,cmod,dmod,prod]) ->
                functor(X11, X15, 2),
                arg(1, X11, polynom(X18)),
                arg(2, X11, polynom(X19)),
                X8 = t(X2, X9, X1, X11)     
            ;
                write(formula_pattern_create_term(X15)), nl, halt
            )
        ;
            write(formula_pattern_create_term(X32)), nl, halt
        )
    ).

formula_pattern_create_polynom([], _, _, _, _, []) :- !.
formula_pattern_create_polynom([t(_,_,0)], _, _, 1, _, []) :- !.                                   
formula_pattern_create_polynom([t(_,_,0)], _, _, 0, _, [monome([],0)]) :- !.                       
formula_pattern_create_polynom([t(_,_,0)|X6], X3, X1, X4, X2, X7) :- !, 
    formula_pattern_create_polynom(X6, X3, X1, X4, X2, X7).
formula_pattern_create_polynom([t(_,X6,X7)|X9], X4, X1, _, X3, [monome(X2,X7)|X10]) :-
    get_non_zero_exponents(X6, 1, X5),
    formula_pattern_create_rest_monome(X5, X4, X1, X3, X2),
    formula_pattern_create_polynom(X9, X4, X1, 1, X3, X10).

formula_pattern_create_rest_monome([], _, _, _, []) :- !.
formula_pattern_create_rest_monome([X13-X5|X14], X4, X2, X3, [t(X7,X5)|X15]) :-
    X3 = t(X9, X10, _, _, _),
    (X13 =< X9 ->                                                            
        nth1(X13, X2, X7)                                           
    ;
     X13 =< X10 ->                                                            
        X11 is X13 - X9,
        formula_pattern_create_unary_term(X11, X2, X3, X7)
    ;                                                                           
        X12 is X13 - X10,
        formula_pattern_create_binary_term(X4, X12, X2, X3, X7)
    ),
    formula_pattern_create_rest_monome(X14, X4, X2, X3, X15).

formula_pattern_create_unary_term(X12, X2, X3, X6) :-
    X3 = t(_, _, X10, _, X1),
    memberchk(u(X9), X1),
    nth1(X12, X9, X11),
    get_pos_value(X11, 1, 1, 1, [X18]),
    nth1(X18, X2, X13),
    nth1(X12, X10, X4),
    functor(X4, X16, _),
    (memberchk(X16, [min,max,floor,ceil,mod,geq,power]) -> arg(1, X4, X14), functor(X6, X16, 2), arg(1, X6, X13), arg(2, X6, X14) ;
     X16 = in                                           -> arg(1, X4, X15), arg(2, X4, X17), X6 = in(X13, X15, X17)                 ;
     X16 = sum_consec                                   -> X6 = sum_consec(X13)                                                                 ;
                                                          write(formula_pattern_create_unary_term(X16)), nl, halt                                   ).

formula_pattern_create_binary_term(X5, X18, X2, X3, X7) :-
    X3 = t(_, _, _, X11, X1),
    memberchk(b(X12), X1),
    nth1(X18, X12, X13),
    get_pos_value(X13, 1, 1, 2, [X19,X20]),
    nth1(X19, X2, X14),
    nth1(X20, X2, X15),
    nth1(X18, X11, X4),
    (X4 = min(_)    -> X7 = min(X14,X15)                                                ;
     X4 = max(_)    -> X7 = max(X14,X15)                                                ;
     X4 = floor(0)  -> X7 = floor(X14,X15)                                              ;
     X4 = floor(1)  -> X7 = floor(X15,X14)                                              ;
     X4 = mfloor(0) -> tab_get_mins_attr_names(X5, X6), nth1(X20, X6, X16),
                               X7 = mfloor(X14,X15,X16)                                        ;
     X4 = mfloor(1) -> tab_get_mins_attr_names(X5, X6), nth1(X19, X6, X17),
                               X7 = mfloor(X15,X14,X17)                                        ;
     X4 = ceil(0)   -> X7 = ceil(X14,X15)                                               ;
     X4 = ceil(1)   -> X7 = ceil(X15,X14)                                               ;
     X4 = mod(0)    -> X7 = mod(X14,X15)                                                ;
     X4 = mod(1)    -> X7 = mod(X15,X14)                                                ;
     X4 = cmod(0)   -> X7 = cmod(X14,X15)                                               ;
     X4 = cmod(1)   -> X7 = cmod(X15,X14)                                               ;
     X4 = dmod(0)   -> X7 = dmod(X14,X15)                                               ;
     X4 = dmod(1)   -> X7 = dmod(X15,X14)                                               ;
     X4 = fmod(0)   -> X7 = fmod(X14,X15)                                               ;
     X4 = fmod(1)   -> X7 = fmod(X15,X14)                                               ;
     X4 = prod(_)   -> X7 = prod(X14,X15)                                               ;
                               write(formula_pattern_create_binary_term(X4)), nl, halt        ).
