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
% Purpose: WRITE A FORMULA PATTERN TO THE CONSOLE
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_formula_write,[formula_pattern_write/1]).

:- use_module(library(lists)).
:- use_module(utility).
:- use_module(table_access).

formula_pattern_write(X1) :-
    (formula_pattern(f(_), X1) ->
        formula_pattern_write_formula(X1) 
    ;
     formula_pattern(cond_ex, X1) ->
        formula_pattern_write_cond(X1)    
    ;
     formula_pattern(op(_), X1) ->
        formula_pattern_write_bool(X1)    
    ;
     formula_pattern(option(_,_,_), X1) ->
        formula_pattern_write_case(X1)    
    ;
        formula_pattern_write_cond(X1)    
    ).

formula_pattern_write_cond(X1) :-
    formula_pattern(mandatory_attr(X3),                                          X1),
    formula_pattern(then(X11, X4, X5,         X17, X12, _, _, _, _, _, _), X1),
    formula_pattern(else(X13, X6, X7,         X18, X14, _, _, _, _, _, _), X1),
    write('('),
    (formula_pattern(cond_ex, X1) ->
        formula_pattern_write_bool(X1),
        X2 = no
    ;
        formula_pattern(cond(X15, X8, X9, X10, X19, X16, _, _, _, _, _, _), X1),
        formula_pattern_write_condition(X3, X15, X8, X9, X10, X19, X16),
        (X15 = attr_eq_coef ->         
                X2 = X8-X16  
        ;
                X2 = no
        )
    ),
    write(' ? '),
    formula_pattern_write_then_else(X3, X11, X4, X5, X17, X12, X2),
    write(' : '),
    formula_pattern_write_then_else(X3, X13, X6, X7, X18, X14, no),
    write(')').

formula_pattern_write_condition(X1, X12, X6, X7, X8, X16, X13) :-
    functor(X12, X3, X2),
    (memberchk(X3, [attr_eq_coef,
                          attr_eq_attr,
                          unary_term_eq_coef,
                          binary_term_eq_coef,
                          linear_eq_coef,
                          minus_mod_eq0]) ->                                                    
        X5 = '='
    ;
     X3 = attr_in_interval ->
        X5 = 'in'
    ;
        X5 = '=<'
    ),
    (X2 = 1 -> arg(1, X12, X14)                          ;                           
     X2 = 2 -> arg(1, X12, X14), arg(2, X12, X4) ;                           
                      true                                          ),
    (X6 > 0 -> get_attr_name(X6, X1, X9) ; true),                            
    (X7 > 0 -> get_attr_name(X7, X1, X10) ; true),                            
    (X8 > 0 -> get_attr_name(X8, X1, X11) ; true),                            
    (memberchk(X3,[attr_eq_attr,attr_leq_attr]) ->                                        
        write(X9), write(X5), write(X10)
    ;
     memberchk(X3,[attr_eq_coef,attr_leq_coef]) ->                                        
        write(X9), write(X5), write(X13)
    ;
     memberchk(X3,[attr_in_interval]) ->                                                  
        write(X9), write(' '), write(X5), write(' '),
        write(X16), write('..'), write(X13)
    ;
     memberchk(X3,[attr_leq_unary]) ->                                                    
        (X14 = prod ->
            write(X9), write(X5),
            write(X16), write('.'), write(X10)
        ;
            write(formula_pattern_write_condition), nl, halt
        )
    ;
     memberchk(X3,[unary_leq_attr]) ->                                                    
        (X14 = prod ->
            write(X16), write('.'), write(X9),
            write(X5), write(X10)
        ;
            write(formula_pattern_write_condition), nl, halt
        )
    ;
     memberchk(X3,[unary_term_eq_coef,unary_term_leq_coef]) ->                            
        (X14 = plus ->
            write(X9), write('+'), write(X16)
        ;
         X14 = minus ->
            write(X9), write('-'), write(X16)
        ;
         X14 = prod ->
            write(X16), write('.'), write(X9)
        ;
         memberchk(X14, [min,max]) ->
            write(X14), write('('), write(X9), write(','), write(X16), write(')')
        ;
         X14 = floor ->
            write(X9), write(' fdiv '), write(X16)
        ;
         X14 = mod ->
            write(X9), write(' mod '), write(X16)
        ;
         X14 = ceil ->
            write(X9), write(' cdiv '), write(X16)
        ;
            write(formula_pattern_write_condition), nl, halt
        ),
        write(X5), write(X13)
    ;
     memberchk(X3,[binary_term_eq_coef,binary_term_leq_coef]) ->                          
        (X14 = plus ->                                                                        
            write(X9), write('+'), write(X10)
        ;
         X14 = minus ->
            write(X9), write('-'), write(X10)
        ;
         X14 = abs ->
            write('|'), write(X9), write('-'), write(X10), write('|')
        ;
         memberchk(X14, [min,max]) ->
            write(X14), write('('), write(X9), write(','), write(X10), write(')')
        ;
         X14 = floor ->
            write(X9), write(' fdiv '), write(X10)
        ;
         X14 = mfloor ->
            write(X9), write(' fdiv max('), write(X10), write('-'), write(X4), write(',1)')
        ;
         X14 = mod ->
            write(X9), write(' mod '), write(X10)
        ;
         X14 = prod ->
            write(X9), write('.'), write(X10)
        ;
         X14 = ceil ->
            write(X9), write(' cdiv '), write(X10)
        ;
         X14 = cmod ->
            write(X9), write('-'), write(X10), write(' mod '), write(X9)
        ;
         X14 = dmod ->
            write(X9), write('-'), write(X9), write(' mod '), write(X10)
        ;
         X14 = fmod ->
            write('('), write(X9), write(' mod '), write(X10), write('=0 ? '),
            write(X10), write(' : '), write(X9), write(' mod '), write(X10), write(')')
        ;
            write(formula_pattern_write_condition), nl, halt
        ),
        write(X5), write(X13)
    ;
     X3 = linear_eq_coef ->
        write(X10), write('+'), write(X11), 
        (X16 =  1 -> write('+')                                           ;
         X16 = -1 -> write('-')                                           ;
         X16 >  0 -> write('+'), write(X16), write('.')                  ;
         X16 <  0 -> X15 is -X16, write('-'), write(X15), write('.') ;
                      write(formula_pattern_write_condition), nl, halt     ),
        write(X9), write(X5), write(X13)
    ;
     X3 = sum_leq_attr ->
        write(X9), write('+'), write(X10), write(X5), write(X11)
    ;
     X3 = minus_mod_eq0 ->
        write('('), write(X11), write('-'), write(X9), write(') mod '), write(X10), write(X5), write('0')
    ;
        write(formula_pattern_write_condition), nl, halt
    ).

formula_pattern_write_then_else(X2, X10, X6, X7, X15, X11, X1) :-
    functor(X10, X4, X3),
    (X3 = 1 -> arg(1, X10, X12)                          ;                      
     X3 = 2 -> arg(1, X10, X12), arg(2, X10, X5) ;                      
                      true                                          ),                     
    (X6 > 0 -> get_attr_name(X6, X2, X8) ; true),                       
    (X7 > 0 -> get_attr_name(X7, X2, X9) ; true),                       
    (X4 = attr ->
        (X1 = X6-X13 ->                                                    
            write(X13)                                                                   
        ;                                                                                  
            write(X8)
        )
    ;
     X4 = coef ->
        write(X11)
    ;
     X4 = unary_term ->
        (X12 = plus ->
            write(X8), write('+'), write(X15)
        ;
         X12 = minus ->
            write(X8), write('-'), write(X15)
        ;
         X12 = prod ->
            write(X15), write('.'), write(X8)
        ;
         memberchk(X12,[min,max]) ->
            write(X12), write('('), write(X8), write(','), write(X15), write(')')
        ;
         X12 = min_min ->
            (X15 > 0 -> true ; write(formula_pattern_write_then_else), nl, halt),
            write('min('), write(X8), write('-'), write(X5), write(','), write(X15), write(')')
        ;
         X12 = max_min ->
            (X15 > 0 -> true ; write(formula_pattern_write_then_else), nl, halt),
            write('max('), write(X8), write('-'), write(X5), write(','), write(X15), write(')')
        ;
         X12 = floor ->
            write(X8), write(' fdiv '), write(X15)
        ;
         X12 = ceil ->
            write(X8), write(' cdiv '), write(X15)
        ;
         X12 = floor_min ->
            (X15 > 0 -> true ; write(formula_pattern_write_then_else), nl, halt),
            write('('), write(X8), write('-'), write(X5), write(') fdiv '), write(X15)
        ;
         X12 = mod ->
            write(X8), write(' mod '), write(X15)
        ;
            write(formula_pattern_write_then_else), nl, halt
        )
    ;
     X4 = binary_term ->
        (X12 = plus ->
            write(X8), write('+'), write(X9)
        ;
         X12 = minus ->
            write(X8), write('-'), write(X9)
        ;
         X12 = linear ->
            write(X8),
            (X15 < 0 ->
                X14 is -X15, write('-'), write(X14), write('.'), write(X9)
            ;
                write('+'),  write(X15), write('.'), write(X9)
            )
        ;
         X12 = abs ->
            write('|'), write(X8), write('-'), write(X9), write('|')
        ;
         memberchk(X12,[min,max]) ->
            write(X12), write('('), write(X8), write(','), write(X9), write(')')
        ;
         X12 = plus_min ->
            write('min('), write(X8), write('+'), write(X9), write('-'), write(X15), write(','), write(X8), write(')')
        ;
         X12 = prod ->
            write(X8), write('.'), write(X9)
        ;
         X12 = floor ->
            write(X8), write(' fdiv '), write(X9)
        ;
         X12 = mfloor ->
            write(X8), write(' fdiv max('), write(X9), write('-'), write(X5), write(',1)')
        ;
         X12 = ceil ->
            write(X8), write(' cdiv '), write(X9)
        ;
         X12 = plus_floor ->
            write('('), write(X8), write('+'), write(X9),
            (X15 < 0 ->
                X14 is -X15, write('-'), write(X14)
            ;
                write('+'),  write(X15)
            ),
            write(') fdiv '), write(X8)
        ;
         X12 = minus_floor ->
            write('('), write(X8), write('-'), write(X9),
            (X15 = 0 -> true                                    ;
             X15 > 0 -> write('+'), write(X15)                 ;
                         write('-'), X14 is -X15, write(X14)),
            write(') fdiv '), write(X11)
        ;
         X12 = mod ->
            write(X8), write(' mod '), write(X9)
        ;
         X12 = cmod ->
            write(X8), write('-'), write(X9), write(' mod '), write(X8)
        ;
         X12 = dmod ->
            write(X8), write('-'), write(X8), write(' mod '), write(X9)
        ;
         X12 = fmod ->
            write('('), write(X8), write(' mod '), write(X9), write('=0 ? '),
            write(X9), write(' : '), write(X8), write(' mod '), write(X9), write(')')
        ;
            write(formula_pattern_write_then_else), nl, halt
        )
    ;
        write(formula_pattern_write_then_else), nl, halt
    ).

formula_pattern_write_case(X1) :-
    write('('),
    formula_pattern_write_cases(X1),
    write(')').

formula_pattern_write_cases([option(_,X2,X1)|X4]) :-
    formula_pattern_write_bool(X1),
    write(' ? '), write(X2),
    formula_pattern_write_cases1(X4).

formula_pattern_write_cases1([option(_,X2,X1)|X4]) :-
    !,
    write(' : '),
    formula_pattern_write_bool(X1),
    write(' ? '), write(X2),
    formula_pattern_write_cases1(X4).
formula_pattern_write_cases1([option(X1)]) :-
    write(' : '), write(X1).

formula_pattern_write_formula(X1) :-
    formula_pattern(f(X21),                                           X1),           
    formula_pattern(nu(X19),                                         X1),           
    formula_pattern(unary(X14),                                   X1),           
    formula_pattern(binary(X12),                                 X1),           
    formula_pattern(mandatory_optional_attributes_names(X5), X1),           
    length(X5, X15),                                                                  
    X16 is X15 + X19,                                                                       
    X6 = t(X15, X16, X14, X12, X5, X3),                      
    (X21 = 0 ->                                                                                  
        formula_pattern(cst(X17), X1),                                             
        write(X17)
    ;
     X21 = 1 ->                                                                                  
        formula_pattern(attributes_use(X3), X1),                        
        formula_pattern(polynoms([X11]),           X1),
        formula_pattern_write_polynom(X11, X6, 1, 0)
    ;
     X21 = 2 ->                                                                                  
        formula_pattern(unaryf([X4]),       X1),                        
        formula_pattern(attributes_use(X3), X1),                        
        formula_pattern(polynoms([X11]),           X1),
        functor(X4, X7, _),
        (X7 = min ->                                                                    
            arg(1, X4, X17), write('min('),
            formula_pattern_write_polynom(X11, X6, 1, 0),
            write(','), write(X17), write(')')                       ;
         X7 = max ->                                                                    
            arg(1, X4, X17), write('max('),
            formula_pattern_write_polynom(X11, X6, 1, 0),
            write(','), write(X17), write(')')                       ;
         X7 = floor ->                                                                  
            arg(1, X4, X17),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write(' fdiv '), write(X17)                              ;
         X7 = mod ->                                                                    
            arg(1, X4, X17),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write(' mod '), write(X17)                               ;
         X7 = geq0 ->                                                                   
            write('['),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write(' >= 0]')                                          ;
         X7 = in ->                                                                     
            arg(1, X4, X18), arg(2, X4, X20), write('['),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write(' in '), write(X18), write('..'), write(X20), write(']');
         X7 = power ->                                                                  
            arg(1, X4, X13),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write('^'), write(X13)                                ;
         X7 = sum_consec ->                                                             
            write('('),
            formula_pattern_write_polynom(X11, X6, 1, 1),
            write('.('),
            formula_pattern_write_polynom(X11, X6, 1, 0),
            write(' + 1)) fdiv 2')                                   ;
            write(formula_pattern_write_formula), nl, halt
        )
    ;
     X21 = 3 ->                                                                                  
        formula_pattern(binaryf([X2]),     X1),                        
        formula_pattern(attributes_use(X3), X1),                        
        formula_pattern(polynoms([X9,X10]), X1),
        functor(X2, X8, _),
        (X8 = min ->                                                                    
            write('min('), formula_pattern_write_polynom(X9, X6, 1, 0),
            write(','), formula_pattern_write_polynom(X10, X6, 1, 0), write(')') ;
         X8 = max ->                                                                    
            write('max('), formula_pattern_write_polynom(X9, X6, 1, 0),
            write(','), formula_pattern_write_polynom(X10, X6, 1, 0), write(')') ;
         X8 = floor ->                                                                  
            formula_pattern_write_polynom(X9, X6, 1, 1), write(' fdiv '),
            formula_pattern_write_polynom(X10, X6, 1, 1)                         ;
         X8 = ceil ->                                                                  
            formula_pattern_write_polynom(X9, X6, 1, 1), write(' cdiv '),
            formula_pattern_write_polynom(X10, X6, 1, 1)                         ;
         X8 = mod ->                                                                    
            formula_pattern_write_polynom(X9, X6, 1, 1), write(' mod '),
            formula_pattern_write_polynom(X10, X6, 1, 1)                         ;
         X8 = cmod ->                                                                   
            formula_pattern_write_polynom(X9, X6, 1, 0), write(' - '),
            formula_pattern_write_polynom(X10, X6, 1, 1), write(' mod '),
            formula_pattern_write_polynom(X9, X6, 1, 1)                         ;
         X8 = dmod ->                                                                   
            formula_pattern_write_polynom(X9, X6, 1, 0), write(' - '),
            formula_pattern_write_polynom(X9, X6, 1, 1), write(' mod '),
            formula_pattern_write_polynom(X10, X6, 1, 1)                         ;
         X8 = prod ->                                                                   
            formula_pattern_write_polynom(X9, X6, 1, 1), write(' . '),
            formula_pattern_write_polynom(X10, X6, 1, 1)                         ;
            write(formula_pattern_write_formula), nl, halt
        )
    ;
        write(formula_pattern_write_formula), nl, halt
    ).

formula_pattern_write_polynom(X3, X2, X4, X1) :-
    ((X1=1, formula_pattern_more_than_one_monome(X3, 2)) ->
        write('('),
        formula_pattern_write_polynom(X3, X2, X4),
        write(')')
    ;
        formula_pattern_write_polynom(X3, X2, X4)
    ).

formula_pattern_more_than_one_monome(_, 0) :- !.
formula_pattern_more_than_one_monome([t(_,_,X1)|X3], X4) :-
    integer(X1), X1 = 0, !,
    formula_pattern_more_than_one_monome(X3, X4).
formula_pattern_more_than_one_monome([_|X3], X4) :-
    X1 is X4-1,
    formula_pattern_more_than_one_monome(X3, X1).

formula_pattern_write_polynom([], _, _) :- !.
formula_pattern_write_polynom([X3|X5], X1, X4) :-
    formula_pattern_write_monome(X3, X1, X4, X2),
    formula_pattern_write_polynom(X5, X1, X2).

formula_pattern_write_monome(t(_,_,X2), _, X1, X1) :-
    integer(X2),
    X2 = 0,
    !.
formula_pattern_write_monome(t(_,X3,X6), X1, X5, 0) :-
    (X6 > 0 -> X7 = 1, X4 is X6 ; X7 = 0, X4 is -X6),
    get_non_zero_exponents(X3, 1, X2),
    length(X2, X9),
    ((X9 = 0, X5 = 1)            -> write(X6)                                                                              ;
     (X9 = 0, X5 = 0, X7  =  1) -> write(' + '), write(X4)                                                             ;
     (X9 = 0, X5 = 0, X7  =  0) -> write(' - '), write(X4)                                                             ;
     (X9 > 0, X5 = 1, X6 =  1) -> formula_pattern_write_rest_monome(X2, X1, 1)                               ;
     (X9 > 0, X5 = 1, X6 = -1) -> write('-'), formula_pattern_write_rest_monome(X2, X1, 1)                   ;
     (X9 > 0, X5 = 1)            -> write(X6), formula_pattern_write_rest_monome(X2, X1, 0)                  ;
     (X9 > 0, X5 = 0, X6 =  1) -> write(' + '), formula_pattern_write_rest_monome(X2, X1, 1)                 ;
     (X9 > 0, X5 = 0, X6 = -1) -> write(' - '), formula_pattern_write_rest_monome(X2, X1, 1)                 ;
     (X9 > 0, X5 = 0, X7  =  1) -> write(' + '), write(X4), formula_pattern_write_rest_monome(X2, X1, 0) ;
     (X9 > 0, X5 = 0, X7  =  0) -> write(' - '), write(X4), formula_pattern_write_rest_monome(X2, X1, 0) ;
                                      write(formula_pattern_write_monome), nl, halt                                            ).

formula_pattern_write_rest_monome([], _, _) :- !.
formula_pattern_write_rest_monome([X13-X4|X14], X2, X7) :-
    X2 = t(X8, X9, _, _, X3, _),
    (X7 = 0 -> write('.') ; true),
    (X13 =< X8 ->                         
        get_attr_name(X13, X3, X10), 
        write(X10)                          
    ;
     X13 =< X9 ->                         
        X11 is X13 - X8,
        formula_pattern_write_unary_term(X11, X2)
    ;                                        
        X12 is X13 - X9,
        formula_pattern_write_binary_term(X12, X2)
    ),
    (X4 > 1 -> write('^'), write(X4) ; true),
    formula_pattern_write_rest_monome(X14, X2, 0).

formula_pattern_write_unary_term(X13, X2) :-
    X2 = t(_, _, X10, _, X3, X1),
    memberchk(u(X8), X1),
    nth1(X13, X8, X11),
    get_pos_value(X11, 1, 1, 1, [X18]),
    get_attr_name(X18, X3, X12),
    nth1(X13, X10, X4),
    functor(X4, X16, _),
    (X16 = min        -> arg(1, X4, X14), write('min('), write(X12), write(','), write(X14), write(')')    ;
     X16 = max        -> arg(1, X4, X14), write('max('), write(X12), write(','), write(X14), write(')')    ;
     X16 = floor      -> arg(1, X4, X14), write('('), write(X12), write(' fdiv '), write(X14), write(')')  ;
     X16 = ceil       -> arg(1, X4, X14), write('('), write(X12), write(' cdiv '), write(X14), write(')')  ;
     X16 = mod        -> arg(1, X4, X14), write('('), write(X12), write(' mod '), write(X14), write(')')   ;
     X16 = geq        -> arg(1, X4, X14), write('['), write(X12), write(' >= '), write(X14), write(']')    ;
     X16 = in         -> arg(1, X4, X15), arg(2, X4, X17), write('['), write(X12), write(' in '),
                        write(X15), write('..'), write(X17), write(']')                                            ;
     X16 = power      -> arg(1, X4, X9), write(X12), write('^'), write(X9)                         ;
     X16 = sum_consec -> write('(('), write(X12), write('.('), write(X12), write('+1)) fdiv 2)')                 ;
                        write(formula_pattern_write_unary_term), nl, halt                                         ).

formula_pattern_write_binary_term(X16, X3) :-
    X3 = t(_, _, _, X11, X4, X1),
    memberchk(b(X12), X1),
    nth1(X16, X12, X13),
    get_pos_value(X13, 1, 1, 2, [X17,X18]),
    get_attr_name(X17, X4, X14),
    get_attr_name(X18, X4, X15),
    nth1(X16, X11, X2),
    (X2 = min(_)    -> write('min('), write(X14), write(','), write(X15), write(')')                                      ;
     X2 = max(_)    -> write('max('), write(X14), write(','), write(X15), write(')')                                      ;
     X2 = floor(0)  -> write('('), write(X14), write(' fdiv '), write(X15), write(')')                                    ;
     X2 = floor(1)  -> write('('), write(X15), write(' fdiv '), write(X14), write(')')                                    ;
     X2 = mfloor(0) -> tab_get_mins_attr_names(X4, X5), nth1(X18, X5, X6),
                               write('('), write(X14), write(' fdiv max('), write(X15), write('-'), write(X6), write(',1))');
     X2 = mfloor(1) -> tab_get_mins_attr_names(X4, X5), nth1(X17, X5, X7),
                               write('('), write(X15), write(' fdiv max('), write(X14), write('-'), write(X7), write(',1))');
     X2 = ceil(0)   -> write('('), write(X14), write(' cdiv '), write(X15), write(')')                                    ;
     X2 = ceil(1)   -> write('('), write(X15), write(' cdiv '), write(X14), write(')')                                    ;
     X2 = mod(0)    -> write('('), write(X14), write(' mod '), write(X15), write(')')                                     ;
     X2 = mod(1)    -> write('('), write(X15), write(' mod '), write(X14), write(')')                                     ;
     X2 = cmod(0)   -> write('('), write(X14), write('-'), write(X15), write(' mod '), write(X14), write(')')           ;
     X2 = cmod(1)   -> write('('), write(X15), write('-'), write(X14), write(' mod '), write(X15), write(')')           ;
     X2 = dmod(0)   -> write('('), write(X14), write('-'), write(X14), write(' mod '), write(X15), write(')')           ;
     X2 = dmod(1)   -> write('('), write(X15), write('-'), write(X15), write(' mod '), write(X14), write(')')           ;
     X2 = fmod(0)   -> write('('), write(X14), write(' mod '), write(X15), write('=0 ? '), write(X15), write(' : '),
                               write(X14), write(' mod '), write(X15), write(')')                                                 ;
     X2 = fmod(1)   -> write('('), write(X15), write(' mod '), write(X14), write('=0 ? '), write(X14), write(' : '),
                               write(X15), write(' mod '), write(X14), write(')')                                                 ;
     X2 = prod(_)   -> write('('), write(X14), write('.'), write(X15), write(')')                                         ;
                               write(formula_pattern_write_binary_term), nl, halt                                                     ).

get_attr_name(X4, X1, X3) :-
    nth1(X4, X1, X2), 
    tab_get_name(X2, X3). 
