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
% Purpose: Eval a formula term (used to check acquired conjectures or to learn by transfer)
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(eval_formula, [eval_formula_term/2]).

eval_formula_term(X1, _) :- 
    \+ ground(X1),          
    !,
    write(eval_formula_term(X1)), nl, halt.
eval_formula_term(X1, X1) :-
    integer(X1), !.
eval_formula_term(X2, X4) :-
    X2 = not(X1),
    !,
    eval_formula_term(X1, X3),
    X4 is 1-X3.
eval_formula_term(X1, X8) :- 
    X1 = bool(X3, X2, X5, X4, X6),
    memberchk(X5, [and,or,allequal,xor,sum,voting,card1]),
    !,
    eval_boolean_conds(X6, X5, X7),
    (X3 = 1 ->
        (X5 = sum ->
            X8 is X2+X4-X7
        ;
            X8 is X2+1-X7
        )
    ;
        X8 is X2+X7
    ).
eval_formula_term(X1, X6) :- 
    functor(X1, if, 3), !,
    arg(1, X1, X3),
    eval_formula_term(X3, X2),
    (X2 = 1 ->
        arg(2, X1, X4),
        eval_formula_term(X4, X6)
    ;
        arg(3, X1, X5),
        eval_formula_term(X5, X6)
    ).
eval_formula_term(X1, X6) :- 
    functor(X1, in, 3), !,
    arg(1, X1, X2),
    arg(2, X1, X3),
    arg(3, X1, X4),
    eval_formula_term(X2, X5),
    ((X5 >= X3, X5 =< X4) -> X6 = 1 ; X6 = 0).
eval_formula_term(X1, X7) :- 
    functor(X1, X2, 2),
    memberchk(X2, [eq,leq,geq]), !,
    arg(1, X1, X3),
    arg(2, X1, X4),
    eval_formula_term(X3, X5),
    eval_formula_term(X4, X6),
    (X2 = eq ->
        (X5 =  X6 -> X7 = 1 ; X7  = 0)
    ;
     X2 = leq ->
        (X5 =< X6 -> X7 = 1 ; X7  = 0)
    ;
        (X5 >= X6 -> X7 = 1 ; X7  = 0)
    ).
eval_formula_term(X1, X3) :-
    functor(X1, polynom, 1), !,
    arg(1, X1, X2),
    eval_and_sumup_monomes(X2, 0, X3).
eval_formula_term(X1, X5) :-
    functor(X1, X2, 1),
    memberchk(X2, [geq0,sum_consec]), !,
    arg(1, X1, X3),
    eval_formula_term(X3, X4),
    (X2 = geq0       -> (X4 >= 0 -> X5 = 1 ; X5 = 0 )               ;
     X2 = sum_consec -> X5 is (X4 * (X4 + 1)) // 2                 ;
                             write(eval_formula_term1(X1)), nl, halt).
eval_formula_term(X1, X7) :- 
    functor(X1, X2, 2),
    memberchk(X2, [plus,minus,abs,min,max,prod,floor,ceil,mod,cmod,dmod,fmod,power]), !,
    arg(1, X1, X3),
    arg(2, X1, X4),
    eval_formula_term(X3, X5),
    eval_formula_term(X4, X6),
    (X2 = plus  -> X7 is X5+X6                                            ;
     X2 = minus -> X7 is X5-X6                                            ;
     X2 = abs   -> X7 is abs(X5-X6)                                       ;
     X2 = min   -> X7 is min(X5,X6)                                       ;
     X2 = max   -> X7 is max(X5,X6)                                       ;
     X2 = prod  -> X7 is X5 * X6                                          ;
     X2 = floor -> X7 is X5 // X6                                         ;
     X2 = ceil  -> X7 is (X5 + X6 - 1) // X6                            ;
     X2 = mod   -> X7 is X5 mod X6                                        ;
     X2 = cmod  -> X7 is X5 - (X6 mod X5)                               ;
     X2 = dmod  -> X7 is X5 - (X5 mod X6)                               ;
     X2 = fmod  -> X8 is X5 mod X6, (X8 = 0 -> X7 is X6 ; X7 is X8) ;
     X2 = power -> X7 is X5 ^ X6                                          ;
                        write(eval_formula_term2(X1)), nl, halt            ).
eval_formula_term(X1, X12) :- 
    functor(X1, X2, 3),
    memberchk(X2, [in,min_min,max_min,floor_min,mfloor,linear,plus_min,plus_floor,
                        sum_leq_attr,minus_mod_eq0,ceil_leq_floor]), !,
    arg(1, X1, X6),
    arg(2, X1, X7),
    arg(3, X1, X8),
    eval_formula_term(X6, X9),
    eval_formula_term(X7, X10),
    eval_formula_term(X8, X11),
    (X2 = in             -> ((X9 >= X10, X9 =< X11) -> X12 = 1 ; X12 = 0)               ;
     X2 = min_min        -> X12 is min(X9-X11,X10)                                        ;
     X2 = max_min        -> X12 is max(X9-X11,X10)                                        ;
     X2 = floor_min      -> X12 is (X9-X11) // X10                                        ;
     X2 = mfloor         -> X12 is X9 // max(X10-X11,1)                                   ;
     X2 = linear         -> X12 is X9+X11*X10                                             ; 
     X2 = plus_min       -> X12 is min(X9+X10-X11,X9)                                   ;
     X2 = plus_floor     -> X12 is (X9+X10+X11) // X9                                   ;
     X2 = sum_leq_attr   -> X5 is X9+X10, (X5 =< X11 -> X12 = 1 ; X12 = 0)          ;
     X2 = minus_mod_eq0  -> X3 is (X11-X9) mod X10, (X3 = 0 -> X12 = 1 ; X12 = 0) ;
     X2 = ceil_leq_floor -> X4 is ((X9 - X11 + X10 - 1) // X10),
                                 X3 is ((X9 - X10) // X11),
                                 (X4 =< X3 -> X12 = 1; X12 = 0)                            ;
                                 write(eval_formula_term3(X1)), nl, halt                  ).
eval_formula_term(X1, X6) :- 
    functor(X1, linear, 4),
    !,
    arg(1, X1, X2),
    arg(2, X1, X3),
    arg(3, X1, X4),
    arg(4, X1, X5),
    X6 is X5*X2+X3+X4.
eval_formula_term(X1, X6) :- 
    functor(X1, minus_floor, 4),
    !,
    arg(1, X1, X2),
    arg(2, X1, X3),
    arg(3, X1, X4),
    arg(4, X1, X5),
    X6 is (X2-X3+X4) // X5.
eval_formula_term(X1, X3) :-
    X1 = cases(X2),
    !,
    eval_cases(X2,X3).
eval_formula_term(X1, _) :-
    write(X1), halt.

eval_boolean_conds([X4|X8], X3, X5) :-
    eval_formula_term(X4, X2),
    (memberchk(X2, [0,1]) -> true ; write(eval_boolean_conds1(X2)), nl, halt),
    (X8 = [] ->
        X5 = X2
    ;
        eval_boolean_conds(X8, X3, X2, X1),
        (X3 = voting ->
            length([X4|X8], X6),
            X7 is (X6+1) // 2,
            (X1 >= X7 -> X5 = 1 ; X5 = 0)
        ;
            X5 = X1
        )
    ).

eval_boolean_conds([X5|X7], X4, X1, X6) :-
    eval_formula_term(X5, X2),
    (memberchk(X2, [0,1]) -> true ; write(eval_boolean_conds2(X2)), nl, halt),
    (X4 = and      -> ((X2 = 1, X1 = 1) -> X3 = 1 ; X3 = 0)    ;
     X4 = or       -> ((X2 = 0, X1 = 0) -> X3 = 0 ; X3 = 1)    ;
     X4 = allequal -> ( X2 = X1         -> X3 = 1 ; X3 = 0)    ;
     X4 = sum      ->                                X3 is X2 + X1 ;
     X4 = xor      ->                                X3 is X2 + X1 ;
     X4 = voting   ->                                X3 is X2 + X1 ;
     X4 = card1    ->                                X3 is X2 + X1 ;
                         write(eval_boolean_conds3(X4)), nl, halt                ),
    ((X7 = [], X4 = xor  )        -> X6 = X3 mod 2                         ;
     (X7 = [], X4 = card1)        -> (X3 = 1 -> X6 = 1 ; X6 = 0)          ;
      X7 = []                        -> X6 = X3                               ; 
     (X4 = allequal, X3 = 0) -> X6 = 0                                    ; 
      X4 = allequal              -> eval_boolean_conds(X7, X4, X2, X6) ;
                                       eval_boolean_conds(X7, X4, X3,  X6) ).

eval_and_sumup_monomes([], X1, X1) :- !.
eval_and_sumup_monomes([X4|X8], X2, X3) :-
    X4 = monome(X5, X6),
    eval_monome(X5, X6, X7),
    X1 is X2 + X7,
    eval_and_sumup_monomes(X8, X1, X3).

eval_monome([], X1, X1) :- !.
eval_monome([t(X6,X3)|X8], X4, X5) :-
    eval_formula_term(X6, X1),
    X7 is X1 ^ X3,
    X2 is X7 * X4,
    eval_monome(X8, X2, X5).

eval_cases([if_then(X1, X2)|X5], X4) :-
    !,
    (eval_formula_term(X1, 1) ->
        eval_formula_term(X2, X3),
        X4 is X3
    ;
        eval_cases(X5, X4)
    ).
eval_cases([otherwise(X1)], X3) :-
    eval_formula_term(X1, X2),
    X3 is X2.
