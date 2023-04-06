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
% Purpose: Generate a list of options telling which candidate formulae to generate and which parameters to use
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_options_for_formulae,[gen_options_bool/2,
                                    gen_options_cond/2,
                                    gen_options_lists/9]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(table_access).
:- use_module(utility).
:- use_module(bool_cond_utility).

option_bool_min_cst(model_seeker,  -9) :- !. 
option_bool_min_cst(_,             -5).      

option_bool_max_cst(model_seeker,   9) :- !. 
option_bool_max_cst(_,              5).      

option_cond_min_cst(model_seeker,  -9) :- !. 
option_cond_min_cst(_,             -3).      

option_cond_max_cst(model_seeker,   9) :- !. 
option_cond_max_cst(_,              3).      

option_poly_min_cst(model_seeker,  -3) :- !. 
option_poly_min_cst(_,             -1).      

option_poly_max_cst(model_seeker,   9) :- !. 
option_poly_max_cst(_,              1).      

option_poly_min_coef(model_seeker, -4) :- !. 
option_poly_min_coef(_,            -2).      

option_poly_max_coef(model_seeker,  4) :- !. 
option_poly_max_coef(_,             2).      

gen_options_bool(X2, X1) :- 
    option_bool_min_cst(X2, X4),    
    option_bool_max_cst(X2, X5),    
    X3 = [t(cond(attr_eq_attr),                                   no_negation,    2),
                 t(cond(attr_leq_attr),                                  no_negation,    2),
                 t(cond(attr_eq_coef(coef(X4,X5))),                    no_negation,    3),
                 t(cond(attr_leq_coef(coef(X4,X5))),                   no_negation,    3),
                 t(cond(attr_geq_coef(coef(X4,X5))),                   no_negation,    3),
                 t(cond(attr_in_interval(1,X5)),                        no_restriction, 1),
                 t(cond(attr_eq_unary([prod(2,X5)])),                   no_negation,    1),
                 t(cond(attr_leq_unary([prod(2,X5)])),                  no_negation,    1),
                 t(cond(unary_leq_attr([prod(2,X5)])),                  no_negation,    1),
                 t(cond(minus_mod_eq0),                                  no_negation,    1),
                 t(cond(sum_leq_attr),                                   no_negation,    1),
                 t(cond(ceil_leq_floor),                                 no_negation,    1),
                 t(cond(unary_term_eq_coef([mod(2,X5)],  coef(0,X5))), no_negation,    1),
                 t(cond(unary_term_leq_coef([mod(2,X5)], coef(0,X5))), no_negation,    1),
                 t(cond(unary_term_geq_coef([mod(2,X5)], coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([plus],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([minus],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([min],        coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([max],        coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([prod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([abs],        coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([floor],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([ceil],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([mod],        coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([mfloor],     coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([cmod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([dmod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_eq_coef([fmod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([plus],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([minus],     coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([min],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([max],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([prod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([abs],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([floor],     coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([ceil],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([mod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([mfloor],    coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([cmod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([dmod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_leq_coef([fmod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([plus],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([minus],     coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([min],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([max],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([prod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([abs],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([floor],     coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([ceil],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([mod],       coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([mfloor],    coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([cmod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([dmod],      coef(0,X5))), no_negation,    1),
                 t(cond(binary_term_geq_coef([fmod],      coef(0,X5))), no_negation,    1)],

   
   
   
   
    (X2 \== model_seeker ->
        X1 = [[bool([neg(0), op([and]),      nb_terms(1,1), conds(X3), use_mods(2)])], 
                       [bool([neg(1), op([and]),      nb_terms(1,1), conds(X3), use_mods(2)])],

                       [bool([neg(0), op([and]),      nb_terms(2,2), conds(X3), use_mods(0)])], 
                       [bool([neg(0), op([or]),       nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([sum]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([allequal]), nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([and]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([or]),       nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([sum]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([allequal]), nb_terms(2,2), conds(X3), use_mods(0)])],
                       
                       [bool([neg(0), op([and]),      nb_terms(2,2), conds(X3), use_mods(1)])], 
                       [bool([neg(0), op([or]),       nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(0), op([sum]),      nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(0), op([allequal]), nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([and]),      nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([or]),       nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([sum]),      nb_terms(2,2), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([allequal]), nb_terms(2,2), conds(X3), use_mods(1)])],

                       [bool([neg(0), op([and]),      nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(0), op([or]),       nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([sum]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([allequal]), nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([card1]),    nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(0), op([xor]),      nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(0), op([voting]),   nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([and]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([or]),       nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([sum]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([allequal]), nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([card1]),    nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(1), op([xor]),      nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(1), op([voting]),   nb_terms(3,3), conds(X3), use_mods(0)])],

                       [bool([neg(0), op([and]),      nb_terms(3,3), conds(X3), use_mods(1)])], 
                       [bool([neg(0), op([or]),       nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(0), op([sum]),      nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(0), op([allequal]), nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(0), op([card1]),    nb_terms(3,3), conds(X3), use_mods(1)])], 
                       [bool([neg(0), op([xor]),      nb_terms(3,3), conds(X3), use_mods(1)])], 
                       [bool([neg(0), op([voting]),   nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([and]),      nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([or]),       nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([sum]),      nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([allequal]), nb_terms(3,3), conds(X3), use_mods(1)])],
                       [bool([neg(1), op([card1]),    nb_terms(3,3), conds(X3), use_mods(1)])], 
                       [bool([neg(1), op([xor]),      nb_terms(3,3), conds(X3), use_mods(1)])], 
                       [bool([neg(1), op([voting]),   nb_terms(3,3), conds(X3), use_mods(1)])]]
    ; 
        X1 = [[bool([neg(0), op([and]),      nb_terms(1,1), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([and]),      nb_terms(1,1), conds(X3), use_mods(0)])],

                       [bool([neg(0), op([and]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([or]),       nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([sum]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([allequal]), nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([and]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([or]),       nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([sum]),      nb_terms(2,2), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([allequal]), nb_terms(2,2), conds(X3), use_mods(0)])],
                       
                       [bool([neg(0), op([and]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([or]),       nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([sum]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([allequal]), nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([card1]),    nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(0), op([xor]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(0), op([voting]),   nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([and]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([or]),       nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([sum]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([allequal]), nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([card1]),    nb_terms(3,3), conds(X3), use_mods(0)])], 
                       [bool([neg(1), op([xor]),      nb_terms(3,3), conds(X3), use_mods(0)])],
                       [bool([neg(1), op([voting]),   nb_terms(3,3), conds(X3), use_mods(0)])]]
    ).

gen_options_cond(X10, X4) :-
    option_cond_min_cst(X10, X15), 
    option_cond_max_cst(X10, X16), 
    (X10 \== model_seeker ->
            X5 = [cond(attr_eq_attr),
                           cond(attr_eq_coef(coef(X15,X16))),
                           cond(attr_leq_attr),
                           cond(attr_leq_coef(coef(X15,X16))),
                           cond(attr_in_interval(1,X16)),
                           cond(binary_term_eq_coef([plus],                      coef(0,X16))),
                           cond(binary_term_eq_coef([minus],                     coef(0,X16))),
                           cond(binary_term_eq_coef([min,max],                   coef(0,X16))),
                           cond(binary_term_eq_coef([prod,abs],                  coef(0,X16))),
                           cond(attr_leq_unary([prod(2,X16)])),
                           cond(unary_leq_attr([prod(2,X16)])),
                           cond(binary_term_leq_coef([plus],                     coef(0,X16))),
                           cond(binary_term_leq_coef([minus],                    coef(0,X16))),
                           cond(sum_leq_attr),
                           cond(binary_term_leq_coef([prod,abs],                 coef(0,X16))),
                           cond(binary_term_leq_coef([min,max],                  coef(0,X16))),
                           cond(binary_term_eq_coef([floor],                     coef(0,X16))),
                           cond(binary_term_eq_coef([ceil],                      coef(0,X16))),
                           cond(binary_term_eq_coef([mod],                       coef(0,X16))),
                           cond(binary_term_eq_coef([mfloor],                    coef(0,X16))),
                           cond(unary_term_eq_coef([mod(2,X16)],                 coef(0,X16))),
                           cond(linear_eq_coef(cst(X15,X16),                     coef(X15,X16))),
                           cond(binary_term_eq_coef([cmod,dmod],                 coef(0,X16))),
                           cond(binary_term_eq_coef([fmod],                      coef(0,X16))),
                           cond(binary_term_leq_coef([floor],                    coef(0,X16))),
                           cond(binary_term_leq_coef([ceil],                     coef(0,X16))),
                           cond(binary_term_leq_coef([mod],                      coef(0,X16))),
                           cond(binary_term_leq_coef([mfloor],                   coef(0,X16))),
                           cond(unary_term_leq_coef([mod(2,X16)],                coef(0,X16))),
                           cond(binary_term_leq_coef([cmod,dmod],                coef(0,X16))),
                           cond(binary_term_leq_coef([fmod],                     coef(0,X16))),
                           cond(minus_mod_eq0)                                                ,
                           cond(ceil_leq_floor)                                               ],
            X6 = [then(attr), 
                           then(coef(X15,X16)),
                           then(binary_term([plus])),
                           then(binary_term([minus])),
                           then(binary_term([linear(X15,X16)])),
                           then(unary_term([plus(1,X16)])),
                           then(unary_term([minus(1,X16)])),
                           then(binary_term([min,max])),
                           then(unary_term([min(X15,X16),max(X15,X16)])),
                           then(binary_term([prod])),
                           then(unary_term([prod(2,X16)])),
                           then(binary_term([abs])),
                           then(binary_term([floor])),
                           then(unary_term([min_min(1,X16)])),
                           then(unary_term([max_min(1,X16)])),
                           then(binary_term([plus_min(1,X16)])),
                           then(unary_term([floor(2,X16)])),
                           then(binary_term([ceil])),
                           then(binary_term([mfloor])),
                           then(binary_term([plus_floor(X15,X16)])),
                           then(binary_term([minus_floor(X15,X16,2,X16)])),
                           then(binary_term([mod])),
                           then(unary_term([mod(2,X16)])),
                           then(unary_term([ceil(2,X16)])),
                           then(unary_term([floor_min(2,X16)])),
                           then(binary_term([cmod,dmod])),
                           then(binary_term([fmod]))],
            X7 = [else(attr),
                           else(coef(X15,X16)),
                           else(binary_term([plus])),
                           else(binary_term([minus])),
                           else(binary_term([linear(X15,X16)])),
                           else(unary_term([plus(1,X16)])),
                           else(unary_term([minus(1,X16)])),
                           else(binary_term([min,max])),
                           else(unary_term([min(X15,X16),max(X15,X16)])),
                           else(binary_term([prod])),
                           else(unary_term([prod(2,X16)])),
                           else(binary_term([abs])),
                           else(binary_term([floor])),
                           else(unary_term([min_min(1,X16)])),
                           else(unary_term([max_min(1,X16)])),
                           else(binary_term([plus_min(1,X16)])),
                           else(unary_term([floor(2,X16)])),
                           else(binary_term([ceil])),
                           else(binary_term([mfloor])),
                           else(binary_term([plus_floor(X15,X16)])),
                           else(binary_term([minus_floor(X15,X16,2,X16)])),
                           else(binary_term([mod])),
                           else(unary_term([mod(2,X16)])),
                           else(unary_term([ceil(2,X16)])),
                           else(unary_term([floor_min(2,X16)])),
                           else(binary_term([cmod,dmod])),
                           else(binary_term([fmod]))]
    ;
            X5 = [cond(attr_eq_attr),
                           cond(attr_eq_coef(coef(X15,X16))),
                           cond(attr_leq_attr),
                           cond(attr_leq_coef(coef(X15,X16))),
                           cond(attr_in_interval(1,X16)),
                           cond(binary_term_eq_coef([plus],                      coef(0,X16))),
                           cond(binary_term_eq_coef([minus],                     coef(0,X16))),
                           cond(binary_term_eq_coef([min,max],                   coef(0,X16))),
                           cond(binary_term_eq_coef([prod,abs],                  coef(0,X16))),
                           cond(attr_leq_unary([prod(2,X16)])),
                           cond(unary_leq_attr([prod(2,X16)])),
                           cond(binary_term_leq_coef([plus],                     coef(0,X16))),
                           cond(binary_term_leq_coef([minus],                    coef(0,X16))),
                           cond(sum_leq_attr),
                           cond(binary_term_leq_coef([prod,abs],                 coef(0,X16))),
                           cond(binary_term_leq_coef([min,max],                  coef(0,X16))),
                           cond(binary_term_eq_coef([floor],                     coef(0,X16))),
                           cond(binary_term_eq_coef([ceil],                      coef(0,X16))),
                           cond(binary_term_eq_coef([mfloor],                    coef(0,X16))),
                           cond(linear_eq_coef(cst(X15,X16),                     coef(X15,X16))),
                           cond(binary_term_leq_coef([floor],                    coef(0,X16))),
                           cond(binary_term_leq_coef([ceil],                     coef(0,X16))),
                           cond(binary_term_leq_coef([mfloor],                   coef(0,X16))),
                           cond(ceil_leq_floor)                                               ],
            X6 = [then(attr), 
                           then(coef(X15,X16)),
                           then(binary_term([plus])),
                           then(binary_term([minus])),
                           then(binary_term([linear(X15,X16)])),
                           then(unary_term([plus(1,X16)])),
                           then(unary_term([minus(1,X16)])),
                           then(binary_term([min,max])),
                           then(unary_term([min(X15,X16),max(X15,X16)])),
                           then(binary_term([prod])),
                           then(unary_term([prod(2,X16)])),
                           then(binary_term([abs])),
                           then(binary_term([floor])),
                           then(unary_term([min_min(1,X16)])),
                           then(unary_term([max_min(1,X16)])),
                           then(binary_term([plus_min(1,X16)])),
                           then(unary_term([floor(2,X16)])),
                           then(binary_term([ceil])),
                           then(binary_term([mfloor])),
                           then(binary_term([plus_floor(X15,X16)])),
                           then(binary_term([minus_floor(X15,X16,2,X16)])),
                           then(unary_term([ceil(2,X16)])),
                           then(unary_term([floor_min(2,X16)]))],
            X7 = [else(attr),
                           else(coef(X15,X16)),
                           else(binary_term([plus])),
                           else(binary_term([minus])),
                           else(binary_term([linear(X15,X16)])),
                           else(unary_term([plus(1,X16)])),
                           else(unary_term([minus(1,X16)])),
                           else(binary_term([min,max])),
                           else(unary_term([min(X15,X16),max(X15,X16)])),
                           else(binary_term([prod])),
                           else(unary_term([prod(2,X16)])),
                           else(binary_term([abs])),
                           else(binary_term([floor])),
                           else(unary_term([min_min(1,X16)])),
                           else(unary_term([max_min(1,X16)])),
                           else(binary_term([plus_min(1,X16)])),
                           else(unary_term([floor(2,X16)])),
                           else(binary_term([ceil])),
                           else(binary_term([mfloor])),
                           else(binary_term([plus_floor(X15,X16)])),
                           else(binary_term([minus_floor(X15,X16,2,X16)])),
                           else(unary_term([ceil(2,X16)])),
                           else(unary_term([floor_min(2,X16)]))]
    ),
    length(X5, X12),
    length(X6, X13),
    length(X7, X14),
    add_key(X5, X1),
    add_key(X6, X2),
    add_key(X7, X3),
    X8 = 3,
    X9 is X12+X13+X14,    
    findall([X20,X21,X22], (X11 in X8..X9,
                      indomain(X11),
                      member(X17-X20, X1),
                      member(X18-X21, X2),
                      member(X19-X22, X3),
                      X11 is X17+X18+X19),               X4).

gen_options_lists(X15, col(X18,X16), X19, X11, X12, X14, X1, X13, X17) :- 
    (X15 \== model_seeker ->
        gen_options_lists_by_type(bool,    X15, col(X18,X16), X19, X11, X12, X14, X1, X13),
        X17 = []
        
    ;
        gen_options_lists_by_type(bool,    X15, col(X18,X16), X19, X11, X12, X14, X1, X9),
        gen_options_lists_by_type(cond_ex, X15, col(X18,X16), X19, X11, X12, X14, X1, X3),
        gen_options_lists_by_type(cond,    X15, col(X18,X16), X19, X11, X12, X14, X1, X10),
        gen_options_lists_by_type(cluster, X15, col(X18,X16), X19, X11, X12, X14, X1, X2),
        ((X9 = [], X3 = [], X10 = []) ->
            X17 = []
        ;
            gen_value_sets_wrt_boolean_operators(X15, X14, col(X18,X16), [], [], X17)
        ),
        gen_options_lists_by_type(formula(1,1), X15, col(X18,X16), X19, X11, X12, X14, X1, X4),
        gen_options_lists_by_type(formula(2,2), X15, col(X18,X16), X19, X11, X12, X14, X1, X5),
        gen_options_lists_by_type(formula(3,3), X15, col(X18,X16), X19, X11, X12, X14, X1, X6),
        gen_options_lists_by_type(formula(4,4), X15, col(X18,X16), X19, X11, X12, X14, X1, X7),
        gen_options_lists_by_type(formula(5,5), X15, col(X18,X16), X19, X11, X12, X14, X1, X8),
        append([X9,
                X4,
                X3,
                X5,
                X10,
                X6,
                X7,
                X8,
                X2], X13)
    ).

gen_options_lists_by_type(bool, _, col(X6,X5), _, _, _, _, _, []) :-
    tab_get_min_max(col(X6,X5), X9, X10), 
    X8 is X10-X9,                                
    (X8 = 0 -> true ;                             
     X8 > 2 -> true ;                             
                  false),                            
    !.
gen_options_lists_by_type(cluster, _, col(X6,X5), _, _, _, _, _, []) :- 
    tab_get_vals_fd(col(X6,X5), []),       
    !.                                               
gen_options_lists_by_type(X17, X14, col(X20,X15), X23, X4, X5, X9, X1, X7) :-
    memberchk(X17,[bool,cond,cond_ex]),         
    !,                                               
    (X1 = 1 ->                    
        X12 = [mandatory_attr(X9)]   
    ;                                                
        gen_filtered_fd(X14, col(X20,X15), X23, X5, X9, X12)
    ),
    X8 = [[attr, coef(X26,X27)],
                    [coef(X26,X27), attr],
                    [coef(X26,X27),coef(X26,X27)]], 
    (X12 = [] ->
        X7 = []
    ;
        (X17 = bool ->                         
            X4 = X10-_,        
            tab_get_min_max(col(X20,X15), X26, X27),
            X21 is X27-X26,
            (X21 = 1 ->                           
                findall([bool([neg(X18), op(X16), nb_terms(X28,X30), conds(X22), use_mods(X19)])],
                        (member([bool([neg(X18), op(X33), nb_terms(X28,X30), conds(X22), use_mods(X19)])], X10),
                         delete(X33, sum, X16), 
                         X16 = [_|_]          
                        ),
                        X6)             
            ;                                       
                findall([bool([neg(X18), op([sum]), nb_terms(X21,X21), conds(X22), use_mods(X19)])],
                        (member([bool([neg(X18), op(X33), nb_terms(X28,X30), conds(X22), use_mods(X19)])], X10),
                         memberchk(sum, X33),
                         X28 =< X21,
                         X30  >= X21
                        ),
                        X6)             
            )
        ;
         X17 = cond_ex ->                         
            X4 = X10-X11, 
            option_cond_min_cst(X14, X26), 
            option_cond_max_cst(X14, X27), 
            findall(X13,
                    (member(X13,X11),
                     X13 = [_,then(X24),else(X25)],
                     member([X24, X25],
                            X8)
                    ),
                    X3),
            findall([cond_ex([then(X24), else(X25), bool([neg(X18), op(X31), nb_terms(X28,X30), conds(X22), use_mods(X19)])])],
                    (member([bool([neg(X18), op(X31), nb_terms(X28,X30), conds(X22), use_mods(X19)])], X10),
                     X18 = 0,             
                     X31 = [X29],
                     memberchk(X29,[and,or]),
                     X28 >= 2,
                     X19 = 0,
                     member([X24, X25],
                            X8)
                    ),
                    X2),     
            append(X3, X2, X6)
        ;
            X4 = _-X3,
            findall(X13,
                    (member(X13,X3),
                     X13 = [_,then(X24),else(X25)],
                     nonmember([X24, X25],
                               X8)
                    ),
                    X6)
        ),
        cartesian_product_without_sort(X12, X6, X7)
    ).

gen_options_lists_by_type(formula(X64,X65), X69, col(X89,X70), X95, _, X40, X60, X15, X56) :- 
    length(X60, X57),

    
    (X69 \== model_seeker -> 
        tab_get_bound_type(X69, X89, X71), 
        (X71 = low ->
            X36 = binary_function([min,max,ceil,prod,mod,cmod,dmod]),  
            X37 = binary_function([ceil,mod,cmod,dmod])
        ;
            X36 = binary_function([min,max,floor,prod,mod,cmod,dmod]), 
            X37 = binary_function([floor,mod,cmod,dmod])
        ),
        option_poly_min_cst(X69,  X83),  
        option_poly_max_cst(X69,  X84),  
        option_poly_min_coef(X69, X77), 
        option_poly_max_coef(X69, X78), 
        X58              = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     main_formula([1-t([degree(1,1),non_zero(1,1,0,4),coef(X77,X78),cst(X83,X84)])])],
        X41           = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     main_formula([1-t([degree(2,2),non_zero(1,2,0,6),coef(X77,X78),cst(X83,X84)])])],
        X25        = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     unary_function([min(-2,2),max(-2,2),floor(2,2),mod(2,2),geq0,in,power(2),sum_consec]),
                                     main_formula([2-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X31         = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                     unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),mod(2,2),in,geq(0,2),power(2),sum_consec]),
                                     main_formula([1-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X11    = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     unary_function([min(-2,2),max(-2,2),floor(2,2),mod(2,2),geq0,in,power(2),sum_consec]),
                                     main_formula([2-t([degree(2,2),non_zero(1,2,0,3),coef(X77,X78),cst(X83,X84)])])],
        X12    = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     unary_function([min(-2,2),max(-2,2),floor(2,2),mod(2,2),geq0,in,power(2),sum_consec]),
                                     main_formula([2-t([degree(2,2),non_zero(1,2,0,6),coef(X77,X78),cst(X83,X84)])])],
        X20      = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                     unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),mod(2,2),in,geq(0,2),power(2),sum_consec]),
                                     main_formula([1-t([degree(2,2),non_zero(1,2,0,4),coef(X77,X78),cst(X83,X84)])])],
        X32         = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                     unary_function([min(-2,2),max(-2,2),floor(2,2),mod(2,2),geq0,in,power(2),sum_consec]),
                                     main_formula([2-t([degree(3,3),non_zero(1,3,0,2),coef(X77,X78),cst(X83,X84)])])],
        X4   = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                     unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),mod(2,2),in,geq(0,2),power(2),sum_consec]),
                                     unary_function([min(-2,2),max(-2,2),floor(2,2),mod(2,2),geq0,in,power(2),sum_consec]),
                                     main_formula([2-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X26        = [nb_polynom([1]),nb_unary([0]),nb_binary([1]),
                                     binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),
                                     main_formula([1-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X16     = [nb_polynom([1]),nb_unary([0]),nb_binary([1]),
                                     binary([min,max,floor,mfloor,prod,ceil,mod,fmod,cmod,dmod]),
                                     main_formula([1-t([degree(2,2),non_zero(1,2,0,4),coef(X77,X78),cst(X83,X84)])])],
        X24       = [nb_polynom([2]),nb_unary([0]),nb_binary([0]),
                                     X36, 
                                     main_formula([3-t([degree(1,1),non_zero(1,1,0,4),coef(X77,X78),cst(X83,X84)],
                                                       [degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X3  = [nb_polynom([2]),nb_unary([1]),nb_binary([0]),
                                     unary([min(-2,2),max(-2,2),floor(2,2),ceil(2,2),mod(2,2),in,geq(0,2),power(2),sum_consec]),
                                     X36, 
                                     main_formula([3-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)],
                                                       [degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X5   = [nb_polynom([2]),nb_unary([0]),nb_binary([0]),
                                     X36, 
                                     main_formula([3-t([degree(1,2),non_zero(1,2,0,4),coef(X77,X78),cst(X83,X84)],
                                                       [degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)])])],
        X6   = [nb_polynom([2]),nb_unary([0]),nb_binary([0]),
                                     X37, 
                                     main_formula([3-t([degree(1,1),non_zero(1,1,0,3),coef(X77,X78),cst(X83,X84)],
                                                       [degree(1,2),non_zero(1,2,0,4),coef(X77,X78),cst(X83,X84)])])],
        X13 = [X58,            X41],
        X27     = [X25,      X31],
        X17  = [X11,  X12,
                                  X20,    X32],
        X28     = [X4,
                                  X26,      X16,    
                                  X24,     X3, 
                                  X5, X6]
    ;                                    
       option_poly_min_cst(X69,  X83),  
       option_poly_max_cst(X69,  X84),  
       option_poly_min_coef(X69, X77), 
       option_poly_max_coef(X69, X78), 
       (for(X104,X64,X65),
        foreach([X48,X49],X18),
        param([X83, X84, X77, X78])
       do
        X102 is min(X104 - 1,0),
        build_poly_options(X83, X84, X77, X78, X102, X104, X48, X49)
       )
    ),
    
    
    (X69 \== model_seeker -> 
        tab_get_primaries(X89, X72),
        length(X72, X85),
        X75 is X85-1,
        ((X95 = secondary, X75 > 0)  ->
             (X15 = 1 ->                   
                X66 = [mandatory_attr(X60)]   
             ;                                               
                gen_filtered_fd(X69, col(X89,X70), X95, X40, X60, X66) 
             ),
             listify(X66, X21)
        ;
         X95 = secondary ->
            X21 = [[mandatory_attr(X72), min_attr(X85), max_attr(X85)]]
        ;
            tab_get_primaries(X89, X72),
            length(X72, X96),
            X67 = [mandatory_attr(X72), min_attr(X96), max_attr(X96)],
            filter_functional_dependencies([X67], X40, X57, X60, X42),
            tab_get_small_fd(X89, X79),
            findall(X86, (member(X103, X79), length(X103, X90),
                             X86 = [mandatory_attr(X103), min_attr(X90), max_attr(X90)]), X7),
            delete(X7, X67, X33),
            filter_functional_dependencies(X33, X40, X57, X60, X21),
            tab_get_secondaries(X89, X61),
            X80 is X85+1,
            findall(X86, (member(X97, X61), append(X72,  [X97], X91),
                             X86 = [mandatory_attr(X91), min_attr(X80), max_attr(X80)]), X52),
            (X79 = [X68|_] ->
                length(X68, X53),
                (X53 = X75 ->
                    findall(X86, (member(X92, X72),
                                     \+ memberchk(X92,X68),
                                     append(X68, [X92], X91),
                                     X86 = [mandatory_attr(X91), min_attr(X85), max_attr(X85)]), X59)
                ;
                    X59 = []
                )
            ;
                X59 = []
            ),
            append([X52, X59], X29),
            filter_functional_dependencies(X29, X40, X57, X60, X14)
        )
    ;                                          
        tab_get_ranked_fd(col(X89, X70), X73),
        (X73 = [] ->                     
            
            X50 = [],
            X51 = []
        ;

            
            
                                               
                                               
            findall(X93, (member([_,X98,_]-X93, X73), X98 =< -0.5), X34),
            length(X34, X22),
                                               
            X76 is min(X22, 10),
            prefix_length(X34, X8, X76),
                                               
            
            findall([mandatory_attr(X93), min_attr(X87), max_attr(X87)],
                    (member(X93, X8),
                     length(X93, X87)),
                    X50),
            

            
            
            tab_get_inputs(X89, X88),     
            findall(col(X89,X99),            
                    (member(col(X89,X99), X88),
                     tab_get_min_max(col(X89,X99), X100, X101),
                     abs(X100) =< 10000, abs(X101) =< 10000
                    ),
                    X43),
            findall(X94,                     
                    (member(X94, X34),(foreach(X,X94) do member(X, X43))),
                    X44),          
            length(X44, X30),
            X74 is min(X30, 10),
            prefix_length(X44, X45, X74),
                                               
            findall([mandatory_attr(X93), min_attr(X87), max_attr(X87)],
                    (member(X93, X45),
                     length(X93, X87)),
                    X51)
        )
        
    ),
    
    (X69 \== model_seeker -> 
        append([X13,X27,X17,X28], X38),
        (X95 = secondary ->
            findall(X86,                                  
                    (member(X81, X38),
                     member(X82, X21),
                     append(X81, X82, X86)),
                    X56)
        ;
            findall(X86,                                  
                    (member(X81, X38),      
                     member(X82, X42),
                     append(X81, X82, X86)),
                    X19),
            findall(X86,                                  
                    (member(X81, X38),
                     member(X82, X21),
                     append(X81, X82, X86)),
                    X39),
            findall(X86,                                  
                    (member(X81, X13),
                     member(X82, X14),
                     append(X81, X82, X86)),
                    X1),
            findall(X86,                                  
                    (member(X81, X27),
                     member(X82, X14),
                     append(X81, X82, X86)),
                    X9),
            findall(X86,                                  
                    (member(X81, X17),
                     member(X82, X14),
                     append(X81, X82, X86)),
                    X2),
            findall(X86,                                  
                    (member(X81, X28),
                     member(X82, X14),
                     append(X81, X82, X86)),
                    X10),
            append([X19,
                    X39,
                    X1,
                    X9,
                    X2,
                    X10], X56)
        )
    ;
        (foreach([X46, X47], X18),
         foreach(X62, X23),
         param([X50, X51])
        do
         findall(X63,                                
                 (member(X81, X47),
                  member(X82, X50),
                  append(X81, X82, X63)),
                 X54),
         findall(X63,
                 (member(X81, X46),
                  member(X82, X51),
                  append(X81, X82, X63)),
                 X55),
         append(X54, X55, X62)
        ),
        append(X23, X56)
    ).

get_augmented_fd(col(X5,X2), X11, X1) :-
    tab_get_arity(col(X5,_), X6),
    findall(col(X5,X13), (X13 in 1..X6,indomain(X13),X13=\=X2,tab_get_inout(col(X5,X13),input)), X7),
    cartesian_product_with_sort(X11, X7, X4),
    append(X11, X4, X9),
    remove_dups(X9, X10),
    sort_wrt_list_length(X10, X3), 
    findall(mandatory_attr(X14), (member(X14, X3), length(X14, X8), X8 =< 6), X1). 

gen_filtered_fd(X8, col(X11,X9), X12, X3, X5, X7) :- 
   X8 \== model_seeker, 
   !,
   length(X5, X4),
   tab_get_fd_eq(col(X11,X9), X13),
   (X13 = [] ->
       X7 = []
   ;
       get_augmented_fd(col(X11,X9), X13, X6),
       split_list_wrt_smallest_length(X6, X2, _),                 
       (X12 = secondary ->
           tab_get_primaries(X11, X10),                                           
           (memberchk(mandatory_attr(X10), X2) ->                    
               X1 = X2                             
           ;
               add_primaries_just_before_first_non_primary(X2,             
                                                           X10,                     
                                                           X1)    
                                                                                          
                                                                                          
                                                                                          
                                                                                          
                                                                                          
           ),
           length(X5, X4),                                             
           filter_functional_dependencies(X1,                     
                                          X3,                                
                                          X4, X5, X7)          
                                                                                          
                                                                                          
       ;
        filter_functional_dependencies(X2,                                 
                                       X3,
                                       X4, X5, X7)
       )
   ).
gen_filtered_fd(model_seeker, col(X9,X6), _, _, _, X5) :- 
   tab_get_ranked_fd(col(X9,X6), X7), 
   findall(mandatory_attr(X11), member(_-X11, X7), X4),
   length(X4, X2),
   X8 is min(X2, 20),                
   
   prefix_length(X4, X5, X8).

add_primaries_just_before_first_non_primary([], X1, [mandatory_attr(X1)]) :- !.
add_primaries_just_before_first_non_primary([X2|X3], X1, [X2|X4]) :-
    \+ list_included(X2, X1),
    !,
    add_primaries_just_before_first_non_primary(X3, X1, X4).
add_primaries_just_before_first_non_primary(X2, X1, [mandatory_attr(X1)|X2]).

filter_functional_dependencies([], _, _, _, []) :- !.
filter_functional_dependencies([X5|X7], X1, X2, X4, X6) :-
    is_list(X5),
    !,                                                                 
    filter_functional_dependencies(X5, X1, X2, X4, X3),
    (X3 = []                                                                             -> X6 = X8               ;
     (\+ memberchk(mandatory_attr(_), X3), \+ memberchk(optional_attr(_), X3)) -> X6 = X8               ;
                                                                                                      X6 = [X3|X8]),
    filter_functional_dependencies(X7, X1, X2, X4, X8).
filter_functional_dependencies([table_attr(X5)|X7], X1, X3, X4, X6) :-
    !,                                                                 
    filter_tuples(X5, X1, X3, X4, X2),  
    (X2 = [] -> X6 = X8 ; X6 = [table_attr(X2)|X8]),
    filter_functional_dependencies(X7, X1, X3, X4, X8).
filter_functional_dependencies([X4|X8], X1, X2, X3, [X4|X9]) :-
    compound(X4),
    functor(X4, X6, 1),
    memberchk(X6, [mandatory_attr,optional_attr]),
    arg(1, X4, X5),
    length(X5, X7),
    X7 =< X2,                                               
    included_in_input_params_and_not_included_in_prev_input_params(X5, X1, X3),
    !,                                                                 
                                                                       
    filter_functional_dependencies(X8, X1, X2, X3, X9).
filter_functional_dependencies([X4|X5], X1, X2, X3, [X4|X6]) :-
    \+ memberchk(X4, [mandatory_attr(_),optional_attr(_)]),
    !,                                                                 
    filter_functional_dependencies(X5, X1, X2, X3, X6).
filter_functional_dependencies([_|X5], X1, X2, X3, X6) :-
                                                                       
                                                                       
    filter_functional_dependencies(X5, X1, X2, X3, X6).

filter_tuples([], _, _, _, []) :- !.
filter_tuples([X4|X6], X1, X2, X3, [X4|X7]) :-
    length(X4, X5),
    X5 =< X2,                                               
    included_in_input_params_and_not_included_in_prev_input_params(X4, X1, X3),
    !,                                                                 
    filter_tuples(X6, X1, X2, X3, X7).   
filter_tuples([_|X5], X1, X2, X3, X6) :- 
    filter_tuples(X5, X1, X2, X3, X6).   

included_in_input_params_and_not_included_in_prev_input_params(X3, X1, X2) :-
    list_included(X3, X2),
    \+ list_included(X3, X1).

list_included([], _) :- !.
list_included([X1|X2], X3) :-
    memberchk(X1, X3),
    list_included(X2, X3).

gen_value_sets_wrt_boolean_operators(X13, X6, X14, X11, X7, X2) :- 
    option_cond_max_cst(X13, X16), 
    
    
    
    tab_get_attribute_values(X6, X14, X11, X7, X16, X1),
    tab_get_unaryf_values(X6, X14, X11, X7, prod, X16, X15),
    tab_get_unary_term_values(X6, X14, X11, X7, mod,  X16, X5),
    tab_get_ternary_values(X6, X14, X11, X7, sum_leq_attr,X8),
    tab_get_ternary_values(X6, X14, X11, X7, minus_mod_eq0,X9),
    tab_get_ternary_values(X6, X14, X11, X7, ceil_leq_floor,X10),
    findall(X4, (member(X12,[plus,abs,min,max,prod,minus,floor,ceil,mfloor,mod,cmod,dmod,fmod]),
                            tab_get_binary_term_values(X6, X14, X11, X7, X12, X16, X4)),
            X3),
    append([X1,X15,X5,X8,X9,X10|X3],X2).

gen_value_sets_wrt_boolean_operators_for_prefix_tree([], _, _) :- !.
gen_value_sets_wrt_boolean_operators_for_prefix_tree([X7|X10], X3, col(X6,X4)) :- 
    X7 = t(X9,X8,X1,X5),
    collect_cluster_zero(X5, X2),
    
    (X2 = [] ->
        X1 = []
    ;
        gen_value_sets_wrt_boolean_operators(X3, X9, col(X6,X4), [X8], X2, X1) 
    ),
    gen_value_sets_wrt_boolean_operators_for_prefix_tree(X5, X3, col(X6,X4)), 
    gen_value_sets_wrt_boolean_operators_for_prefix_tree(     X10, X3, col(X6,X4)). 


filter_vals_fd([], _, _, []) :- !.
filter_vals_fd([X4|X5], X1, X3, [X4|X2]) :-
    compound_included_in_list(X4, X3),
    \+ compound_included_in_list(X4, X1),
    !,
    filter_vals_fd(X5, X1, X3, X2).
filter_vals_fd([_|X5], X1, X3, X2) :-
    filter_vals_fd(X5, X1, X3, X2).

compound_included_in_list([], _) :-
    !.
compound_included_in_list(X1, _) :-
    integer(X1),
    !.
compound_included_in_list(X2, X1) :-
    compound(X2),
    memberchk(X2, X1),
    !.
compound_included_in_list(X3, X1) :-
    compound(X3),
    functor(X3, _, X2),
    compound_included_in_list(1, X2, X3, X1).

compound_included_in_list(X1, X2, _, _) :-
    X1 > X2, !.
compound_included_in_list(X5, X6, X2, X1) :-
    X5 =< X6,
    arg(X5, X2, X3),
    compound_included_in_list(X3, X1),
    X4 is X5+1,
    compound_included_in_list(X4, X6, X2, X1).

build_poly_options(X21, X22, X19, X20,
                   X10, X11,
                   X17, X15):-
    X7 is X11 - 1,
    X8 is max(X10 - 1, 0),
    X18              = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                 main_formula([1-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X12        = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                 unary_function([min(-3,3),max(-3,3),floor(2,3),geq0,in,power(2)]),
                                 main_formula([2-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X9       = [nb_polynom([2]),nb_unary([0]),nb_binary([0]),
                                 binary_function([min,max,floor,prod]),
                                 main_formula([3-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)],
                                                   [degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X16           = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                 main_formula([1-t([degree(1,2),non_zero(1,2,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X14         = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                 unary([min(-3,3),max(-3,3),floor(2,3),ceil(2,3),in,geq(0,3),power(2)]),
                                 main_formula([1-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X13        = [nb_polynom([1]),nb_unary([0]),nb_binary([1]),
                                 binary([min,max,floor,prod,ceil]),
                                 main_formula([1-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X2   = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                 unary([min(-3,3),max(-3,3),floor(2,3),ceil(2,3),in,geq(0,3),power(2)]),
                                 unary_function([min(-3,3),max(-3,3),floor(2,3),geq0,in,power(2)]),
                                 main_formula([2-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X1  = [nb_polynom([2]),nb_unary([1]),nb_binary([0]),
                                 unary([min(-3,3),max(-3,3),floor(2,3),ceil(2,3),in,geq(0,3),power(2)]),
                                 binary_function([min,max,floor,prod]),
                                 main_formula([3-t([degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)],
                                                   [degree(1,1),non_zero(1,1,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X4     = [nb_polynom([1]),nb_unary([0]),nb_binary([0]),
                                 unary_function([min(-3,3),max(-3,3),floor(2,3),geq0,in,power(2)]),
                                 main_formula([2-t([degree(2,2),non_zero(1,2,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X3    = [nb_polynom([2]),nb_unary([0]),nb_binary([0]),
                                 binary_function([min,max,floor,prod]),
                                 main_formula([3-t([degree(1,2),non_zero(1,2,X10,X11),coef(X19,X20),cst(X21,X22)],
                                                   [degree(1,2),non_zero(1,2,X10,X11),coef(X19,X20),cst(X21,X22)])])],
    X6      = [nb_polynom([1]),nb_unary([1]),nb_binary([0]),
                                 unary([min(-3,3),max(-3,3),floor(2,3),ceil(2,3),in,geq(0,3),power(2)]),
                                 main_formula([1-t([degree(2,2),non_zero(1,2,X8,X7),coef(X19,X20),cst(X21,X22)])])],
    X5     = [nb_polynom([1]),nb_unary([0]),nb_binary([1]),
                                 binary([min,max,floor,prod,ceil]),
                                 main_formula([1-t([degree(2,2),non_zero(1,2,X8,X7),coef(X19,X20),cst(X21,X22)])])],
    X17           = [X16,
                                 X4, X3,
                                 X6,  X5 ],
    X15         = [X18 ,
                                 X12,      X9,
                                 X2, X1,
                                 X14,       X13      ].
