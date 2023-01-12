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
% Purpose: Main program to run to generate conjectures (in the context of combinatorial objects) or
%          to acquire constraints (in the context of ASSISTANT)
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(clpfd)).
:- use_module(gen_candidate_tables).

:- use_module(table_access).
:- use_module(tables). 

:- multifile conjecture/6.
:- dynamic conjecture/6.

:- multifile table_metadata/31.
:- dynamic table_metadata/31.

top(X5) :-                                     
    attributes_combi(X5, X4),          
    member(X19, [low(_), up(_)]),
    member(X6, X4),                    
    functor(X19, X7, 1),
    atom_concat('conjectures_', X7, X14  ), 
    atom_concat(X14,         '_',       X15  ), 
    atom_concat(X15,         X6, X11), 
    atom_concat('found_conjectures/', X11, X8),
    atom_concat(X8, '_bool.pl', X20),
    consult(X20),
    gen_tables(X21, X5, X6, X19, _), 
    max_size_combi(X5, X24),         
    number_codes(X24, X9),           
    atom_codes(X12, X9),         
    atom_concat('data/', X5, X14), 
    atom_concat(X14,  '/data',   X15), 
    atom_concat(X15,  X12,  X16), 
    atom_concat(X16,  '/',       X17), 
    atom_concat(X17,  X21,     X18), 
    atom_concat(X18, '_metadata.pl', X2),
    consult(X2),
    tab_get_arity(col(X21,_), X22),
    X28 in 1..X22,
    indomain(X28),
    tab_get_name(col(X21,X28), X25),
    tab_get_kind(col(X21,X28), X26),
    memberchk(X26, [low,up,secondary]),
    tab_get_min(col(X21,X28), X29),
    tab_get_max(col(X21,X28), X30),
    tab_get_nval(col(X21,X28), X27),
    X23 is X30-X29,
    check_range_nval(X23, X27, X10),
    (conjecture(X26,col(X21,X28),_,_,_,_) ->
        false
    ;
        write(X21), write(' '),
        write(X10), write(' '),
        write(X25), write(' '),
        (X10 = range ->
            write(X29), write(' '), write(X30)
        ;
            write(X27)
        ),
        nl,
        false
    ),
    get_metadata_arity(X1),                    
    functor(X3, table_metadata, X1), 
    retractall(X3),
    false.

check_range_nval(X1, _, range) :-
    X1 > 1,
    X1 =< 3,
    !.
check_range_nval(_, X1, val) :-
    X1 > 2,
    X1 =< 4.

gen_tables(X4, X1, X2, X5, X3) :-             
    gen_candidate_tables(X4, X1, X2, X5, X3). 
gen_tables(_, _, _, _, _) :-                                          
    functor(X1, conjecture, 6),
    retractall(X1),
    false.
