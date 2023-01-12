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
% Purpose: primitives for instrumenting the code in order to collect statistics on the execution
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(instrument_code,[record_trace/1,
                           instrument_code/2,
                           instrument_code/3]).

:- use_module(utility).

:- dynamic instrument_in_search_formula/3.
:- dynamic instrument_found_trivial/3.
:- dynamic instrument_found_conjecture/4.
:- dynamic instrument_fail_without_time_out/3.
:- dynamic instrument_time_out/3.
:- dynamic instrument_in_formula_generator/3.

record_trace(X7) :-                                          
    findall(instrument_in_search_formula(X10, X8, X11),
            instrument_in_search_formula(X10, X8, X11),
            X1),
    write_list(X1, X7),
    format(X7, '~n', []),
    findall(instrument_found_trivial(X10, X8, X11),
            instrument_found_trivial(X10, X8, X11),
            X2),
    write_list(X2, X7),
    format(X7, '~n', []),
    findall(instrument_found_conjecture(X10, X8, X11, X9),
            instrument_found_conjecture(X10, X8, X11, X9),
            X3),
    write_list(X3, X7),
    format(X7, '~n', []),
    findall(instrument_fail_without_time_out(X10, X8, X11),
            instrument_fail_without_time_out(X10, X8, X11),
            X4),
    write_list(X4, X7),
    format(X7, '~n', []),
    findall(instrument_time_out(X10, X8, X11),
            instrument_time_out(X10, X8, X11),
            X5),
    write_list(X5, X7),
    format(X7, '~n', []),
    findall(instrument_in_formula_generator(X10, X8, X11),
            instrument_in_formula_generator(X10, X8, X11),
            X6),
    write_list(X6, X7),  
    format(X7, '~n', []).

instrument_code(X1, X3-X5) :-
    functor(X4, X1, 3),    
    arg(1, X4, X5),            
    arg(2, X4, X3),           
    (call(X4) ->
        arg(3, X4, X7),          
        retract(X4)             
    ;
        X7 = 0
    ),
    X6 is X7+1,                    
    functor(X2, X1, 3), 
    arg(1, X2, X5),         
    arg(2, X2, X3),        
    arg(3, X2, X6),          
    assert(X2),              
    !.
instrument_code(X1, X2) :-
    write(instrument_code(X1, X2)), nl, halt.

instrument_code(X1, X3-X6, X4) :-
    functor(X5, X1, 4),    
    arg(1, X5, X6),            
    arg(2, X5, X3),           
    arg(3, X5, X4),           
    (call(X5) ->
        arg(4, X5, X8),          
        retract(X5)             
    ;
        X8 = 0
    ),
    X7 is X8+1,                    
    functor(X2, X1, 4), 
    arg(1, X2, X6),         
    arg(2, X2, X3),        
    arg(3, X2, X4),        
    arg(4, X2, X7),          
    assert(X2),              
    !.    
instrument_code(X1, X2, X3) :-
    write(instrument_code(X1, X2, X3)), nl, halt.
