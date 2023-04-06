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
% Purpose: a set of utility predicates used for the ranking of functional dependencies
% Author : Ramiz Gindullin, IMT Atlantique

:- module(rank_fd, [rank_fds/6]).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(library(statistics)).
:- use_module(tables).
:- use_module(table_access).
:- use_module(utility).
:- use_module(stat_utility).

rank_fds(X33, X34, X23, X6, X44, X7) :-    
    findall(X62, (member(X, X44), sort(X, X62)), X55),       
    critical_vals_for_pearson_correlation_coef(X23, X35),
    rows_retrieved([X6], X33, X34, X24),      
    append(X24, X36),                                  
    findall([X8,X25,X66]-X62,                        
                                                            
                                                            
                                                            
            (member(X62, X55),                               
             findall(X56, member(col(_,X56), X62), X26),  
             length(X26, X66),                             
             rows_retrieved(X26, X33, X34, X45),    
             sort(X45, X37),
             length(X37, X8),                      

               
               
               (X26 = [_] ->

                    
                    append(X45, X15), 
                    protected_correlation(X15, X36, X10),
                    get_correlation_wrt_test(X10, X35, X16),
                    
                    
                    findall(X46, (X68 in 1..X23,          
                                   indomain(X68), 
                                   nth1(X68, X45, [X47]),
                                   (X47 = 0 -> X46 is 100000 ; X46 is 1 / X47)
                                  ), X11), 
                    protected_correlation(X11, X36, X12),
                    get_correlation_wrt_test(X12, X35, X17),
                    X27 = [X16,X17]              
               ;

               
               
                X26 = [_,_] ->

                    
                    
                    adjusted_multiple_correlation(X36, X45, X2, X63),
                    f_multiple_correlation(X63, X23, 2, X69),
                    X57 is X23 - 2 - 1,                  
                    f_distribution(X66, X57, X38),
                    (X69 > X38 -> X5 is -abs(X2) ; X5 is 0),
                
                    
                    
                    findall([X58,X48,X49,X46,X50,X59,X60], (X68 in 1..X23,
                                                                indomain(X68),
                                                                nth1(X68, X45, [X39,X40]),
                                                                X58  is X39 + X40,
                                                                X48 is X39 - X40,
                                                                X49 is X39 * X40,
                                                                (X40 = 0 -> X46 is X39 * 100000 ; X46 is X39 / X40),
                                                                (X39 = 0 -> X50 is X40 * 100000 ; X50 is X40 / X39),
                                                                min_member(X59, [X39, X40]),
                                                                max_member(X60, [X39, X40])
                                                                ), X3),
                    transpose(X3, X1),
                    findall(X51,(memberchk(X41, X1),
                                  protected_correlation(X41, X36, X42),
                                  get_correlation_wrt_test(X42, X35, X51)), X18),

                    X27 = [X5|X18]         

               ;

               
               
                    length(X28, X66),                      
                    X28 = [1|_],
                    findall(X28, gen_combinations_of_values(X28, [1,-1]), X9),
                    
                    
                    
                    adjusted_multiple_correlation(X36, X45, X2, X63),
                    f_multiple_correlation(X63, X23, X66, X69),
                    X57 is X23 - X66 - 1,                  
                    f_distribution(X66, X57, X38),
                    (X69 > X38 -> X5 is -abs(X2) ; X5 is 0),
                
                    
                    
                    findall(X29, (member(X28, X9),
                                     findall(X4, (X68 in 1..X23,
                                                             indomain(X68),
                                                             nth1(X68, X45, X52),
                                                             scalar_prod(X52, X28, X4)
                                                            ), X30),
                                     protected_correlation(X30, X36, X19),
                                     get_correlation_wrt_test(X19, X35, X29)), X13),

                    
                    
                    findall(X31, (X70 in 1..X66,
                                     indomain(X70),
                                     findall(X64, (X68 in 1..X23,
                                                  indomain(X68),
                                                  nth1(X68, X45, X52),
                                                  nth1(X70, X52, X53),
                                                  X61 is X53 * X53,
                                                  findall(X54, (X71 in 1..X66,
                                                                 indomain(X71),
                                                                 X71 =\= X70, 
                                                                 nth1(X71, X52, X54)), X43),
                                                  X64 = [X61|X43]
                                                 ), X32),
                                     adjusted_multiple_correlation(X36, X32, X14, X63),
                                     f_multiple_correlation(X63, X23, X66, X69),
                                     X57 is X23 - X66 - 1,
                                     f_distribution(X66, X57, X38),
                                     (X69 > X38 -> X20 is X14 ; X20 is 0),
                                     X31 is -abs(X20)), X21),
                    append([[X5], X13, X21], X27)                
               ), 
               min_member(X25, X27)
            ), 
            X22),
    sort(X22, X7).

rows_retrieved(X3, X1, X2, X4) :- 
    findall(X, (functor(X5,X1,X2),
                user:call(X5),                       
                row_retrieved(X3, X5, X)        
               ),
            X4).

row_retrieved([], _, []) :- !.
row_retrieved(X1, X2, X4) :- 
    X1 = [X5|X6],
    arg(X5, X2, X),                 
    X4 = [X|X3],
    row_retrieved(X6, X2, X3).    
