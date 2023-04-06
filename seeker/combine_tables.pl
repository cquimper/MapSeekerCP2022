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
% Purpose: Merge two (or potentially more) data tables into one file using the information from primary and foreign keys of these tables
% Author : Ramiz Gindullin, IMT Atlantique

:- use_module(library(lists)).
:- use_module(library(between)).

:- use_module(table_access).

top:-
    combine_tables(use_case_tasks_sc1, use_case_machines, 1, _, _),
    combine_tables(use_case_tasks_sc2, use_case_machines, 1, _, _),
    combine_tables(use_case_tasks_sc3, use_case_machines, 1, _, _).

combine_tables(X14, X12, X20, X27, X31):-
    
    X15 = 'data/model_seeker/data0/', 
    X7 = merge_table_info,
    atom_concat(X15, X14, X2), atom_concat(X15, X12, X1),
    atom_concat(X2, '.pl', X8), atom_concat(X1, '.pl', X5),
    atom_concat(X2, '_metadata.pl', X6), atom_concat(X1, '_metadata.pl', X4),
    consult(X8), consult(X5),
    consult(X6), consult(X4),
    
    
    tab_get_arity(col(X14,_), X34),                   
    tab_get_arity(col(X12,_), X32),                 
    tab_get_pks(col(X14,_), [_-X48|_]),                   
    tab_get_fks(col(X14,_), X35),                     
                                                                
                                                                
                                                                
                                                                
                                                                
    memberchk([ind(_,pk(X12,X45),fk(X46))|_], X35),  
    length(X45, X28),                                      

    ((X20 = 1) ->
        findall(col(X14,X53),
                between(1,X34,X53), X21)                 
    ;
        findall(col(X14,X53), (between(1,X34,X53),        
                nonmember(X53, X46)), X21)                  
    ),
    findall(col(X12,X53), (between(1,X32,X53),          
                nonmember(X53, X45)), X16),                
    
    append(X21,X16,X31),                       
    
                                                                
    ((X20 = 1) ->               
        X54 is X34 + X32 - X28                        
    ;
        X54 is X34 + X32 - 2 * X28                    
    ),
    X49 is X54 + 1,
    
                           
    atom_concat(X14, '_', X22),                    
    atom_concat(X22, X12, X27),
    atom_concat(X27, '.pl', X3),
    atom_concat(X15, X3, X10),
    open(X10, write, X42),
    format(X42, ':- multifile signature/3.~n:- multifile ~w/~w.~n:- multifile ~w/~w.~n:- dynamic signature/3.~n:- dynamic ~w/~w.~n:- dynamic ~w/~w.~n~n',
           [X27,X54,X7,X49,X27,X54,X7,X49]),
    
    functor(X23, signature, 3),                           
    arg(1, X23, X27),                                
    arg(2, X23, 0),                                       
    functor(X13,t,X54),                                   
    (foreach(col(X9,X11), X31), for(X17,1,X54),
     param(X13), param(X14)                      
     do (functor(X18,t,3),                               
         tab_get_name(col(X9,X11), X43),  
         arg(1, X18, X43),                              
         (X9 = X14 ->                        
                tab_get_kind(col(X9,X11),
                              X44),                            
                tab_get_inout(col(X9,X11),
                              X37)                            
         ;
          X44 = primary,                                       
          X37 = input),                                       
         arg(2, X18, X44),                              
         arg(3, X18, X37),                             
         arg(X17, X13, X18))),            
    arg(3, X23, X13),                             
    format(X42, '~w.~n~n', X23),
    

    functor(X29, X7, X49),
    arg(1,X29,X27),
    (foreach(col(X24, X38), X31), for(X39,2,X49), param(X29), param([X14,X12,X48,X46, X45])
    do
     arg(X39, X29, X33),
     (X24 = X14 ->
        X25 = child,
        (memberchk(X38,X48)  -> X19 = primary                   ;
         memberchk(X38,X46) -> X19 = foreign(X12,X45)  ;
                                 X19 = data                      )
     ;
        X25 = parent,
        X19 = data
     ),
     X33 = t(X24,X25,X19,X38)
    ),
    
    format(X42, '~w.~n~n', X29),


    findall(X36, (functor(X30, X14, X34), call(X30),           
                     functor(X26, X12, X32), call(X26),       
                     ( foreach(X50, X46), foreach(X51, X45), param(X30), param(X26)
                       do (arg(X50, X30, X40),                                  
                           arg(X51, X26, X40)                                  
                          )                                                           
                     ),
                     functor(X36,X27,X54),                                      
                                                                                      
                     (foreach(col(X41,X47), X31),for(X53,1,X54),                    
                      param(X36), param(X30), param(X26)
                      
                      do ((X41 = X14 -> arg(X47, X30,  X40);          
                                                 arg(X47, X26, X40)),         
                          arg(X53, X36, X40)                                       
                         )
                     ),
                     
                     format(X42, '~w.~n', X36),
                     
                     true), _),
        close(X42),
        write(table(X27,0,X54,0,[pk(X48),no_fk])),write('.'),nl,
        remove_signature_and_table_facts(X14, X12).


remove_signature_and_table_facts(X4, X3) :-
    signature(X4, _, X7),                                
    functor(X7, t, X2),                              
    functor(X8, X4, X2),                     
    signature(X3, _, X5),                              
    functor(X5, t, X1),                            
    functor(X6, X3, X1),                  
    retractall(signature(_,_,_)),                                       
    retractall(X8),
    retractall(X6).                                             
