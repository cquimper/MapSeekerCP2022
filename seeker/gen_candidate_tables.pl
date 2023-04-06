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
% Purpose: Test program
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_candidate_tables,[gen_candidate_tables/5,                
                                gen_table_and_metadata_file_names/5,
                                remove_signature_and_table_facts/1]).  

:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(utility).

gen_candidate_tables(X8, X5, X6, X9, X7) :- 
    (X5 = graph ->                                           
        X2 = [low_c_minc_maxc_mins_maxs,
                           low_c_minc_mins_maxs,
                           low_maxc_mins_maxs,
                           low_maxc_mins_maxs_minc,
                           low_maxc_mins_minc,
                           low_maxc_s_mins_maxs_mina,
                           low_maxc_s_mins_maxs_minc,
                           low_maxc_s_mins_minc,
                           low_minc_maxc_maxs_mins,
                           low_minc_maxc_mins_maxs,
                           low_minc_maxc_s_mins_maxs_mina,
                           low_minc_mins_maxs,
                           low_minc_mins_maxs_maxc,
                           low_minc_s_maxc,
                           low_minc_s_maxs_maxc,
                           low_minc_s_mins_maxc,
                           low_minc_s_mins_maxs_maxc,
                           up_c_maxs_mins,
                           up_c_minc_maxs_mins,
                           up_maxc_maxs_mins,
                           up_maxc_mins_maxs,
                           up_maxc_mins_maxs_minc,
                           up_maxc_s_c,
                           up_maxc_s_maxs,
                           up_maxc_s_minc,
                           up_maxc_s_mins,
                           up_maxc_s_mins_c,
                           up_maxc_s_mins_maxs,
                           up_maxc_s_mins_minc,
                           up_minc_maxc_maxs_mins,
                           up_minc_maxc_mins_maxs,
                           up_minc_maxc_s_c,
                           up_minc_maxc_s_maxs,
                           up_minc_maxc_s_mins,
                           up_minc_maxc_s_mins_c,
                           up_minc_maxc_s_mins_maxs,
                           up_minc_maxs_mins,
                           up_minc_s_c,
                           up_minc_s_mins_c]
    ;
     memberchk(X5, [partition,partition0,group,cgroup,forest]) ->   
        X2 = []
    ;                                                                      
        write(gen_candidate_tables(X5)), nl, halt                   
    ),                                                                     
    attributes_combi(X5, X3), 
    member(X6, X3),           
    low_up_attributes_combi(X5, X1),
    ((memberchk(low-X6, X1), \+memberchk(up-X6,  X1)) -> X9 = low(_)                ;  
     (memberchk(up-X6,  X1), \+memberchk(low-X6, X1)) -> X9 = up(_)                 ;  
                                                                                                                 member(X9, [low(_), up(_)])), 

    X7 in 1..3, indomain(X7),                         
    get_tables(X5, 2, X7, X9, X4), 
    member(X8, X4),                                
    atom_proper_suffix_add_underscore(X8, X6),      
    (memberchk(X8, X2) -> false ; true).      

gen_table_and_metadata_file_names(X5, X10, X9, X6, X2) :-
	number_codes(X10, X7),                              
	atom_codes(X8, X7),                            
	atom_concat(X5, X8, X3),              
	atom_concat(X3, '/', X4),                  
	atom_concat(X4, X9, X1),            
	atom_concat(X1, '.pl', X6),             
	atom_concat(X1, '_metadata.pl', X2). 

remove_signature_and_table_facts(X2) :-
    user:signature(X2, _, X3),                               
    functor(X3, t, X1),                                  
    functor(X4, X2, X1),                              
    retractall(user:signature(_,_,_)),                            
    retractall(user:X4).                                             
