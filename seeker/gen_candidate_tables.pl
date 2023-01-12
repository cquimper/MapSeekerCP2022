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
% Purpose: Generate names for metadata files
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(gen_candidate_tables,[gen_table_and_metadata_file_names/5,
                                remove_signature_and_table_facts/1]).

:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(utility).

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
    retractall(X4).                                             
