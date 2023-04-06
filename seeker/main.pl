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

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(tables).
:- use_module(table_access).
:- use_module(utility).
:- use_module(stat_utility).
:- use_module(gen_bool_formula).
:- use_module(gen_formula).
:- use_module(gen_formula_term).
:- use_module(gen_formula_write).
:- use_module(gen_candidate_tables).
:- use_module(gen_options_for_formulae).
:- use_module(eval_formula).
:- use_module(instrument_code).

:- multifile table_metadata/31.
:- dynamic table_metadata/31.
:- multifile table_info/6.
:- dynamic table_info/6.

:- multifile max_cost/1.
:- dynamic max_cost/1.
:-dynamic fout/1.


average_size(X1) :-                                                             
        atoms_concat(['data/',X1,'/meta_metadata_',X1,'.pl'], X2), 
        consult(X2),                                      
        findall(X5, (gen_candidate_tables(X4, X1, _, _, _), 
                       write(X4), nl,
                       size_to_compute_conjectures(X4,_,X5,_)), X3),
        sumlist(X3, X6),
        length(X3, X7),
        X8 is X6 / X7,
        write(t(sum,X6,len,X7,av,X8)), nl,

        
        retractall(size_to_compute_conjectures(_,_,_,_)). 

top(0) :-
    !,
    top(model_seeker, assistant, 0),
retractall(table_info(_,_,_,_,_,_)). 
top(1) :-
    g8.                              

g1  :- top(graph,  v,    low(v)).                             
g2  :- top(graph,  c,    low(c)).                             
g3  :- top(graph,  minc, low(minc)).                          
g4  :- top(graph,  maxc, low(maxc)).                          
g5  :- top(graph,  s,    low(s)).                             
g6  :- top(graph,  mins, low(mins)).                          
g7  :- top(graph,  maxs, low(maxs)).                          
g8  :- top(graph,  mina, low(mina)).                          
g9  :- top(graph,  v,    up(v)).                              
g10 :- top(graph,  c,    up(c)).                              
g11 :- top(graph,  minc, up(minc)).                           
g12 :- top(graph,  maxc, up(maxc)).                           
g13 :- top(graph,  s,    up(s)).                              
g14 :- top(graph,  mins, up(mins)).                           
g15 :- top(graph,  maxs, up(maxs)).                           
g16 :- top(graph,  maxa, up(maxa)).                           

f1  :- top(forest, t,    low(t)).                             
f2  :- top(forest, v,    low(v)).                             
f3  :- top(forest, f,    low(f)).                             
f4  :- top(forest, minf, low(minf)).                          
f5  :- top(forest, maxf, low(maxf)).                          
f6  :- top(forest, mind, low(mind)).                          
f7  :- top(forest, maxd, low(maxd)).                          
f8  :- top(forest, minp, low(minp)).                          
f9  :- top(forest, maxp, low(maxp)).                          
f10 :- top(forest, mint, low(mint)).                          
f11 :- top(forest, maxt, low(maxt)).                          
f12 :- top(forest, t,    up(t)).                              
f13 :- top(forest, v,    up(v)).                              
f14 :- top(forest, f,    up(f)).                              
f15 :- top(forest, minf, up(minf)).                           
f16 :- top(forest, maxf, up(maxf)).                           
f17 :- top(forest, mind, up(mind)).                           
f18 :- top(forest, maxd, up(maxd)).                           
f19 :- top(forest, minp, up(minp)).                           
f20 :- top(forest, maxp, up(maxp)).                           
f21 :- top(forest, mint, up(mint)).                           
f22 :- top(forest, maxt, up(maxt)).                           

p1  :- top(partition, nval,        low(nval)).                
p2  :- top(partition, min,         low(min)).                 
p3  :- top(partition, max,         low(max)).                 
p4  :- top(partition, range,       low(range)).               
p5  :- top(partition, sum_squares, low(sum_squares)).         
p6  :- top(partition, nval,        up(nval)).                 
p7  :- top(partition, min,         up(min)).                  
p8  :- top(partition, max,         up(max)).                  
p9  :- top(partition, range,       up(range)).                
p10 :- top(partition, sum_squares, up(sum_squares)).          

p01  :- top(partition0, nval,        low(nval)).              
p02  :- top(partition0, min,         low(min)).               
p03  :- top(partition0, max,         low(max)).               
p04  :- top(partition0, range,       low(range)).             
p05  :- top(partition0, sum_squares, low(sum_squares)).       
p06  :- top(partition0, nval,        up(nval)).               
p07  :- top(partition0, min,         up(min)).                
p08  :- top(partition0, max,         up(max)).                
p09  :- top(partition0, range,       up(range)).              
p010 :- top(partition0, sum_squares, up(sum_squares)).        

group01 :- top(group, ng,           low(ng)).                 
group02 :- top(group, nv,           low(nv)).                 
group03 :- top(group, smin,         low(smin)).               
group04 :- top(group, smax,         low(smax)).               
group05 :- top(group, srange,       low(srange)).             
group06 :- top(group, ssum_squares, low(ssum_squares)).       
group07 :- top(group, dmin,         low(dmin)).               
group08 :- top(group, dmax,         low(dmax)).               
group09 :- top(group, drange,       low(drange)).             
group10 :- top(group, dsum_squares, low(dsum_squares)).       
group11 :- top(group, ng,           up(ng)).                  
group12 :- top(group, nv,           up(nv)).                  
group13 :- top(group, smin,         up(smin)).                
group14 :- top(group, smax,         up(smax)).                
group15 :- top(group, srange,       up(srange)).              
group16 :- top(group, ssum_squares, up(ssum_squares)).        
group17 :- top(group, dmin,         up(dmin)).                
group18 :- top(group, dmax,         up(dmax)).                
group19 :- top(group, drange,       up(drange)).              
group20 :- top(group, dsum_squares, up(dsum_squares)).        

cgroup01 :- top(cgroup, ng,           low(ng)).               
cgroup02 :- top(cgroup, nv,           low(nv)).               
cgroup03 :- top(cgroup, smin,         low(smin)).             
cgroup04 :- top(cgroup, smax,         low(smax)).             
cgroup05 :- top(cgroup, srange,       low(srange)).           
cgroup06 :- top(cgroup, ssum_squares, low(ssum_squares)).     
cgroup07 :- top(cgroup, dmin,         low(dmin)).             
cgroup08 :- top(cgroup, dmax,         low(dmax)).             
cgroup09 :- top(cgroup, drange,       low(drange)).           
cgroup10 :- top(cgroup, dsum_squares, low(dsum_squares)).     
cgroup11 :- top(cgroup, ng,           up(ng)).                
cgroup12 :- top(cgroup, nv,           up(nv)).                
cgroup13 :- top(cgroup, smin,         up(smin)).              
cgroup14 :- top(cgroup, smax,         up(smax)).              
cgroup15 :- top(cgroup, srange,       up(srange)).            
cgroup16 :- top(cgroup, ssum_squares, up(ssum_squares)).      
cgroup17 :- top(cgroup, dmin,         up(dmin)).              
cgroup18 :- top(cgroup, dmax,         up(dmax)).              
cgroup19 :- top(cgroup, drange,       up(drange)).            
cgroup20 :- top(cgroup, dsum_squares, up(dsum_squares)).      

top(X4, X5, X7) :-                                                     
    (X4 \== model_seeker ->                                                      
        functor(X7, X8, 1),
        atoms_concat([X4,'_',X8,'_',X5], X2),              
        atoms_concat(['data/',X4,'/found_conjectures_',X2,'.pl'], X1), 
        atoms_concat(['data/',X4,'/meta_metadata_',X4,'.pl'], X6),  
        consult(X6)                                    
    ;
        X2 = found_model, 
        atoms_concat(['data/',X4,'/',X2,'.pl'], X1) 
    ),
    open(X1, write, X9),                        
    format(X9, '% Contains all found conjectures generated by main, where each conjecture is a conjecture\\6 fact of the form:~n', []),
    format(X9, '%  . Kind:           low (if lower bound); up (if upper bound); primary, secondary (if equality),~n', []),
    format(X9, '%  . col(Table,Col): table and column for which the conjecture holds (left-hand side of the conjecture),~n', []),
    format(X9, '%  . Name:           name corresponding to col(Table,Col),~n', []),
    format(X9, '%  . MaxN:           size that was used for generating the conjecture,~n', []),
    format(X9, '%  . Cost:           cost associated with the conjecture,~n', []),
    format(X9, '%  . Formula:        formula associated with the conjecture (right-hand side of the conjecture).~n~n', []),
    format(X9, ':- multifile conjecture/6.~n', []),             
    format(X9, ':- dynamic conjecture/6.~n~n', []),             
    top_search(X4, X5, X7, X9),                
    close(X9),
    atoms_concat(['data/',X4,'/trace_',X2,'.pl'], X3), 
    open(X3, write, X10),
    record_trace(X10),
    close(X10),
    (X4 \== model_seeker -> 
        get_number_of_found_bounds(X4, X1),
        check_conjectures(X4, X1), 
        retractall(size_to_compute_conjectures(_,_,_,_)) 
    ;
        true
    ).

top_search(X17, X18, X26, X28) :- 
    gen_options_bool(X17, X9), 
    gen_options_cond(X17, X10), 
    X3 = X9-X10,                     
    (X17 \== model_seeker -> 
        gen_candidate_tables(X27, X17, X18, X26, X25), 
        size_to_compute_conjectures(X27, _, X29, _),            
        X30 = t(X18, X25, X27)                          
    ;                                                              
        get_tables(X17, 0, _, _, X15), 
        X29 = 0,                                                  
        member(X27, X15),                                 
        X30 = 0
    ),
    retractall(max_cost(_)),                                       
    nl,
    write('--------------------------------------------------------------------------------'), nl,
    write('Handle table '), write(X27), write(' of '), write(X29), nl,
    write('--------------------------------------------------------------------------------'), nl,
    atoms_concat(['data/',X17,'/data'], X24),                               
    gen_table_and_metadata_file_names(X24, X29, X27, X19, X5), 
    consult(X19),                                            
    consult(X5),                                         
    clear_type_found_formula,                                      
    (X17 \== model_seeker -> 
        tab_get_primaries(X27, X20),                       
 
        tab_get_secondaries(X27, X11),                   
        search_secondaries(X11, X3,           
                           [], X20, X29, 2-X30, X28, X12),
        nl,
        tab_get_bound_col(X27,X31),                              
        (tab_get_type(col(X27,X31), cst) ->                      
            write_found_constant(X27, X31, X29, 1-X30, X28),
            assert(max_cost(0)),                                   
            assert(max_cost(col(X27,X31), 0))                    
        ;
         (tab_get_equal(col(X27,X31), X16),               
          memberchk(col(X27,X16), X20)) ->
            write_found_identical_column(X27, X31, X16, X29, 1-X30, X28),
            assert(max_cost(0)),                                   
            assert(max_cost(col(X27,X31), 0))                    
        ;                                                          
         get_first_found_secondary_equal_to_bound(X12, X27, X31, X6) ->
            write_found_identical_column(X27, X31, X6, X29, 1-X30, X28),
            assert(max_cost(0)),                                   
            assert(max_cost(col(X27,X31), 0))                    
        ;
            append(X20, X11, X21),
            length(X20, X7),
            length(X21, X8),
            length(X12, X4),
            remove_cst_columns(X12, X1),
            remove_cst_columns(X21, X2),    
                                                                   
            tab_get_fd(col(X27,X31), X32),                        
            search_with_small_fd_primaries(X32, X7, X20, X3, X29, X27, X31, 1-X30, X28),
            (max_cost(X22) -> X13 is X22+1 ; X13 = 100000),
            (X4 = X7 -> true                 
            ;                                                      
                search_a_formula(X13, X17, X3, X20, X1, 0, X29, X27, X31, 1-X30, X28) 
            ),
            (X8 = X4 -> true                 
            ;                                                      
                (max_cost(X23) -> X14 is X23+1 ; X14 = X13),
                search_a_formula(X14, X17, X3,   
                                 X1, X2,
                                 0, X29, X27, X31, 1-X30, X28)
            )
        )
    ;                                                              
        tab_get_secondaries(X27, X11),                   
        nl,                                                        
        search_secondaries(X11, X3, 0, 1-0, X28)
    ),
    remove_signature_and_table_facts(X27),                       
    false.
top_search(_, _, _, _).

get_first_found_secondary_equal_to_bound([col(X3,X1)|_], X3, X2, X1) :-
    tab_get_kind(col(X3,X1), secondary),
    tab_get_equal(col(X3,X1), X2),
    !.
get_first_found_secondary_equal_to_bound([_|X5], X3, X2, X1) :-
    get_first_found_secondary_equal_to_bound(X5, X3, X2, X1).

remove_cst_columns(X2, X1) :-
    findall(X4, (member(X4, X2), tab_get_type(X4, X3), X3 \== cst), X1).


search_secondaries(X7, X2, X4, X10, X12, X11, X13, X8) :-
    retractall(max_cost(_,_)),                           
                                                         
                                                         
                                                         
                                                         
    search_secondaries1(X7, X2, X4, X10, X12, X11, X13, X9, X3),
    (X3 = [_|_] ->
        write('----------'), nl,
        append(X10, X3, X5), 
        search_secondaries1(X3, X2, X10, X5, X12, X11, X13, _, X1),
        (X1 = [_|_] ->
            write('----------'), nl
        ;
            true
        )
    ;
        true
    ),
    ((X9    = [_|_],                            
      X3 = [_|_]) ->                         
        append(X10, X3, X6), 
        search_secondaries(X9,                  
                           X2, X10, X6, X12, X11, X13, X8)
    ;                                                    
     X9 = [_|_] ->                              
        X8 = X10,
        write('could not find a formula for '), write_col_names(X9)
    ;                                                    
        append(X10, X3, X8)
    ).

get_smallest_set_included_in([], _, _, [], []) :- !.
get_smallest_set_included_in([X3|X1], _, X2, X3, X1) :-
    included_in_set(X3, X2), !.
get_smallest_set_included_in([_|X6], X2, X3, X4, X1) :-
    get_smallest_set_included_in(X6, X2, X3, X4, X1).

included_in_set([], _) :- !.
included_in_set([X1|X2], [X1|X3]) :- !,
    included_in_set(X2, X3).
included_in_set([col(X1,X2)|X3], [col(X1,X4)|X5]) :-
    X4 < X2,
    included_in_set([col(X1,X2)|X3], X5).

search_with_small_fd_primaries(X11, X2, X3, X1, X8, X7, X10, X6, X9) :-
    get_smallest_set_included_in(X11, X2, X3, X5, X4), 
    (X5 = [] ->                                                                     
        (max_cost(_) ->                                                                     
            true                                                                            
        ;                                                                                   
            search_a_formula(100000, 1, X1, [], X3, 0,                
                             X8, X7, X10, X6, X9)
        )
    ;                                                                                       
        search_a_formula(100000, 1, X1, [], X5, 1,                     
                         X8, X7, X10, X6, X9),
        (max_cost(_) ->                                                                     
            true                                                                            
        ;                                                                                   
            search_with_small_fd_primaries(X4, X2, X3,        
                                           X1, X8, X7, X10, X6, X9)
        )
    ).

search_secondaries1([], _, _, _, _, _, _, [], []) :- !.
search_secondaries1([col(X12,X15)|X17], X2, X3, X6, X13, X11, X14, X7, X4) :-
(X2 = [] -> write('option bool cond is empty') ; true),
    (X3 = [] ->                                                            
        retractall(max_cost(_)),                                                        
        length(X6, X5),                                            
        tab_get_fd(col(X12,X15), X16),                                                 
        search_with_small_fd_primaries(X16, X5, X6, X2, X13, X12, X15, X11, X14)
    ;
        delete(X6, col(X12,X15), X1),                       
        (max_cost(col(X12,X15),X9) ->                                         
            true                                                                        
        ;                                                                               
            X9 = 100000                                                         
        ),                                                                              
        search_a_formula(X9, 1, X2, X3, X1, 0, X13, X12, X15, X11, X14)
    ),
    (max_cost(_) ->                                                                     
        X7 = X10,                                                         
        X4 = [col(X12,X15)|X8]                                   
    ;                                                                                   
        X7    = [col(X12,X15)|X10],                                     
        X4 = X8                                                    
    ),                                                                                  
    search_secondaries1(X17, X2, X3, X6, X13, X11, X14, X10, X8).

search_secondaries([], _, _, _, _) :- !.
search_secondaries([col(X11,X22)|X24], X1, X15, X5, X16) :-
   tab_get_name(col(X11,X22),X17),
   tab_get_inputs(X11, X9),     
   findall(X12, (member(X12,X9),
                   tab_get_type(X12, X18),
                   memberchk(X18, [int,bool])),                                         
            X2),
   write('Search formula for column '), write(X22), write(': '), write(X17), nl,
   statistics(total_runtime,[X13|_]),
   search_a_formula(100000, model_seeker, X1, [], X2, 0, X15, X11, X22, X5, X16), 
   statistics(total_runtime,[X19|_]),
   X6 is X19 - X13,
   write(X6), write('ms'), nl,

   tab_get_arity(col(X11,_),X20), X7 is X20 - 1,
   tab_get_nb_rows(col(X11,_),X10),
   call(table_info(X11,X3,X23,_,X14,X8)),
   call(fout(X21)),
   format(X21,'performance(~w,~w,~w,~w,~w,~w,~w).~n',[X11,X7-X10,X3,X23,X14,X8,X6]),
   
            
   
   search_secondaries(X24, X1, X15, X5, X16).

write_col_names([]) :- !, nl.
write_col_names([col(X1,X3)|X4]) :-
    tab_get_name(col(X1,X3), X2),
    write(X2),
    (X4 = [_|_] ->
        (X4 = [_] -> write(' and ') ; write(', '))
    ;
        true
    ),
    write_col_names(X4).

search_a_formula(X11, X16, X2, X3, X8, X1, 
                 X24, X22, X30, X18, X25) :-
    instrument_code(instrument_in_search_formula, X18),
    retractall(max_cost(_)),                                                    
    X11 > 0,                                                             
    tab_get_equal(col(X22,X30), X31),                                          
    tab_get_type(col(X22,X30), X26),
    tab_get_kind(col(X22,X30), X27),
    tab_get_name(col(X22,X30), X28),
    tab_get_max_name_length(X22, secondary, X5),
    atom_codes(X28, X23),
    length(X23, X12),
    X6 is X5-X12,                                  
    (X16 \== model_seeker -> 
        (X27 = secondary ->                                                    
            X13 = 1                                                      
        ;
        X3 = [] ->
            X13 = 1
        ;
            X13 = 0
        )
    ;
        X13 = 1
    ),
    (X31 > 0 ->
        get_first_equal_column(X22, X30, X17),
        (X30 = X17 -> X19 = 0 ; X19 = X17)
    ;
        X19 = 0
    ),    
    (X19 > 0 ->                                                             
        (X13 = 1 ->
            (memberchk(col(X22,X19), X8) ->                      
                X14 = 1                                                  
            ;
                X14 = 0
            ),
            (X14 = 1 ->
                write_found_identical_column(X22, X30, X19, X24, X18, X25),
                assert(max_cost(0)),                                            
                assert(max_cost(col(X22,X30), 0))                             
            ;
                false
            )
        ;
            true
        )
    ;
     X26 = cst ->                                                              
        (X13 = 1 ->                                                      
            write_found_constant(X22, X30, X24, X18, X25),
            assert(max_cost(0)),                                                
            assert(max_cost(col(X22,X30), 0))                                 
        ;
            true
        )
    ;
        keep_conditional_formula(X27, X30),                                    
                                                                                
        gen_options_lists(X16, col(X22,X30), X27, X2,     
                          X3, X8, X1,  
                          X7, X9),
        tab_get_min(col(X22,X30),                                             
                        X20),                                                

        formula_generator(X18, X7, X9, X20, X27, X22, X30, X11,
                          X4, X29, X21),
        (X21 = time_out ->
            instrument_code(instrument_time_out, X18),
            false                                                               
        ;
            record_type_found_formula(X4, X30, X29),               
            retractall(max_cost(_)),
            retractall(max_cost(col(X22,X30), _)),
            X15 is X29-1,
            assert(max_cost(X15)),
            assert(max_cost(col(X22,X30), X15)),                       
            write('Cost = '),
            (X29 < 10 -> write(' ') ; true),
            write(X29), write(':  '),
            write(X28),
            (X27 = secondary -> write_spaces(X6), write(' = ')  ;
             X27 = low       ->                              write(' >= ') ;
                                                              write(' =< ') ),
            formula_pattern_write(X4), nl,
            formula_pattern_create_term(X4, X10),
            format(X25, 'conjecture(~w,~w,~w,~w,~w,~w).~n~n', [X27,col(X22,X30),X28,X24,X29,X10]),
            instrument_code(instrument_found_conjecture, X18, X29)
        )
    ),
    formula_generator_if_cost_reach_0,
    !.
search_a_formula(_, _, _, _, _, _, _, _, _, _, _).                                

formula_generator_if_cost_reach_0 :- max_cost(X1), X1 =< 0, !.
formula_generator_if_cost_reach_0 :- false.

write_found_constant(X8, X12, X10, X4, X11) :-
    tab_get_kind(col(X8,X12), X5),
    tab_get_name(col(X8,X12), X6),
    tab_get_max_name_length(X8, secondary, X1),
    atom_codes(X6, X9),
    length(X9, X3),
    X2 is X1-X3,                            
    tab_get_min(col(X8,X12), X7), write('Cost =  0:  '),
    write(X6),
    (X5 = secondary -> write_spaces(X2), write(' = ')  ;
     X5 = low       ->                              write(' >= ') ;
                                                         write(' =< ') ),
    write(X7), nl,
    format(X11, 'conjecture(~w,~w,~w,~w,~w,~w).~n~n', [X5,col(X8,X12),X6,X10,0,t([],[],[],X7)]),
    instrument_code(instrument_found_trivial, X4).

write_found_identical_column(X9, X14, X5, X12, X6, X13) :-
    tab_get_kind(col(X9,X14), X7),
    tab_get_name(col(X9,X14), X8),
    tab_get_max_name_length(X9, secondary, X1),
    atom_codes(X8, X10),
    length(X10, X4),
    X2 is X1-X4,                            
    tab_get_name(col(X9,X5), X3), write('Cost =  0:  '),
    write(X8),
    (X7 = secondary -> write_spaces(X2), write(' = ')  ;
     X7 = low       ->                              write(' >= ') ;
                                                         write(' =< ') ),
    write(X3), nl,
    format(X13, 'conjecture(~w,~w,~w,~w,~w,~w).~n~n', [X7,col(X9,X14),X8,X12,1,
                                                        t([col(X9,X5)],[X3],[X11],
                                                        polynom([monome([t(X11,1)],1)]))]),
    instrument_code(instrument_found_trivial, X6).

get_first_equal_column(X3, X5, X1) :-     
    tab_get_equal(col(X3,X5), X4),
    X4 > 0,                                        
    (tab_get_inout(col(X3,X4), input) ->
        true                                          
    ;
        tab_get_equal(col(X3,X4), X2),     
        (X2 > 0 -> true ; false)                 
    ),
    !,
    get_first_equal_column(X3, X4, X1). 
get_first_equal_column(_, X1, X1).    


get_number_of_found_bounds(X16, X21) :- 
    consult(X21),                                               
    findall(X23, conjecture(low, X23, _, _, _, _), X17),
    sort(X17, X3),
    length(X3, X1),
    nl,
    write('number of lower bounds for which found at least one formula: '),
    write(X1), nl, nl,
    findall(X23, conjecture(up, X23, _, _, _, _), X22),
    sort(X22, X4),
    length(X4, X2),
    write('number of upper bounds for which found at least one formula: '),
    write(X2), nl, nl,
    get_tables(X16, 2, 1, low(_), X13), 
    get_tables(X16, 2, 2, low(_), X14), 
    get_tables(X16, 2, 3, low(_), X15), 
    length(X13, X5),
    length(X14, X6),
    length(X15, X7),
    X8 is X5+X6+X7,
    write('number of lower bounds for which try to find a formula: '),
    write(X8), nl,
    write('dispatched by number of parameters: '),
    write(X5), write('  '),
    write(X6), write('  '),
    write(X7), nl, nl,
    get_tables(X16, 2, 1, up(_), X18), 
    get_tables(X16, 2, 2, up(_), X19), 
    get_tables(X16, 2, 3, up(_), X20), 
    length(X18, X9),
    length(X19, X10),
    length(X20, X11),
    X12 is X9+X10+X11,
    write('number of upper bounds for which try to find a formula: '),
    write(X12), nl,
    write('dispatched by number of parameters: '),
    write(X9), write('  '),
    write(X10), write('  '),
    write(X11), nl, nl.

check_conjectures(X5, X7) :- 
    X13 = t(0,0,0,0,0,0,0),                                        
    low_up_attributes_combi(X5, X1),   
    assert_map_stats(X1, X13),              
    (memberchk(X5, [graph, partition, partition0, forest]) -> 
        true                                                         
    ;
        write(check_conjectures(X5)), nl, halt                                           
    ),                                                                                          
    max_size_combi(X5, X8), 
    consult(X7),                                               
    conjecture(_,col(X15,X27),_,X22,_,X2),   
    atoms_concat(['data/',X5,'/data'], X9), 
    gen_table_and_metadata_file_names(X9, X8, X15,
                                      X6, _),                 
    consult(X6),                                              
    (X22 = X8 ->                                               
        true
    ;
        check_conjecture_wrt_table_entries(0, col(X15,X27),        
                                           X22, X2)        
    ),
    signature(X15, _, X18),
    arg(X27, X18, t(_,X23,_)),
    functor(X18, t, X24),
    findall(X19-X20, (X29 in 1..X24,
                          indomain(X29),
                          arg(X29, X18, t(X20,X19,_)),
                          memberchk(X19, [low,up])
                         ),                                [X10-X11]),
    (X23 = low       -> (X10 = low -> true ; write(check_conjecture_wrt_table_entry), nl, halt) ;
     X23 = up        -> (X10 = up  -> true ; write(check_conjecture_wrt_table_entry), nl, halt) ;
     X23 = secondary -> true                                                                        ;
                         write(check_conjecture_wrt_table_entry), nl, halt                           ),
    findall(X25, (X29 in 1..X24,
                   indomain(X29),
                   arg(X29, X18, t(_,X25,_)),
                   X25=primary
                  ),                           X4),          
    length(X4, X3),                                 
    map_stat(X10, X11, X23, X26),                          
    functor(X26, t, X21),                                         
    functor(X12, t, X21),                                      
    update_stat_counters(1, X21, X3, X26, X12),      
    retractall(map_stat(X10, X11, X23, _)),                 
    assert(map_stat(X10, X11, X23, X12)),
    remove_signature_and_table_facts(X15),                         
    false.
check_conjectures(_, _) :- 
    findall(t(X10, X11, X12, X13), map_stat(X10, X11, X12, X13), X1),
    write_list(X1),
    findall(X13, map_stat(low, _, low,       X13), X2), sum_list_terms(X2, X3),
    findall(X13, map_stat(low, _, secondary, X13), X4), sum_list_terms(X4, X5),
    findall(X13, map_stat(up,  _, up,        X13), X8),   sum_list_terms(X8,   X9),
    findall(X13, map_stat(up,  _, secondary, X13), X6),  sum_list_terms(X6,  X7),
    write('Number of lower bounds:                                             '), write(X3), nl,
    write('Number of secondary characteristics associated with a lower bound:  '), write(X5), nl,
    write('Number of upper bounds:                                             '), write(X9),   nl,
    write('Number of secondary characteristics associated with an upper bound: '), write(X7),  nl.

assert_map_stats([], _) :- !.                             
assert_map_stats([X2-X1|X4], X3) :-           
    assert(map_stat(X2, X1, X2,     X3)), 
    assert(map_stat(X2, X1, secondary, X3)), 
    assert_map_stats(X4, X3).                           

check_conjecture_wrt_table_entries(X3, col(X4,X7), X5, X1) :-
    signature(X4, _, X6),                                     
    functor(X6, t, X2),                                   
    functor(X8, X4, X2),                                
    check_conjecture_wrt_table_entries1(X3, col(X4,X7),  
                                        X5, X1, X8).

check_conjecture_wrt_table_entries1(X2, col(X3,X5), X4, X1, X6) :-
    call(X6),
    (check_conjecture_wrt_table_entry(col(X3,X5), X4, X1, X6) -> 
        false                                                             
    ;                                                                     
        true                                                              
    ),
    !,                                                                    
    (X2 = 0 ->                                                      
        true                                                              
    ;                                                                     
        false                                                             
    ).                                       
check_conjecture_wrt_table_entries1(_, _, _, _, _).                       

check_conjecture_wrt_table_entry(col(X10,X16), X13, X6, X17) :-
    arg(X16, X17, X7),
    X6 = t(X2, _, X1, X8),
    findall(X11, (member(col(X10,X18),X2),arg(X18,X17,X11)), X3),
    copy_term(X1-X8, X3-X9),
    eval_formula_term(X9, X4),
    signature(X10, _, X12),
    arg(X16, X12, t(X14,X15,_)),
    (X7 = X4 ->
        true
    ;
        write('conjecture '),
        write(X6),
        write(' of type '),
        write(X15),
        write(' and name '),
        write(X14),
        write(' failed on row '),
        write(X17),
        write(' as expected value '),
        write(X7),
        write(' is different from value computed by the conjecture, namely value '),
        write(X4),
        write(' on size '),
        write(X13), nl,
        write('(maybe this row is missing from the table used to compute the invariant)'), nl,
        false
    ).

sum_list_terms([], t) :- !.
sum_list_terms(X1, X6) :-
    X1 = [X5|_],
    functor(X5,  X2, X3),
    functor(X4, X2, X3),
    set_term_to_zero(X4),
    sum_list_terms(X1, X4, X6).

set_term_to_zero(X2) :-
    functor(X2, _, X1),
    set_term_to_zero(1, X1, X2).

set_term_to_zero(X2, X1, _) :-
    X2 > X1, !.
set_term_to_zero(X4, X1, X2) :-
    X4 =< X1,
    arg(X4, X2, 0),
    X3 is X4+1,
    set_term_to_zero(X3, X1, X2).

sum_list_terms([], X1, X1) :- !.
sum_list_terms([X4|X5], X1, X2) :-
    sum_terms(X4, X1, X3),
    sum_list_terms(X5, X3, X2).

sum_terms(X4, X1, X2) :-
    functor(X4, t, X3),
    functor(X2, t, X3),
    sum_terms(1, X3, X4, X1, X2).

sum_terms(X1, X2, _, _, _) :-
    X1 > X2, !.
sum_terms(X8, X9, X5, X1, X2) :-
    X8 =< X9,
    !,
    arg(X8, X5, X6),
    arg(X8, X1, X3),
    X4 is X6+X3,
    arg(X8, X2, X4),
    X7 is X8+1,
    sum_terms(X7, X9, X5, X1, X2).

update_stat_counters(X1, X2, _, _, _) :-
    X1 > X2, !.
update_stat_counters(X6, X7, X8, X2, X1) :-
    X6 =< X7,
    arg(X6, X2, X4),
    (X6 = X8 -> X3 is X4+1 ; X3 = X4),
    arg(X6, X1, X3),
    X5 is X6+1,
    update_stat_counters(X5, X7, X8, X2, X1).

transfer_learning(X6, X7, X14) :- 
    functor(X14, X15, 1),    
    atoms_concat([X6,'_',X15,'_',X7],         X3),      
    atoms_concat(['data/',X6,'/found_conjectures_',X3,'.pl'], X1), 
    consult(X1),                                   
    gen_candidate_tables(X16, X6, X7, X14, _), 
    functor(X14, X4, 1),                                
    (conjecture(X4, col(X16, _), _, _, _, _) ->         
        true                                                        
    ;                                                               
        write('did not find a bound conjecture for '),
        write(X16), write(', so try to transfer an existing conjecture'), nl,
        max_size_combi(X6,  X11),                                        
        X8 is X11-1,                                                     
        atoms_concat(['data/',X6,'/datatransfer'], X12),                 
        gen_table_and_metadata_file_names(X12, X8, X16, X9, _), 
        write(consult(X9)), nl,                              
        consult(X9),                                         
        write(consulted), nl,
        findall(X13-X17,
                conjecture(X4,X17,X7,_,_,X13), 
                X5),                                        
        remove_duplicated_formulae(X5, X2), 
        transfer_conjectures(X2, X6, X16),
        remove_signature_and_table_facts(X16)                     
    ),
    false.
transfer_learning(_, _, _). 

remove_duplicated_formulae([], []) :- !.
remove_duplicated_formulae([X2-_|X4], X1) :-     
    \+ \+ duplicated_formula(X4, X2), !,          
    remove_duplicated_formulae(X4, X1).
remove_duplicated_formulae([X1-X2|X3], [X1-X2|X4]) :- 
    remove_duplicated_formulae(X3, X4).

duplicated_formula([X3-_|_], X4) :- 
    X3 = t(_,X1,_,X2), 
    X4 = t(_,X1,_,X2), 
    !.
duplicated_formula([_|X2], X3) :-
    duplicated_formula(X2, X3).

transfer_conjectures([], _, _) :- !. 
transfer_conjectures([X1|_], X2, X3) :- 
    write(try(X1)), nl,
    transfer_conjecture(X2, X1, X3), 
    !.
transfer_conjectures([_|X4], X1, X2) :- 
    transfer_conjectures(X4, X1, X2).   

transfer_conjecture(X10, X8, X14) :-
    X8 = X6-_,
    X6 = t(X3, X7, X1, X9),
    add_key(X7, X4),
    signature(X14, _, X15),
    functor(X15, t, X17),
    findall(X19-X20, (member(X19-X18,X4),X20 in 1..X17,indomain(X20),arg(X20,X15,t(X18,_,_))), X13),    
    findall(X23, (X23 in 1..X17,indomain(X23),arg(X23,X15,t(_,X16,_)),memberchk(X16,[low,up])), [X21]),
    substitute_parameters(X3, X14, X13, X2),
    X5 = t(X2, X7, X1, X9),
    max_size_combi(X10,  X12),                                                              
    X11 is X12-1,                                                                           
    transfer_conjecture_wrt_table_entries(X5, col(X14,X21), X11, X5). 

substitute_parameters([], _, _, []) :- !.
substitute_parameters([col(_,X4)|X6], X3, X1, [col(X3,X2)|X7]) :-
    memberchk(X4-X2, X1),
    substitute_parameters(X6, X3, X1, X7).

transfer_conjecture_wrt_table_entries(X2, col(X3,X4), X5, X1) :-
    check_conjecture_wrt_table_entries(1, col(X3,X4), X5, X1), 
    !,
    write('--------------------------------------------------'), nl,
    write('transfer '), write(X2), write(' to '), write(X3), nl, nl.

cmp(X2) :- 
    low_up_attributes_combi(X2, X1),    
    cmp1(X1).                                  

cmp1([]) :- !.                                                 
cmp1([X2-X1|X6]) :-                                   
    write('----------------------- '),                         
    write(X2),                                              
    write(' '),                                                
    write(X1),                                          
    write(' -----------------------'),                         
    nl,                                                        
    atoms_concat(['conjectures_',X2,'_',X1], X3), 
    atom_concat(X3, '_bool.pl', X4 ),                     
    atom_concat(X3, '_poly.pl', X5 ),                     
    cmp_print(X4, 'BoolCondPoly', X2),                    
    cmp_print(X5, 'Poly',         X2),                    
    cmp1(X6).                                                   

cmp_print(X1, X3, X2) :-
    consult(X1),
    write(X3), nl,
    get_type_simplest_formulae(X2,       _),
    get_type_simplest_formulae(secondary, _),
    retractall(conjecture(_,_,_,_,_,_)),
    nl.

comp(X2) :- 
    findall(X13, (bs(X2, _, bool, _, X10, X11, X12), X13 is X10+X11+X12), X3), 
    findall(X13, (bs(X2, _, poly, _, X10, X11, X12), X13 is X10+X11+X12), X4), 
    sumlist(X3, X7),
    sumlist(X4, X8),
    X6 is ((X7-X8)*100)/X8,
    write(X6), nl,
    findall(X13,  (bs(X2, _, bool, _, X10, X11, _ ), X13 is X10+X11), X1), 
    sumlist(X1, X5),
    nl, nl, write(X5), write('  '), write(X7), nl, nl,
    X9 is (100*X5)/X8,
    write(X9), nl,
    true.

bs(graph, low_c,    bool, bound,  13,  0,  23). 
bs(graph, low_c,    bool, second, 34, 25, 171). 
bs(graph, low_c,    poly, bound,   0,  0,  36). 
bs(graph, low_c,    poly, second,  0,  0, 223). 
bs(graph, low_maxc, bool, bound,   0,  4,  21). 
bs(graph, low_maxc, bool, second,  0,  9,  99). 
bs(graph, low_maxc, poly, bound,   0,  0,  25). 
bs(graph, low_maxc, poly, second,  0,  0, 104). 
bs(graph, low_maxs, bool, bound,   0,  1,  24). 
bs(graph, low_maxs, bool, second,  0,  7,  66). 
bs(graph, low_maxs, poly, bound,   0,  0,  24). 
bs(graph, low_maxs, poly, second,  0,  0,  73). 
bs(graph, low_mina, bool, bound,   0,  7,  43). 
bs(graph, low_mina, bool, second, 38, 95, 212). 
bs(graph, low_mina, poly, bound,   0,  0,  50). 
bs(graph, low_mina, poly, second,  0,  0, 317). 
bs(graph, low_minc, bool, bound,   0, 17,  20). 
bs(graph, low_minc, bool, second, 10, 10,   7). 
bs(graph, low_minc, poly, bound,   0,  0,  36). 
bs(graph, low_minc, poly, second,  0,  0,  27). 
bs(graph, low_mins, bool, bound,   0, 13,  24). 
bs(graph, low_mins, bool, second,  0,  5,   1). 
bs(graph, low_mins, poly, bound,   0,  0,  37). 
bs(graph, low_mins, poly, second,  0,  0,   6). 
bs(graph, low_s,    bool, bound,   5,  4,  26). 
bs(graph, low_s,    bool, second, 32, 27, 172). 
bs(graph, low_s,    poly, bound,   0,  0,  35). 
bs(graph, low_s,    poly, second,  0,  0, 228). 
bs(graph, low_v,    bool, bound,   0, 11,  26). 
bs(graph, low_v,    bool, second, 30, 64, 179). 
bs(graph, low_v,    poly, bound,   0,  0,  36). 
bs(graph, low_v,    poly, second,  0,  0, 258). 
bs(graph, up_c,     bool, bound,   0,  1,  20). 
bs(graph, up_c,     bool, second,  9, 16,  57). 
bs(graph, up_c,     poly, bound,   0,  0,  21). 
bs(graph, up_c,     poly, second,  0,  0,  79). 
bs(graph, up_maxc,  bool, bound,   0,  4,  12). 
bs(graph, up_maxc,  bool, second, 32, 27,  82). 
bs(graph, up_maxc,  poly, bound,   0,  0,  16). 
bs(graph, up_maxc,  poly, second,  0,  0, 137). 
bs(graph, up_maxs,  bool, bound,   0,  2,  16). 
bs(graph, up_maxs,  bool, second, 15, 29,  44). 
bs(graph, up_maxs,  poly, bound,   0,  0,  18). 
bs(graph, up_maxs,  poly, second,  0,  0,  84). 
bs(graph, up_maxa,  bool, bound,   0,  0,  20). 
bs(graph, up_maxa,  bool, second, 46, 84, 254). 
bs(graph, up_maxa,  poly, bound,   0,  0,  20). 
bs(graph, up_maxa,  poly, second,  0,  0, 364). 
bs(graph, up_minc,  bool, bound,   0, 10,  17). 
bs(graph, up_minc,  bool, second, 16,  4,  85). 
bs(graph, up_minc,  poly, bound,   0,  0,  27). 
bs(graph, up_minc,  poly, second,  0,  0, 103). 
bs(graph, up_mins,  bool, bound,   0,  2,  14). 
bs(graph, up_mins,  bool, second,  1,  6,  26). 
bs(graph, up_mins,  poly, bound,   0,  0,  16). 
bs(graph, up_mins,  poly, second,  0,  0,  32). 
bs(graph, up_s,     bool, bound,   0,  2,  18). 
bs(graph, up_s,     bool, second,  5, 15,  55). 
bs(graph, up_s,     poly, bound,   0,  0,  20). 
bs(graph, up_s,     poly, second,  0,  0,  73). 
bs(graph, up_v,     bool, bound,   0,  0,  11). 
bs(graph, up_v,     bool, second,  0,  2,   1). 
bs(graph, up_v,     poly, bound,   0,  0,  11). 
bs(graph, up_v,     poly, second,  0,  0,   3). 

get_type_simplest_formulae(X13, X5) :-
    findall(X3, conjecture(X13,X3,_,_,_,_), X2),
    sort(X2, X1),
    get_all_conjectures_of_each_param(X1, X13, X4),
    get_type_simplest_formula(X4, X5),
    findall(bool, member(_-bool, X5), X6), length(X6, X7),
    findall(cond, member(_-cond, X5), X8), length(X8, X9),
    findall(cond, member(_-poly, X5), X10), length(X10, X11),
    (X13 = secondary -> write('Secondary: ') ; write('Bound:     ')),
    write('nbool='), (X7 < 10 -> write('   ') ; X7 < 100 -> write('  ') ; write(' ')), write(X7), write('  '),
    write('ncond='), (X9 < 10 -> write('   ') ; X9 < 100 -> write('  ') ; write(' ')), write(X9), write('  '),
    write('npoly='), (X11 < 10 -> write('   ') ; X11 < 100 -> write('  ') ; write(' ')), write(X11), write('  '),
    X12 is X7+X9+X11,
    write('('), (X12 < 10 -> write('  ') ; X12 < 100 -> write(' ') ; true), write(X12), write(')'), nl.

get_all_conjectures_of_each_param([], _, []) :- !.
get_all_conjectures_of_each_param([X4|X5], X2, [X4-X1|X6]) :-
    findall(X3, conjecture(X2,X4,_,_,_,t(_,_,_,X3)), X1),
    get_all_conjectures_of_each_param(X5, X2, X6).

get_type_simplest_formula([], []) :- !.
get_type_simplest_formula([X3-X1|X4], [X3-X2|X5]) :-
    get_type_simplest_conjectures(X1, poly, X2),
    get_type_simplest_formula(X4, X5).

get_type_simplest_conjectures([], X1, X1) :- !.
get_type_simplest_conjectures([X3|X5], X1, X4) :-
    functor(X3, X2, _),
    (X2 = bool -> X4 = bool                                      ;
     X2 = not  -> X4 = bool                                      ;
     X2 = if   -> get_type_simplest_conjectures(X5, cond,     X4) ;
                       get_type_simplest_conjectures(X5, X1, X4) ).

gen_links(X2, X3, X1) :-                       
    X4 = 1, X5 = 3,                                      
    gen_links(X4, X5, X2, X3, X1). 

gen_links(X5, X6, X3, X4, X2) :-                        
    load_metadata(X5, X6, X3, X4, X2, X1),  
    write('metadata loaded'), nl,
    write_list(X1), nl,
    gen_links_to_sources(X5, X6, X1).

load_metadata(X1, X2, _, _, _, []) :-                                              
    X1 > X2,
    !.
load_metadata(X9, X10, X6, X7, X3, [X2|X12]) :- 
    X9 =< X10,
    low_up_attributes_combi(X6, X1),                                             
    ((X3 = 1, memberchk(low-X7, X1)) -> X11 = low(_)                ;  
     (X3 = 0, memberchk(up-X7,  X1)) -> X11 = up(_)                 ;  
                                                                            write(load_metadata), nl, halt), 
    X4 = 2,                                                               
    get_tables(X6, X4, X9, X11, X5), 
    filter_table_names_wrt_kind_bound(X5, X7, X2),
    load_metadata(X6, X2, X4),                
    X8 is X9+1,
    load_metadata(X8, X10, X6, X7, X3, X12). 

load_metadata(X3, X1, X2) :- 
    member(X4, X1),
    write('load '), write(X4), nl,
    consult_metadata_of_functor(X3, X2, X2, X4), 
    false.
load_metadata(_, _, _). 

filter_table_names_wrt_kind_bound([], _, []) :- !.
filter_table_names_wrt_kind_bound([X1|X3], X2, [X1|X4]) :-
    atom_proper_suffix_add_underscore(X1, X2),
    !,
    filter_table_names_wrt_kind_bound(X3, X2, X4).
filter_table_names_wrt_kind_bound([_|X3], X1, X4) :-
    filter_table_names_wrt_kind_bound(X3, X1, X4).

gen_links_to_sources(X1, X1, _) :- !.
gen_links_to_sources(X3, X4, [_|X5]) :-
    X3 < X4,
    X2 is X3+1,
    gen_links_to_sources(X2, X4, X5).
