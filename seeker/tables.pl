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
% Purpose: Tables giving the lower/upper bound of a partition characteristics wrt a set of partition characteristics
% Warning: should be added within the tables.pl and tables_list.pl file containing all the tables of all combinatorial objects.
%          do not forget to add both the max_size_combi/2 in tables.pl and the table/5 in tables_list.pl facts.
% Author : Nicolas Beldiceanu, IMT Atlantique

:- module(tables,[attributes_combi/2,
                  low_up_attributes_combi/2,
                  max_size_combi/2,
                  get_tables/5,
                  get_table/5,
                  table/6,
                  extract_index_names_from_table_signature/3]).

:- use_module(tables_list).

attributes_combi(graph,      [v,c,minc,maxc,s,mins,maxs,mina,maxa]).                                 
attributes_combi(forest,     [v,t,f,minf,maxf,mind,maxd,minp,maxp,mint,maxt]).                       
attributes_combi(forest0,    [v,t,f,minf,maxf,mind,maxd,minp,maxp,mint,maxt]).                       
attributes_combi(tree,       [v,f,mind,maxd,minp,maxp]).                                             
attributes_combi(partition,  [n,nval,min,max,range,sum_squares]).                                    
attributes_combi(partition0, [n,m,nval,min,max,range,sum_squares]).                                  
attributes_combi(group,      [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]). 
attributes_combi(cgroup,     [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]). 

low_up_attributes_combi(graph,      [low-v,low-c,low-minc,low-maxc,low-s,low-mins,low-maxs,low-mina,
                                     up-v, up-c, up-minc, up-maxc, up-s, up-mins, up-maxs, up-maxa]).
low_up_attributes_combi(forest,     [low-t,low-f,low-minf,low-maxf,low-mind,low-maxd,low-minp,low-maxp,low-mint,low-maxt,
                                     up-t, up-f, up-minf, up-maxf, up-mind, up-maxd, up-minp, up-maxp, up-mint, up-maxt]).
low_up_attributes_combi(forest0,     [low-t,low-f,low-minf,low-maxf,low-mind,low-maxd,low-minp,low-maxp,low-mint,low-maxt,
                                     up-t, up-f, up-minf, up-maxf, up-mind, up-maxd, up-minp, up-maxp, up-mint, up-maxt]).
low_up_attributes_combi(tree,       [low-f,low-mind,low-maxd,low-minp,low-maxp,
                                     up-f, up-mind, up-maxd, up-minp, up-maxp]).
low_up_attributes_combi(partition,  [low-nval,low-min,low-max,low-range,low-sum_squares,
                                     up-nval, up-min, up-max, up-range, up-sum_squares]).
low_up_attributes_combi(partition0, [low-nval,low-min,low-max,low-range,low-sum_squares,
                                     up-nval, up-min, up-max, up-range, up-sum_squares]).
low_up_attributes_combi(group,      [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,
                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).
low_up_attributes_combi(cgroup,     [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,
                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).

max_size_combi(model_seeker,  0). 
max_size_combi(graph,        26). 
max_size_combi(forest,       18). 
max_size_combi(forest0,      18). 
max_size_combi(tree,         18). 
max_size_combi(partition,    30). 
max_size_combi(partition0,   30). 
max_size_combi(group,        20). 
max_size_combi(cgroup,       20). 

get_tables(X3, X5, X4, X1, X2) :-
    findall(X6, table(X3,X6,X5,_,X4,X1), X2).

get_table(X2, X5, X4, X1, X3) :-
    table(X2, X3, X5, _, X4, X1),
    !. 


table(X3, X5, X6, X7, X4, X1) :-
    table(X3, X5, X2, X4, X1),
    member(X6-X7, X2).

extract_index_names_from_table_signature(X4, X3, X1) :-
    functor(X4, _, X2),
    extract_index_name_from_signatures(X3, X2, X4, X1).

extract_index_name_from_signatures([], _, _, []) :- !.
extract_index_name_from_signatures([X3|X5], X1, X4, [X2|X6]) :-
    extract_index_name_from_signature(X3, 1, X1, X4, X2),
    extract_index_name_from_signatures(X5, X1, X4, X6).

extract_index_name_from_signature(X4, X3, X2, X5, X3) :-
    X3 =< X2,
    arg(X3, X5, X1),
    arg(1, X1, X4), 
    !.
extract_index_name_from_signature(X3, X6, X1, X4, X2) :-
    (X6 = X1 ->
        write(extract_index_name_from_signature(X3)), nl, halt
    ;
        X5 is X6+1,
        extract_index_name_from_signature(X3, X5, X1, X4, X2)
    ).
