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
% Purpose: Scripts to generate Test 1 tables from acquired conjectures for
%          various combinatorial objects
% and aggregate the test results
% Author : Ramiz Gindullin, IMT Atlantique

:- use_module(library(lists)).
:- use_module(table_access).
:- use_module(tables).
:- use_module(utility).
:- use_module(gen_candidate_tables).



create_examples:-
    open('performance_test_list.pl', write, X1),
    format(X1, ':- multifile table_info/6.~n:- dynamic table_info/6.~n~n~n', []),
    X2 = [[forest,     low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest,      up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,    low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,     up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [cgroup,     low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [cgroup,      up, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [graph,      low, [v, c, minc, maxc, s, mins, maxs, mina]],
            [graph,       up, [v, c, minc, maxc, s, mins, maxs, maxa]],
            [group,      low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [group,       up, [dmax, dmin, drange, dsum_squares, ng, nv,       smin, srange              ]],
            [partition,  low, [max, min, nval, range, sum_squares]],
            [partition,   up, [max, min, nval, range, sum_squares]],
            [partition0, low, [max, min, nval, range, sum_squares]],
            [partition0,  up, [max, min, nval, range, sum_squares]],
            [tree,       low, [f, maxd, maxp, mind, minp]],
            [tree,        up, [f, maxd, maxp, mind, minp]]
            ], 
    
    (foreach(X3,X2), param(X1) do consult_map(X3, X1)),
    close(X1).

maps(      [[forest,     low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest,      up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,    low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,     up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [cgroup,     low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [cgroup,      up, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [graph,      low, [v, c, minc, maxc, s, mins, maxs, mina]],
            [graph,       up, [v, c, minc, maxc, s, mins, maxs, maxa]],
            [group,      low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [group,       up, [dmax, dmin, drange, dsum_squares, ng, nv,       smin, srange              ]],
            [partition,  low, [max, min, nval, range, sum_squares]],
            [partition,   up, [max, min, nval, range, sum_squares]],
            [partition0, low, [max, min, nval, range, sum_squares]],
            [partition0,  up, [max, min, nval, range, sum_squares]],
            [tree,       low, [f, maxd, maxp, mind, minp]],
            [tree,        up, [f, maxd, maxp, mind, minp]]
            ]).

consult_map([X7, X16, X3], X18) :-
    (foreach(X8, X3), param([X7, X16, X18])
    do
     write('% '),write([X7, X16, X8]),nl,
     consult_map(X7, X16, X8),
     findall(conjecture(X19,X9,X4,X20,X21,X12),
           (conjecture(X19,X9,X4,X20,X21,X13),
            X13 = t(X10, X5, _, bool(X14, _, X17, X15, _)),
            X12 = t(X10, X5, 0, bool(X14, 0, X17, X15, none))
           ),
            X2),
     sort(X2,X1),
     create_example(X1, [X7, X16, X8], X6),
     (foreach(X11, X6), param(X18)
     do
      format(X18, '~w.~n', [X11])
     ),
     retractall(conjecture(_,_,_,_,_,_))
    ).


create_example(X1, [X3, X5, X4], X2) :-
    create_example(X1, 1, [X3, X5, X4], X2).

create_example([], _, _, []) :- !.
create_example([X5|X38], X39, [X9, X24, X10], [table_info(X11,X9,X24-X10,X17,X25,X18)|X40]):-
    X5 = conjecture(_,col(X1,X12), X6, X31, _,
                            t(X13, X7, _, bool(X17, _, X25, X18, _))), 
    load_table_metadata(X9, X31, X1),
    
    number_codes(X39, X23),                              
    atom_codes(X28, X23),                            
    atoms_concat(['test_table_',X9,'_',X24,'_',X10,'_', X28], X11),
    atoms_concat(['data/model_seeker/data0/',X11,'.pl'],X14),
    length(X13, X29),
    X32 is X29 + 1,
    open(X14, write, X33),
    format(X33, ':- multifile signature/3.~n:- multifile ~w/~w.~n:- dynamic signature/3.~n:- dynamic ~w/~w.~n~n~n',
           [X11,X32,X11,X32]),
    write(table(model_seeker, X11, [0-X32], 0, [no_pk,no_fk])),write('.'),
    
    
    functor(X15, signature, 3),
    arg(1, X15, X11),
    arg(2, X15, 0),
    functor(X19, t, X32),
    (foreach(X20, X7), for(X35,1,X29), param(X19)
    do
     arg(X35, X19, t(X20, primary, input))
    ),
    arg(X32, X19, t(X6, secondary, output)),
    arg(3, X15, X19),
    format(X33, '~w.~n~n', [X15]),
    
    tab_get_arity(col(X1,_), X21),
    findall(X16,
            (functor(X2, X1, X21),
             functor(X16,       X11,       X32   ),
             call(X2),
             (foreach(col(_,X34), X13), for(X36,1,X29),
              param([X19, X16, X2])
             do
              arg(X34, X2, X30),
              arg(X36,   X16,       X30)
             ),
             arg(X12, X2, X4),
             arg(X32,      X16,       X4),
             format(X33, '~w.~n', [X16])
            ),
            _),
    
    close(X33),
    nl,
    remove_signature_and_table_facts(X1),
    functor(X3, table_metadata, 31), 
    retractall(user:X3),
    X37 is X39 + 1,
    create_example(X38, X37, [X9, X24, X10], X40).

consult_map(X8, X11, X9) :-
    atom_concat('existing_maps/', X8, X6),
    atom_concat(X6, '/found_conjectures_', X7),
    atom_concat(X7, X8, X3),
    atom_concat(X3, '_', X5),
    atom_concat(X5, X11, X2),
    atom_concat(X2, '_', X4),
    atom_concat(X4, X9, X1),
    atom_concat(X1, '.pl', X10),
    consult(X10).

load_table_metadata(X2, X6, X5):-
    atoms_concat(['data/',X2,'/data'], X4),
    gen_table_and_metadata_file_names(X4, X6, X5, X3, X1),
    consult(X3),
    consult(X1).




create_stats :-
    create_stat('performance_test_stats_core.pl'),
    create_stat('performance_test_stats_adv.pl'),
    create_stat('performance_test_stats_all.pl').

create_stats2 :-
    create_stat('performance_test_stats_adv_5_1_only.pl'),
    create_stat('performance_test_stats_adv_5_2_only.pl'),
    create_stat('performance_test_stats_adv_5_3_only.pl').

create_stat(X17) :-
    write('Results for '),write(X17),write(':'),nl,
    consult(X17),
    findall(X7, performance(_,_,X7,_,_,_,_), X10),
    
    findall(X15-X11, performance(_,_,_,_,X15,X11,_), X1),
    sort(X10,X18),
    sort(X1,X3),
    write('Per map:'),nl,
    
    (foreach(X5,X18)
    do
     findall(X12,performance(_,_,X5,_,_,_,X12),X8),
     sumlist(X8, X4),
     length(X8,  X13),
     X2 is X4 div 1000,
     X6 is X2 div X13,
     
     write(X5), write(' ('), write(X13), write('): '), write(X2), write('s / '), write(X6), write('s.'), nl
    ),
    nl,nl,
    write('Per formula complexity:'),nl,
    (foreach(X14-X9,X3)
    do
     findall(X12,performance(_,_,_,_,X14,X9,X12),X8),
     sumlist(X8, X4),
     length(X8,  X13),
     X2 is X4 div 1000,
     X6 is X2 div X13,
     write(X14-X9), write(' ('), write(X13), write('): '), write(X2), write('s / '), write(X6), write('s.'), nl
    ),
    nl,nl,nl,
    retractall(performance(_,_,_,_,_,_,_)).
