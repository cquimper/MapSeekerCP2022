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
% Purpose: GENERATE THE TABLES ASSOCIATED TO EACH BOUND WE ARE LOOKING FOR: BOUNDS FOR DIGRAPHS AND PARTITIONS
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(lists)).
:- use_module(library(samsort)).
:- use_module(library(clpfd)).
:- use_module(utility).

max_nb_of_input_parameters(graph,      4).
max_nb_of_input_parameters(partition,  4).
max_nb_of_input_parameters(partition0, 4).
max_nb_of_input_parameters(group,      3).
max_nb_of_input_parameters(cgroup,     3).

top(X4, X5, X1) :- 
    (X1 = 1 ->
        atoms_concat(['data/',X4,'/tables_',X4], X2)
    ;
        atoms_concat(['data/',X4,'/tablestransfer_',X4], X2)
    ),
    atom_concat(X2, '.pl', X3),
    open(X3, write, X7),                                                     
    (X4 = graph      -> format(X7, '
     KindCombi = partition  -> format(Tout, '
     X4 = partition0 -> format(X7, '
     KindCombi = group      -> format(Tout, '
     X4 = cgroup     -> format(X7, '
                               write(top(KindCombi)), nl, halt                                                                                                                  ), 
    format(Tout, '% X6: should be added within the table.pl file containing all the tables of all combinatorial objects.~n', []),
    format(Tout, '%          do not forget to add both the max_size_combi/2 and the table/5 facts.~n', []),
    format(Tout, '% X4 : X3 X1, X5 X2~n~n', []),
    format(Tout, ':- module(table,[attributes_combi/2,~n', []),
    format(Tout, '                 low_up_attributes_combi/2,~n', []),
    format(Tout, '                 max_size_combi/2,~n', []),
    format(Tout, '                 get_tables/5,~n', []),
    format(Tout, '                 get_table/5,~n', []),
    format(Tout, '                 table/6]).~n~n', []),
    format(Tout, 'attributes_combi(graph,      [v,c,minc,maxc,s,mins,maxs,mina,maxa]).~n',                                 []),
    format(Tout, 'attributes_combi(partition,  [n,nval,min,max,range,sum_squares]).~n',                                    []),
    format(Tout, 'attributes_combi(partition0, [n,m,nval,min,max,range,sum_squares]).~n',                                  []),
    format(Tout, 'attributes_combi(group,      [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]).~n', []),
    format(Tout, 'attributes_combi(cgroup,     [n,ng,nv,smin,smax,srange,ssum_squares,dmin,dmax,drange,dsum_squares]).~n', []),
    format(Tout, 'attributes_combi(forest,     [v,t,f,minf,maxf,mind,maxd,minp,maxp,mint,maxt]).~n~n',                     []),
    format(Tout, 'low_up_attributes_combi(graph,      [low-v,low-c,low-minc,low-maxc,low-s,low-mins,low-maxs,low-mina,~n',  []),
    format(Tout, '                                     up-v, up-c, up-minc, up-maxc, up-s, up-mins, up-maxs, up-maxa]).~n', []),
    format(Tout, 'low_up_attributes_combi(partition,  [low-nval,low-min,low-max,low-range,low-sum_squares,~n',  []),
    format(Tout, '                                     up-nval, up-min, up-max, up-range, up-sum_squares]).~n', []),
    format(Tout, 'low_up_attributes_combi(partition0, [low-nval,low-min,low-max,low-range,low-sum_squares,~n',  []),
    format(Tout, '                                     up-nval, up-min, up-max, up-range, up-sum_squares]).~n', []),
    format(Tout, 'low_up_attributes_combi(group,      [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,~n',  []),
    format(Tout, '                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).~n', []),
    format(Tout, 'low_up_attributes_combi(cgroup,     [low-ng,low-nv,low-smin,low-smax,low-srange,low-ssum_squares,low-dmin,low-dmax,low-drange,low-dsum_squares,~n',  []),
    format(Tout, '                                     up-ng, up-nv, up-smin, up-smax, up-srange, up-ssum_squares, up-dmin, up-dmax, up-drange, up-dsum_squares]).~n', []),
    format(Tout, 'low_up_attributes_combi(forest,     [low-t,low-f,low-minf,low-maxf,low-mind,low-maxd,low-minp,low-maxp,low-mint,low-maxt,~n',    []),
    format(Tout, '                                     up-t, up-f, up-minf, up-maxf, up-mind, up-maxd, up-minp, up-maxp, up-mint, up-maxt]).~n~n', []),
    format(Tout, 'max_size_combi(graph,     26). % maximum number of nodes for which we generate graphs~n', []),
    format(Tout, 'max_size_combi(partition, 30). % maximum number of elements for which we generate partitions~n', []),
    format(Tout, 'max_size_combi(partition0,30). % maximum number of elements for which we generate partitions0~n', []),
    format(Tout, 'max_size_combi(group,     20). % maximum number of elements for which we generate groups~n', []),
    format(Tout, 'max_size_combi(cgroup,    20). % maximum number of elements for which we generate circular groups~n', []),
    format(Tout, 'max_size_combi(forest,    18). % maximum number of nodes for which we generate forests~n~n', []),
    format(Tout, 'get_tables(X3, X5, X4, X1, X2) :-~n', []),
    format(Tout, '    findall(X6, table(X3,X6,X5,_,X4,X1), X2).~n~n', []),
    format(Tout, 'get_table(X2, X5, X4, X1, X3) :-~n', []),
    format(Tout, '    table(X2, X3, X5, _, X4, X1),~n', []),
    format(Tout, '    !. % normally table names should be distinct, but who knows~n~n', []),
    format(Tout, 'table(X3, X5, X6, X7, X4, X1) :-~n', []),
    format(Tout, '    table(X3, X5, X2, X4, X1),~n', []),
    format(Tout, '    member(X6-X7, X2).~n~n', []),
    format(Tout, '% X1 table has the following arguments:~n', []),
    format(Tout, '%  . the type of combinatorial object (graph, partition, partition0, group, cgroup, forest) or the fact that we use the model seeker (model_seeker)~n', []),
    format(Tout, '%  . the name of the table~n', []),
    format(Tout, '%  . the list of pairs of the form X1-X2 where~n', []),
    format(Tout, '%     - X1 is the maximum number of elements used to generate a table~n', []),
    format(Tout, '%     - X2 is the corresponding number of columns of the same table~n', []),
    format(Tout, '%  . the number of parameters of the lower/upper bound~n', []),
    format(Tout, '%  . the lower/upper bound considered~n~n', []),
    format(Tout, ':- dynamic table/5.~n~n', []),
    gen_data(KindCombi, MaxParams, KeepOnlySecondaryWithFD, Tout), 
    close(Tout).

gen_data(KindCombi, MaxParams, KeepOnlySecondaryWithFD, _Tout) :- 
    atom_concat('data/', KindCombi, Directory0),            
    (KeepOnlySecondaryWithFD = 1 ->                         
        MaxN in 2..MaxParams,                                                           
        atom_concat(Directory0, '/data', Directory)         
    ;                                                                                   
        MaxN = MaxParams,                                   
        atom_concat(Directory0, '/datatransfer', Directory) 
    ),
    indomain(MaxN),
    write(gen(MaxN)), nl,
    statistics(runtime, [Time0|_]),
    number_codes(MaxN, CodesMaxN),                                                      
    atom_codes(AtomMaxN, CodesMaxN),                                                    
    atom_concat(Directory, AtomMaxN, PrefixName0),                                      
    atom_concat(PrefixName0, '/', PrefixName),
    gen_tables_up_to_a_given_parameter_size(KindCombi, MaxN, KeepOnlySecondaryWithFD, PrefixName), 
    statistics(runtime, [Time1|_]), Time is Time1-Time0, write(time(Time)), nl,
    false.
gen_data(KindCombi, _, _, Tout) :-                   
    findall(Name, table(Name,_,_,_,_), TableNames),  
    sort(TableNames, Names),                         
    gen_table_data(Names, KindCombi, Tout).          

gen_table_data([], _, _) :- !, retractall(table(_,_,_,_,_)). 
gen_table_data([Name|R], KindCombi, Tout) :- 
    findall(Size-NCol, table(Name, Size, NCol, _, _), Pairs), 
    once(table(Name, _, _, LenCombination, Bound)),
    format(Tout, 'table(~w, ~w, ~w, ~w, ~w).~n', [KindCombi,Name,Pairs,LenCombination,Bound]), 
    gen_table_data(R, KindCombi, Tout).                                                        

gen_tables_up_to_a_given_parameter_size(KindCombi, MaxN, KeepOnlySecondaryWithFD, PrefixName) :- 
    (KindCombi = graph ->                                                                        
        Primaries   = [1-v,2-c,3-minc,4-maxc,5-s,6-mins,7-maxs,8-mina,9-maxa],                                                                        
        Secondaries = [10-minmaxc,11-midc,12-rminc,13-ominc,14-omaxc,15-omidc,16-oc,17-oc23,18-omins,19-omaxs,20-os]                                  
    ;                                                                                                                                                 
     KindCombi = partition ->                                                                                                                         
        Primaries   = [1-n,2-nval,3-min,4-max,5-range,6-sum_squares],                                                                                 
        Secondaries = [7-minmax,8-mid,9-rmin,10-omin,11-omax,12-omid,13-oc]                                                                           
    ;                                                                                                                                                 
     KindCombi = partition0 ->                                                                                                                        
        Primaries   = [1-n,2-m,3-nval,4-min,5-max,6-range,7-sum_squares],                                                                             
        Secondaries = [8-mid,9-rmin,10-omin,11-omax,12-omid,13-oc,14-oc1]                                                                             
    ;                                                                                                                                                 
     KindCombi = group ->                                                                                                                             
        Primaries   = [1-n,2-ng,3-nv,4-smin,5-smax,6-srange,7-ssum_squares,8-dmin,9-dmax,10-drange,11-dsum_squares],                                  
        Secondaries = [12-sminsmax,13-smid,14-rsmin,15-osmin,16-osmax,17-osmid,18-osc,19-dmindmax,20-dmid,21-rdmin,22-odmin,23-odmax,24-odmid,25-odc] 
    ;                                                                                                                                                 
     KindCombi = cgroup ->                                                                                                                            
        Primaries   = [1-n,2-ng,3-nv,4-smin,5-smax,6-srange,7-ssum_squares,8-dmin,9-dmax,10-drange,11-dsum_squares],                                  
        Secondaries = [12-sminsmax,13-smid,14-rsmin,15-osmin,16-osmax,17-osmid,18-osc,19-dmindmax,20-dmid,21-rdmin,22-odmin,23-odmax,24-odmid,25-odc] 
    ;
        write(gen_tables_up_to_a_given_parameter_size(KindCombi)), nl, halt                                                                           
    ),                                                                                                                                                
    append(Primaries, Secondaries, PrimariesSecondaries),
    (KindCombi = graph ->
        findall(Char, gen_partitions_of_partitions(MaxN, Char), Sol), sort(Sol, SortedSol) 
    ;
     KindCombi = partition ->
        findall(Char,               gen_partitions(MaxN, Char), Sol), sort(Sol, SortedSol) 
    ;
     KindCombi = partition0 ->
        findall(Char,              gen_partitions0(MaxN, Char), Sol), sort(Sol, SortedSol) 
    ;
     KindCombi = group ->
        findall(Char,                   gen_groups(MaxN, Char), Sol), sort(Sol, SortedSol) 
    ;
        findall(Char,                  gen_cgroups(MaxN, Char), Sol), sort(Sol, SortedSol) 
    ),
    SortedSol = [FirstSol|_],
    functor(FirstSol, t, LenSource),
    length(Primaries, LenPrimary),
    gen_combination(KindCombi, Primaries, Bound, LenCombination, Combination), 
    arg(1, Bound, PrimaryBound),
    append(Combination, [PrimaryBound], CombinationBound),                              
    findall(Char, (member(Char,Primaries),
                   \+ memberchk(Char,CombinationBound),
                   Char \= _-mina, Char \= _-maxa), UnselectedPrimaries),
    gen_extraction_terms(KindCombi, LenSource, LenPrimary, LenCombination, Combination, 
                         Bound, UnselectedPrimaries, SelectedPrimaryNames,
                         LenSecondary, Functor, TargetTerm, SourceTerm, ITargetISource),
    handle_one_combination_of_characteristics(SortedSol, KeepOnlySecondaryWithFD, LenSecondary,
                                              LenCombination, TargetTerm, SourceTerm, Bound,
                                              IndexSelectedSecondary, NormalisedOptimalSol),
    filter_invalid_optimals(KindCombi, Bound, Combination, MaxN, NormalisedOptimalSol, FilteredOptimalSol), 
    findall(Char, (member(I,IndexSelectedSecondary),
                   memberchk(I-J, ITargetISource),
                   memberchk(J-Char, PrimariesSecondaries)), SelectedSecondaryNames),
    append(SelectedPrimaryNames, SelectedSecondaryNames, SelectedNames),
    build_signature(MaxN, Functor, SelectedNames, Combination, Bound, Signature),
    length(SelectedNames, A),
    (FilteredOptimalSol = [] ->
        nl, write('X4 X10 X1 X14 X5 X8 '), write(Functor), write(' X11 X2 X3 X12 X6 '), write(MaxN), write(' X13 X9 X7'), nl
    ;
        
        
        functor(Bound, FBound, _),
        arg(1, Bound, _-ABound),
        functor(FABound, FBound, 1), arg(1, FABound, ABound),    
        assert(table(Functor, MaxN, A, LenCombination, FABound)) 
    ),
    atom_concat(PrefixName, Functor, PrefixNameFunctor),
    atom_concat(PrefixNameFunctor, '.pl', PrologFile),
    open(PrologFile, write, Sout),
    format(Sout,':- multifile signature/3.~n',[]),
    format(Sout,':- multifile ~w/~w.~n',[Functor,A]),
    format(Sout,':- dynamic signature/3.~n',[]),
    format(Sout,':- dynamic ~w/~w.~n~n',[Functor,A]),
    format(Sout,'~w.~n~n',[Signature]),
    write_list(FilteredOptimalSol, Sout),
    close(Sout),
    false.
gen_tables_up_to_a_given_parameter_size(_, _, _, _). 

build_signature(MaxN, Functor, Args, Combination, Bound, Signature) :-
    functor(Signature, signature, 3),
    arg(1, Signature, Functor),
    arg(2, Signature, MaxN),
    arg(3, Signature, Arg3),
    length(Args, A),
    functor(Arg3, t, A),
    build_signature1(Args, 1, Combination, Bound, Arg3).

build_signature1([], _, _, _, _) :- !.
build_signature1([Name|R], I, Combination, Bound, Term) :-
    (Bound = low(_-Name)            -> P = low,       S = output ;  
     Bound =  up(_-Name)            -> P = up,        S = output ;  
     memberchk(_-Name, Combination) -> P = primary,   S = input  ;  
                                       P = secondary, S = input  ), 
    arg(I, Term, t(Name, P, S)),
    I1 is I+1,
    build_signature1(R, I1, Combination, Bound, Term).

gen_combination(KindCombi, Primaries, Bound, LenCombination, Combination) :- 
    length(Primaries, NPrimary),                                        
    length(Selection, NPrimary),                                        
    Ignored  = 0,                                                       
    Selected = 1,                                                       
    Lower    = 2,                                                       
    Upper    = 3,                                                       
    domain(Selection, Ignored, Upper),
    max_nb_of_input_parameters(KindCombi, MaxNbOfInputParameters),      
    MinIgnored is max(0,NPrimary-MaxNbOfInputParameters-1),             
    count(Ignored, Selection, #>=, MinIgnored),                         
    (KindCombi = graph -> 
        memberchk(V-v,                    Primaries), nth1(V,          Selection, SV),          
        memberchk(C-c,                    Primaries), nth1(C,          Selection, SC),          
        memberchk(Minc-minc,              Primaries), nth1(Minc,       Selection, SMinc),       
        memberchk(Maxc-maxc,              Primaries), nth1(Maxc,       Selection, SMaxc),       
        memberchk(S-s,                    Primaries), nth1(S,          Selection, SS),          
        memberchk(Mins-mins,              Primaries), nth1(Mins,       Selection, SMins),       
        memberchk(Maxs-maxs,              Primaries), nth1(Maxs,       Selection, SMaxs),       
        memberchk(Mina-mina,              Primaries), nth1(Mina,       Selection, SMina),       
        memberchk(Maxa-maxa,              Primaries), nth1(Maxa,       Selection, SMaxa),       
        SMina #\= Selected, SMina #\= Upper,                                                    
        SMaxa #\= Selected, SMaxa #\= Lower,                                                    
                                                                                                
        SV    #= Upper #=> ((SC#=Selected #/\ SMaxc#=Selected) #\/ (SS#=Selected #/\ SMaxs#=Selected) #\/ (SS#=Selected #/\ SMaxc#=Selected)),
        SC    #= Upper #=> (SV#=Selected #\/ SS#=Selected),
        SMinc #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected #\/ (SS#=Selected #/\ SMaxs#=Selected)),
        SMaxc #= Upper #=> (SV#=Selected),
        SS    #= Upper #=> (SV#=Selected #\/ (SC#=Selected #/\ SMaxc#=Selected)),
        SMins #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected #\/ SMaxs#=Selected),
        SMaxs #= Upper #=> (SV#=Selected #\/ SMaxc#=Selected),
        SMaxa #= Upper #=> (SV#=Selected #\/ (SC#=Selected #/\ SMaxc#=Selected) #\/ (SS#=Selected #/\ SMaxs#=Selected) #\/ (SS#=Selected #/\ SMaxc#=Selected))
    ;
     KindCombi = partition -> 
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          
        memberchk(NVal-nval,                Primaries), nth1(NVal,        Selection, _SNVal),       
        memberchk(Min-min,                  Primaries), nth1(Min,         Selection, _SMin),        
        memberchk(Max-max,                  Primaries), nth1(Max,         Selection, _SMax),        
        memberchk(Range-range,              Primaries), nth1(Range,       Selection, _SRange),      
        memberchk(SumSquares-sum_squares,   Primaries), nth1(SumSquares,  Selection, _SSumSquares), 
        SN #= 1                                                                                     
    ; 
     KindCombi = partition0 -> 
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          
        memberchk(M-m,                      Primaries), nth1(M,           Selection,  SM),          
        memberchk(NVal-nval,                Primaries), nth1(NVal,        Selection, _SNVal),       
        memberchk(Min-min,                  Primaries), nth1(Min,         Selection, _SMin),        
        memberchk(Max-max,                  Primaries), nth1(Max,         Selection, _SMax),        
        memberchk(Range-range,              Primaries), nth1(Range,       Selection, _SRange),      
        memberchk(SumSquares-sum_squares,   Primaries), nth1(SumSquares,  Selection, _SSumSquares), 
        SN #= 1,                                                                                    
        SM #= 1                                                                                     
    ;
     memberchk(KindCombi, [group,cgroup]) -> 
        memberchk(N-n,                      Primaries), nth1(N,           Selection,  SN),          
        memberchk(NG-ng,                    Primaries), nth1(NG,          Selection, _NG),          
        memberchk(NV-nv,                    Primaries), nth1(NV,          Selection, _NV),          
        memberchk(SMin-smin,                Primaries), nth1(SMin,        Selection, _SMin),        
        memberchk(SMax-smax,                Primaries), nth1(SMax,        Selection, _SMax),        
        memberchk(SRange-srange,            Primaries), nth1(SRange,      Selection, _SRange),      
        memberchk(SSumSquares-ssum_squares, Primaries), nth1(SSumSquares, Selection, _SSumSquares), 
        memberchk(DMin-dmin,                Primaries), nth1(DMin,        Selection, _DMin),        
        memberchk(DMax-dmax,                Primaries), nth1(DMax,        Selection, _DMax),        
        memberchk(DRange-drange,            Primaries), nth1(DRange,      Selection, _DRange),      
        memberchk(DSumSquares-dsum_squares, Primaries), nth1(DSumSquares, Selection, _DSumSquares), 
        SN #= 1                                                                                     
    ;
        write(gen_combination(KindCombi)), nl, halt
    ),
    domain([Low,Up], 0, 1),                                             
    count(Lower,    Selection, #=,  Low),                               
    count(Upper,    Selection, #=,  Up),                                
    count(Selected, Selection, #>=, 1),                                 
    Low + Up #= 1,                                                      
    gen_sum_term(Selection, var, SumTerm),                              
    call(Sum #= SumTerm),
    labeling_select(Selection, [Lower,Upper]),                          
    indomain(Sum),                                                      
    labeling_vals(Selection, [Selected,Ignored,Lower,Upper]),           
    get_combination(Primaries, Selection, Selected, Combination),       
    get_bound(Selection, 1, Lower, Upper, Primaries, Bound),            
    length(Combination, LenCombination).

get_combination([], _, _, []) :- !.
get_combination([I-C|R], Selection, Selected, Res) :-
    nth1(I, Selection, Val),
    (Val = Selected -> Res = [I-C|Combination] ; Res = Combination),
     get_combination(R, Selection, Selected, Combination).

get_bound([Lower|_], Index, Lower, _, Primaries, Bound) :- !, memberchk(Index-Name, Primaries), Bound = low(Index-Name).
get_bound([Upper|_], Index, _, Upper, Primaries, Bound) :- !, memberchk(Index-Name, Primaries), Bound = up(Index-Name).
get_bound([_|R], Index, Lower, Upper, Primaries, Bound) :-
    Index1 is Index+1,
    get_bound(R, Index1, Lower, Upper, Primaries, Bound).

gen_extraction_terms(KindCombi, LenSource, LenPrimary, LenCombination, Combination, Bound, UnselectedPrimaries, SelectedPrimaryNames, 
                     LenSecondary, Functor, TargetTerm, SourceTerm, ITargetISource) :-
    functor(Bound, LowUp, 1),
    arg(1, Bound, Opt),
    append(Combination, [Opt], Names),
    keys_and_values(Names, _, SelectedPrimaryNames),
    build_functor_name(Names, LowUp, Functor),
    length(Combination, LenCombination),
    Opt = _-B,
    (KindCombi = graph ->
        (memberchk(B, [mina,maxa]) ->  
            Correction = 1             
        ;                              
            Correction = 2             
        )
    ;
        Correction = 0                 
    ),
    LenTarget is LenSource-Correction,
    functor(TargetTerm, Functor, LenTarget),
    functor(SourceTerm, t,       LenSource),
    unify_vars_extraction_terms_primary(Combination, 1, Opt, TargetTerm, SourceTerm),                      
    ITarget1 is LenCombination+2,
    unify_vars_extraction_terms_unselected_primary(UnselectedPrimaries, ITarget1,                          
                                                   TargetTerm, SourceTerm, ITargetISource1),
    ISource2 is LenPrimary+1,                                                                              
    ITarget2 is ISource2-Correction,
    unify_vars_extraction_terms_secondary(ISource2, ITarget2, LenSource,                                   
                                          TargetTerm, SourceTerm, ITargetISource2),
    LenSecondary is LenTarget-LenCombination-1,
    append(ITargetISource1, ITargetISource2, ITargetISource).

build_functor_name([], FunctorName, FunctorName) :- !.
build_functor_name([_-NameChar|R], Prefix, FunctorName) :-
    atom_concat(Prefix, '_', P),
    atom_concat(P, NameChar, Q),
    build_functor_name(R, Q, FunctorName).

unify_vars_extraction_terms_primary([], I, J-_, TargetTerm, SourceTerm) :- !,
    arg(J, SourceTerm, Var),    
    arg(I, TargetTerm, Var).
unify_vars_extraction_terms_primary([J-_|R], I, Opt, TargetTerm, SourceTerm) :-
    arg(J, SourceTerm, Var),
    arg(I, TargetTerm, Var),
    I1 is I+1,
    unify_vars_extraction_terms_primary(R, I1, Opt, TargetTerm, SourceTerm).

unify_vars_extraction_terms_unselected_primary([], _, _, _, []) :- !.
unify_vars_extraction_terms_unselected_primary([J-Char|R], I, TargetTerm, SourceTerm, [I-J|S]) :-
    (memberchk(Char,[mina,maxa]) -> 
        I1 = I                      
    ;
        arg(J, SourceTerm, Var),
        arg(I, TargetTerm, Var),
        I1 is I+1
    ),
    unify_vars_extraction_terms_unselected_primary(R, I1, TargetTerm, SourceTerm, S).

unify_vars_extraction_terms_secondary(ISource, _, Len, _, _, []) :-
    ISource > Len, !.
unify_vars_extraction_terms_secondary(ISource, ITarget, Len, TargetTerm, SourceTerm, [ITarget-ISource|S]) :-
    ISource =< Len,
    arg(ISource, SourceTerm, Var),
    arg(ITarget, TargetTerm, Var),
    ISource1 is ISource+1,
    ITarget1 is ITarget+1,
    unify_vars_extraction_terms_secondary(ISource1, ITarget1, Len, TargetTerm, SourceTerm, S).

handle_one_combination_of_characteristics(SortedSol, KeepOnlySecondaryWithFD, LenSecondary, LenCombination, Term1, Term2, Bound, NewSecondary, NormalisedOptimalSol) :-
    findall(Term1, member(Term2, SortedSol), ProjectedSol),
    sort(ProjectedSol, SortedProjectedSol),
    LenCombination1 is LenCombination+1,
    StartSecondary is LenCombination1+1,
    EndSecondary is LenCombination1+LenSecondary,
    findall(Ind, (Ind in StartSecondary..EndSecondary, indomain(Ind)), IndSecondary),
    (Bound = low(_) -> NormalisedSortedProjectedSol = SortedProjectedSol ; reverse(SortedProjectedSol, NormalisedSortedProjectedSol)),
    keep_optimal(KeepOnlySecondaryWithFD, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary),
    length(NewSecondary, LenNewSecondary),
    (LenNewSecondary = LenSecondary ->
        Optimal = OptimalSol
    ;
        filter_non_fd_secondary(OptimalSol, LenCombination, LenSecondary, LenNewSecondary, NewSecondary, Optimal)
    ),
    (Bound = low(_) -> NormalisedOptimalSol = Optimal ; reverse(Optimal, NormalisedOptimalSol)).

keep_optimal(1, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary) :- !,
    keep_optimal1(NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, NewSecondary).
keep_optimal(0, NormalisedSortedProjectedSol, LenCombination, LenCombination1, IndSecondary, OptimalSol, IndSecondary) :-
    keep_optimal0(NormalisedSortedProjectedSol, LenCombination, LenCombination1, OptimalSol).

keep_optimal1([], _, _, NewSecondary, [], NewSecondary) :- !.
keep_optimal1([Char|R], LenCombination, LenCombination1, IndSecondary, [Char|S], NewSecondary) :-
    skip_same_optimal(R, Char, LenCombination1, IndSecondary, Rest, RestSecondary),
    skip_non_optimal(Rest, Char, LenCombination, NewRest),
    keep_optimal1(NewRest, LenCombination, LenCombination1, RestSecondary, S, NewSecondary).

keep_optimal0([], _, _, []) :- !.
keep_optimal0([Char|R], LenCombination, LenCombination1, [Char|Anchor]) :- 
    keep_opt0(R, Char, LenCombination, LenCombination1, Anchor).           

keep_opt0([], _, _, _, []) :- !.                                        
keep_opt0([Char2|R], Char1, LenCombination, LenCombination1, Anchor) :- 
    same_args(1, LenCombination1, Char1, Char2), !,                     
    Anchor = [Char2|NewAnchor],                                         
    keep_opt0(R, Char1, LenCombination, LenCombination1, NewAnchor).
keep_opt0(Sols, Char1, LenCombination, LenCombination1, Anchor) :-      
    skip_non_opt(Sols, Char1, LenCombination, Rest),                    
    (Rest = [] ->                                                       
        Anchor = []                                                     
    ;                                                                   
        Rest = [NextChar1|NextRest],                                    
        Anchor = [NextChar1|NewAnchor],                                 
        keep_opt0(NextRest, NextChar1, LenCombination, LenCombination1, NewAnchor)
    ).

skip_non_opt([], _, _, []) :- !.                       
skip_non_opt([Char2|R], Char1, LenCombination, Res) :- 
    same_args(1, LenCombination, Char1, Char2), !,     
    !,                                                 
    skip_non_opt(R, Char1, LenCombination, Res).       
skip_non_opt(Res, _, _, Res).

keep_same_optimal([], _, _, RestSecondary, [], RestSecondary) :- !.
keep_same_optimal([Char1|R], Char, LenCombination1, IndSecondary, Rest, RestSecondary) :-
    same_args(1, LenCombination1, Char1, Char), !,
    keep_same_optimal(R, Char, LenCombination1, IndSecondary, Rest, RestSecondary).
keep_same_optimal(Rest, _, _, RestSecondary, Rest, RestSecondary).

skip_same_optimal([], _, _, RestSecondary, [], RestSecondary) :- !.
skip_same_optimal([Char1|R], Char, LenCombination1, IndSecondary, Rest, RestSecondary) :-
    same_args(1, LenCombination1, Char1, Char), !,
    update_functional_dependency_secondary(IndSecondary, Char1, Char, NewSecondary),
    skip_same_optimal(R, Char, LenCombination1, NewSecondary, Rest, RestSecondary).
skip_same_optimal(Rest, _, _, RestSecondary, Rest, RestSecondary).

skip_non_optimal([], _, _, []) :- !.
skip_non_optimal([Char1|R], Char, LenCombination, Rest) :-
    same_args(1, LenCombination, Char1, Char), !,
    skip_non_optimal(R, Char, LenCombination, Rest).
skip_non_optimal(Rest, _, _, Rest).

update_functional_dependency_secondary([], _, _, []) :- !.
update_functional_dependency_secondary([I|R], Term1, Term2, [I|S]) :-
    arg(I, Term1, Val),
    arg(I, Term2, Val),
    !,
    update_functional_dependency_secondary(R, Term1, Term2, S).
update_functional_dependency_secondary([_|R], Term1, Term2, S) :-
    update_functional_dependency_secondary(R, Term1, Term2, S).

filter_non_fd_secondary(OptimalSol, LenCombination, LenSecondary, LenNewSecondary, NewSecondary, Optimal) :-
    (OptimalSol = [Sol|_] -> functor(Sol, Functor, _) ; write(filter_non_fd_secondary), nl, halt),
    LenCombination1 is LenCombination+1,
    LenCombination2 is LenCombination1+1,
    LenSource is LenCombination1+LenSecondary,
    LenTarget is LenCombination1+LenNewSecondary,
    functor(SourceTerm, Functor, LenSource),
    functor(TargetTerm, Functor, LenTarget),
    unify_consecutive_vars(1, LenCombination1, SourceTerm, TargetTerm),
    unify_non_consecutive_vars(NewSecondary, LenCombination2, SourceTerm, TargetTerm),
    findall(TargetTerm, member(SourceTerm, OptimalSol), Optimal).

filter_invalid_optimals(KindCombi, BoundTerm, Combination, MaxN, NormalisedOptimalSol, FilteredOptimalSol) :- 
    arg(1, BoundTerm, _-Bound),                                           
    functor(BoundTerm, BoundType, 1),                                     
    gen_target_combination(Combination, 1, TargetCombination),
    filter_invalid_optimals1(NormalisedOptimalSol, KindCombi, BoundType, Bound, 
                             TargetCombination, MaxN, FilteredOptimalSol).

filter_invalid_optimals1([], _, _, _, _, _, []) :- !.                                         
filter_invalid_optimals1([Sol|R], KindCombi, BoundType, Bound, Combination, MaxN, [Sol|S]) :- 
    valid_optimal(KindCombi, BoundType, Bound, Sol, Combination, MaxN), !,                    
    filter_invalid_optimals1(R, KindCombi, BoundType, Bound, Combination, MaxN, S).           
filter_invalid_optimals1([_|R], KindCombi, BoundType, Bound, Combination, MaxN, S) :-         
    filter_invalid_optimals1(R, KindCombi, BoundType, Bound, Combination, MaxN, S).           

gen_target_combination([], _, []) :- !.
gen_target_combination([_-Char|R], I, [I-Char|S]) :-
    I1 is I+1,
    gen_target_combination(R, I1, S).

valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxs],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,_-maxs], Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,J-s],    Combination), arg(I,Sol,MaxC), arg(J,Sol,S), MaxC = MaxN, S > 1, !, false.
valid_optimal(graph, low, minc, Sol, Combination, MaxN) :- eq_memberchks([I-maxc,J-s,K-maxs], Combination), arg(I,Sol,MaxC), arg(J,Sol,S), arg(K,Sol,MaxS),
                                                           A is (MaxC+MaxS-1) // MaxS, A < S, MaxC = MaxN, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-maxs],        Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([_-maxc,I-maxs], Combination), arg(I,Sol,X), MaxN = X, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-c,J-maxs],    Combination), arg(I,Sol,C), arg(J,Sol,MaxS), C = 1, MaxS = MaxN, !, false.
valid_optimal(graph, low, mins, Sol, Combination, MaxN) :- eq_memberchks([I-minc,J-maxs], Combination), arg(I,Sol,MinC), arg(J,Sol,MaxS), 
                                                           MinC = MaxS, MinC2 is MinC+MinC, MinC2 > MaxN, !, false.
valid_optimal(graph, low, _,    _,   _,           _)    :- !.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MaxC), P is C*MaxC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MaxS), P is S*MaxS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-minc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MinC), P is C*MinC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-mins], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MinS), P is S*MinS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-minc,J-maxc], Combination),
                                                           arg(I,Sol,MinC), arg(J,Sol,MaxC), P is MinC+MaxC, MinC < MaxC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-mins,J-maxs], Combination),
                                                           arg(I,Sol,MinS), arg(J,Sol,MaxS), P is MinS+MaxS, MinS < MaxS, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-c,J-minc,K-maxc], Combination),
                                                           arg(I,Sol,C), arg(J,Sol,MinC), arg(K,Sol,MaxC), P is (C-1)*MaxC+MinC, P > MaxN, !, false.
valid_optimal(graph, up,  _,    Sol, Combination, MaxN) :- memberchks([I-s,J-mins,K-maxs], Combination),
                                                           arg(I,Sol,S), arg(J,Sol,MinS), arg(K,Sol,MaxS), P is (S-1)*MaxS+MinS, P > MaxN, !, false.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  v,    Sol, Combination, MaxN) :- memberchks([I-s,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  c,    _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  c,    _,   Combination, _)    :- memberchk(_-s,           Combination), !.
valid_optimal(graph, up,  minc, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  minc, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  minc, Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxc, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  s,    _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  s,    Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  mins, _,   Combination, _)    :- memberchk(_-maxs,        Combination), !.
valid_optimal(graph, up,  maxs, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  maxs, _,   Combination, _)    :- memberchk(_-maxc,        Combination), !.
valid_optimal(graph, up,  maxa, _,   Combination, _)    :- memberchk(_-v,           Combination), !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-c,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-s,J-maxs], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(graph, up,  maxa, Sol, Combination, MaxN) :- memberchks([I-s,J-maxc], Combination), arg(I, Sol, X), arg(J, Sol, Y), P is X*Y, MaxN >= P, !.
valid_optimal(partition,  _, _, _, _, _). 
valid_optimal(partition0, _, _, _, _, _). 
valid_optimal(group,      _, _, _, _, _). 
valid_optimal(cgroup,     _, _, _, _, _). 

unify_consecutive_vars(I, N, _, _) :-
    I > N, !.
unify_consecutive_vars(I, N, T1, T2) :-
    I =< N,
    arg(I, T1, Var),
    arg(I, T2, Var),
    I1 is I+1,
    unify_consecutive_vars(I1, N, T1, T2).

unify_non_consecutive_vars([], _, _, _) :- !.
unify_non_consecutive_vars([I|R], J, T1, T2) :-
    arg(I, T1, Var),
    arg(J, T2, Var),
    J1 is J+1,
    unify_non_consecutive_vars(R, J1, T1, T2).

labeling_select([V|_], Values) :-
    member(V, Values).
labeling_select([_|R], Values) :-
    labeling_select(R, Values).

labeling_vals([], _) :- !.
labeling_vals([V|R], Values) :-
    member(V, Values),
    labeling_vals(R, Values).


gen_partitions_of_partitions(MaxN, Sol) :-
    N in 1..MaxN,
    indomain(N),
    N2 is N*N,
    length(L, N2),
    domain(L, 0, N),
    gen_sum_term(L, var, Sum),
    call(Sum #= N),
    gen_partition(L, N, N, Part),
    lex_chain(Part),
    reverse(L,LR),
    N1 is N+1,
    labeling([ffc,down], LR),
    compute_characteristics(Part,                                           
                            N1,                                             
                            t(0,0,N1,0,0,N1,0,0,0,N1,N1,0,0,0,0,0,0,0,0,0), 
                            Sol).                                           

gen_partition([], _, _, []) :- !.
gen_partition(L, N, I, [Prefix|R]) :-
    append_length(Prefix, Suffix, L, N),
    increasing(Prefix),
    bound_prefix(Prefix, I, N, Suffix, N),
    I1 is I-1,
    gen_partition(Suffix, N, I1, R).

increasing([_]) :- !.
increasing([U,V|R]) :-
    U #=< V,
    increasing([V|R]).

bound_prefix([], _, _, _, _) :- !.
bound_prefix([V|R], I, J, S, N) :-
    ((R = [], S = []) -> V #> 0 ; true),
    IJ is I*J,
    MaxV is max(1,(N-(J+1)*(I-1)) // J),
    (IJ > N -> V = 0 ; V #=< MaxV),
    J1 is J-1,
    bound_prefix(R, I, J1, S, N).

compute_characteristics(Part, N1, InitValCharacteristics, Result) :-
    compute_characteristics1(Part, t(N1,0), IntermediateResult, InitValCharacteristics, Result),
    IntermediateResult = t(MinC2,OMinC2),                             
    Result = t(_,_,MinC,MaxC,_,_,_,_,_,_,MidC,_,_,_,OMidC,_,_,_,_,_), 
    (MinC  = MaxC -> MidC = 0,     OMidC = 0      ;                   
     MinC2 = MaxC -> MidC = 0,     OMidC = 0      ;                   
                     MidC = MinC2, OMidC = OMinC2).                   
                                                                      

compute_characteristics1([], IntermediateResult, IntermediateResult, Result, Result) :- !,
    Result = t(V, C, MinC, MaxC,  _, _, _, _, _, MinMaxC, _, RMinC, _, _, _, _, _, _, _, _), 
    (MinC = MaxC -> MinMaxC = 0 ; MinMaxC = MinC),
    RMinC is V-C*MinC.
compute_characteristics1([P|R], CurResult, IntermediateResult, CurCharacteristics, Result) :-
    remove_values(P, 0, Q),                     
    remove_values(Q, 1, Q1),                    
    (Q = [_|_] ->                               
         length(Q, Len),                        
         min_member(Min, Q),                    
         max_member(Max, Q),                    
         length_same_prefix(Q, OMin),           
         reverse(Q, QR),                        
         length_same_prefix(QR, OMax),          
         sumlist(Q, Sum),                       
         (Sum =< 0 -> write(broken_invariant(compute_characteristics1)), nl, halt ; true),
         CurResult  = t(MinC2,  OMinC2),        
         NextResult = t(MinC21, OMinC21),       
         CurCharacteristics  = t(V, C, MinC, MaxC, S, MinS, MaxS, MinA, MaxA, _MinMaxC, _MidC, _RMinC, OMinC, OMaxC, _OMidC, OC, OC23, OMinS, OMaxS, OS),
         NextCharacteristics = t(V1,C1,MinC1,MaxC1,S1,MinS1,MaxS1,MinA1,MaxA1,_MinMaxC1,_MidC1,_RMinC1,OMinC1,OMaxC1,_OMidC1,OC1,OC231,OMinS1,OMaxS1,OS1),
         V1    is V+Sum,                        
         C1    is C+1,                          
         MinC1 is min(MinC,Sum),                
         MaxC1 is max(MaxC,Sum),                
         (Sum < MinC  -> MinC21  =  MinC,       
                         OMinC21 =  OMinC    ;  
          Sum = MinC  -> MinC21  =  MinC2,      
                         OMinC21 =  OMinC2   ;  
          Sum < MinC2 -> MinC21  =  Sum,        
                         OMinC21 =  1        ;  
          Sum = MinC2 -> MinC21  =  MinC2,      
                         OMinC21 is OMinC2+1 ;  
                         MinC21  =  MinC2,      
                         OMinC21 =  OMinC2   ), 
         (Sum = MinC -> OMinC1 is OMinC+1 ;     
          Sum < MinC -> OMinC1 =  1       ;     
                        OMinC1 =  OMinC   ),    
         (Sum = MaxC -> OMaxC1 is OMaxC+1 ;     
          Sum > MaxC -> OMaxC1 =  1       ;     
                        OMaxC1 =  OMaxC   ),    
         (Sum > 1 -> OC1 is OC+1 ; OC1 = OC),   
         (Q=[1,1]   -> OC231 is OC23 + 1 ;      
          Q=[1,1,1] -> OC231 is OC23 + 1 ;      
                       OC231 =  OC23     ),
         S1    is S+Len,                        
         MinS1 is min(MinS,Min),                
         MaxS1 is max(MaxS,Max),                
         (Min = MinS -> OMinS1 is OMinS+OMin ;  
          Min < MinS -> OMinS1 =  OMin       ;  
                        OMinS1 =  OMinS      ), 
         (Max = MaxS -> OMaxS1 is OMaxS+OMax ;  
          Max > MaxS -> OMaxS1 =  OMax       ;  
                        OMaxS1 =  OMaxS      ), 
         length(Q1, Len1),                      
         OS1 is OS+Len1,                        
         (Sum = 1 ->                            
              MinA1 is MinA + 1
         ;
              sumlist(Q1, Sum1),
              MinA1 is MinA+Sum1+Len-1
         ),
         sum_prod_after(Q, Arcs),               
         MaxA1 is MaxA+Arcs                     
    ;
         NextCharacteristics = CurCharacteristics
    ),
    compute_characteristics1(R, NextResult, IntermediateResult, NextCharacteristics, Result).


gen_partitions(MaxN, Characteristics) :-
    gen_partitions(MaxN, 0, Characteristics).

gen_partitions0(MaxN, Characteristics) :-
    gen_partitions(MaxN, 1, Characteristics).

gen_partitions(MaxN, All, Characteristics) :-
    N in 1..MaxN,                    
    indomain(N),
    (All = 1 ->
        M in 1..N,                   
        indomain(M),
        AllM = M
    ;
        M = N,                       
        AllM = 0
    ),
    length(LOcc, M),                 
    domain(LOcc, 0, N),              
    gen_sum_term(LOcc, var, SumOcc),
    call(SumOcc #= N),               
    increasing(LOcc),                
    labeling([ffc,down], LOcc),
    compute_characteristics0(LOcc, N, AllM, Characteristics).

compute_characteristics0(Partition, N, AllM, Result) :-
    remove_first_elem(Partition, 0, Partition0),
    length(Partition0, NVal),
    (AllM = 0 ->
        Result = t(N,       NVal, Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC),
        [Min|_] = Partition0
    ;
        Result = t(N, AllM, NVal, Min, Max, Range, SumSquares, Mid, RMin, OMin, OMax, OMid, OC, OC1),
        [Min|_] = Partition,
        length_prefix(Partition0, 1, 0, OC1)
    ),
    last(Partition0, Max),
    Range is Max-Min,
    sum_squares(Partition0, SumSquares),
    (Min = Max ->
        (AllM = 0 -> MinMax = 0 ; true),
        Mid    = 0,
        OMin   = NVal,
        OMax   = NVal,
        OMid   = 0
    ;
        (AllM = 0 ->
            MinMax = Min,
            length_prefix(Partition0, Min, 0, OMin)
        ;
            length_prefix(Partition,  Min, 0, OMin)
        ),
        reverse(Partition0, ReversePartition0),
        length_prefix(ReversePartition0, Max, 0, OMax),
        remove_first_elem(Partition0, Min, Partition1),
        (Partition1 = [Max|_] ->
            Mid  = 0,
            OMid = 0
        ;
            [Mid|_] = Partition1,
            length_prefix(Partition1, Mid, 0, OMid)
        )
    ),
    RMin is N - NVal*Min,
    remove_first_elem(Partition0, 1, Partition01),
    length(Partition01, OC).


gen_groups(MaxN, Characteristics) :-
    gen_groups(MaxN, 0, Characteristics).

gen_cgroups(MaxN, Characteristics) :-
    gen_groups(MaxN, 1, Characteristics).

gen_groups(MaxN, Circular, Characteristics) :-
    Characteristics = t(N, NG, NV, SMin, SMax, SRange, SSumSquares, DMin, DMax, DRange, DSumSquares, 
                        SMinSMax, SMid, RSMin, OSMin, OSMax, OSMid, OSC,                             
                        DMinDMax, DMid, RDMin, ODMin, ODMax, ODMid, ODC),                            
    N in 1..MaxN,
    indomain(N),
    length(VARS, N),
    domain(VARS, 0, 1),
    (Circular = 0 ->
        States = [source(s),sink(a),sink(b),sink(c),sink(d),sink(e)]
    ;
        States = [source(s),sink(a),sink(b),sink(d),sink(e)]
    ),
    Transitions = [arc(s,0,e                                   ),
                   arc(s,1,a,             [P0,  1,   C0,  C1  ]),
                   arc(a,0,b,             [ 1,  P1,  C0,  C1  ]),
                   arc(a,1,a,             [P0,  P1+1,C0,  C1  ]),
                   arc(b,0,b,             [P0+1,P1,  C0,  C1  ]),
                   arc(b,1,c,             [P0,  P1,  C0,  1   ]),
                   arc(c,0,d,             [P0,  C1,  1,   C1  ]),
                   arc(c,1,c,(P1 #> C1 -> [P0,  P1,  C0,  C1+1])),
                   arc(d,0,d,(P0 #> C0 -> [P0,  P1,  C0+1,C1  ])),
                   arc(d,1,c,             [C0,  P1,  C0,  1   ]),
                   arc(e,0,e,             [P0,  P1,  C0,  C1  ])],
    automaton(VARS, _, VARS, States, Transitions, [P0,P1,C0,C1], [0,0,0,0], [_,_,_,_]),
    labeling([], VARS),
    extract_sizes(VARS, Circular, Sizes1, Sizes0),
    compute_characteristics_groups(Sizes1, [NG, NV, SMin, SMax, SRange, SSumSquares, SMinSMax, SMid, RSMin, OSMin, OSMax, OSMid, OSC]),
    compute_characteristics_groups(Sizes0, [        DMin, DMax, DRange, DSumSquares, DMinDMax, DMid, RDMin, ODMin, ODMax, ODMid, ODC]),
    length(Sizes1, LenSizes1), (LenSizes1 = 0 -> Cor1 = 1 ; Cor1 = 0),
    length(Sizes0, LenSizes0), (LenSizes0 = 0 -> Cor0 = 1 ; Cor0 = 0).

compute_characteristics_groups(Sizes, Primaries) :-
    (length(Primaries, 11) ->
        Primaries = [      Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC] 
    ;
        Primaries = [G, V, Min, Max, Range, SumSquares, MinMax, Mid, RMin, OMin, OMax, OMid, OC] 
    ),
    (Sizes = [] ->
        G          = 0,
        V          = 0,
        Min        = 0,
        Max        = 0,
        Range      = 0,
        SumSquares = 0,
        MinMax     = 0,
        Mid        = 0,
        RMin       = 0,
        OMin       = 0,
        OMax       = 0,
        OMid       = 0,
        OC         = 0
    ;
        reverse(Sizes, RSizes),
        length(Sizes, G),
        sumlist(Sizes, V),
        min_member(Min, Sizes),
        max_member(Max, Sizes),
        Range is Max - Min,
        sum_squares(Sizes, SumSquares),
        (Min = Max -> MinMax = 0 ; MinMax = Min),
        sort(Sizes, SortedSizes),                                       
        (SortedSizes = [_,_,_|_] ->
            SortedSizes = [_,Mid|_],
            remove_first_elem(RSizes, Min, SizesWithoutMin),
            length_prefix(SizesWithoutMin, Mid, 0, OMid)
        ;
            Mid = 0,
            OMid = 0
        ),
        RMin is V - Min*G,
        length_prefix(RSizes, Min, 0, OMin),
        length_prefix( Sizes, Max, 0, OMax),
        remove_first_elem(RSizes, 1, SizesWithoutOne),
        length(SizesWithoutOne, OC)
    ).

extract_sizes(L, 1, [], []) :- 
    max_member(0, L),
    !.
extract_sizes(L, Circular, S, T) :-
    extract_sizes1(L, Circular, S, T).

extract_sizes1([], _, [], []) :- !.
extract_sizes1([1|R], Circular, [Size|S], T) :- !,
    extract_sizes2(R, 1, 1, Size, Rest),
    extract_sizes1(Rest, Circular, S, T).
extract_sizes1([0|R], 1, S, [Size|T]) :- !,
    extract_sizes2(R, 0, 1, Size, Rest), 
    extract_sizes1(Rest, 1, S, T).
extract_sizes1([0|R], 0, S, [Size|T]) :-
    extract_sizes2(R, 0, 1, Size, Rest),
    Rest = [_|_], !,                    
    extract_sizes1(Rest, 0, S, T).
extract_sizes1([0|_], 0, [], []).        

extract_sizes2([], _, Size, Size, []) :- !.
extract_sizes2([Val|R], Val, CurSize, Size, Rest) :- !,
    NextSize is CurSize+1,
    extract_sizes2(R, Val, NextSize, Size, Rest).
extract_sizes2(Rest, _, Size, Size, Rest).

