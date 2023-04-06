%This script is for eleminating columns which are not functionnaly dependent and doubles entries

:- use_module(library(lists)).
:- use_module(library(clpfd)).

top1:- top(1,'data_tree/','tree/').

top2:- top(2,'data_foret_sans_point_isole/','forest/').
           
top3:- top(2,'data_foret_avec_point_isole/','forest0/').

top(I,Dir,Dir1):-
    (I = 1 -> consult('tables_tree.pl')
            ;
             consult('tables_foret.pl')
     ),
    get_tables(_, _, _, TableNames),
    member(TableName-MaxN,TableNames),
    number_codes(MaxN,CodeMaxN),
    atom_codes(AtomMaxN,CodeMaxN),
    atom_concat('data',AtomMaxN,Dir0),
    atom_concat(Dir,Dir0,Directory0),
    atom_concat(Directory0,'/',Directory),
    atom_concat(TableName,'.pl',TableFile),
    atom_concat('data/',Dir1,Directory000),
    atom_concat(Directory000,'data',Directory0000),
    atom_concat(Directory0000,AtomMaxN,Directory00),
    atom_concat(Directory00,'/',Directory2),
    gen_new_table(Directory,Directory2,TableFile,Dir),false.

top(_,_):-
    retractall(get_tables(_, _, _, _)),
    retractall(get_table(_, _, _, _)),
    retractall(table(_,_,_,_,_)),
    halt.



gen_new_table(Directory,Directory2,TableFileToAdjust,Dir):-
    atom_concat(Directory,TableFileToAdjust,DirectoryFileToAdjust),
    consult(DirectoryFileToAdjust),
    signature(NameFunctor,MaxN,FunctorChars),
    functor(FunctorChars,t,NbCols),
    findall(Functor,(functor(Functor,NameFunctor,NbCols),call(Functor)),PredicateList),
    atom_concat(Directory2,TableFileToAdjust,NewTablefile),
    findall(FunctorChar,(Rank in 1..NbCols,indomain(Rank),arg(Rank,FunctorChars,FunctorChar)),ListFunctorChars),

    nth1(NbParams,ListFunctorChars,t(Bound,UpLow,output)),
    get_list_ranks_to_remov(NbParams,PredicateList,[],ListRankToRemovNotSorted,NbCols),
    sort(ListRankToRemovNotSorted,ListRankToRemov),
    length(ListRankToRemov,NbNotFDChars),
    NewNbCols is NbCols - NbNotFDChars,
    tell(NewTablefile),
    write(':- multifile signature/3.'),nl,
    write(':- multifile '),write(NameFunctor),write('/'),write(NewNbCols),write('.'),nl,
    write(':- dynamic signature/3.'),nl,
    write(':- dynamic '),write(NameFunctor),write('/'),write(NewNbCols),write('.'),nl,nl,
    write('signature('),write(NameFunctor),write(','),write(MaxN),write(','),%format(user_output,'~w~n',[salut]),nl,
    functor(NewFunctorChars,t,NewNbCols),%format(user_output,'~w~n',[salut]),nl,
    get_new_functor(FunctorChars,NewFunctorChars,NbCols,ListRankToRemov,1,1),
    write(NewFunctorChars),
    write(').'),nl,nl,
    write_new_predicates(PredicateList,0,ListRankToRemov),
    told,
    (Dir = 'data_tree/' -> write_table_functor(NewNbCols,UpLow,NameFunctor,MaxN,Bound,NbParams);true),
    retract(signature(_,_,_)),
    functor(Predicate,NameFunctor,NbCols),
    retractall(Predicate).


write_table_functor(NewNbCols,UpLow,NameFunctor,MaxN,Bound,NbParams):-
NbEntreeParams is NbParams-1,
open('tables.pl',append,Sout),
format(Sout,'table(~w, ~w, ~w, ~w, ~w(~w)).~n',[NameFunctor,MaxN,NewNbCols,NbEntreeParams,UpLow,Bound]),
close(Sout).

get_list_ranks_to_remov1(NbParams,PredicateList,[],ListRankToRemovSorted,NbCols):-
   length(PredicateList,NbPredicates),
   NbPredicatesMoins1 is NbPredicates - 1,
   findall(Rank,(Rank in 1..NbCols,
                 indomain(Rank),
                 Rank > NbParams,
                 I in 1..NbPredicatesMoins1,
                 indomain(I),
                 I1 is I + 1,
                 nth1(I,PredicateList,Predicate0),
                 nth1(I1,PredicateList,Predicate1),
                 not_different(Predicate0,Predicate1,NbParams),
                 arg(Rank,Predicate0,Val0),
                 arg(Rank,Predicate1,Val1),
                 \+ Val0 = Val1,
                 once(Predicate0)),ListRankToRemov),sort(ListRankToRemov,ListRankToRemovSorted).



get_list_ranks_to_remov(_,[_],ListRankToRemov,ListRankToRemov,_):- !.
get_list_ranks_to_remov(NbParams,[Predicate0,Predicate1|R],InitListRankToRemov,ListRankToRemov,NbCols):-
NbParamsPlus1 is NbParams + 1,
   get_ranks(NbParams,Predicate0,Predicate1,InitListRankToRemov,ListRankToRemov0,NbCols,NbParamsPlus1),
((length(ListRankToRemov0,NbRanksToRemov),NbRanksToRemov is NbCols-NbParams) -> ListRankToRemov0=ListRankToRemov,!;
 get_list_ranks_to_remov(NbParams,[Predicate1|R],ListRankToRemov0,ListRankToRemov,NbCols)).
   

get_ranks(_,_,_,ListRankToRemov,ListRankToRemov,NbCols,I):- I is NbCols + 1,  !.
get_ranks(NbParams,Predicate0,Predicate1,InitListRankToRemov,ListRankToRemov,NbCols,I):-
    (not_different(Predicate0,Predicate1,NbParams) -> (
    (arg(I,Predicate0,Val0),arg(I,Predicate1,Val1),
     Val0 \== Val1 ,\+memberchk(I,InitListRankToRemov)) ->
                                                       append([I],InitListRankToRemov,ListRankToRemov0);
                                                       ListRankToRemov0 = InitListRankToRemov);
     ListRankToRemov0 = InitListRankToRemov),I1 is I + 1,
    get_ranks(NbParams,Predicate0,Predicate1,ListRankToRemov0,ListRankToRemov,NbCols,I1).
     

not_different(_,_,0):- !.
not_different(Predicate0,Predicate1,I):-
     arg(I,Predicate0,Val),arg(I,Predicate1,Val), I1 is I-1,
     not_different(Predicate0,Predicate1,I1).

get_new_functor(_,_,NbCols,_,I,_):- I is NbCols + 1,!.
get_new_functor(FunctorChars,NewFunctorChars,NbCols,ListRankToRemov,I,J):-
  arg(I,FunctorChars,CharFuntor),I1 is I + 1,
  (memberchk(I,ListRankToRemov) -> J1 = J;arg(J,NewFunctorChars,CharFuntor),J1 is J + 1),
get_new_functor(FunctorChars,NewFunctorChars,NbCols,ListRankToRemov,I1,J1).


write_new_predicates([],_,_):- !.
write_new_predicates([Predicate|R],FirstNewPredicate,ListRankToRemov):-
  length(ListRankToRemov,NbNotFDChars),
  functor(Predicate,NamePredicate,NbCols),
  NewNbCols is NbCols - NbNotFDChars,
  functor(NewPredicate,NamePredicate,NewNbCols),
  get_new_functor(Predicate,NewPredicate,NbCols,ListRankToRemov,1,1),
  (NewPredicate = FirstNewPredicate -> true;write(NewPredicate),write('.'),nl),
  write_new_predicates(R,NewPredicate,ListRankToRemov).


