# -*- coding: utf-8 -*-

from utility_to_gen_prolog_tab import trans_allfeaturestabledata_prolog
from utility_to_get_extrem_foret import extrac_foret_extrem,gen_name_datatable
import sys
import numpy as np
import pandas as pd

def taille(root,rooted_tree):
    taille1 = 1
    if len(rooted_tree) == 1:
        return taille1
    for i in rooted_tree[root+1:]:
        if i == 0:
            return taille1
        else:
            taille1 = taille1 + 1
    return taille1


def caracteristiques(rooted_tree):
    sizeforest = len(rooted_tree)
    vecteur_pere = [0]*sizeforest
    index_feuilles = []
    prof_feuilles = []
    vecteur_prof = [0]*sizeforest
   
    vecteur_deg = [0]*sizeforest
    vecteur_deg_pere = []
    
    for i in range(1,sizeforest):
            vecteur_pere[rooted_tree[i]]= 1
            vecteur_prof[i]= vecteur_prof[rooted_tree[i]]+1
            vecteur_deg[rooted_tree[i]]=  vecteur_deg[rooted_tree[i]]+1
    
    for i in range(sizeforest):
        if vecteur_pere[i] == 0:
            index_feuilles.append(i)     
    for i in index_feuilles:
        prof_feuilles.append(vecteur_prof[i])

    for i in range(sizeforest):
        if vecteur_deg[i] != 0:
            vecteur_deg_pere.append(vecteur_deg[i])
    if len(vecteur_deg_pere)== 0:
         vecteur_deg_pere.append(0)
    deg_min = min(vecteur_deg_pere)
    deg_max = max(vecteur_deg_pere)
    
    nb_feuilles_total = len(index_feuilles)
    prof_min = min(prof_feuilles)
    prof_max = max(prof_feuilles)
   
    return [sizeforest,nb_feuilles_total,deg_min,deg_max,prof_min,prof_max]


def largest_k_such_pk_not_0(oriented_tree):
    largest_k = 0
    for i in range(len(oriented_tree[:-1])):
        if oriented_tree[i] != 0:
            largest_k = i
        
    return largest_k
    

def visit(oriented_tree,sizeforest,j,d,with_tree):
    
    oriented_trees = []
    nb_solutions = 0
    saut2 = False
    saut3 = False
    saut4 = False
    saut5 = False
    largest_k = 1    
    while largest_k != 0:
        if saut2 == False:
        
            if with_tree :
                oriented_trees.append([list(oriented_tree)]+caracteristiques(oriented_tree))
            else :
                oriented_trees.append(caracteristiques(oriented_tree))
            nb_solutions = nb_solutions + 1
            saut3 = False
            saut4 = False
        
        if saut3 == False:
            if  oriented_tree[sizeforest] > 0:
                oriented_tree[sizeforest] = oriented_tree[oriented_tree[sizeforest]]
                saut2 = False
                saut4 = True
                saut5 = True
            
        
        if saut4 == False:
            largest_k = largest_k_such_pk_not_0(oriented_tree)
            if largest_k == 0:
                saut5 = True
            
            else:
                j = int(oriented_tree[largest_k])
                d = largest_k - j
                saut5 = False
                
            
        if saut5 == False:
            if oriented_tree[largest_k - d] == oriented_tree[j]:
                oriented_tree[largest_k] = oriented_tree[j]
            else :
                oriented_tree[largest_k] = oriented_tree[largest_k - d] + d
            

            if largest_k == sizeforest:
                saut2 = False
            else :
                largest_k = largest_k + 1
                saut4 = True
                saut2 = True
                saut3 = True
                saut5 = False
    return oriented_trees,nb_solutions

def all_oriented_tree_of_size(sizeforest,with_tree):
    
    oriented_tree = [0]*(sizeforest+1)
    nb_solutions = 0
    for i in range(sizeforest+1):
        oriented_tree[i] = i - 1
    
    #print(f"Forets de taille  {sizeforest} :")
    #print(oriented_tree)
    
    if sizeforest == 0:
        nb_solutions = nb_solutions + 1
        
       
        #print(f"Nombre d'arbres orientés de taille {sizeforest+1} = {nb_solutions} ")
        
        if with_tree :
            return [[oriented_tree]+caracteristiques(oriented_tree)]
        else :
            return [caracteristiques(oriented_tree)]
    
    j = 0
    d = 0
    oriented_trees,nb_solutions1 = visit(oriented_tree, sizeforest, j, d,with_tree)
              
    #print(f"Nombre d'arbres orientés de taille {sizeforest+1} = {nb_solutions1} ")
    return oriented_trees

def gen_tree_taille_max(v,with_tree):
    columns_with_tree = ["tree","v", "f","mind","maxd", "minp","maxp"]
    columns_without_tree = ["v", "f","mind","maxd", "minp","maxp"]
    data = []
    for n in range(1,v+1):
          data = data + all_oriented_tree_of_size(n-1,with_tree) 
    if with_tree:
           df = pd.DataFrame(data=data,columns=columns_with_tree)
    else :
           df = pd.DataFrame(data=data,columns=columns_without_tree)
    return df 

def gen_ext_tree():
    arguments = sys.argv[1].split(" ")

    maxn = int(arguments[0])

    combinaison = arguments[1:]

    list_carac_forets = ["v", "f","mind","maxd", "minp","maxp"]

    tree = pd.read_csv("tree_18.csv")
        
    nom_de_la_tab = gen_name_datatable(combinaison)
    bounded = combinaison[-1]
    nb_param = len(combinaison[:-1])

    valeurs_de_la_colonne_v = np.array(tree["v"])
    array_ind_entrees_egales_maxn = np.flatnonzero(valeurs_de_la_colonne_v == maxn)
    tree_maxn = tree.loc[0:max(array_ind_entrees_egales_maxn.tolist())]
                   
    tree_low = extrac_foret_extrem(combinaison,tree_maxn,"low",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,tree_low,"low",maxn,bounded,nb_param,"tree")
            
    tree_up = extrac_foret_extrem(combinaison,tree_maxn,"up",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,tree_up,"up",maxn,bounded,nb_param,"tree")
            
