# -*- coding: utf-8 -*-

from utility_to_gen_prolog_tab import trans_allfeaturestabledata_prolog
from utility_to_get_extrem_foret import extrac_foret_extrem,gen_name_datatable
import sys
import numpy as np
import pandas as pd

def taille(root,oriented_forest):
    taille1 = 1
    if len(oriented_forest) == 1:
        return taille1
    for i in oriented_forest[root+1:]:
        if i == 0:
            return taille1
        else:
            taille1 = taille1 + 1
    return taille1

def caracteristiques(oriented_forest):
    sizeforest = len(oriented_forest)
    vecteur_pere = [0]*sizeforest
    index_feuilles = []
    prof_feuilles = []
    vecteur_prof = [0]*sizeforest
    vecteur_root = []
    vecteur_taille = []
    vecteur_deg = [0]*sizeforest
    vecteur_deg_pere = []
    nb_arbres  = 0
    nb_noeud_int = 0
    vect_nb_feuilles_par_arbre = []
    vect_nb_noeud_int = []
    for i in range(sizeforest):
        if oriented_forest[i] == 0:
            nb_arbres = nb_arbres + 1
            vecteur_root.append(i)
            if i != 0:
                vect_nb_noeud_int.append(nb_noeud_int)
                nb_noeud_int = 0
        else:
            if vecteur_pere[oriented_forest[i]-1] == 0:
                nb_noeud_int = nb_noeud_int + 1
            vecteur_pere[oriented_forest[i]-1]= 1
            vecteur_prof[i]= vecteur_prof[oriented_forest[i]-1]+1
            vecteur_deg[oriented_forest[i]-1]=  vecteur_deg[oriented_forest[i]-1]+1
    vect_nb_noeud_int.append(nb_noeud_int)
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
    rang_arbre = 0
    for i in vecteur_root:
        vecteur_taille.append(taille(i,oriented_forest))
        vect_nb_feuilles_par_arbre.append(taille(i,oriented_forest)-vect_nb_noeud_int[rang_arbre])
        rang_arbre = rang_arbre + 1
    
    nb_feuilles_min = min(vect_nb_feuilles_par_arbre)
    nb_feuilles_max = max(vect_nb_feuilles_par_arbre)
    nb_feuilles_total = sum(vect_nb_feuilles_par_arbre)
    prof_min = min(prof_feuilles)
    prof_max = max(prof_feuilles)
    taille_min = min(vecteur_taille)
    taille_max = max(vecteur_taille)
    return [sizeforest,nb_arbres,nb_feuilles_total,nb_feuilles_min,nb_feuilles_max,deg_min,deg_max,prof_min,prof_max,taille_min,taille_max]


def largest_k_such_pk_not_0(oriented_forest):
    largest_k = 0
    for i in range(len(oriented_forest[:-1])):
        if oriented_forest[i] != 0:
            largest_k = i
        
    return largest_k
    

def visit(oriented_forest,sizeforest,j,d,point_isole,with_forest):
    
    oriented_forests = []
    nb_solutions = 0
    saut2 = False
    saut3 = False
    saut4 = False
    saut5 = False
    largest_k = 1    
    while largest_k != 0:
        if saut2 == False:
            if point_isole:
                if with_forest:
                    oriented_forests.append([oriented_forest[1:]]+caracteristiques(oriented_forest[1:]))
                else :
                    oriented_forests.append(caracteristiques(oriented_forest[1:]))
                nb_solutions = nb_solutions + 1
            else:
                if caracteristiques(oriented_forest[1:])[7] != 0:
                    if with_forest:
                        oriented_forests.append([oriented_forest[1:]]+caracteristiques(oriented_forest[1:]))
                    else :
                        oriented_forests.append(caracteristiques(oriented_forest[1:]))
                    nb_solutions = nb_solutions + 1
                
                
            saut3 = False
            saut4 = False
        
        if saut3 == False:
            if  oriented_forest[sizeforest] > 0:
                oriented_forest[sizeforest] = oriented_forest[oriented_forest[sizeforest]]
                saut2 = False
                saut4 = True
                saut5 = True
            
        
        if saut4 == False:
            largest_k = largest_k_such_pk_not_0(oriented_forest)
            if largest_k == 0:
                saut5 = True
            
            else:
                j = int(oriented_forest[largest_k])
                d = largest_k - j
                saut5 = False
                
            
        if saut5 == False:
            if oriented_forest[largest_k - d] == oriented_forest[j]:
                oriented_forest[largest_k] = oriented_forest[j]
            else :
                oriented_forest[largest_k] = oriented_forest[largest_k - d] + d
            

            if largest_k == sizeforest:
                saut2 = False
            else :
                largest_k = largest_k + 1
                saut4 = True
                saut2 = True
                saut3 = True
                saut5 = False
    return oriented_forests,nb_solutions
 
def all_oriented_forest_of_size(sizeforest,point_isole,with_forest):
    
    oriented_forest = [0]*(sizeforest+1)
    nb_solutions = 0
    for i in range(sizeforest+1):
        oriented_forest[i] = i - 1
    
    #print(f"Forets de taille  {sizeforest} :")
    #print(oriented_forest)
    
    if sizeforest == 1:
        nb_solutions = nb_solutions + 1
        #print(oriented_forest[1:])
       
        #print(f"Nombre de forets de taille {sizeforest} = {nb_solutions} ")
        #fichier.write("forest_with_free_vertex("+write_carac(caracteristiques(oriented_forest[1:]))+").\n")
        if with_forest:
            return [[oriented_forest[1:]]+caracteristiques(oriented_forest[1:])]
        else :
            return [caracteristiques(oriented_forest[1:])]
    
    j = 0
    d = 0
    
    oriented_forests,nb_solutions1 = visit(oriented_forest, sizeforest, j, d,point_isole,with_forest)
              
    #print(f"Nombre de forets de taille {sizeforest} = {nb_solutions1} ")
    
    return oriented_forests


def gen_foret_taille_max(v,point_isole,with_forest):
    columns_with_forest = ["forest","v", "t","f","minf","maxf","mind","maxd", "minp","maxp","mint","maxt"]
    columns_without_forest = ["v", "t","f","minf","maxf","mind","maxd", "minp","maxp","mint","maxt"]
    data = []
    for n in range(1,v+1):
        data = data + all_oriented_forest_of_size(n,point_isole,with_forest) 
    if with_forest:
        df = pd.DataFrame(data=data,columns=columns_with_forest)
    else :
        df = pd.DataFrame(data=data,columns=columns_without_forest)
    return df

def gen_ext_foret_avec_point_isole():
    arguments = sys.argv[1].split(" ")
    
    maxn = int(arguments[0])

    combinaison = arguments[1:]

    list_carac_forets = ["v","t","f","minf","maxf","mind","maxd", "minp","maxp","mint","maxt"]

    foret_avec_point_isole = pd.read_csv("foret_avec_point_isole_18.csv")
        
    nom_de_la_tab = gen_name_datatable(combinaison)
    
    bounded = combinaison[-1]
    nb_param = len(combinaison[:-1])

    valeurs_de_la_colonne_v = np.array(foret_avec_point_isole["v"])
    array_ind_entrees_egales_maxn = np.flatnonzero(valeurs_de_la_colonne_v == maxn)
    foret_avec_point_isole_maxn = foret_avec_point_isole.loc[0:max(array_ind_entrees_egales_maxn.tolist())]

    foret_avec_point_isole_low = extrac_foret_extrem(combinaison,foret_avec_point_isole_maxn,"low",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,foret_avec_point_isole_low,"low",maxn,bounded,nb_param,"foret_avec_point_isole")   
            
    foret_avec_point_isole_up = extrac_foret_extrem(combinaison,foret_avec_point_isole_maxn,"up",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,foret_avec_point_isole_up,"up",maxn,bounded,nb_param,"foret_avec_point_isole")
            
def gen_ext_foret_sans_point_isole():
    arguments = sys.argv[1].split(" ")

    maxn = int(arguments[0])

    combinaison = arguments[1:]

    list_carac_forets = ["v","t","f","minf","maxf","mind","maxd", "minp","maxp","mint","maxt"]

    foret_sans_point_isole = pd.read_csv("foret_sans_point_isole_18.csv")
        
    nom_de_la_tab = gen_name_datatable(combinaison)
    bounded = combinaison[-1]
    nb_param = len(combinaison[:-1])

    valeurs_de_la_colonne_v = np.array(foret_sans_point_isole["v"])
    array_ind_entrees_egales_maxn = np.flatnonzero(valeurs_de_la_colonne_v == maxn)
    foret_sans_point_isole_maxn = foret_sans_point_isole.loc[0:max(array_ind_entrees_egales_maxn.tolist())]
            
    foret_sans_point_isole_low = extrac_foret_extrem(combinaison,foret_sans_point_isole_maxn,"low",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,foret_sans_point_isole_low,"low",maxn,bounded,nb_param,"foret_sans_point_isole")
            
    foret_sans_point_isole_up = extrac_foret_extrem(combinaison,foret_sans_point_isole_maxn,"up",list_carac_forets)
    trans_allfeaturestabledata_prolog(nom_de_la_tab,foret_sans_point_isole_up,"up",maxn,bounded,nb_param,"foret_sans_point_isole")
            
