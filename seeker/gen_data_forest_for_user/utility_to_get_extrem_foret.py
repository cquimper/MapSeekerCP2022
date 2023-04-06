#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sat Apr 16 20:50:37 2022

@author: jovial
"""

from constraint import *
import pandas as pd
import numpy as np
import json



def gen_comb_foret_taille(nb_carac_comb,list_carac_names):
    problem = Problem()
    nb_carac_total = len(list_carac_names)
    problem.addVariables(range(nb_carac_comb), range(nb_carac_total))
    problem.addConstraint(AllDifferentConstraint())
    for indice1 in range(1):
        for indice2 in range(1,2):
             problem.addConstraint(lambda row1,row3: row1 == 0,
                                    (indice1,indice2))
    for indice1 in range(nb_carac_comb-2):
        for indice2 in range(indice1+1,nb_carac_comb-1):
             problem.addConstraint(lambda row1,row2: row1 < row2,
                                    (indice1,indice2))
    ind_carac_names = problem.getSolutions()
    combinaisons = []
    combinaison = [0]*nb_carac_comb
    for comb_dict in ind_carac_names:
        for key,value in comb_dict.items():
            combinaison[key]=list_carac_names[value]   
        combinaisons.append(combinaison)
        combinaison = [0]*nb_carac_comb
    return combinaisons 





def extrac_foret_extrem(combinaison,data_fram_tab,lowup,list_carac_names):
    colomns_final = combinaison+list( set(list_carac_names).difference(set(combinaison)))
    nb_params = len(combinaison)-1
    indice_initial = 0
    indices_forets_extrem = []
    df_0 = data_fram_tab.sort_values(by=combinaison[:-1])
    df_1 = pd.DataFrame(data=np.array(df_0)[:,1:],columns=df_0.columns[1:])
    df = df_1[combinaison]
    nb_lignes = df.shape[0]
    for i in range(nb_lignes-1):
        if not (df.loc[i][:nb_params] == df.loc[i+1][:nb_params]).all():
            list_entrees_egales = np.array(df[combinaison[-1]].loc[indice_initial:i])
            
            if lowup == "low":
               array_ind_entrees_egales = np.flatnonzero(list_entrees_egales == np.min(list_entrees_egales))
            else : 
               array_ind_entrees_egales = np.flatnonzero(list_entrees_egales == np.max(list_entrees_egales))
            list_ind_entrees_egales = array_ind_entrees_egales.tolist()
            for j in range(len(list_ind_entrees_egales)):
                list_ind_entrees_egales[j] = int(list_ind_entrees_egales[j]+indice_initial)
            indices_forets_extrem = indices_forets_extrem + list_ind_entrees_egales
            indice_initial = i+1
            
    k = indice_initial   
    list_entrees_egales = np.array(df[combinaison[-1]].loc[k:])         
    if lowup == "low":
            array_ind_entrees_egales = np.flatnonzero(list_entrees_egales == np.min(list_entrees_egales))
    else : 
            array_ind_entrees_egales = np.flatnonzero(list_entrees_egales == np.max(list_entrees_egales))
    list_ind_entrees_egales = array_ind_entrees_egales.tolist()
    for j in range(len(list_ind_entrees_egales)):
            list_ind_entrees_egales[j] = int(list_ind_entrees_egales[j]+k)
    indices_forets_extrem = indices_forets_extrem + list_ind_entrees_egales    
                              
    return  df_1.loc[indices_forets_extrem][colomns_final] 




def gen_name_datatable(combinaison):
    name_datatable = ""
    for param in combinaison:
        param_sans_moins = param.replace('-','').lower()
        name_datatable =  name_datatable + "_" + param_sans_moins                    
    return name_datatable    

 