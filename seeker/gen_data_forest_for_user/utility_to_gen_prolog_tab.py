#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Apr 17 11:21:10 2022

@author: jovial
"""


def ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param):
    list_parametres = ""
    k = 0
    for parametre in dataframe_tabledata.columns[:-1]:
        k = k + 1
        param_sans_moins = parametre.replace('-','').lower()
        if param_sans_moins == bounded:
            list_parametres = list_parametres + "t("+param_sans_moins+","+lowup+",output),\n"
        elif k <= nb_param : 
           list_parametres = list_parametres + "t("+param_sans_moins+",primary,input),\n"
        else:
           list_parametres = list_parametres + "t("+param_sans_moins+",secondary,input),\n" 
    
           
    if dataframe_tabledata.columns[-1] == bounded:
       list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+","+lowup+",output)\n"
    else:
       list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+",secondary,input)\n"  
    return list_parametres

def ecrire_un_fait(nom_de_la_table,entreetable):
    fait = nom_de_la_table+"("
    for valeur in entreetable[:-1]:
        fait = fait + str(int(valeur))+","
    fait = fait + str(int(entreetable[-1])) + ").\n" 
    return fait
        
def ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata):
    list_faits_prolog = ""
    for entreetable in dataframe_tabledata.values.tolist():
        list_faits_prolog = list_faits_prolog + ecrire_un_fait(nom_de_la_table,entreetable)
    return list_faits_prolog
    

    
def trans_allfeaturestabledata_prolog(nom_de_la_tab,dataframe_tabledata,lowup,maxn,bounded,nb_param,objet_combinatoire):
    nom_de_la_table = lowup+nom_de_la_tab
    
    nom_table_prolog = "data_"+objet_combinatoire+"/data"+str(maxn)+"/" + nom_de_la_table + ".pl"
    nb_col = dataframe_tabledata.shape[1]
    fichier0 = open(nom_table_prolog, "w")
    fichier0.write(":- multifile signature/3.\n"+
                  ":- multifile "+ nom_de_la_table+"/"+str(nb_col)+".\n"+
                  ":- dynamic signature/3.\n"+
                  ":- dynamic "+ nom_de_la_table+"/"+str(nb_col)+".\n\n"+
                  "signature("+ nom_de_la_table+","+str(maxn)+",t(\n"+
                  ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param)+")).\n\n"+
                  ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata))
    fichier0.close() 
    
    fichier1 = open("tables_"+objet_combinatoire+".pl", "a")
    fichier1.write("table("+ nom_de_la_table+","+str(maxn)+","+str(nb_col)+","+str(nb_param)+","+lowup+"("+bounded+")).\n")
    fichier1.close() 
