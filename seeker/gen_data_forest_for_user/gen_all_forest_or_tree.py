#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 15:34:06 2023

@author: jovial

This file is to generate all forests or all trees of size 1 vertex up to maxn vertex
"""

from utility_to_gen_all_foret import gen_foret_taille_max
from utility_to_gen_all_tree import gen_tree_taille_max
import sys


 
arguments = sys.argv[1].split(" ")

print('args=',arguments)

taille_max_foret = int(arguments[0])


if arguments[1] == 'forest0' :
   foret_avec_point_isole = gen_foret_taille_max(taille_max_foret,True,True).sort_values(by="v")
   foret_avec_point_isole.to_csv("foret_avec_point_isole_" +str(taille_max_foret)+ ".csv")
   
if arguments[1] == 'forest' : 
   foret_sans_point_isole = gen_foret_taille_max(taille_max_foret,False,True).sort_values(by="v")
   foret_sans_point_isole.to_csv("foret_sans_point_isole_" +str(taille_max_foret)+ ".csv")
   
if arguments[1] == 'tree' :
   tree = gen_tree_taille_max(taille_max_foret,True).sort_values(by="v")
   tree.to_csv("tree_" +str(taille_max_foret)+ ".csv")
   
    
   