#!/bin/sh

python3 gen_all_forest_or_tree.py "18 $1"

if [ $1 == 'forest' ]
then
cat threads_foret.txt | parallel -j4 python3 main_forest.py

$2 --noinfo -f -l gfd --goal top2.
fi

if [ $1 == 'tree' ]
then
cat threads_tree.txt | parallel -j4 python3 main_tree.py

$2 --noinfo -f -l gfd --goal top1.
fi

if [ $1 == 'forest0' ]
then
cat threads_foret.txt | parallel -j4 python3 main_forest0.py

$2 --noinfo -f -l gfd --goal top3.
fi

