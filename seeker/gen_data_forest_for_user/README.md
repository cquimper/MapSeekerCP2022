## Description of the generated objects

> The files insides this directory are used to generate three combinatorials objects, namely :
1. forest without isolated vertices noted _forest_
2. forest with isolated vertices noted _forest0_
3. trees noted _tree_

> The goal of thoses scripts is to generate instances of the three objects where one of their characteristics are optimal acccording to their values. As exemples of characteristics, we have the greatest depth of a node noted _maxp_, the number of leaves noted _f_ or the number of nodes noted _v_ and etc...

> The main method used to generate those objects is a dedicated algorithm of [Donald E. Knuth](https://www-cs-faculty.stanford.edu/~knuth/taocp.html) stated Algorithm O (_Oriented forest_) of his book titled _Art of Computer Programming, Volume 4, Fascicle 4, Generating All Trees, History of Combinatorial Generation_ 

## Command lines to generate the objects

### Dependencies
> The programs [`python3`](https://www.python.org/downloads/), [`GNU Parallel`](https://www.gnu.org/software/parallel/)  and [`sicstus`](https://sicstus.sics.se/download4.html) should be installed
### Preparation for running the files to generate the combinatorials objects
> During installing `sicstus` make sure to keep the path directory of installation as to use it to run the script below in the Terminal

### Running the files to generate the combinatorial objects
> To generate the combinatorial object _forest_, _forest0_, or _tree_, after making sure that you are in the same directory of thoses files, you just need to run in the Terminal the script below

```./gen_forest.sh object full_path_where_is_installed_sicstus/sicstus```

where `object` is either _forest_, _forest0_, or _tree_

### Results of running the scripts above
> After running the scripts above, the generated objects which have extremal values of their caracteristics and no more than 18 vertices are stored in the directory named _data_ 