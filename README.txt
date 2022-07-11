To generate data,
create a directory data,
within this directory create a set of empty directories names data2, data3, ..., data26,
and use SICStus Prolog (https://sicstus.sics.se/):
 load gen_data.pl
 and call the goal top(26,1).

The code check_generated_data.pl identifies tables for which the generated data is not consistent,
namely the following tables:
	low_c_minc_maxc_mins_maxs,
	low_c_minc_mins_maxs,
	low_maxc_mins_maxs,
	low_maxc_mins_maxs_minc,
	low_maxc_mins_minc,
	low_maxc_s_mins_maxs_mina,
	low_maxc_s_mins_maxs_minc,
	low_maxc_s_mins_minc,
	low_minc_maxc_maxs_mins,
	low_minc_maxc_mins_maxs,
	low_minc_maxc_s_mins_maxs_mina,
	low_minc_mins_maxs,
	low_minc_mins_maxs_maxc,
	low_minc_s_maxc,
	low_minc_s_maxs_maxc,
	low_minc_s_mins_maxc,
	low_minc_s_mins_maxs_maxc,
	up_c_maxs_mins,
	up_c_minc_maxs_mins,
	up_maxc_maxs_mins,
	up_maxc_mins_maxs,
	up_maxc_mins_maxs_minc,
	up_maxc_s_c,
	up_maxc_s_maxs,
	up_maxc_s_minc,
	up_maxc_s_mins,
	up_maxc_s_mins_c,
	up_maxc_s_mins_maxs,
	up_maxc_s_mins_minc,
	up_minc_maxc_maxs_mins,
	up_minc_maxc_mins_maxs,
	up_minc_maxc_s_c,
	up_minc_maxc_s_maxs,
	up_minc_maxc_s_mins,
	up_minc_maxc_s_mins_c,
	up_minc_maxc_s_mins_maxs,
	up_minc_maxs_mins,
	up_minc_s_c,
	up_minc_s_mins_c

Such tables cannot be uses in an acquisition process.

The map_results folder contains the map found both
with and without using the acquisition of Boolean formulae.
