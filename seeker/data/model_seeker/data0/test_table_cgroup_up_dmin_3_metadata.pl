:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_cgroup_up_dmin_3,0,2,30,name(n,odc),kind(primary,secondary),inout(input,output),min(1,0),max(30,1),types(int,bool),nval(30,2),median(15.5,1.0),gcd(1,1),sum(465,28),mean(15.5,0.9333333333333333),equal(0,0),fd([],[[col(test_table_cgroup_up_dmin_3,1)]]),nb_fd(0,1),cmp([gt(col(test_table_cgroup_up_dmin_3,1),col(test_table_cgroup_up_dmin_3,2))],[lt(col(test_table_cgroup_up_dmin_3,2),col(test_table_cgroup_up_dmin_3,1))]),nb_cmp(1,1),ctr([permutation,include_except_default_value_no_cycle(1,2,0,[]),strictly_increasing],[increasing]),maxocc(1,28),maxoccval(1,1),[],[],affinity(none,none),0-30,ranked_fd([],[[30,-0.86880470890498,1]-[col(test_table_cgroup_up_dmin_3,1)]]),distinct_vals([],[0-2,1-28]),vals_fds([],[]),monotonicities([],[])).
