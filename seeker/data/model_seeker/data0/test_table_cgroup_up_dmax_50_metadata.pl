:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_cgroup_up_dmax_50,0,3,495,name(n,nv,odc),kind(primary,primary,secondary),inout(input,input,output),min(1,0,0),max(30,30,1),types(int,int,bool),nval(30,31,2),median(21,9,1),gcd(1,1,1),sum(9920,4960,406),mean(20.04040404040404,10.02020202020202,0.8202020202020202),equal(0,0,0),fd([],[],[[col(test_table_cgroup_up_dmax_50,1),col(test_table_cgroup_up_dmax_50,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_cgroup_up_dmax_50,1),col(test_table_cgroup_up_dmax_50,2)),gt(col(test_table_cgroup_up_dmax_50,1),col(test_table_cgroup_up_dmax_50,3))],[geq(col(test_table_cgroup_up_dmax_50,2),col(test_table_cgroup_up_dmax_50,3)),leq(col(test_table_cgroup_up_dmax_50,2),col(test_table_cgroup_up_dmax_50,1))],[lt(col(test_table_cgroup_up_dmax_50,3),col(test_table_cgroup_up_dmax_50,1)),leq(col(test_table_cgroup_up_dmax_50,3),col(test_table_cgroup_up_dmax_50,2))]),nb_cmp(2,2,2),ctr([increasing],[],[]),maxocc(31,30,406),maxoccval(30,0,1),[],[],affinity(none,none,none),0-30,ranked_fd([],[],[[495,-0.31829309617176127,2]-[col(test_table_cgroup_up_dmax_50,1),col(test_table_cgroup_up_dmax_50,2)]]),distinct_vals([],[],[0-89,1-406]),vals_fds([],[],[]),monotonicities([],[],[])).
