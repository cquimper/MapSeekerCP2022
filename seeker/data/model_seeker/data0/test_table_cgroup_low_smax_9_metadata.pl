:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_cgroup_low_smax_9,0,4,1087,name(n,ng,dmin,osc),kind(primary,primary,primary,secondary),inout(input,input,input,output),min(1,0,0,0),max(30,15,29,1),types(int,int,int,bool),nval(30,16,30,2),median(23,2,4,0),gcd(1,1,1,1),sum(23182,2999,6437,435),mean(21.32658693652254,2.7589696412143514,5.921803127874885,0.40018399264029436),equal(0,0,0,0),fd([],[],[],[[col(test_table_cgroup_low_smax_9,1),col(test_table_cgroup_low_smax_9,2),col(test_table_cgroup_low_smax_9,3)]]),nb_fd(0,0,0,1),cmp([geq(col(test_table_cgroup_low_smax_9,1),col(test_table_cgroup_low_smax_9,2)),gt(col(test_table_cgroup_low_smax_9,1),col(test_table_cgroup_low_smax_9,3)),gt(col(test_table_cgroup_low_smax_9,1),col(test_table_cgroup_low_smax_9,4))],[geq(col(test_table_cgroup_low_smax_9,2),col(test_table_cgroup_low_smax_9,4)),leq(col(test_table_cgroup_low_smax_9,2),col(test_table_cgroup_low_smax_9,1))],[lt(col(test_table_cgroup_low_smax_9,3),col(test_table_cgroup_low_smax_9,1))],[lt(col(test_table_cgroup_low_smax_9,4),col(test_table_cgroup_low_smax_9,1)),leq(col(test_table_cgroup_low_smax_9,4),col(test_table_cgroup_low_smax_9,2))]),nb_cmp(3,2,1,2),ctr([increasing],[],[],[]),maxocc(83,465,225,652),maxoccval(30,1,1,0),[],[],affinity(none,none,none,t(631,1,1,-2,2,0)),0-30,ranked_fd([],[],[],[[1087,-0.6106774390271719,3]-[col(test_table_cgroup_low_smax_9,1),col(test_table_cgroup_low_smax_9,2),col(test_table_cgroup_low_smax_9,3)]]),distinct_vals([],[],[],[0-652,1-435]),vals_fds([],[],[],[]),monotonicities([],[],[],[])).