:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_cgroup_low_dmax_2,0,3,1985,name(ng,drange,dmax),kind(primary,primary,secondary),inout(input,input,output),min(0,0,0),max(15,1,2),types(int,bool,int),nval(16,2,3),median(4,0,1),gcd(1,1,1),sum(9795,338,2263),mean(4.934508816120907,0.17027707808564232,1.1400503778337532),equal(0,0,0),fd([],[],[[col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,2)),geq(col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,3))],[leq(col(test_table_cgroup_low_dmax_2,2),col(test_table_cgroup_low_dmax_2,3)),leq(col(test_table_cgroup_low_dmax_2,2),col(test_table_cgroup_low_dmax_2,1))],[leq(col(test_table_cgroup_low_dmax_2,3),col(test_table_cgroup_low_dmax_2,1)),geq(col(test_table_cgroup_low_dmax_2,3),col(test_table_cgroup_low_dmax_2,2))]),nb_cmp(2,2,2),ctr([],[],[]),maxocc(378,1647,1587),maxoccval(2,0,1),[],[],affinity(none,none,t(1925,1,-1,-1,2,0)),0-15,ranked_fd([],[],[[29,-0.9233170447469697,2]-[col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,2)]]),distinct_vals([],[0-1647,1-338],[0-60,1-1587,2-338]),vals_fds([],[],[[[col(test_table_cgroup_low_dmax_2,1)]-0,[col(test_table_cgroup_low_dmax_2,2)]-2,[]-1],[[col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,2)]-1,[col(test_table_cgroup_low_dmax_2,1)]-0,[]-2],[[col(test_table_cgroup_low_dmax_2,1),col(test_table_cgroup_low_dmax_2,2)]-1,[col(test_table_cgroup_low_dmax_2,2)]-0,[]-2],[[col(test_table_cgroup_low_dmax_2,2)]-2,[col(test_table_cgroup_low_dmax_2,1)]-0,[]-1]]),monotonicities([],[],[])).