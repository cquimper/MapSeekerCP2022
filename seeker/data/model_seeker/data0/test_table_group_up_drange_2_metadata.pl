:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_group_up_drange_2,0,3,436,name(dmax,dmin,dmindmax),kind(primary,primary,secondary),inout(input,input,output),min(0,0,0),max(28,28,1),types(int,int,bool),nval(29,29,2),median(8.0,1.0,1.0),gcd(1,1,1),sum(4060,1135,325),mean(9.311926605504587,2.603211009174312,0.7454128440366973),equal(0,0,0),fd([],[],[[col(test_table_group_up_drange_2,1),col(test_table_group_up_drange_2,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_group_up_drange_2,1),col(test_table_group_up_drange_2,2)),geq(col(test_table_group_up_drange_2,1),col(test_table_group_up_drange_2,3))],[geq(col(test_table_group_up_drange_2,2),col(test_table_group_up_drange_2,3)),leq(col(test_table_group_up_drange_2,2),col(test_table_group_up_drange_2,1))],[leq(col(test_table_group_up_drange_2,3),col(test_table_group_up_drange_2,1)),leq(col(test_table_group_up_drange_2,3),col(test_table_group_up_drange_2,2))]),nb_cmp(2,2,2),ctr([],[],[]),maxocc(30,353,325),maxoccval(0,1,1),[],[],affinity(none,none,t(355,1,-1,0,2,0)),0-28,ranked_fd([],[],[[54,-0.6957929073433634,2]-[col(test_table_group_up_drange_2,1),col(test_table_group_up_drange_2,2)]]),distinct_vals([],[],[0-111,1-325]),vals_fds([],[],[]),monotonicities([],[],[])).