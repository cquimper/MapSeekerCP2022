:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_partition0_up_max_6,0,3,220,name(n,nval,oc),kind(primary,primary,secondary),inout(input,input,output),min(1,1,0),max(10,10,1),types(int,int,bool),nval(10,10,2),median(8.0,3.0,1.0),gcd(1,1,1),sum(1705,715,210),mean(7.75,3.25,0.9545454545454546),equal(0,0,0),fd([],[],[[col(test_table_partition0_up_max_6,1),col(test_table_partition0_up_max_6,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_partition0_up_max_6,1),col(test_table_partition0_up_max_6,2)),gt(col(test_table_partition0_up_max_6,1),col(test_table_partition0_up_max_6,3))],[geq(col(test_table_partition0_up_max_6,2),col(test_table_partition0_up_max_6,3)),leq(col(test_table_partition0_up_max_6,2),col(test_table_partition0_up_max_6,1))],[lt(col(test_table_partition0_up_max_6,3),col(test_table_partition0_up_max_6,1)),leq(col(test_table_partition0_up_max_6,3),col(test_table_partition0_up_max_6,2))]),nb_cmp(2,2,2),ctr([increasing],[],[]),maxocc(55,55,210),maxoccval(10,1,1),[],[],affinity(none,none,none),0-10,ranked_fd([],[],[[55,-0.39640609617221256,2]-[col(test_table_partition0_up_max_6,1),col(test_table_partition0_up_max_6,2)]]),distinct_vals([],[],[0-10,1-210]),vals_fds([],[],[]),monotonicities([],[],[])).
