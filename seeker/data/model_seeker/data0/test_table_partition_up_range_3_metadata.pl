:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_partition_up_range_3,0,3,120,name(n,min,nval),kind(primary,primary,secondary),inout(input,input,output),min(1,1,1),max(20,20,2),types(int,int,int),nval(20,20,2),median(14.0,4.0,2.0),gcd(1,1,1),sum(1595,595,220),mean(13.291666666666666,4.958333333333333,1.8333333333333333),equal(0,0,0),fd([],[],[[col(test_table_partition_up_range_3,1),col(test_table_partition_up_range_3,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_partition_up_range_3,1),col(test_table_partition_up_range_3,2)),geq(col(test_table_partition_up_range_3,1),col(test_table_partition_up_range_3,3))],[leq(col(test_table_partition_up_range_3,2),col(test_table_partition_up_range_3,1))],[leq(col(test_table_partition_up_range_3,3),col(test_table_partition_up_range_3,1))]),nb_cmp(2,1,1),ctr([increasing],[],[]),maxocc(11,20,100),maxoccval(20,1,2),[],[],affinity(none,none,none),1-20,ranked_fd([],[],[[120,-0.7817326451398301,2]-[col(test_table_partition_up_range_3,1),col(test_table_partition_up_range_3,2)]]),distinct_vals([],[],[1-20,2-100]),vals_fds([],[],[]),monotonicities([],[],[])).
