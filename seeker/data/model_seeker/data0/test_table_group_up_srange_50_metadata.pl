:- multifile table_metadata/31.
:- dynamic table_metadata/31.

table_metadata(test_table_group_up_srange_50,0,3,270,name(ng,osmax,sminsmax),kind(primary,primary,secondary),inout(input,input,output),min(0,0,0),max(15,15,1),types(int,int,bool),nval(16,16,2),median(4.0,1.0,1.0),gcd(1,1,1),sum(1360,345,196),mean(5.037037037037037,1.2777777777777777,0.725925925925926),equal(0,0,0),fd([],[],[[col(test_table_group_up_srange_50,1),col(test_table_group_up_srange_50,2)]]),nb_fd(0,0,1),cmp([geq(col(test_table_group_up_srange_50,1),col(test_table_group_up_srange_50,2)),geq(col(test_table_group_up_srange_50,1),col(test_table_group_up_srange_50,3))],[geq(col(test_table_group_up_srange_50,2),col(test_table_group_up_srange_50,3)),leq(col(test_table_group_up_srange_50,2),col(test_table_group_up_srange_50,1))],[leq(col(test_table_group_up_srange_50,3),col(test_table_group_up_srange_50,1)),leq(col(test_table_group_up_srange_50,3),col(test_table_group_up_srange_50,2))]),nb_cmp(2,2,2),ctr([],[],[]),maxocc(30,226,196),maxoccval(0,1,1),[],[],affinity(none,none,t(226,1,-1,0,2,0)),0-15,ranked_fd([],[],[[30,-0.6472035288966551,2]-[col(test_table_group_up_srange_50,1),col(test_table_group_up_srange_50,2)]]),distinct_vals([],[],[0-74,1-196]),vals_fds([],[],[]),monotonicities([],[],[])).