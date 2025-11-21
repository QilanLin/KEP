

From 928 Axiom clauses, 2 were allowed.


A precedence of symbols which satisfies all compatible equal:lr annotations (the actual ordering is in general less restricted):
	[]

SPASS V 3.8ds 
SPASS beiseite: Completion found.
Problem: /Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob5405502_1.p 
SPASS derived 22 clauses, backtracked 0 clauses, performed 0 splits and kept 621 clauses.
SPASS allocated 95920 KBytes.
SPASS spent	0:00:00.29 on the problem.
		0:00:00.02 for the input.
		0:00:00.12 for the FLOTTER CNF translation.
		0:00:00.00 for inferences.
		0:00:00.00 for the backtracking.
		0:00:00.07 for the reduction.


 The saturated set of worked-off clauses is :
(d0,C,r1000,rw6000) 119[0:Inp] || equal(plus_plus_a(x,zero_zero_a),x)** -> .
(d0,A,r3345,rw1244340) 928[0:Inp] || SkP1(X8:booL,X9:booL,X27:booL)* SkP1(X9:booL,X27:booL,X8:booL)* SkP1(X9:booL,X8:booL,X27:booL)* SkP1(X8:booL,X27:booL,X9:booL)* SkP1(X27:booL,X9:booL,X8:booL)* SkP1(X27:booL,X8:booL,X9:booL)* -> .
(d0,A,r3349,rw1245828) 927[0:Inp] || SkP2(U:inT,X2:inT,X13:inT)* SkP2(X2:inT,X13:inT,U:inT)* SkP2(X2:inT,U:inT,X13:inT)* SkP2(U:inT,X13:inT,X2:inT)* SkP2(X13:inT,X2:inT,U:inT)* SkP2(X13:inT,U:inT,X2:inT)* -> .
(d0,A,r3340,rw1242480) 929[0:Inp] || SkP0(V:naT,X3:naT,X4:naT)* SkP0(X3:naT,X4:naT,V:naT)* SkP0(X3:naT,V:naT,X4:naT)* SkP0(V:naT,X4:naT,X3:naT)* SkP0(X4:naT,X3:naT,V:naT)* SkP0(X4:naT,V:naT,X3:naT)* -> .
(d0,A,r1391,rw357487) 915[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_int2(U:inT,aa_bool_int(X37:fun_bool_int,X8:booL)))* pp(ord_less_eq_int2(aa_bool_int(X37:fun_bool_int,skf118(X37:fun_bool_int)),aa_bool_int(X37:fun_bool_int,skf119(X37:fun_bool_int))))* -> pp(ord_less_int2(U:inT,aa_bool_int(X37:fun_bool_int,X9:booL)))*.
(d0,A,r1391,rw357487) 906[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_int2(aa_bool_int(X37:fun_bool_int,X9:booL),U:inT))* pp(ord_less_eq_int2(aa_bool_int(X37:fun_bool_int,skf136(X37:fun_bool_int)),aa_bool_int(X37:fun_bool_int,skf137(X37:fun_bool_int))))* -> pp(ord_less_int2(aa_bool_int(X37:fun_bool_int,X8:booL),U:inT))*.
(d0,A,r1391,rw357487) 916[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_bool2(X27:booL,aa_bool_bool(X35:fun_bool_bool,X8:booL)))* pp(ord_less_eq_bool2(aa_bool_bool(X35:fun_bool_bool,skf116(X35:fun_bool_bool)),aa_bool_bool(X35:fun_bool_bool,skf117(X35:fun_bool_bool))))* -> pp(ord_less_bool2(X27:booL,aa_bool_bool(X35:fun_bool_bool,X9:booL)))*.
(d0,A,r1391,rw357487) 907[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_bool2(aa_bool_bool(X35:fun_bool_bool,X9:booL),X27:booL))* pp(ord_less_eq_bool2(aa_bool_bool(X35:fun_bool_bool,skf134(X35:fun_bool_bool)),aa_bool_bool(X35:fun_bool_bool,skf135(X35:fun_bool_bool))))* -> pp(ord_less_bool2(aa_bool_bool(X35:fun_bool_bool,X8:booL),X27:booL))*.
(d0,A,r1391,rw357487) 917[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_nat2(V:naT,aa_bool_nat(X33:fun_bool_nat,X8:booL)))* pp(ord_less_eq_nat2(aa_bool_nat(X33:fun_bool_nat,skf114(X33:fun_bool_nat)),aa_bool_nat(X33:fun_bool_nat,skf115(X33:fun_bool_nat))))* -> pp(ord_less_nat2(V:naT,aa_bool_nat(X33:fun_bool_nat,X9:booL)))*.
(d0,A,r1391,rw357487) 908[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_nat2(aa_bool_nat(X33:fun_bool_nat,X9:booL),V:naT))* pp(ord_less_eq_nat2(aa_bool_nat(X33:fun_bool_nat,skf132(X33:fun_bool_nat)),aa_bool_nat(X33:fun_bool_nat,skf133(X33:fun_bool_nat))))* -> pp(ord_less_nat2(aa_bool_nat(X33:fun_bool_nat,X8:booL),V:naT))*.
(d0,A,r3215,rw826255) 912[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_int2(X13:inT,aa_int_int(X32:fun_int_int,U:inT)))* pp(ord_less_eq_int2(aa_int_int(X32:fun_int_int,skf124(X32:fun_int_int)),aa_int_int(X32:fun_int_int,skf125(X32:fun_int_int))))* -> pp(ord_less_int2(X13:inT,aa_int_int(X32:fun_int_int,X2:inT)))*.
(d0,A,r1668,rw428676) 897[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(X13:inT,aa_int_int(X32:fun_int_int,U:inT)))* pp(ord_less_int2(aa_int_int(X32:fun_int_int,skf154(X32:fun_int_int)),aa_int_int(X32:fun_int_int,skf155(X32:fun_int_int))))* -> pp(ord_less_int2(X13:inT,aa_int_int(X32:fun_int_int,X2:inT)))*.
(d0,A,r3255,rw836535) 903[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_int2(aa_int_int(X32:fun_int_int,X2:inT),X13:inT))* pp(ord_less_eq_int2(aa_int_int(X32:fun_int_int,skf142(X32:fun_int_int)),aa_int_int(X32:fun_int_int,skf143(X32:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X32:fun_int_int,U:inT),X13:inT))*.
(d0,A,r1668,rw428676) 921[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(aa_int_int(X32:fun_int_int,X2:inT),X13:inT))* pp(ord_less_int2(aa_int_int(X32:fun_int_int,skf106(X32:fun_int_int)),aa_int_int(X32:fun_int_int,skf107(X32:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X32:fun_int_int,U:inT),X13:inT))*.
(d0,A,r3206,rw823942) 914[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_nat2(V:naT,aa_int_nat(X31:fun_int_nat,U:inT)))* pp(ord_less_eq_nat2(aa_int_nat(X31:fun_int_nat,skf120(X31:fun_int_nat)),aa_int_nat(X31:fun_int_nat,skf121(X31:fun_int_nat))))* -> pp(ord_less_nat2(V:naT,aa_int_nat(X31:fun_int_nat,X2:inT)))*.
(d0,A,r1668,rw428676) 901[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_nat2(V:naT,aa_int_nat(X31:fun_int_nat,U:inT)))* pp(ord_less_nat2(aa_int_nat(X31:fun_int_nat,skf146(X31:fun_int_nat)),aa_int_nat(X31:fun_int_nat,skf147(X31:fun_int_nat))))* -> pp(ord_less_nat2(V:naT,aa_int_nat(X31:fun_int_nat,X2:inT)))*.
(d0,A,r3246,rw834222) 905[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_nat2(aa_int_nat(X31:fun_int_nat,X2:inT),V:naT))* pp(ord_less_eq_nat2(aa_int_nat(X31:fun_int_nat,skf138(X31:fun_int_nat)),aa_int_nat(X31:fun_int_nat,skf139(X31:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X31:fun_int_nat,U:inT),V:naT))*.
(d0,A,r1668,rw428676) 925[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_nat2(aa_int_nat(X31:fun_int_nat,X2:inT),V:naT))* pp(ord_less_nat2(aa_int_nat(X31:fun_int_nat,skf98(X31:fun_int_nat)),aa_int_nat(X31:fun_int_nat,skf99(X31:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X31:fun_int_nat,U:inT),V:naT))*.
(d0,A,r1512,rw388584) 900[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_bool2(X8:booL,aa_nat_bool(X21:fun_nat_bool,V:naT)))* pp(ord_less_bool2(aa_nat_bool(X21:fun_nat_bool,skf148(X21:fun_nat_bool)),aa_nat_bool(X21:fun_nat_bool,skf149(X21:fun_nat_bool))))* -> pp(ord_less_bool2(X8:booL,aa_nat_bool(X21:fun_nat_bool,X3:naT)))*.
(d0,A,r1378,rw354146) 919[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_bool2(X8:booL,aa_nat_bool(X21:fun_nat_bool,V:naT)))* pp(ord_less_eq_bool2(aa_nat_bool(X21:fun_nat_bool,skf110(X21:fun_nat_bool)),aa_nat_bool(X21:fun_nat_bool,skf111(X21:fun_nat_bool))))* -> pp(ord_less_bool2(X8:booL,aa_nat_bool(X21:fun_nat_bool,X3:naT)))*.
(d0,A,r1512,rw388584) 924[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_bool2(aa_nat_bool(X21:fun_nat_bool,X3:naT),X8:booL))* pp(ord_less_bool2(aa_nat_bool(X21:fun_nat_bool,skf100(X21:fun_nat_bool)),aa_nat_bool(X21:fun_nat_bool,skf101(X21:fun_nat_bool))))* -> pp(ord_less_bool2(aa_nat_bool(X21:fun_nat_bool,V:naT),X8:booL))*.
(d0,A,r1378,rw354146) 910[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_bool2(aa_nat_bool(X21:fun_nat_bool,X3:naT),X8:booL))* pp(ord_less_eq_bool2(aa_nat_bool(X21:fun_nat_bool,skf128(X21:fun_nat_bool)),aa_nat_bool(X21:fun_nat_bool,skf129(X21:fun_nat_bool))))* -> pp(ord_less_bool2(aa_nat_bool(X21:fun_nat_bool,V:naT),X8:booL))*.
(d0,A,r3211,rw825227) 913[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_bool2(X8:booL,aa_int_bool(X20:fun_int_bool,U:inT)))* pp(ord_less_eq_bool2(aa_int_bool(X20:fun_int_bool,skf122(X20:fun_int_bool)),aa_int_bool(X20:fun_int_bool,skf123(X20:fun_int_bool))))* -> pp(ord_less_bool2(X8:booL,aa_int_bool(X20:fun_int_bool,X2:inT)))*.
(d0,A,r1668,rw428676) 899[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_bool2(X8:booL,aa_int_bool(X20:fun_int_bool,U:inT)))* pp(ord_less_bool2(aa_int_bool(X20:fun_int_bool,skf150(X20:fun_int_bool)),aa_int_bool(X20:fun_int_bool,skf151(X20:fun_int_bool))))* -> pp(ord_less_bool2(X8:booL,aa_int_bool(X20:fun_int_bool,X2:inT)))*.
(d0,A,r3251,rw835507) 904[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_bool2(aa_int_bool(X20:fun_int_bool,X2:inT),X8:booL))* pp(ord_less_eq_bool2(aa_int_bool(X20:fun_int_bool,skf140(X20:fun_int_bool)),aa_int_bool(X20:fun_int_bool,skf141(X20:fun_int_bool))))* -> pp(ord_less_bool2(aa_int_bool(X20:fun_int_bool,U:inT),X8:booL))*.
(d0,A,r1668,rw428676) 923[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_bool2(aa_int_bool(X20:fun_int_bool,X2:inT),X8:booL))* pp(ord_less_bool2(aa_int_bool(X20:fun_int_bool,skf102(X20:fun_int_bool)),aa_int_bool(X20:fun_int_bool,skf103(X20:fun_int_bool))))* -> pp(ord_less_bool2(aa_int_bool(X20:fun_int_bool,U:inT),X8:booL))*.
(d0,A,r1378,rw354146) 920[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X4:naT,aa_nat_nat(W:fun_nat_nat,V:naT)))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf108(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf109(W:fun_nat_nat))))* -> pp(ord_less_nat2(X4:naT,aa_nat_nat(W:fun_nat_nat,X3:naT)))*.
(d0,A,r1512,rw388584) 902[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(X4:naT,aa_nat_nat(W:fun_nat_nat,V:naT)))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf144(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf145(W:fun_nat_nat))))* -> pp(ord_less_nat2(X4:naT,aa_nat_nat(W:fun_nat_nat,X3:naT)))*.
(d0,A,r1378,rw354146) 911[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,X3:naT),X4:naT))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf126(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf127(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,V:naT),X4:naT))*.
(d0,A,r1512,rw388584) 926[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,X3:naT),X4:naT))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf96(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf97(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,V:naT),X4:naT))*.
(d0,A,r1512,rw388584) 898[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_int2(U:inT,aa_nat_int(X:fun_nat_int,V:naT)))* pp(ord_less_int2(aa_nat_int(X:fun_nat_int,skf152(X:fun_nat_int)),aa_nat_int(X:fun_nat_int,skf153(X:fun_nat_int))))* -> pp(ord_less_int2(U:inT,aa_nat_int(X:fun_nat_int,X3:naT)))*.
(d0,A,r1378,rw354146) 918[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_int2(U:inT,aa_nat_int(X:fun_nat_int,V:naT)))* pp(ord_less_eq_int2(aa_nat_int(X:fun_nat_int,skf112(X:fun_nat_int)),aa_nat_int(X:fun_nat_int,skf113(X:fun_nat_int))))* -> pp(ord_less_int2(U:inT,aa_nat_int(X:fun_nat_int,X3:naT)))*.
(d0,A,r1512,rw388584) 922[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_int2(aa_nat_int(X:fun_nat_int,X3:naT),U:inT))* pp(ord_less_int2(aa_nat_int(X:fun_nat_int,skf104(X:fun_nat_int)),aa_nat_int(X:fun_nat_int,skf105(X:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X:fun_nat_int,V:naT),U:inT))*.
(d0,A,r1378,rw354146) 909[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_int2(aa_nat_int(X:fun_nat_int,X3:naT),U:inT))* pp(ord_less_eq_int2(aa_nat_int(X:fun_nat_int,skf130(X:fun_nat_int)),aa_nat_int(X:fun_nat_int,skf131(X:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X:fun_nat_int,V:naT),U:inT))*.
(d0,A,r1114,rw236168) 1009[0:Rew:195.0,886.0] ||  -> pp(ord_less_nat2(suc1(V:naT),X3:naT)) equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,suc1(V:naT)),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(X3:naT,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(X3:naT,suc1(V:naT))))**.
(d0,A,r1110,rw235320) 1008[0:Rew:194.0,885.0] ||  -> pp(ord_less_nat2(suc1(V:naT),X3:naT)) equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(V:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(X3:naT,V:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(X3:naT,suc1(V:naT))))**.
(d0,A,r1105,rw234260) 1010[0:Rew:193.0,887.0] ||  -> pp(ord_less_nat2(suc1(V:naT),X3:naT)) equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(V:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(X3:naT,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(X3:naT,suc1(V:naT))))**.
(d0,A,r1114,rw232826) 1003[0:Rew:195.0,877.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,V:naT),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(X3:naT,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r1110,rw231990) 1004[0:Rew:194.0,878.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,V:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(X3:naT,V:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r1105,rw230945) 1002[0:Rew:193.0,876.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,V:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(X3:naT,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r2969,rw561141) 855[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,times_1419655522nteger(X1:code_integer,X14:code_integer)),plus_p715165435teger2(Z:code_integer,times_1419655522nteger(X1:code_integer,X18:code_integer)))* -> equal(X14:code_integer,X18:code_integer) equal(X1:code_integer,zero_z413810534nteger).
(d0,A,r2974,rw562086) 856[0:Inp] || equal(plus_plus_int2(U:inT,times_times_int2(X2:inT,X13:inT)),plus_plus_int2(U:inT,times_times_int2(X2:inT,X17:inT)))* -> equal(X13:inT,X17:inT) equal(X2:inT,zero_zero_int).
(d0,A,r2978,rw562842) 857[0:Inp] || equal(plus_plus_nat2(V:naT,times_times_nat2(X3:naT,X4:naT)),plus_plus_nat2(V:naT,times_times_nat2(X3:naT,X16:naT)))* -> equal(X4:naT,X16:naT) equal(X3:naT,zero_zero_nat).
(d0,A,r900,rw153000) 999[0:Rew:44.0,882.0] || pp(aa_nat_bool(X21:fun_nat_bool,V:naT))* pp(dvd_dvd_nat2(X3:naT,V:naT))* -> pp(aa_nat_bool(X21:fun_nat_bool,times_times_nat2(X3:naT,skf90(X3:naT,X21:fun_nat_bool))))*.
(d0,A,r908,rw154360) 1000[0:Rew:46.0,883.0] || pp(aa_int_bool(X20:fun_int_bool,U:inT))* pp(dvd_dvd_int2(X2:inT,U:inT))* -> pp(aa_int_bool(X20:fun_int_bool,times_times_int2(X2:inT,skf88(X2:inT,X20:fun_int_bool))))*.
(d0,A,r904,rw153680) 1001[0:Rew:45.0,884.0] || pp(aa_Code_integer_bool(X19:fun_Co535713875r_bool,Z:code_integer))* pp(dvd_dv413397790teger2(X1:code_integer,Z:code_integer))* -> pp(aa_Code_integer_bool(X19:fun_Co535713875r_bool,times_1419655522nteger(X1:code_integer,skf86(X1:code_integer,X19:fun_Co535713875r_bool))))*.
(d0,A,r2026,rw344420) 843[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) pp(ord_le1687847920teger2(X14:code_integer,X18:code_integer)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X18:code_integer,X1:code_integer)))*.
(d0,A,r1780,rw302600) 825[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(X14:code_integer,X18:code_integer)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X18:code_integer,X1:code_integer)))*.
(d0,A,r1807,rw307190) 831[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(X14:code_integer,X18:code_integer)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X18:code_integer,X1:code_integer)))*.
(d0,A,r1794,rw304980) 828[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1687847920teger2(X14:code_integer,X18:code_integer)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X18:code_integer,X1:code_integer)))*.
(d0,A,r2035,rw345950) 845[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) pp(ord_less_int2(X13:inT,X17:inT)) -> pp(ord_less_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X17:inT,X2:inT)))*.
(d0,A,r1789,rw304130) 827[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X13:inT,X17:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X17:inT,X2:inT)))*.
(d0,A,r1816,rw308720) 833[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X13:inT,X17:inT)) -> pp(ord_less_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X17:inT,X2:inT)))*.
(d0,A,r1802,rw306340) 830[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_int2(X13:inT,X17:inT)) -> pp(ord_less_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X17:inT,X2:inT)))*.
(d0,A,r2030,rw345100) 844[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) pp(ord_less_nat2(X4:naT,X16:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X16:naT,X3:naT)))*.
(d0,A,r1785,rw303450) 826[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X4:naT,X16:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X16:naT,X3:naT)))*.
(d0,A,r1811,rw307870) 832[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X4:naT,X16:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X16:naT,X3:naT)))*.
(d0,A,r1798,rw305660) 829[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_nat2(X4:naT,X16:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X16:naT,X3:naT)))*.
(d0,A,r1114,rw187152) 1006[0:Rew:1003.0,880.0,195.0,880.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(X3:naT,suc1(V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r1110,rw186480) 1005[0:Rew:1004.0,879.0,194.0,879.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(X3:naT,suc1(V:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r1105,rw185640) 1007[0:Rew:1002.0,881.0,193.0,881.0] ||  -> pp(ord_less_nat2(V:naT,X3:naT)) equal(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(X3:naT,suc1(V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(X3:naT,V:naT)))**.
(d0,A,r1110,rw177600) 997[0:Rew:194.0,895.0] ||  -> equal(times_times_int2(numeral_numeral_int1(bit0(onE)),groups332228664at_int(aTP_Lamm_ad_2(U:inT,X2:inT),set_or601162459st_nat(zero_zero_nat,V:naT))),times_times_int2(plus_plus_int2(one_one_int,semiri501196819t_int1(V:naT)),plus_plus_int2(times_times_int2(numeral_numeral_int1(bit0(onE)),U:inT),times_times_int2(semiri501196819t_int1(V:naT),X2:inT))))*.
(d0,A,r1114,rw178240) 998[0:Rew:195.0,896.0] ||  -> equal(times_1419655522nteger(numera1961560056ntegeR(bit0(onE)),groups1456475753ntegeR(aTP_Lamm_ac_2(Z:code_integer,X1:code_integer),set_or601162459st_nat(zero_zero_nat,V:naT))),times_1419655522nteger(plus_p715165435teger2(one_one_Code_integer,semiri1360655138teger1(V:naT)),plus_p715165435teger2(times_1419655522nteger(numera1961560056ntegeR(bit0(onE)),Z:code_integer),times_1419655522nteger(semiri1360655138teger1(V:naT),X1:code_integer))))*.
(d0,A,r900,rw141300) 996[0:Rew:44.0,894.0,364.0,894.0,17.0,894.0,940.0,894.0] ||  -> equal(times_times_nat2(numeral_numeral_nat(bit0(onE)),groups1842438620at_nat(aTP_Lamm_ae_2(V:naT,X3:naT),set_or601162459st_nat(zero_zero_nat,X4:naT))),times_times_nat2(suc1(X4:naT),plus_plus_nat2(times_times_nat2(numeral_numeral_nat(bit0(onE)),V:naT),times_times_nat2(X4:naT,X3:naT))))*.
(d0,A,r3389,rw511739) 860[0:Inp] SkP5(X40:fun_int_fun_int_bool) || pp(aa_int_bool(aa_int_fun_int_bool(X40:fun_int_fun_int_bool,skf165(X40:fun_int_fun_int_bool)),skf164(X40:fun_int_fun_int_bool)))* -> pp(aa_int_bool(aa_int_fun_int_bool(X40:fun_int_fun_int_bool,U:inT),X2:inT))*.
(d0,A,r1391,rw210041) 859[0:Inp] SkP4(X39:fun_bo1373903021l_bool) || pp(aa_bool_bool(aa_boo1142376798l_bool(X39:fun_bo1373903021l_bool,skf161(X39:fun_bo1373903021l_bool)),skf160(X39:fun_bo1373903021l_bool)))* -> pp(aa_bool_bool(aa_boo1142376798l_bool(X39:fun_bo1373903021l_bool,X8:booL),X9:booL))*.
(d0,A,r1378,rw208078) 858[0:Inp] SkP3(X38:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X38:fun_nat_fun_nat_bool,skf157(X38:fun_nat_fun_nat_bool)),skf156(X38:fun_nat_fun_nat_bool)))* -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X38:fun_nat_fun_nat_bool,V:naT),X3:naT))*.
(d0,A,r2947,rw436156) 765[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL)) pp(ord_less_eq_bool2(X9:booL,X27:booL)) -> member_bool(X9:booL,set_or842601420t_bool(X8:booL,X27:booL))*.
(d0,A,r2951,rw436748) 766[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X2:inT,X13:inT)) -> member_int(X2:inT,set_or1238436151st_int(U:inT,X13:inT))*.
(d0,A,r2942,rw435416) 764[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X3:naT,X4:naT)) -> member_nat(X3:naT,set_or601162459st_nat(V:naT,X4:naT))*.
(d0,A,r3304,rw485688) 731[0:Inp] || equal(times_1419655522nteger(Z:code_integer,X1:code_integer),times_1419655522nteger(X14:code_integer,X1:code_integer))* -> equal(Z:code_integer,X14:code_integer) equal(X1:code_integer,zero_z413810534nteger).
(d0,A,r2929,rw430563) 722[0:Inp] || equal(times_1419655522nteger(Z:code_integer,X1:code_integer),times_1419655522nteger(Z:code_integer,X14:code_integer))* -> equal(X1:code_integer,X14:code_integer) equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r3309,rw486423) 732[0:Inp] || equal(times_times_int2(U:inT,X2:inT),times_times_int2(X13:inT,X2:inT))* -> equal(U:inT,X13:inT) equal(X2:inT,zero_zero_int).
(d0,A,r2933,rw431151) 723[0:Inp] || equal(times_times_int2(U:inT,X2:inT),times_times_int2(U:inT,X13:inT))* -> equal(X2:inT,X13:inT) equal(U:inT,zero_zero_int).
(d0,A,r3313,rw487011) 733[0:Inp] || equal(times_times_nat2(V:naT,X3:naT),times_times_nat2(X4:naT,X3:naT))* -> equal(V:naT,X4:naT) equal(X3:naT,zero_zero_nat).
(d0,A,r2938,rw431886) 724[0:Inp] || equal(times_times_nat2(V:naT,X3:naT),times_times_nat2(V:naT,X4:naT))* -> equal(X3:naT,X4:naT) equal(V:naT,zero_zero_nat).
(d0,A,r2424,rw353904) 658[0:Inp] ||  -> equal(plus_p715165435teger2(times_1419655522nteger(Z:code_integer,X1:code_integer),times_1419655522nteger(Z:code_integer,X14:code_integer)),times_1419655522nteger(Z:code_integer,plus_p715165435teger2(X1:code_integer,X14:code_integer)))**.
(d0,A,r1771,rw258566) 636[0:Inp] ||  -> equal(plus_p715165435teger2(times_1419655522nteger(Z:code_integer,X1:code_integer),times_1419655522nteger(X14:code_integer,X1:code_integer)),times_1419655522nteger(plus_p715165435teger2(Z:code_integer,X14:code_integer),X1:code_integer))**.
(d0,A,r2419,rw353174) 657[0:Inp] ||  -> equal(plus_plus_int2(times_times_int2(U:inT,X2:inT),times_times_int2(U:inT,X13:inT)),times_times_int2(U:inT,plus_plus_int2(X2:inT,X13:inT)))**.
(d0,A,r1767,rw257982) 635[0:Inp] ||  -> equal(plus_plus_int2(times_times_int2(U:inT,X2:inT),times_times_int2(X13:inT,X2:inT)),times_times_int2(plus_plus_int2(U:inT,X13:inT),X2:inT))**.
(d0,A,r2428,rw354488) 659[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(V:naT,X3:naT),times_times_nat2(V:naT,X4:naT)),times_times_nat2(V:naT,plus_plus_nat2(X3:naT,X4:naT)))**.
(d0,A,r1776,rw259296) 637[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(V:naT,X3:naT),times_times_nat2(X4:naT,X3:naT)),times_times_nat2(plus_plus_nat2(V:naT,X4:naT),X3:naT))**.
(d0,A,r1114,rw145934) 989[0:Rew:195.0,821.0] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,suc1(V:naT)),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(zero_zero_nat,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r1110,rw145410) 988[0:Rew:194.0,820.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(V:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(zero_zero_nat,V:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r1105,rw144755) 987[0:Rew:193.0,819.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(V:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(zero_zero_nat,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2361,rw306930) 812[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) pp(ord_le1687847920teger2(zero_z413810534nteger,X14:code_integer)) -> pp(ord_le1687847920teger2(Z:code_integer,plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r2178,rw283140) 800[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(zero_z413810534nteger,X14:code_integer)) -> pp(ord_le1442264292teger2(Z:code_integer,plus_p715165435teger2(X1:code_integer,X14:code_integer)))*.
(d0,A,r2160,rw280800) 797[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(zero_z413810534nteger,X14:code_integer)) -> pp(ord_le1442264292teger2(Z:code_integer,plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r1959,rw254670) 785[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(zero_z413810534nteger,X14:code_integer)) -> pp(ord_le1687847920teger2(Z:code_integer,plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r1919,rw249470) 782[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1687847920teger2(zero_z413810534nteger,X14:code_integer)) -> pp(ord_le1687847920teger2(Z:code_integer,plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r2232,rw290160) 806[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(X14:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X14:code_integer),X1:code_integer))*.
(d0,A,r2218,rw288340) 803[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) pp(ord_le1442264292teger2(X14:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),X1:code_integer))*.
(d0,A,r2370,rw308100) 814[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) pp(ord_less_int2(zero_zero_int,X13:inT)) -> pp(ord_less_int2(U:inT,plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r2187,rw284310) 802[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(zero_zero_int,X13:inT)) -> pp(ord_less_eq_int2(U:inT,plus_plus_int2(X2:inT,X13:inT)))*.
(d0,A,r2169,rw281970) 799[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(zero_zero_int,X13:inT)) -> pp(ord_less_eq_int2(U:inT,plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r1968,rw255840) 787[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(zero_zero_int,X13:inT)) -> pp(ord_less_int2(U:inT,plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r1928,rw250640) 784[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_int2(zero_zero_int,X13:inT)) -> pp(ord_less_int2(U:inT,plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r2241,rw291330) 808[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X13:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(U:inT,X13:inT),X2:inT))*.
(d0,A,r2227,rw289510) 805[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X13:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X13:inT,U:inT),X2:inT))*.
(d0,A,r1923,rw249990) 783[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_nat2(zero_zero_nat,X4:naT)) -> pp(ord_less_nat2(V:naT,plus_plus_nat2(X4:naT,X3:naT)))*.
(d0,A,r2236,rw290680) 807[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X4:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X4:naT),X3:naT))*.
(d0,A,r2223,rw288990) 804[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X4:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X4:naT,V:naT),X3:naT))*.
(d0,A,r1114,rw144820) 986[0:Rew:195.0,817.0] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,V:naT),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(zero_zero_nat,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r1110,rw144300) 985[0:Rew:194.0,816.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,V:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,V:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r1105,rw143650) 984[0:Rew:193.0,815.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,V:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r1731,rw221568) 704[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_eq_bool2(X27:booL,X8:booL))* -> pp(ord_less_eq_bool2(X27:booL,X9:booL))*.
(d0,A,r2679,rw342912) 714[0:Inp] || pp(ord_less_bool2(X8:booL,X9:booL))* pp(ord_less_eq_bool2(X27:booL,X8:booL))* -> pp(ord_less_bool2(X27:booL,X9:booL))*.
(d0,A,r2196,rw281088) 709[0:Inp] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_bool2(X27:booL,X8:booL))* -> pp(ord_less_bool2(X27:booL,X9:booL))*.
(d0,A,r3014,rw385792) 726[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_int2(X13:inT,U:inT))* -> pp(ord_less_int2(X13:inT,X2:inT))*.
(d0,A,r1735,rw222080) 705[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(X13:inT,U:inT))* -> pp(ord_less_eq_int2(X13:inT,X2:inT))*.
(d0,A,r2683,rw343424) 715[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(X13:inT,U:inT))* -> pp(ord_less_int2(X13:inT,X2:inT))*.
(d0,A,r2200,rw281600) 710[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_int2(X13:inT,U:inT))* -> pp(ord_less_int2(X13:inT,X2:inT))*.
(d0,A,r3009,rw385152) 725[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X4:naT,V:naT))* -> pp(ord_less_nat2(X4:naT,X3:naT))*.
(d0,A,r1726,rw220928) 703[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(X4:naT,V:naT))* -> pp(ord_less_eq_nat2(X4:naT,X3:naT))*.
(d0,A,r2674,rw342272) 713[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(X4:naT,V:naT))* -> pp(ord_less_nat2(X4:naT,X3:naT))*.
(d0,A,r2191,rw280448) 708[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X4:naT,V:naT))* -> pp(ord_less_nat2(X4:naT,X3:naT))*.
(d0,A,r1226,rw155702) 608[0:Inp] || pp(aa_nat_bool(X21:fun_nat_bool,times_times_nat2(V:naT,X3:naT)))* -> pp(aa_nat_bool(X21:fun_nat_bool,skf89(X21:fun_nat_bool,V:naT)))*.
(d0,A,r917,rw116459) 979[0:Rew:48.0,747.1,193.0,747.1] || pp(aa_nat_bool(X21:fun_nat_bool,times_times_nat2(V:naT,X3:naT)))* -> pp(dvd_dvd_nat2(V:naT,skf89(X21:fun_nat_bool,V:naT)))*.
(d0,A,r1221,rw155067) 607[0:Inp] || pp(aa_int_bool(X20:fun_int_bool,times_times_int2(U:inT,X2:inT)))* -> pp(aa_int_bool(X20:fun_int_bool,skf87(X20:fun_int_bool,U:inT)))*.
(d0,A,r926,rw117602) 978[0:Rew:50.0,746.1,194.0,746.1] || pp(aa_int_bool(X20:fun_int_bool,times_times_int2(U:inT,X2:inT)))* -> pp(dvd_dvd_int2(U:inT,skf87(X20:fun_int_bool,U:inT)))*.
(d0,A,r1217,rw154559) 606[0:Inp] || pp(aa_Code_integer_bool(X19:fun_Co535713875r_bool,times_1419655522nteger(Z:code_integer,X1:code_integer)))* -> pp(aa_Code_integer_bool(X19:fun_Co535713875r_bool,skf85(X19:fun_Co535713875r_bool,Z:code_integer)))*.
(d0,A,r922,rw117094) 977[0:Rew:49.0,745.1,195.0,745.1] || pp(aa_Code_integer_bool(X19:fun_Co535713875r_bool,times_1419655522nteger(Z:code_integer,X1:code_integer)))* -> pp(dvd_dv413397790teger2(Z:code_integer,skf85(X19:fun_Co535713875r_bool,Z:code_integer)))*.
(d0,A,r1583,rw201041) 629[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer)))* -> pp(ord_le1687847920teger2(Z:code_integer,X14:code_integer)).
(d0,A,r1557,rw197739) 623[0:Inp] || pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer)))* -> pp(ord_le1442264292teger2(Z:code_integer,X14:code_integer)).
(d0,A,r1539,rw195453) 617[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(Z:code_integer,X14:code_integer)))* -> pp(ord_le1687847920teger2(X1:code_integer,X14:code_integer)).
(d0,A,r1364,rw173228) 609[0:Inp] || pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(Z:code_integer,X14:code_integer)))* -> pp(ord_le1442264292teger2(X1:code_integer,X14:code_integer)).
(d0,A,r1583,rw201041) 630[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X14:code_integer),plus_p715165435teger2(X1:code_integer,X14:code_integer)))*.
(d0,A,r1557,rw197739) 624[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X14:code_integer),plus_p715165435teger2(X1:code_integer,X14:code_integer)))*.
(d0,A,r1539,rw195453) 618[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,X1:code_integer)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r1364,rw173228) 610[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,X1:code_integer)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer)))*.
(d0,A,r1592,rw202184) 633[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(X13:inT,X2:inT)))* -> pp(ord_less_int2(U:inT,X13:inT)).
(d0,A,r1566,rw198882) 627[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(X13:inT,X2:inT)))* -> pp(ord_less_eq_int2(U:inT,X13:inT)).
(d0,A,r1548,rw196596) 621[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(U:inT,X13:inT)))* -> pp(ord_less_int2(X2:inT,X13:inT)).
(d0,A,r1373,rw174371) 613[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(U:inT,X13:inT)))* -> pp(ord_less_eq_int2(X2:inT,X13:inT)).
(d0,A,r1592,rw202184) 634[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) -> pp(ord_less_int2(plus_plus_int2(U:inT,X13:inT),plus_plus_int2(X2:inT,X13:inT)))*.
(d0,A,r1566,rw198882) 628[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(U:inT,X13:inT),plus_plus_int2(X2:inT,X13:inT)))*.
(d0,A,r1548,rw196596) 622[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) -> pp(ord_less_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r1373,rw174371) 614[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X13:inT,X2:inT)))*.
(d0,A,r1588,rw201676) 631[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(X4:naT,X3:naT)))* -> pp(ord_less_nat2(V:naT,X4:naT)).
(d0,A,r1561,rw198247) 625[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(X4:naT,X3:naT)))* -> pp(ord_less_eq_nat2(V:naT,X4:naT)).
(d0,A,r1543,rw195961) 619[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(V:naT,X4:naT)))* -> pp(ord_less_nat2(X3:naT,X4:naT)).
(d0,A,r1369,rw173863) 611[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(V:naT,X4:naT)))* -> pp(ord_less_eq_nat2(X3:naT,X4:naT)).
(d0,A,r1588,rw201676) 632[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> pp(ord_less_nat2(plus_plus_nat2(V:naT,X4:naT),plus_plus_nat2(X3:naT,X4:naT)))*.
(d0,A,r1561,rw198247) 626[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X4:naT),plus_plus_nat2(X3:naT,X4:naT)))*.
(d0,A,r1543,rw195961) 620[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X4:naT,X3:naT)))*.
(d0,A,r1369,rw173863) 612[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X4:naT,X3:naT)))*.
(d0,A,r1516,rw192532) 615[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(X3:naT,V:naT))* -> equal(X3:naT,V:naT).
(d0,A,r1525,rw193675) 616[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(X2:inT,U:inT))* -> equal(X2:inT,U:inT).
(d0,A,r1749,rw220374) 581[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* -> pp(ord_less_nat2(V:naT,X3:naT)) equal(V:naT,X3:naT).
(d0,A,r2433,rw306558) 587[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* -> equal(plus_plus_nat2(V:naT,skf93(V:naT,X3:naT)),X3:naT)**.
(d0,A,r2174,rw273924) 584[0:Inp] || pp(ord_less_eq_nat2(V:naT,X3:naT))* -> equal(plus_plus_nat2(V:naT,skf92(V:naT,X3:naT)),X3:naT)**.
(d0,A,r1887,rw237762) 583[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* -> equal(plus_plus_nat2(V:naT,skf91(V:naT,X3:naT)),X3:naT)**.
(d0,A,r1512,rw190512) 603[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* -> equal(plus_plus_nat2(V:naT,skf168(X3:naT,V:naT)),X3:naT)**.
(d0,A,r1172,rw147672) 580[0:Inp] || pp(dvd_dvd_nat2(V:naT,X3:naT))* -> equal(times_times_nat2(V:naT,skf84(V:naT,X3:naT)),X3:naT)**.
(d0,A,r1758,rw221508) 582[0:Inp] || pp(ord_less_eq_int2(U:inT,X2:inT))* -> pp(ord_less_int2(U:inT,X2:inT)) equal(U:inT,X2:inT).
(d0,A,r1000,rw126000) 974[0:Rew:579.0,383.0] ||  -> equal(aa_nat_int(aTP_Lamm_ad_2(U:inT,X2:inT),V:naT),plus_plus_int2(U:inT,times_times_int2(semiri501196819t_int1(V:naT),X2:inT)))**.
(d0,A,r1000,rw126000) 971[0:Rew:577.0,382.0] ||  -> equal(aa_nat_Code_integer(aTP_Lamm_ac_2(Z:code_integer,X1:code_integer),V:naT),plus_p715165435teger2(Z:code_integer,times_1419655522nteger(semiri1360655138teger1(V:naT),X1:code_integer)))**.
(d0,A,r1266,rw158250) 469[0:Inp] ||  -> equal(plus_plus_literal2(plus_plus_literal2(X11:literaL,X12:literaL),X25:literaL),plus_plus_literal2(X11:literaL,plus_plus_literal2(X12:literaL,X25:literaL)))**.
(d0,A,r1101,rw137625) 444[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer))* -> equal(Z:code_integer,X14:code_integer).
(d0,A,r1078,rw134750) 438[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(Z:code_integer,X14:code_integer))* -> equal(X1:code_integer,X14:code_integer).
(d0,A,r3304,rw413000) 561[0:Inp] || equal(Z:code_integer,X1:code_integer) -> equal(times_1419655522nteger(Z:code_integer,X14:code_integer),times_1419655522nteger(X1:code_integer,X14:code_integer))*.
(d0,A,r2929,rw366125) 544[0:Inp] || equal(Z:code_integer,X1:code_integer) -> equal(times_1419655522nteger(X14:code_integer,Z:code_integer),times_1419655522nteger(X14:code_integer,X1:code_integer))*.
(d0,A,r1101,rw137625) 445[0:Inp] || equal(Z:code_integer,X1:code_integer) -> equal(plus_p715165435teger2(Z:code_integer,X14:code_integer),plus_p715165435teger2(X1:code_integer,X14:code_integer))*.
(d0,A,r1078,rw134750) 439[0:Inp] || equal(Z:code_integer,X1:code_integer) -> equal(plus_p715165435teger2(X14:code_integer,Z:code_integer),plus_p715165435teger2(X14:code_integer,X1:code_integer))*.
(d0,A,r1127,rw140875) 448[0:Inp] ||  -> equal(plus_p715165435teger2(Z:code_integer,plus_p715165435teger2(X1:code_integer,X14:code_integer)),plus_p715165435teger2(X1:code_integer,plus_p715165435teger2(Z:code_integer,X14:code_integer)))*.
(d0,A,r1186,rw148250) 454[0:Inp] ||  -> equal(plus_p715165435teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),X14:code_integer),plus_p715165435teger2(Z:code_integer,plus_p715165435teger2(X1:code_integer,X14:code_integer)))**.
(d0,A,r2956,rw369500) 549[0:Inp] ||  -> equal(minus_1582103350nteger(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(Z:code_integer,X14:code_integer)),minus_1582103350nteger(X1:code_integer,X14:code_integer))**.
(d0,A,r1096,rw137000) 442[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(X13:inT,X2:inT))* -> equal(U:inT,X13:inT).
(d0,A,r1074,rw134250) 436[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(U:inT,X13:inT))* -> equal(X2:inT,X13:inT).
(d0,A,r3309,rw413625) 563[0:Inp] || equal(U:inT,X2:inT) -> equal(times_times_int2(U:inT,X13:inT),times_times_int2(X2:inT,X13:inT))*.
(d0,A,r2933,rw366625) 546[0:Inp] || equal(U:inT,X2:inT) -> equal(times_times_int2(X13:inT,U:inT),times_times_int2(X13:inT,X2:inT))*.
(d0,A,r1096,rw137000) 443[0:Inp] || equal(U:inT,X2:inT) -> equal(plus_plus_int2(U:inT,X13:inT),plus_plus_int2(X2:inT,X13:inT))*.
(d0,A,r1074,rw134250) 437[0:Inp] || equal(U:inT,X2:inT) -> equal(plus_plus_int2(X13:inT,U:inT),plus_plus_int2(X13:inT,X2:inT))*.
(d0,A,r1123,rw140375) 447[0:Inp] ||  -> equal(plus_plus_int2(U:inT,plus_plus_int2(X2:inT,X13:inT)),plus_plus_int2(X2:inT,plus_plus_int2(U:inT,X13:inT)))*.
(d0,A,r1181,rw147625) 453[0:Inp] ||  -> equal(plus_plus_int2(plus_plus_int2(U:inT,X2:inT),X13:inT),plus_plus_int2(U:inT,plus_plus_int2(X2:inT,X13:inT)))**.
(d0,A,r2960,rw370000) 550[0:Inp] ||  -> equal(minus_minus_int2(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(U:inT,X13:inT)),minus_minus_int2(X2:inT,X13:inT))**.
(d0,A,r1092,rw136500) 440[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(X4:naT,X3:naT))* -> equal(V:naT,X4:naT).
(d0,A,r1069,rw133625) 434[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(V:naT,X4:naT))* -> equal(X3:naT,X4:naT).
(d0,A,r3313,rw414125) 565[0:Inp] || equal(V:naT,X3:naT) -> equal(times_times_nat2(V:naT,X4:naT),times_times_nat2(X3:naT,X4:naT))*.
(d0,A,r2938,rw367250) 548[0:Inp] || equal(V:naT,X3:naT) -> equal(times_times_nat2(X4:naT,V:naT),times_times_nat2(X4:naT,X3:naT))*.
(d0,A,r1092,rw136500) 441[0:Inp] || equal(V:naT,X3:naT) -> equal(plus_plus_nat2(V:naT,X4:naT),plus_plus_nat2(X3:naT,X4:naT))*.
(d0,A,r1069,rw133625) 435[0:Inp] || equal(V:naT,X3:naT) -> equal(plus_plus_nat2(X4:naT,V:naT),plus_plus_nat2(X4:naT,X3:naT))*.
(d0,A,r1119,rw139875) 446[0:Inp] ||  -> equal(plus_plus_nat2(V:naT,plus_plus_nat2(X3:naT,X4:naT)),plus_plus_nat2(X3:naT,plus_plus_nat2(V:naT,X4:naT)))*.
(d0,A,r3434,rw429250) 566[0:Inp] ||  -> equal(times_times_nat2(times_times_nat2(V:naT,X3:naT),X4:naT),times_times_nat2(V:naT,times_times_nat2(X3:naT,X4:naT)))**.
(d0,A,r1177,rw147125) 452[0:Inp] ||  -> equal(plus_plus_nat2(plus_plus_nat2(V:naT,X3:naT),X4:naT),plus_plus_nat2(V:naT,plus_plus_nat2(X3:naT,X4:naT)))**.
(d0,A,r1000,rw125000) 973[0:Rew:972.0,384.0] ||  -> equal(aa_nat_nat(aTP_Lamm_ae_2(V:naT,X3:naT),X4:naT),plus_plus_nat2(V:naT,times_times_nat2(X4:naT,X3:naT)))**.
(d0,A,r2965,rw370625) 551[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(V:naT,X4:naT)),minus_minus_nat2(X3:naT,X4:naT))**.
(d0,A,r2996,rw374500) 552[0:Inp] ||  -> pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X3:naT,V:naT))* equal(X3:naT,V:naT).
(d0,A,r3000,rw375000) 553[0:Inp] ||  -> pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_int2(X2:inT,U:inT))* equal(X2:inT,U:inT).
(d0,A,r3595,rw449375) 579[0:Inp] ||  -> equal(aTP_Lamm_ad_3(U:inT,X2:inT,V:naT),plus_plus_int2(U:inT,times_times_int2(semiri501196819t_int1(V:naT),X2:inT)))**.
(d0,A,r3586,rw448250) 577[0:Inp] ||  -> equal(aTP_Lamm_ac_3(Z:code_integer,X1:code_integer,V:naT),plus_p715165435teger2(Z:code_integer,times_1419655522nteger(semiri1360655138teger1(V:naT),X1:code_integer)))**.
(d0,A,r1000,rw124000) 972[0:Rew:940.0,578.0] ||  -> equal(aTP_Lamm_ae_3(V:naT,X3:naT,X4:naT),plus_plus_nat2(V:naT,times_times_nat2(X4:naT,X3:naT)))**.
(d0,A,r2156,rw245784) 874[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int))* pp(ord_less_eq_int2(X2:inT,zero_zero_int))* equal(plus_plus_int2(X2:inT,U:inT),zero_zero_int)** -> equal(X2:inT,zero_zero_int).
(d0,A,r2156,rw245784) 875[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int))* pp(ord_less_eq_int2(X2:inT,zero_zero_int))* equal(plus_plus_int2(X2:inT,U:inT),zero_zero_int)** -> equal(U:inT,zero_zero_int).
(d0,A,r2129,rw242706) 868[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT))* pp(ord_less_eq_int2(zero_zero_int,X2:inT))* equal(plus_plus_int2(X2:inT,U:inT),zero_zero_int)** -> equal(X2:inT,zero_zero_int).
(d0,A,r2129,rw242706) 869[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT))* pp(ord_less_eq_int2(zero_zero_int,X2:inT))* equal(plus_plus_int2(X2:inT,U:inT),zero_zero_int)** -> equal(U:inT,zero_zero_int).
(d0,A,r2147,rw244758) 870[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger))* pp(ord_le1442264292teger2(X1:code_integer,zero_z413810534nteger))* equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger)** -> equal(X1:code_integer,zero_z413810534nteger).
(d0,A,r2147,rw244758) 871[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger))* pp(ord_le1442264292teger2(X1:code_integer,zero_z413810534nteger))* equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger)** -> equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r2120,rw241680) 864[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer))* pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer))* equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger)** -> equal(X1:code_integer,zero_z413810534nteger).
(d0,A,r2120,rw241680) 865[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer))* pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer))* equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger)** -> equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r2893,rw326909) 854[0:Inp] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,zero_zero_nat),groups1456475753ntegeR(comp_n1752466914er_nat(Y:fun_nat_Code_integer,suC),set_or562006527an_nat(zero_zero_nat,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2866,rw323858) 851[0:Inp] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,zero_zero_nat),groups1456475753ntegeR(comp_n1752466914er_nat(Y:fun_nat_Code_integer,suC),set_or601162459st_nat(zero_zero_nat,V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2889,rw326457) 853[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(comp_nat_int_nat(X:fun_nat_int,suC),set_or562006527an_nat(zero_zero_nat,V:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2862,rw323406) 850[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(comp_nat_int_nat(X:fun_nat_int,suC),set_or601162459st_nat(zero_zero_nat,V:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2884,rw325892) 852[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(comp_nat_nat_nat(W:fun_nat_nat,suC),set_or562006527an_nat(zero_zero_nat,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2857,rw322841) 849[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(comp_nat_nat_nat(W:fun_nat_nat,suC),set_or601162459st_nat(zero_zero_nat,V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(zero_zero_nat,suc1(V:naT))))**.
(d0,A,r2598,rw285780) 755[0:Inp] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,zero_zero_nat),groups1456475753ntegeR(aTP_Lamm_ab(Y:fun_nat_Code_integer),set_ord_atMost_nat(V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_ord_atMost_nat(suc1(V:naT))))**.
(d0,A,r2594,rw285340) 754[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(aTP_Lamm_aa(X:fun_nat_int),set_ord_atMost_nat(V:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(suc1(V:naT))))**.
(d0,A,r2589,rw284790) 753[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(aTP_Lamm_a(W:fun_nat_nat),set_ord_atMost_nat(V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(suc1(V:naT))))**.
(d0,A,r2705,rw294845) 718[0:Inp] ||  -> equal(plus_p715165435teger2(aa_nat_Code_integer(Y:fun_nat_Code_integer,zero_zero_nat),groups1456475753ntegeR(aTP_Lamm_ab(Y:fun_nat_Code_integer),set_ord_lessThan_nat(V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_ord_atMost_nat(V:naT)))**.
(d0,A,r2701,rw294409) 717[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(aTP_Lamm_aa(X:fun_nat_int),set_ord_lessThan_nat(V:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(V:naT)))**.
(d0,A,r2697,rw293973) 716[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(aTP_Lamm_a(W:fun_nat_nat),set_ord_lessThan_nat(V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(V:naT)))**.
(d0,A,r2835,rw306180) 698[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(X3:naT,suc1(V:naT))),zero_zero_int)**.
(d0,A,r2831,rw305748) 697[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or562006527an_nat(X3:naT,suc1(V:naT))),zero_z413810534nteger)**.
(d0,A,r2826,rw305208) 696[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(X3:naT,suc1(V:naT))),zero_zero_nat)**.
(d0,A,r2540,rw271780) 980[0:MRR:752.0,189.0] pp(X8:booL) || pp(ord_less_eq_bool2(X8:booL,X9:booL))* -> pp(ord_less_eq_bool2(X27:booL,X9:booL))*.
(d0,A,r2853,rw305271) 590[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(X3:naT,V:naT)),zero_zero_int)**.
(d0,A,r2849,rw304843) 589[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups1456475753ntegeR(Y:fun_nat_Code_integer,set_or601162459st_nat(X3:naT,V:naT)),zero_z413810534nteger)**.
(d0,A,r2844,rw304308) 588[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> equal(groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(X3:naT,V:naT)),zero_zero_nat)**.
(d0,A,r2656,rw281536) 975[0:MRR:687.2,222.0] || pp(ord_less_eq_bool2(X8:booL,X9:booL))* -> pp(X9:booL) pp(ord_less_eq_bool2(X8:booL,X27:booL))*.
(d0,A,r3304,rw350224) 560[0:Inp] || equal(Z:code_integer,zero_z413810534nteger) -> equal(times_1419655522nteger(X1:code_integer,Z:code_integer),times_1419655522nteger(X14:code_integer,Z:code_integer))*.
(d0,A,r2929,rw310474) 543[0:Inp] || equal(Z:code_integer,zero_z413810534nteger) -> equal(times_1419655522nteger(Z:code_integer,X1:code_integer),times_1419655522nteger(Z:code_integer,X14:code_integer))*.
(d0,A,r3309,rw350754) 562[0:Inp] || equal(U:inT,zero_zero_int) -> equal(times_times_int2(X2:inT,U:inT),times_times_int2(X13:inT,U:inT))*.
(d0,A,r2933,rw310898) 545[0:Inp] || equal(U:inT,zero_zero_int) -> equal(times_times_int2(U:inT,X2:inT),times_times_int2(U:inT,X13:inT))*.
(d0,A,r1378,rw146068) 981[0:MRR:786.0,13.0] || pp(ord_less_nat2(V:naT,X3:naT)) -> pp(ord_less_nat2(V:naT,plus_plus_nat2(X4:naT,X3:naT)))*.
(d0,A,r1378,rw146068) 982[0:MRR:798.0,13.0] || pp(ord_less_eq_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(V:naT,plus_plus_nat2(X4:naT,X3:naT)))*.
(d0,A,r1378,rw146068) 983[0:MRR:801.0,13.0] || pp(ord_less_eq_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(V:naT,plus_plus_nat2(X3:naT,X4:naT)))*.
(d0,A,r3313,rw351178) 564[0:Inp] || equal(V:naT,zero_zero_nat) -> equal(times_times_nat2(X3:naT,V:naT),times_times_nat2(X4:naT,V:naT))*.
(d0,A,r2938,rw311428) 547[0:Inp] || equal(V:naT,zero_zero_nat) -> equal(times_times_nat2(V:naT,X3:naT),times_times_nat2(V:naT,X4:naT))*.
(d0,A,r2947,rw309435) 424[0:Inp] || member_bool(X8:booL,set_or842601420t_bool(X9:booL,X27:booL))* -> pp(ord_less_eq_bool2(X9:booL,X8:booL)).
(d0,A,r2947,rw309435) 425[0:Inp] || member_bool(X8:booL,set_or842601420t_bool(X9:booL,X27:booL))* -> pp(ord_less_eq_bool2(X8:booL,X27:booL)).
(d0,A,r2951,rw309855) 426[0:Inp] || member_int(U:inT,set_or1238436151st_int(X2:inT,X13:inT))* -> pp(ord_less_eq_int2(X2:inT,U:inT)).
(d0,A,r2951,rw309855) 427[0:Inp] || member_int(U:inT,set_or1238436151st_int(X2:inT,X13:inT))* -> pp(ord_less_eq_int2(U:inT,X13:inT)).
(d0,A,r2942,rw308910) 422[0:Inp] || member_nat(V:naT,set_or601162459st_nat(X3:naT,X4:naT))* -> pp(ord_less_eq_nat2(X3:naT,V:naT)).
(d0,A,r2942,rw308910) 423[0:Inp] || member_nat(V:naT,set_or601162459st_nat(X3:naT,X4:naT))* -> pp(ord_less_eq_nat2(V:naT,X4:naT)).
(d0,A,r2174,rw228270) 390[0:Inp] || equal(V:naT,plus_plus_nat2(X3:naT,X4:naT))* -> pp(ord_less_eq_nat2(X3:naT,V:naT))*.
(d0,A,r1172,rw123060) 385[0:Inp] || equal(V:naT,times_times_nat2(X3:naT,X4:naT))* -> pp(dvd_dvd_nat2(X3:naT,V:naT))*.
(d0,A,r3345,rw344535) 297[0:Inp] ||  -> pp(ord_less_eq_bool2(X8:booL,X9:booL))* SkP1(X27:booL,X9:booL,X8:booL)*.
(d0,A,r3345,rw344535) 298[0:Inp] ||  -> pp(ord_less_eq_bool2(X8:booL,X9:booL))* SkP1(X9:booL,X8:booL,X27:booL)*.
(d0,A,r3349,rw344947) 299[0:Inp] ||  -> pp(ord_less_eq_int2(U:inT,X2:inT))* SkP2(X13:inT,X2:inT,U:inT)*.
(d0,A,r3349,rw344947) 300[0:Inp] ||  -> pp(ord_less_eq_int2(U:inT,X2:inT))* SkP2(X2:inT,U:inT,X13:inT)*.
(d0,A,r3340,rw344020) 295[0:Inp] ||  -> pp(ord_less_eq_nat2(V:naT,X3:naT))* SkP0(X4:naT,X3:naT,V:naT)*.
(d0,A,r3340,rw344020) 296[0:Inp] ||  -> pp(ord_less_eq_nat2(V:naT,X3:naT))* SkP0(X3:naT,V:naT,X4:naT)*.
(d0,A,r2250,rw207000) 810[0:Inp] || pp(ord_less_eq_nat2(V:naT,zero_zero_nat)) pp(ord_less_eq_nat2(X3:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X3:naT,V:naT),zero_zero_nat))*.
(d0,A,r2089,rw192188) 793[0:Inp] || pp(ord_less_int2(zero_zero_int,U:inT)) pp(ord_less_int2(zero_zero_int,X2:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r2075,rw190900) 790[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT)) pp(ord_less_eq_int2(zero_zero_int,X2:inT)) -> pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r1870,rw172040) 778[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT)) pp(ord_less_int2(zero_zero_int,X2:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r1856,rw170752) 775[0:Inp] || pp(ord_less_int2(zero_zero_int,U:inT)) pp(ord_less_eq_int2(zero_zero_int,X2:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r2254,rw207368) 811[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int)) pp(ord_less_eq_int2(X2:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X2:inT,U:inT),zero_zero_int))*.
(d0,A,r2102,rw193384) 796[0:Inp] || pp(ord_less_int2(U:inT,zero_zero_int)) pp(ord_less_int2(X2:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X2:inT,U:inT),zero_zero_int))*.
(d0,A,r1883,rw173236) 781[0:Inp] || pp(ord_less_int2(U:inT,zero_zero_int)) pp(ord_less_eq_int2(X2:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X2:inT,U:inT),zero_zero_int))*.
(d0,A,r1843,rw169556) 772[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int)) pp(ord_less_int2(X2:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X2:inT,U:inT),zero_zero_int))*.
(d0,A,r2080,rw191360) 791[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)) pp(ord_le1687847920teger2(zero_z413810534nteger,X1:code_integer)) -> pp(ord_le1687847920teger2(zero_z413810534nteger,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r2066,rw190072) 788[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)) pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer)) -> pp(ord_le1442264292teger2(zero_z413810534nteger,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r1861,rw171212) 776[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)) pp(ord_le1687847920teger2(zero_z413810534nteger,X1:code_integer)) -> pp(ord_le1687847920teger2(zero_z413810534nteger,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r1847,rw169924) 773[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)) pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer)) -> pp(ord_le1687847920teger2(zero_z413810534nteger,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r2245,rw206540) 809[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)) pp(ord_le1442264292teger2(X1:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r2093,rw192556) 794[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)) pp(ord_le1687847920teger2(X1:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r1874,rw172408) 779[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)) pp(ord_le1442264292teger2(X1:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r1834,rw168728) 770[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)) pp(ord_le1687847920teger2(X1:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r3568,rw324688) 769[0:Inp] || pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(V:naT,X3:naT)))* -> pp(ord_less_nat2(zero_zero_nat,V:naT)) pp(ord_less_nat2(zero_zero_nat,X3:naT)).
(d0,A,r2607,rw237237) 757[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),zero_zero_int))* -> pp(ord_less_int2(X2:inT,zero_zero_int)) pp(ord_less_int2(U:inT,zero_zero_int)).
(d0,A,r2603,rw236873) 756[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),zero_z413810534nteger))* -> pp(ord_le1687847920teger2(X1:code_integer,zero_z413810534nteger)) pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)).
(d0,A,r3389,rw294843) 572[0:Inp] || pp(aa_int_bool(aa_int_fun_int_bool(X40:fun_int_fun_int_bool,skf166(X40:fun_int_fun_int_bool)),skf167(X40:fun_int_fun_int_bool)))* -> SkP5(X40:fun_int_fun_int_bool).
(d0,A,r3389,rw294843) 571[0:Inp] SkP5(X40:fun_int_fun_int_bool) ||  -> pp(aa_int_bool(aa_int_fun_int_bool(X40:fun_int_fun_int_bool,skf164(X40:fun_int_fun_int_bool)),skf165(X40:fun_int_fun_int_bool)))*.
(d0,A,r1391,rw121017) 570[0:Inp] || pp(aa_bool_bool(aa_boo1142376798l_bool(X39:fun_bo1373903021l_bool,skf162(X39:fun_bo1373903021l_bool)),skf163(X39:fun_bo1373903021l_bool)))* -> SkP4(X39:fun_bo1373903021l_bool).
(d0,A,r1391,rw121017) 569[0:Inp] SkP4(X39:fun_bo1373903021l_bool) ||  -> pp(aa_bool_bool(aa_boo1142376798l_bool(X39:fun_bo1373903021l_bool,skf160(X39:fun_bo1373903021l_bool)),skf161(X39:fun_bo1373903021l_bool)))*.
(d0,A,r1378,rw119886) 568[0:Inp] || pp(aa_nat_bool(aa_nat_fun_nat_bool(X38:fun_nat_fun_nat_bool,skf158(X38:fun_nat_fun_nat_bool)),skf159(X38:fun_nat_fun_nat_bool)))* -> SkP3(X38:fun_nat_fun_nat_bool).
(d0,A,r1378,rw119886) 567[0:Inp] SkP3(X38:fun_nat_fun_nat_bool) ||  -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X38:fun_nat_fun_nat_bool,skf156(X38:fun_nat_fun_nat_bool)),skf157(X38:fun_nat_fun_nat_bool)))*.
(d0,A,r1753,rw152511) 542[0:Inp] pp(X8:booL) pp(X9:booL) || pp(ord_less_bool2(X9:booL,X8:booL))* -> .
(d0,A,r1494,rw129978) 506[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X3:naT),X3:naT))* -> pp(ord_less_eq_nat2(V:naT,zero_zero_nat)).
(d0,A,r1481,rw128847) 500[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X3:naT),V:naT))* -> pp(ord_less_eq_nat2(X3:naT,zero_zero_nat)).
(d0,A,r1686,rw146682) 535[0:Inp] || pp(ord_less_nat2(zero_zero_nat,V:naT)) -> pp(ord_less_nat2(X3:naT,plus_plus_nat2(V:naT,X3:naT)))*.
(d0,A,r1637,rw142419) 529[0:Inp] || pp(ord_less_nat2(zero_zero_nat,V:naT)) -> pp(ord_less_nat2(X3:naT,plus_plus_nat2(X3:naT,V:naT)))*.
(d0,A,r1686,rw146682) 534[0:Inp] || pp(ord_less_nat2(V:naT,plus_plus_nat2(X3:naT,V:naT)))* -> pp(ord_less_nat2(zero_zero_nat,X3:naT)).
(d0,A,r1637,rw142419) 528[0:Inp] || pp(ord_less_nat2(V:naT,plus_plus_nat2(V:naT,X3:naT)))* -> pp(ord_less_nat2(zero_zero_nat,X3:naT)).
(d0,A,r1494,rw129978) 507[0:Inp] || pp(ord_less_eq_nat2(V:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(V:naT,X3:naT),X3:naT))*.
(d0,A,r1481,rw128847) 501[0:Inp] || pp(ord_less_eq_nat2(V:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X3:naT,V:naT),X3:naT))*.
(d0,A,r1628,rw141636) 524[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),X2:inT))* -> pp(ord_less_int2(U:inT,zero_zero_int)).
(d0,A,r1606,rw139722) 518[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),U:inT))* -> pp(ord_less_int2(X2:inT,zero_zero_int)).
(d0,A,r1499,rw130413) 508[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(U:inT,X2:inT),X2:inT))* -> pp(ord_less_eq_int2(U:inT,zero_zero_int)).
(d0,A,r1485,rw129195) 502[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(U:inT,X2:inT),U:inT))* -> pp(ord_less_eq_int2(X2:inT,zero_zero_int)).
(d0,A,r1691,rw147117) 537[0:Inp] || pp(ord_less_int2(zero_zero_int,U:inT)) -> pp(ord_less_int2(X2:inT,plus_plus_int2(U:inT,X2:inT)))*.
(d0,A,r1642,rw142854) 531[0:Inp] || pp(ord_less_int2(zero_zero_int,U:inT)) -> pp(ord_less_int2(X2:inT,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r1445,rw125715) 491[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT)) -> pp(ord_less_eq_int2(X2:inT,plus_plus_int2(X2:inT,U:inT)))*.
(d0,A,r1423,rw123801) 481[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT)) -> pp(ord_less_eq_int2(X2:inT,plus_plus_int2(U:inT,X2:inT)))*.
(d0,A,r1691,rw147117) 536[0:Inp] || pp(ord_less_int2(U:inT,plus_plus_int2(X2:inT,U:inT)))* -> pp(ord_less_int2(zero_zero_int,X2:inT)).
(d0,A,r1642,rw142854) 530[0:Inp] || pp(ord_less_int2(U:inT,plus_plus_int2(U:inT,X2:inT)))* -> pp(ord_less_int2(zero_zero_int,X2:inT)).
(d0,A,r1445,rw125715) 490[0:Inp] || pp(ord_less_eq_int2(U:inT,plus_plus_int2(U:inT,X2:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,X2:inT)).
(d0,A,r1423,rw123801) 480[0:Inp] || pp(ord_less_eq_int2(U:inT,plus_plus_int2(X2:inT,U:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,X2:inT)).
(d0,A,r1628,rw141636) 525[0:Inp] || pp(ord_less_int2(U:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(U:inT,X2:inT),X2:inT))*.
(d0,A,r1606,rw139722) 519[0:Inp] || pp(ord_less_int2(U:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X2:inT,U:inT),X2:inT))*.
(d0,A,r1499,rw130413) 509[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(U:inT,X2:inT),X2:inT))*.
(d0,A,r1485,rw129195) 503[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X2:inT,U:inT),X2:inT))*.
(d0,A,r3537,rw307719) 574[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(U:inT,one_one_int),X2:inT))*.
(d0,A,r1619,rw140853) 520[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer))* -> pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)).
(d0,A,r1597,rw138939) 514[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),Z:code_integer))* -> pp(ord_le1687847920teger2(X1:code_integer,zero_z413810534nteger)).
(d0,A,r1490,rw129630) 504[0:Inp] || pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer))* -> pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)).
(d0,A,r1476,rw128412) 498[0:Inp] || pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),Z:code_integer))* -> pp(ord_le1442264292teger2(X1:code_integer,zero_z413810534nteger)).
(d0,A,r1682,rw146334) 533[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1687847920teger2(X1:code_integer,plus_p715165435teger2(Z:code_integer,X1:code_integer)))*.
(d0,A,r1633,rw142071) 527[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1687847920teger2(X1:code_integer,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r1436,rw124932) 487[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1442264292teger2(X1:code_integer,plus_p715165435teger2(X1:code_integer,Z:code_integer)))*.
(d0,A,r1414,rw123018) 477[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1442264292teger2(X1:code_integer,plus_p715165435teger2(Z:code_integer,X1:code_integer)))*.
(d0,A,r1682,rw146334) 532[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,plus_p715165435teger2(X1:code_integer,Z:code_integer)))* -> pp(ord_le1687847920teger2(zero_z413810534nteger,X1:code_integer)).
(d0,A,r1633,rw142071) 526[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,plus_p715165435teger2(Z:code_integer,X1:code_integer)))* -> pp(ord_le1687847920teger2(zero_z413810534nteger,X1:code_integer)).
(d0,A,r1436,rw124932) 486[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,plus_p715165435teger2(Z:code_integer,X1:code_integer)))* -> pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer)).
(d0,A,r1414,rw123018) 476[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,plus_p715165435teger2(X1:code_integer,Z:code_integer)))* -> pp(ord_le1442264292teger2(zero_z413810534nteger,X1:code_integer)).
(d0,A,r1619,rw140853) 521[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer))*.
(d0,A,r1597,rw138939) 515[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),X1:code_integer))*.
(d0,A,r1490,rw129630) 505[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer))*.
(d0,A,r1476,rw128412) 499[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(X1:code_integer,Z:code_integer),X1:code_integer))*.
(d0,A,r1655,rw142330) 417[0:Inp] || pp(aa_nat_bool(X21:fun_nat_bool,skf95(X21:fun_nat_bool)))* -> pp(aa_nat_bool(X21:fun_nat_bool,V:naT))*.
(d0,A,r1655,rw142330) 416[0:Inp] || pp(ord_less_nat2(V:naT,skf95(X21:fun_nat_bool)))* -> pp(aa_nat_bool(X21:fun_nat_bool,V:naT)).
(d0,A,r1664,rw143104) 387[0:Inp] || pp(ord_less_bool2(X8:booL,X9:booL)) pp(ord_less_eq_bool2(X9:booL,X8:booL))* -> .
(d0,A,r3528,rw303408) 433[0:Inp] pp(X8:booL) || pp(ord_less_eq_bool2(X8:booL,X9:booL))* -> pp(X9:booL).
(d0,A,r2996,rw257656) 429[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X3:naT,V:naT))* -> .
(d0,A,r1659,rw142674) 386[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) pp(ord_less_eq_nat2(X3:naT,V:naT))* -> .
(d0,A,r3510,rw301860) 432[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(suc1(V:naT),X3:naT))*.
(d0,A,r3000,rw258000) 430[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* pp(ord_less_int2(X2:inT,U:inT))* -> .
(d0,A,r1668,rw143448) 388[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) pp(ord_less_eq_int2(X2:inT,U:inT))* -> .
(d0,A,r2714,rw233404) 408[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),zero_zero_int)** -> equal(U:inT,uminus_uminus_int1(X2:inT)).
(d0,A,r2629,rw226094) 400[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),zero_zero_int)** -> equal(uminus_uminus_int1(U:inT),X2:inT).
(d0,A,r2714,rw233404) 407[0:Inp] || equal(U:inT,uminus_uminus_int1(X2:inT)) -> equal(plus_plus_int2(U:inT,X2:inT),zero_zero_int)**.
(d0,A,r2692,rw231512) 404[0:Inp] || equal(U:inT,uminus_uminus_int1(X2:inT)) -> equal(plus_plus_int2(X2:inT,U:inT),zero_zero_int)**.
(d0,A,r2710,rw233060) 406[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),zero_z413810534nteger)** -> equal(Z:code_integer,uminus636303014ntegeR(X1:code_integer)).
(d0,A,r2625,rw225750) 399[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),zero_z413810534nteger)** -> equal(uminus636303014ntegeR(Z:code_integer),X1:code_integer).
(d0,A,r2710,rw233060) 405[0:Inp] || equal(Z:code_integer,uminus636303014ntegeR(X1:code_integer)) -> equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),zero_z413810534nteger)**.
(d0,A,r2688,rw231168) 402[0:Inp] || equal(Z:code_integer,uminus636303014ntegeR(X1:code_integer)) -> equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),zero_z413810534nteger)**.
(d0,A,r2705,rw232630) 970[0:Rew:718.0,761.0] ||  -> equal(groups1456475753ntegeR(Y:fun_nat_Code_integer,set_ord_lessThan_nat(suc1(V:naT))),groups1456475753ntegeR(Y:fun_nat_Code_integer,set_ord_atMost_nat(V:naT)))**.
(d0,A,r2701,rw232286) 969[0:Rew:717.0,760.0] ||  -> equal(groups332228664at_int(X:fun_nat_int,set_ord_lessThan_nat(suc1(V:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(V:naT)))**.
(d0,A,r2697,rw231942) 968[0:Rew:716.0,759.0] ||  -> equal(groups1842438620at_nat(W:fun_nat_nat,set_ord_lessThan_nat(suc1(V:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(V:naT)))**.
(d0,A,r1615,rw137275) 352[0:Inp] ||  -> equal(suB(X7:nuM,X26:nuM),minus_minus_int2(numeral_numeral_int1(X7:nuM),numeral_numeral_int1(X26:nuM)))**.
(d0,A,r1753,rw149005) 356[0:Inp] || pp(ord_less_bool2(X8:booL,X9:booL))* -> pp(X9:booL) pp(X8:booL).
(d0,A,r1753,rw149005) 355[0:Inp] || pp(ord_less_bool2(X8:booL,X9:booL)) -> pp(ord_less_eq_bool2(X8:booL,X9:booL))*.
(d0,A,r1753,rw149005) 976[0:MRR:707.1,222.1] pp(X8:booL) ||  -> pp(X9:booL) pp(ord_less_bool2(X9:booL,X8:booL))*.
(d0,A,r1749,rw148665) 354[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT))* equal(V:naT,X3:naT) -> .
(d0,A,r1749,rw148665) 353[0:Inp] || pp(ord_less_nat2(V:naT,X3:naT)) -> pp(ord_less_eq_nat2(V:naT,X3:naT))*.
(d0,A,r984,rw83640) 319[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),V:naT)** -> equal(X3:naT,zero_zero_nat).
(d0,A,r944,rw80240) 313[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),X3:naT)** -> equal(V:naT,zero_zero_nat).
(d0,A,r984,rw83640) 320[0:Inp] || equal(V:naT,zero_zero_nat) -> equal(plus_plus_nat2(X3:naT,V:naT),X3:naT)**.
(d0,A,r944,rw80240) 314[0:Inp] || equal(V:naT,zero_zero_nat) -> equal(plus_plus_nat2(V:naT,X3:naT),X3:naT)**.
(d0,A,r2464,rw209440) 364[0:Inp] ||  -> equal(plus_plus_nat2(V:naT,suc1(X3:naT)),suc1(plus_plus_nat2(V:naT,X3:naT)))**.
(d0,A,r3036,rw258060) 373[0:Inp] ||  -> equal(plus_plus_nat2(suc1(V:naT),X3:naT),suc1(plus_plus_nat2(V:naT,X3:naT)))**.
(d0,A,r3403,rw289255) 380[0:Inp] ||  -> equal(minus_minus_nat2(suc1(V:naT),suc1(X3:naT)),minus_minus_nat2(V:naT,X3:naT))**.
(d0,A,r1758,rw149430) 358[0:Inp] || pp(ord_less_int2(U:inT,X2:inT))* equal(U:inT,X2:inT) -> .
(d0,A,r1758,rw149430) 357[0:Inp] || pp(ord_less_int2(U:inT,X2:inT)) -> pp(ord_less_eq_int2(U:inT,X2:inT))*.
(d0,A,r993,rw84405) 323[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),U:inT)** -> equal(X2:inT,zero_zero_int).
(d0,A,r953,rw81005) 317[0:Inp] || equal(plus_plus_int2(U:inT,X2:inT),X2:inT)** -> equal(U:inT,zero_zero_int).
(d0,A,r993,rw84405) 324[0:Inp] || equal(U:inT,zero_zero_int) -> equal(plus_plus_int2(X2:inT,U:inT),X2:inT)**.
(d0,A,r953,rw81005) 318[0:Inp] || equal(U:inT,zero_zero_int) -> equal(plus_plus_int2(U:inT,X2:inT),X2:inT)**.
(d0,A,r989,rw84065) 321[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),Z:code_integer)** -> equal(X1:code_integer,zero_z413810534nteger).
(d0,A,r949,rw80665) 315[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer)** -> equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r989,rw84065) 322[0:Inp] || equal(Z:code_integer,zero_z413810534nteger) -> equal(plus_p715165435teger2(X1:code_integer,Z:code_integer),X1:code_integer)**.
(d0,A,r949,rw80665) 316[0:Inp] || equal(Z:code_integer,zero_z413810534nteger) -> equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer)**.
(d0,A,r1000,rw85000) 954[0:Rew:306.0,226.0] ||  -> equal(aa_nat_Code_integer(aTP_Lamm_ab(Y:fun_nat_Code_integer),V:naT),aa_nat_Code_integer(Y:fun_nat_Code_integer,suc1(V:naT)))**.
(d0,A,r1000,rw85000) 956[0:Rew:308.0,225.0] ||  -> equal(aa_nat_int(aTP_Lamm_aa(X:fun_nat_int),V:naT),aa_nat_int(X:fun_nat_int,suc1(V:naT)))**.
(d0,A,r1000,rw85000) 955[0:Rew:307.0,224.0] ||  -> equal(aa_nat_nat(aTP_Lamm_a(W:fun_nat_nat),V:naT),aa_nat_nat(W:fun_nat_nat,suc1(V:naT)))**.
(d0,A,r1000,rw84000) 248[0:Inp] ||  -> equal(aa_literal_literal(plus_plus_literal1(X11:literaL),X12:literaL),plus_plus_literal2(X11:literaL,X12:literaL))**.
(d0,A,r1000,rw84000) 245[0:Inp] ||  -> equal(aa_Code_integer_bool(monoid_Code_integer(X10:fun_Co708814609nteger),Z:code_integer),monoid_Code_integer2(X10:fun_Co708814609nteger,Z:code_integer))**.
(d0,A,r1000,rw84000) 250[0:Inp] ||  -> equal(aa_Code_integer_bool(comm_m604335976nteger(X10:fun_Co708814609nteger),Z:code_integer),comm_m138292217teger2(X10:fun_Co708814609nteger,Z:code_integer))**.
(d0,A,r2299,rw193116) 267[0:Inp] ||  -> pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_eq_bool2(X9:booL,X8:booL))*.
(d0,A,r1664,rw139776) 262[0:Inp] ||  -> pp(ord_less_eq_bool2(X8:booL,X9:booL))* pp(ord_less_bool2(X9:booL,X8:booL)).
(d0,A,r1000,rw84000) 244[0:Inp] ||  -> equal(aa_bool_bool(ord_less_bool1(X8:booL),X9:booL),ord_less_bool2(X8:booL,X9:booL))**.
(d0,A,r1000,rw84000) 249[0:Inp] ||  -> equal(aa_bool_bool(ord_less_eq_bool1(X8:booL),X9:booL),ord_less_eq_bool2(X8:booL,X9:booL))**.
(d0,A,r1000,rw84000) 231[0:Inp] ||  -> equal(aa_nat_bool(monoid_nat(X6:fun_nat_fun_nat_nat),V:naT),monoid_nat2(X6:fun_nat_fun_nat_nat,V:naT))**.
(d0,A,r1000,rw84000) 233[0:Inp] ||  -> equal(aa_nat_bool(comm_monoid_nat(X6:fun_nat_fun_nat_nat),V:naT),comm_monoid_nat2(X6:fun_nat_fun_nat_nat,V:naT))**.
(d0,A,r1000,rw84000) 230[0:Inp] ||  -> equal(aa_int_bool(monoid_int(X5:fun_int_fun_int_int),U:inT),monoid_int2(X5:fun_int_fun_int_int,U:inT))**.
(d0,A,r1000,rw84000) 232[0:Inp] ||  -> equal(aa_int_bool(comm_monoid_int(X5:fun_int_fun_int_int),U:inT),comm_monoid_int2(X5:fun_int_fun_int_int,U:inT))**.
(d0,A,r2294,rw192696) 266[0:Inp] || equal(V:naT,X3:naT) -> pp(ord_less_eq_nat2(X3:naT,V:naT))*.
(d0,A,r2294,rw192696) 265[0:Inp] ||  -> pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_eq_nat2(X3:naT,V:naT))*.
(d0,A,r1659,rw139356) 261[0:Inp] ||  -> pp(ord_less_eq_nat2(V:naT,X3:naT))* pp(ord_less_nat2(X3:naT,V:naT)).
(d0,A,r1000,rw84000) 229[0:Inp] ||  -> equal(aa_nat_fun_nat_nat(aTP_Lamm_ae(V:naT),X3:naT),aTP_Lamm_ae_2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 235[0:Inp] ||  -> equal(aa_nat_bool(dvd_dvd_nat1(V:naT),X3:naT),dvd_dvd_nat2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 237[0:Inp] ||  -> equal(aa_nat_nat(plus_plus_nat1(V:naT),X3:naT),plus_plus_nat2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 239[0:Inp] ||  -> equal(aa_nat_nat(minus_minus_nat(V:naT),X3:naT),minus_minus_nat2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 241[0:Inp] ||  -> equal(aa_nat_nat(times_times_nat(V:naT),X3:naT),times_times_nat2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 243[0:Inp] ||  -> equal(aa_nat_bool(ord_less_nat1(V:naT),X3:naT),ord_less_nat2(V:naT,X3:naT))**.
(d0,A,r1000,rw84000) 247[0:Inp] ||  -> equal(aa_nat_bool(ord_less_eq_nat1(V:naT),X3:naT),ord_less_eq_nat2(V:naT,X3:naT))**.
(d0,A,r2303,rw193452) 270[0:Inp] || equal(U:inT,X2:inT) -> pp(ord_less_eq_int2(X2:inT,U:inT))*.
(d0,A,r2303,rw193452) 269[0:Inp] ||  -> pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_eq_int2(X2:inT,U:inT))*.
(d0,A,r1668,rw140112) 263[0:Inp] ||  -> pp(ord_less_eq_int2(U:inT,X2:inT))* pp(ord_less_int2(X2:inT,U:inT)).
(d0,A,r1360,rw114240) 256[0:Inp] ||  -> equal(plus_plus_int2(U:inT,uminus_uminus_int1(X2:inT)),minus_minus_int2(U:inT,X2:inT))**.
(d0,A,r1409,rw118356) 258[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int1(U:inT),X2:inT),minus_minus_int2(X2:inT,U:inT))**.
(d0,A,r1000,rw84000) 228[0:Inp] ||  -> equal(aa_int_fun_nat_int(aTP_Lamm_ad(U:inT),X2:inT),aTP_Lamm_ad_2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 234[0:Inp] ||  -> equal(aa_int_bool(dvd_dvd_int1(U:inT),X2:inT),dvd_dvd_int2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 236[0:Inp] ||  -> equal(aa_int_int(plus_plus_int1(U:inT),X2:inT),plus_plus_int2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 238[0:Inp] ||  -> equal(aa_int_int(minus_minus_int(U:inT),X2:inT),minus_minus_int2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 240[0:Inp] ||  -> equal(aa_int_int(times_times_int(U:inT),X2:inT),times_times_int2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 242[0:Inp] ||  -> equal(aa_int_bool(ord_less_int1(U:inT),X2:inT),ord_less_int2(U:inT,X2:inT))**.
(d0,A,r1000,rw84000) 246[0:Inp] ||  -> equal(aa_int_bool(ord_less_eq_int1(U:inT),X2:inT),ord_less_eq_int2(U:inT,X2:inT))**.
(d0,A,r1355,rw113820) 255[0:Inp] ||  -> equal(plus_p715165435teger2(Z:code_integer,uminus636303014ntegeR(X1:code_integer)),minus_1582103350nteger(Z:code_integer,X1:code_integer))**.
(d0,A,r1405,rw118020) 257[0:Inp] ||  -> equal(plus_p715165435teger2(uminus636303014ntegeR(Z:code_integer),X1:code_integer),minus_1582103350nteger(X1:code_integer,Z:code_integer))**.
(d0,A,r1000,rw84000) 227[0:Inp] ||  -> equal(aa_Cod2063310661nteger(aTP_Lamm_ac(Z:code_integer),X1:code_integer),aTP_Lamm_ac_2(Z:code_integer,X1:code_integer))**.
(d0,A,r1000,rw84000) 251[0:Inp] ||  -> equal(aa_Code_integer_bool(dvd_dvd_Code_integer(Z:code_integer),X1:code_integer),dvd_dv413397790teger2(Z:code_integer,X1:code_integer))**.
(d0,A,r1000,rw84000) 252[0:Inp] ||  -> equal(aa_Cod479057144nteger(plus_p715165434teger1(Z:code_integer),X1:code_integer),plus_p715165435teger2(Z:code_integer,X1:code_integer))**.
(d0,A,r1000,rw84000) 253[0:Inp] ||  -> equal(aa_Code_integer_bool(ord_le945590961nteger(Z:code_integer),X1:code_integer),ord_le1687847920teger2(Z:code_integer,X1:code_integer))**.
(d0,A,r1000,rw84000) 254[0:Inp] ||  -> equal(aa_Code_integer_bool(ord_le1426714813nteger(Z:code_integer),X1:code_integer),ord_le1442264292teger2(Z:code_integer,X1:code_integer))**.
(d0,A,r3573,rw300132) 306[0:Inp] ||  -> equal(aTP_Lamm_ab_2(Y:fun_nat_Code_integer,V:naT),aa_nat_Code_integer(Y:fun_nat_Code_integer,suc1(V:naT)))**.
(d0,A,r3582,rw300888) 308[0:Inp] ||  -> equal(aTP_Lamm_aa_2(X:fun_nat_int,V:naT),aa_nat_int(X:fun_nat_int,suc1(V:naT)))**.
(d0,A,r3577,rw300468) 307[0:Inp] ||  -> equal(aTP_Lamm_a_2(W:fun_nat_nat,V:naT),aa_nat_nat(W:fun_nat_nat,suc1(V:naT)))**.
(d0,A,r2755,rw228665) 219[0:Inp] ||  -> equal(times_times_nat2(V:naT,X3:naT),times_times_nat2(X3:naT,V:naT))*.
(d0,A,r1105,rw91715) 193[0:Inp] ||  -> equal(plus_plus_nat2(V:naT,X3:naT),plus_plus_nat2(X3:naT,V:naT))*.
(d0,A,r2397,rw198951) 218[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(V:naT,X3:naT),X3:naT),V:naT)**.
(d0,A,r1713,rw142179) 212[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(V:naT,X3:naT),V:naT),X3:naT)**.
(d0,A,r1110,rw92130) 194[0:Inp] ||  -> equal(plus_plus_int2(U:inT,X2:inT),plus_plus_int2(X2:inT,U:inT))*.
(d0,A,r1110,rw92130) 951[0:Rew:194.0,221.0] ||  -> equal(plus_plus_int2(U:inT,minus_minus_int2(X2:inT,U:inT)),X2:inT)**.
(d0,A,r2393,rw198619) 217[0:Inp] ||  -> equal(minus_minus_int2(plus_plus_int2(U:inT,X2:inT),X2:inT),U:inT)**.
(d0,A,r1709,rw141847) 211[0:Inp] ||  -> equal(minus_minus_int2(plus_plus_int2(U:inT,X2:inT),U:inT),X2:inT)**.
(d0,A,r1114,rw92462) 195[0:Inp] ||  -> equal(plus_p715165435teger2(Z:code_integer,X1:code_integer),plus_p715165435teger2(X1:code_integer,Z:code_integer))*.
(d0,A,r1114,rw92462) 950[0:Rew:195.0,220.0] ||  -> equal(plus_p715165435teger2(Z:code_integer,minus_1582103350nteger(X1:code_integer,Z:code_integer)),X1:code_integer)**.
(d0,A,r2388,rw198204) 216[0:Inp] ||  -> equal(minus_1582103350nteger(plus_p715165435teger2(Z:code_integer,X1:code_integer),X1:code_integer),Z:code_integer)**.
(d0,A,r1704,rw141432) 210[0:Inp] ||  -> equal(minus_1582103350nteger(plus_p715165435teger2(Z:code_integer,X1:code_integer),Z:code_integer),X1:code_integer)**.
(d0,A,r1114,rw83550) 948[0:Rew:195.0,861.0] ||  -> equal(times_1419655522nteger(numera1961560056ntegeR(bit0(onE)),groups1456475753ntegeR(semiri401560510ntegeR,set_or601162459st_nat(suc1(zero_zero_nat),V:naT))),times_1419655522nteger(semiri1360655138teger1(V:naT),plus_p715165435teger2(one_one_Code_integer,semiri1360655138teger1(V:naT))))*.
(d0,A,r1110,rw83250) 945[0:Rew:194.0,862.0] ||  -> equal(times_times_int2(numeral_numeral_int1(bit0(onE)),groups332228664at_int(semiri2019852685at_int,set_or601162459st_nat(suc1(zero_zero_nat),V:naT))),times_times_int2(semiri501196819t_int1(V:naT),plus_plus_int2(one_one_int,semiri501196819t_int1(V:naT))))*.
(d0,A,r1114,rw82436) 947[0:Rew:195.0,822.0] ||  -> equal(times_1419655522nteger(numera1961560056ntegeR(bit0(onE)),groups1456475753ntegeR(semiri401560510ntegeR,set_or601162459st_nat(zero_zero_nat,V:naT))),times_1419655522nteger(semiri1360655138teger1(V:naT),plus_p715165435teger2(one_one_Code_integer,semiri1360655138teger1(V:naT))))*.
(d0,A,r1110,rw82140) 944[0:Rew:194.0,823.0] ||  -> equal(times_times_int2(numeral_numeral_int1(bit0(onE)),groups332228664at_int(semiri2019852685at_int,set_or601162459st_nat(zero_zero_nat,V:naT))),times_times_int2(semiri501196819t_int1(V:naT),plus_plus_int2(one_one_int,semiri501196819t_int1(V:naT))))*.
(d0,A,r900,rw64800) 962[0:Rew:44.0,960.0] ||  -> equal(times_times_nat2(numeral_numeral_nat(bit0(onE)),groups1842438620at_nat(semiri1382578993at_nat,set_or601162459st_nat(suc1(zero_zero_nat),V:naT))),times_times_nat2(V:naT,suc1(V:naT)))*.
(d0,A,r900,rw63900) 961[0:Rew:44.0,959.0] ||  -> equal(times_times_nat2(numeral_numeral_nat(bit0(onE)),groups1842438620at_nat(semiri1382578993at_nat,set_or601162459st_nat(zero_zero_nat,V:naT))),times_times_nat2(V:naT,suc1(V:naT)))*.
(d0,A,r1610,rw111090) 941[0:Rew:17.0,573.1] || pp(ord_less_nat2(zero_zero_nat,V:naT)) -> equal(suc1(minus_minus_nat2(V:naT,suc1(zero_zero_nat))),V:naT)**.
(d0,A,r3568,rw242624) 575[0:Inp] || pp(ord_less_nat2(zero_zero_nat,V:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(V:naT,X3:naT)))*.
(d0,A,r3568,rw242624) 576[0:Inp] || pp(ord_less_nat2(zero_zero_nat,V:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(X3:naT,V:naT)))*.
(d0,A,r1695,rw115260) 538[0:Inp] || pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,Z:code_integer),zero_z413810534nteger))* -> pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)).
(d0,A,r1454,rw98872) 492[0:Inp] || pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,Z:code_integer),zero_z413810534nteger))* -> pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)).
(d0,A,r1530,rw104040) 510[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,plus_p715165435teger2(Z:code_integer,Z:code_integer)))* -> pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)).
(d0,A,r1427,rw97036) 482[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,plus_p715165435teger2(Z:code_integer,Z:code_integer)))* -> pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)).
(d0,A,r1530,rw104040) 511[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1687847920teger2(zero_z413810534nteger,plus_p715165435teger2(Z:code_integer,Z:code_integer)))*.
(d0,A,r1427,rw97036) 483[0:Inp] || pp(ord_le1442264292teger2(zero_z413810534nteger,Z:code_integer)) -> pp(ord_le1442264292teger2(zero_z413810534nteger,plus_p715165435teger2(Z:code_integer,Z:code_integer)))*.
(d0,A,r1695,rw115260) 539[0:Inp] || pp(ord_le1687847920teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1687847920teger2(plus_p715165435teger2(Z:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r1454,rw98872) 493[0:Inp] || pp(ord_le1442264292teger2(Z:code_integer,zero_z413810534nteger)) -> pp(ord_le1442264292teger2(plus_p715165435teger2(Z:code_integer,Z:code_integer),zero_z413810534nteger))*.
(d0,A,r1700,rw115600) 540[0:Inp] || pp(ord_less_int2(plus_plus_int2(U:inT,U:inT),zero_zero_int))* -> pp(ord_less_int2(U:inT,zero_zero_int)).
(d0,A,r1458,rw99144) 494[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(U:inT,U:inT),zero_zero_int))* -> pp(ord_less_eq_int2(U:inT,zero_zero_int)).
(d0,A,r1534,rw104312) 512[0:Inp] || pp(ord_less_int2(zero_zero_int,plus_plus_int2(U:inT,U:inT)))* -> pp(ord_less_int2(zero_zero_int,U:inT)).
(d0,A,r1431,rw97308) 484[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(U:inT,U:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,U:inT)).
(d0,A,r1534,rw104312) 513[0:Inp] || pp(ord_less_int2(zero_zero_int,U:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(U:inT,U:inT)))*.
(d0,A,r1431,rw97308) 485[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,U:inT)) -> pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(U:inT,U:inT)))*.
(d0,A,r1700,rw115600) 541[0:Inp] || pp(ord_less_int2(U:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(U:inT,U:inT),zero_zero_int))*.
(d0,A,r1458,rw99144) 495[0:Inp] || pp(ord_less_eq_int2(U:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(U:inT,U:inT),zero_zero_int))*.
(d0,A,r1038,rw68508) 337[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),zero_zero_nat)** -> equal(V:naT,zero_zero_nat).
(d0,A,r1038,rw68508) 338[0:Inp] || equal(plus_plus_nat2(V:naT,X3:naT),zero_zero_nat)** -> equal(X3:naT,zero_zero_nat).
(d0,A,r935,rw61710) 309[0:Inp] || equal(plus_p715165435teger2(Z:code_integer,Z:code_integer),zero_z413810534nteger)** -> equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r940,rw62040) 311[0:Inp] || equal(plus_plus_int2(U:inT,U:inT),zero_zero_int)** -> equal(U:inT,zero_zero_int).
(d0,A,r3515,rw224960) 222[0:Inp] pp(X8:booL) ||  -> pp(ord_less_eq_bool2(X9:booL,X8:booL))*.
(d0,A,r3559,rw227776) 223[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(V:naT,X3:naT),X3:naT))* -> .
(d0,A,r1601,rw102464) 965[0:MRR:516.1,78.0] || pp(ord_less_nat2(plus_plus_nat2(V:naT,X3:naT),V:naT))* -> .
(d0,A,r3515,rw221445) 189[0:Inp] ||  -> pp(X8:booL) pp(ord_less_eq_bool2(X8:booL,X9:booL))*.
(d0,A,r1378,rw86814) 963[0:MRR:479.0,13.0] ||  -> pp(ord_less_eq_nat2(V:naT,plus_plus_nat2(X3:naT,V:naT)))*.
(d0,A,r1378,rw86814) 964[0:MRR:489.0,13.0] ||  -> pp(ord_less_eq_nat2(V:naT,plus_plus_nat2(V:naT,X3:naT)))*.
(d0,A,r1512,rw71064) 351[0:Inp] || pp(ord_less_nat2(zero_zero_nat,V:naT))* equal(V:naT,zero_zero_nat) -> .
(d0,A,r1503,rw69138) 260[0:Inp] || equal(V:naT,zero_zero_nat) -> pp(ord_less_eq_nat2(V:naT,zero_zero_nat))*.
(d0,A,r1503,rw69138) 259[0:Inp] || pp(ord_less_eq_nat2(V:naT,zero_zero_nat))* -> equal(V:naT,zero_zero_nat).
(d0,A,r1145,rw51525) 196[0:Inp] || equal(zero_zero_a,X15:a)* -> equal(X15:a,zero_zero_a).
(d0,A,r1163,rw52335) 204[0:Inp] || equal(zero_zero_literal,X11:literaL)* -> equal(X11:literaL,zero_zero_literal).
(d0,A,r1154,rw51930) 200[0:Inp] || equal(zero_z413810534nteger,Z:code_integer)* -> equal(Z:code_integer,zero_z413810534nteger).
(d0,A,r1150,rw51750) 198[0:Inp] || equal(zero_zero_nat,V:naT)* -> equal(V:naT,zero_zero_nat).
(d0,A,r1512,rw68040) 209[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,V:naT))* equal(V:naT,zero_zero_nat).
(d0,A,r1159,rw52155) 202[0:Inp] || equal(zero_zero_int,U:inT)* -> equal(U:inT,zero_zero_int).
(d0,A,r3389,rw149116) 188[0:Inp] ||  -> pp(ord_less_eq_int2(skf166(X40:fun_int_fun_int_bool),skf167(X40:fun_int_fun_int_bool)))*.
(d0,A,r1391,rw61204) 187[0:Inp] ||  -> pp(ord_less_eq_bool2(skf162(X39:fun_bo1373903021l_bool),skf163(X39:fun_bo1373903021l_bool)))*.
(d0,A,r1378,rw60632) 186[0:Inp] ||  -> pp(ord_less_eq_nat2(skf158(X38:fun_nat_fun_nat_bool),skf159(X38:fun_nat_fun_nat_bool)))*.
(d0,A,r1391,rw61204) 163[0:Inp] ||  -> pp(ord_less_eq_bool2(skf118(X37:fun_bool_int),skf119(X37:fun_bool_int)))*.
(d0,A,r1391,rw61204) 172[0:Inp] ||  -> pp(ord_less_eq_bool2(skf136(X37:fun_bool_int),skf137(X37:fun_bool_int)))*.
(d0,A,r1391,rw61204) 162[0:Inp] ||  -> pp(ord_less_eq_bool2(skf116(X35:fun_bool_bool),skf117(X35:fun_bool_bool)))*.
(d0,A,r1391,rw61204) 171[0:Inp] ||  -> pp(ord_less_eq_bool2(skf134(X35:fun_bool_bool),skf135(X35:fun_bool_bool)))*.
(d0,A,r1391,rw61204) 161[0:Inp] ||  -> pp(ord_less_eq_bool2(skf114(X33:fun_bool_nat),skf115(X33:fun_bool_nat)))*.
(d0,A,r1391,rw61204) 170[0:Inp] ||  -> pp(ord_less_eq_bool2(skf132(X33:fun_bool_nat),skf133(X33:fun_bool_nat)))*.
(d0,A,r3255,rw143220) 175[0:Inp] ||  -> pp(ord_less_eq_int2(skf142(X32:fun_int_int),skf143(X32:fun_int_int)))*.
(d0,A,r3215,rw141460) 166[0:Inp] ||  -> pp(ord_less_eq_int2(skf124(X32:fun_int_int),skf125(X32:fun_int_int)))*.
(d0,A,r1668,rw73392) 157[0:Inp] ||  -> pp(ord_less_int2(skf106(X32:fun_int_int),skf107(X32:fun_int_int)))*.
(d0,A,r1668,rw73392) 181[0:Inp] ||  -> pp(ord_less_int2(skf154(X32:fun_int_int),skf155(X32:fun_int_int)))*.
(d0,A,r3246,rw142824) 173[0:Inp] ||  -> pp(ord_less_eq_int2(skf138(X31:fun_int_nat),skf139(X31:fun_int_nat)))*.
(d0,A,r3206,rw141064) 164[0:Inp] ||  -> pp(ord_less_eq_int2(skf120(X31:fun_int_nat),skf121(X31:fun_int_nat)))*.
(d0,A,r1668,rw73392) 153[0:Inp] ||  -> pp(ord_less_int2(skf98(X31:fun_int_nat),skf99(X31:fun_int_nat)))*.
(d0,A,r1668,rw73392) 177[0:Inp] ||  -> pp(ord_less_int2(skf146(X31:fun_int_nat),skf147(X31:fun_int_nat)))*.
(d0,A,r1239,rw54516) 144[0:Inp] ||  -> equal(image_int_int(plus_plus_int1(zero_zero_int),X24:set_int),X24:set_int)**.
(d0,A,r1235,rw54340) 143[0:Inp] ||  -> equal(image_1151633089nteger(plus_p715165434teger1(zero_z413810534nteger),X23:set_Code_integer),X23:set_Code_integer)**.
(d0,A,r1230,rw54120) 142[0:Inp] ||  -> equal(image_nat_nat(plus_plus_nat1(zero_zero_nat),X22:set_nat),X22:set_nat)**.
(d0,A,r1512,rw66528) 154[0:Inp] ||  -> pp(ord_less_nat2(skf100(X21:fun_nat_bool),skf101(X21:fun_nat_bool)))*.
(d0,A,r1512,rw66528) 178[0:Inp] ||  -> pp(ord_less_nat2(skf148(X21:fun_nat_bool),skf149(X21:fun_nat_bool)))*.
(d0,A,r1378,rw60632) 159[0:Inp] ||  -> pp(ord_less_eq_nat2(skf110(X21:fun_nat_bool),skf111(X21:fun_nat_bool)))*.
(d0,A,r1378,rw60632) 168[0:Inp] ||  -> pp(ord_less_eq_nat2(skf128(X21:fun_nat_bool),skf129(X21:fun_nat_bool)))*.
(d0,A,r3251,rw143044) 174[0:Inp] ||  -> pp(ord_less_eq_int2(skf140(X20:fun_int_bool),skf141(X20:fun_int_bool)))*.
(d0,A,r3211,rw141284) 165[0:Inp] ||  -> pp(ord_less_eq_int2(skf122(X20:fun_int_bool),skf123(X20:fun_int_bool)))*.
(d0,A,r1668,rw73392) 155[0:Inp] ||  -> pp(ord_less_int2(skf102(X20:fun_int_bool),skf103(X20:fun_int_bool)))*.
(d0,A,r1668,rw73392) 179[0:Inp] ||  -> pp(ord_less_int2(skf150(X20:fun_int_bool),skf151(X20:fun_int_bool)))*.
(d0,A,r1000,rw44000) 134[0:Inp] ||  -> equal(aa_lit1494493019iteral(plus_plus_literal,X11:literaL),plus_plus_literal1(X11:literaL))**.
(d0,A,r1000,rw44000) 192[0:Inp] ||  -> equal(X8:booL,fFalsE)* equal(X8:booL,fTruE).
(d0,A,r1000,rw44000) 130[0:Inp] ||  -> equal(aa_boo1142376798l_bool(ord_less_bool,X8:booL),ord_less_bool1(X8:booL))**.
(d0,A,r1000,rw44000) 137[0:Inp] ||  -> equal(aa_boo1142376798l_bool(ord_less_eq_bool,X8:booL),ord_less_eq_bool1(X8:booL))**.
(d0,A,r1000,rw44000) 138[0:Inp] ||  -> equal(aa_bool_int(zero_n1994027371ol_int,X8:booL),zero_n988859829l_int1(X8:booL))**.
(d0,A,r1000,rw44000) 139[0:Inp] ||  -> equal(aa_bool_nat(zero_n1356753679ol_nat,X8:booL),zero_n1672634641l_nat1(X8:booL))**.
(d0,A,r3519,rw154836) 190[0:Inp] ||  -> equal(plus_plus_num(X7:nuM,onE),inC(X7:nuM))**.
(d0,A,r1000,rw44000) 129[0:Inp] ||  -> equal(aa_num_int(numeral_numeral_int,X7:nuM),numeral_numeral_int1(X7:nuM))**.
(d0,A,r1887,rw83028) 147[0:Inp] || equal(skf91(V:naT,X3:naT),zero_zero_nat)** -> .
(d0,A,r1512,rw66528) 191[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,skf168(V:naT,X3:naT)))*.
(d0,A,r1000,rw44000) 140[0:Inp] ||  -> equal(aa_Cod1485984722nteger(plus_p2058578406nteger,Z:code_integer),plus_p715165434teger1(Z:code_integer))**.
(d0,A,r1512,rw66528) 156[0:Inp] ||  -> pp(ord_less_nat2(skf104(X:fun_nat_int),skf105(X:fun_nat_int)))*.
(d0,A,r1512,rw66528) 180[0:Inp] ||  -> pp(ord_less_nat2(skf152(X:fun_nat_int),skf153(X:fun_nat_int)))*.
(d0,A,r1378,rw60632) 160[0:Inp] ||  -> pp(ord_less_eq_nat2(skf112(X:fun_nat_int),skf113(X:fun_nat_int)))*.
(d0,A,r1378,rw60632) 169[0:Inp] ||  -> pp(ord_less_eq_nat2(skf130(X:fun_nat_int),skf131(X:fun_nat_int)))*.
(d0,A,r1512,rw66528) 152[0:Inp] ||  -> pp(ord_less_nat2(skf96(W:fun_nat_nat),skf97(W:fun_nat_nat)))*.
(d0,A,r1512,rw66528) 176[0:Inp] ||  -> pp(ord_less_nat2(skf144(W:fun_nat_nat),skf145(W:fun_nat_nat)))*.
(d0,A,r1378,rw60632) 158[0:Inp] ||  -> pp(ord_less_eq_nat2(skf108(W:fun_nat_nat),skf109(W:fun_nat_nat)))*.
(d0,A,r1378,rw60632) 167[0:Inp] ||  -> pp(ord_less_eq_nat2(skf126(W:fun_nat_nat),skf127(W:fun_nat_nat)))*.
(d0,A,r1610,rw70840) 936[0:Rew:17.0,77.0] ||  -> equal(times_times_nat2(V:naT,suc1(zero_zero_nat)),V:naT)**.
(d0,A,r1000,rw44000) 121[0:Inp] ||  -> equal(aa_nat_nat(suC,V:naT),suc1(V:naT))**.
(d0,A,r1000,rw44000) 124[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(dvd_dvd_nat,V:naT),dvd_dvd_nat1(V:naT))**.
(d0,A,r1000,rw44000) 126[0:Inp] ||  -> equal(aa_nat_fun_nat_nat(plus_plus_nat,V:naT),plus_plus_nat1(V:naT))**.
(d0,A,r1000,rw44000) 128[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_nat,V:naT),ord_less_nat1(V:naT))**.
(d0,A,r1000,rw44000) 133[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_eq_nat,V:naT),ord_less_eq_nat1(V:naT))**.
(d0,A,r1000,rw44000) 135[0:Inp] ||  -> equal(aa_nat_int(semiri2019852685at_int,V:naT),semiri501196819t_int1(V:naT))**.
(d0,A,r1000,rw44000) 141[0:Inp] ||  -> equal(aa_nat_Code_integer(semiri401560510ntegeR,V:naT),semiri1360655138teger1(V:naT))**.
(d0,A,r1579,rw69476) 935[0:Rew:17.0,75.0] ||  -> equal(times_times_nat2(suc1(zero_zero_nat),V:naT),V:naT)**.
(d0,A,r1000,rw44000) 120[0:Inp] ||  -> equal(aa_int_nat(naT2,U:inT),nat1(U:inT))**.
(d0,A,r1000,rw44000) 123[0:Inp] ||  -> equal(aa_int_fun_int_bool(dvd_dvd_int,U:inT),dvd_dvd_int1(U:inT))**.
(d0,A,r1000,rw44000) 125[0:Inp] ||  -> equal(aa_int_fun_int_int(plus_plus_int,U:inT),plus_plus_int1(U:inT))**.
(d0,A,r1000,rw44000) 127[0:Inp] ||  -> equal(aa_int_fun_int_bool(ord_less_int,U:inT),ord_less_int1(U:inT))**.
(d0,A,r1000,rw44000) 131[0:Inp] ||  -> equal(aa_int_int(uminus_uminus_int,U:inT),uminus_uminus_int1(U:inT))**.
(d0,A,r1000,rw44000) 132[0:Inp] ||  -> equal(aa_int_fun_int_bool(ord_less_eq_int,U:inT),ord_less_eq_int1(U:inT))**.
(d0,A,r913,rw39259) 47[0:Inp] ||  -> equal(plus_plus_literal2(X11:literaL,zero_zero_literal),X11:literaL)**.
(d0,A,r931,rw40033) 51[0:Inp] ||  -> equal(plus_plus_literal2(zero_zero_literal,X11:literaL),X11:literaL)**.
(d0,A,r2907,rw125001) 102[0:Inp] ||  -> equal(minus_1582103350nteger(Z:code_integer,Z:code_integer),zero_z413810534nteger)**.
(d0,A,r1932,rw83076) 87[0:Inp] ||  -> equal(minus_1582103350nteger(Z:code_integer,zero_z413810534nteger),Z:code_integer)**.
(d0,A,r904,rw38872) 45[0:Inp] ||  -> equal(plus_p715165435teger2(Z:code_integer,zero_z413810534nteger),Z:code_integer)**.
(d0,A,r922,rw39646) 49[0:Inp] ||  -> equal(plus_p715165435teger2(zero_z413810534nteger,Z:code_integer),Z:code_integer)**.
(d0,A,r1740,rw74820) 81[0:Inp] || pp(ord_less_nat2(V:naT,V:naT))* -> .
(d0,A,r3550,rw152650) 118[0:Inp] ||  -> pp(ord_less_nat2(V:naT,suc1(V:naT)))*.
(d0,A,r2916,rw125388) 104[0:Inp] ||  -> equal(minus_minus_nat2(V:naT,V:naT),zero_zero_nat)**.
(d0,A,r1941,rw83463) 89[0:Inp] ||  -> equal(minus_minus_nat2(V:naT,zero_zero_nat),V:naT)**.
(d0,A,r900,rw38700) 44[0:Inp] ||  -> equal(plus_plus_nat2(V:naT,zero_zero_nat),V:naT)**.
(d0,A,r1000,rw43000) 939[0:Rew:5.0,122.0,26.0,122.0] ||  -> equal(aa_nat_nat(semiri1382578993at_nat,V:naT),V:naT)**.
(d0,A,r917,rw39431) 48[0:Inp] ||  -> equal(plus_plus_nat2(zero_zero_nat,V:naT),V:naT)**.
(d0,A,r1744,rw74992) 82[0:Inp] || pp(ord_less_int2(U:inT,U:inT))* -> .
(d0,A,r2911,rw125173) 103[0:Inp] ||  -> equal(minus_minus_int2(U:inT,U:inT),zero_zero_int)**.
(d0,A,r1937,rw83291) 88[0:Inp] ||  -> equal(minus_minus_int2(U:inT,zero_zero_int),U:inT)**.
(d0,A,r1646,rw70778) 76[0:Inp] ||  -> equal(times_times_int2(U:inT,one_one_int),U:inT)**.
(d0,A,r908,rw39044) 46[0:Inp] ||  -> equal(plus_plus_int2(U:inT,zero_zero_int),U:inT)**.
(d0,A,r1575,rw67725) 74[0:Inp] ||  -> equal(times_times_int2(one_one_int,U:inT),U:inT)**.
(d0,A,r926,rw39818) 50[0:Inp] ||  -> equal(plus_plus_int2(zero_zero_int,U:inT),U:inT)**.
(d0,A,r1391,rw58422) 15[0:Inp] ||  -> pp(ord_less_eq_bool2(X8:booL,X8:booL))*.
(d0,A,r1387,rw58254) 14[0:Inp] ||  -> pp(ord_less_eq_nat2(V:naT,V:naT))*.
(d0,A,r2401,rw100842) 26[0:Inp] ||  -> equal(id_nat1(V:naT),V:naT)**.
(d0,A,r1000,rw42000) 940[0:Rew:939.0,136.0] ||  -> equal(semiri1184971631t_nat1(V:naT),V:naT)**.
(d0,A,r1396,rw58632) 16[0:Inp] ||  -> pp(ord_less_eq_int2(U:inT,U:inT))*.
(d0,A,r3032,rw72768) 107[0:Inp] || equal(numeral_numeral_int1(X7:nuM),zero_zero_int)** -> .
(d0,A,r3027,rw72648) 106[0:Inp] || equal(numera1961560056ntegeR(X7:nuM),zero_z413810534nteger)** -> .
(d0,A,r3023,rw72552) 105[0:Inp] || equal(numeral_numeral_nat(X7:nuM),zero_zero_nat)** -> .
(d0,A,r2053,rw49272) 90[0:Inp] ||  -> equal(times_1419655522nteger(Z:code_integer,zero_z413810534nteger),zero_z413810534nteger)**.
(d0,A,r1892,rw45408) 84[0:Inp] ||  -> equal(times_1419655522nteger(zero_z413810534nteger,Z:code_integer),zero_z413810534nteger)**.
(d0,A,r1655,rw39720) 78[0:Inp] || pp(ord_less_nat2(V:naT,zero_zero_nat))* -> .
(d0,A,r1762,rw42288) 83[0:Inp] || equal(suc1(V:naT),zero_zero_nat)** -> .
(d0,A,r3103,rw74472) 108[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,suc1(V:naT)))*.
(d0,A,r2062,rw49488) 92[0:Inp] ||  -> equal(times_times_nat2(V:naT,zero_zero_nat),zero_zero_nat)**.
(d0,A,r1901,rw45624) 86[0:Inp] ||  -> equal(times_times_nat2(zero_zero_nat,V:naT),zero_zero_nat)**.
(d0,A,r2057,rw49368) 91[0:Inp] ||  -> equal(times_times_int2(U:inT,zero_zero_int),zero_zero_int)**.
(d0,A,r1896,rw45504) 85[0:Inp] ||  -> equal(times_times_int2(zero_zero_int,U:inT),zero_zero_int)**.
(d0,A,r1378,rw31694) 13[0:Inp] ||  -> pp(ord_less_eq_nat2(zero_zero_nat,V:naT))*.
(d0,A,r1610,rw9660) 934[0:Rew:17.0,110.0] || pp(ord_less_eq_nat2(suc1(zero_zero_nat),zero_zero_nat))* -> .
(d0,A,r2133,rw10665) 93[0:Inp] || pp(ord_le1687847920teger2(zero_z413810534nteger,zero_z413810534nteger))* -> .
(d0,A,r3161,rw15805) 111[0:Inp] || pp(ord_less_eq_int2(one_one_int,zero_zero_int))* -> .
(d0,A,r3152,rw15760) 109[0:Inp] || pp(ord_le1442264292teger2(one_one_Code_integer,zero_z413810534nteger))* -> .
(d0,A,r1610,rw8050) 932[0:Rew:17.0,34.0] ||  -> equal(zero_n1672634641l_nat1(fTruE),suc1(zero_zero_nat))**.
(d0,A,r1610,rw8050) 933[0:Rew:17.0,27.0] ||  -> equal(numeral_numeral_nat(onE),suc1(zero_zero_nat))**.
(d0,A,r3456,rw17280) 115[0:Inp] ||  -> equal(groups2034138775iteraL(plus_plus_literal,zero_zero_literal),groups48143213iteraL)**.
(d0,A,r3452,rw17260) 114[0:Inp] ||  -> equal(groups_monoid_F_int(plus_plus_int,zero_zero_int),groups1559178963st_int)**.
(d0,A,r3448,rw17240) 113[0:Inp] ||  -> equal(groups575448154ntegeR(plus_p2058578406nteger,zero_z413810534nteger),groups2087840004ntegeR)**.
(d0,A,r3443,rw17215) 112[0:Inp] ||  -> equal(groups_monoid_F_nat(plus_plus_nat,zero_zero_nat),groups921905271st_nat)**.
(d0,A,r3175,rw12700) 38[0:Inp] || equal(zero_zero_int,one_one_int)** -> .
(d0,A,r3170,rw12680) 37[0:Inp] || equal(zero_z413810534nteger,one_one_Code_integer)** -> .
(d0,A,r2205,rw8820) 20[0:Inp] ||  -> pp(ord_le1442264292teger2(zero_z413810534nteger,zero_z413810534nteger))*.
(d0,A,r3389,rw13556) 41[0:Inp] ||  -> pp(ord_less_eq_int2(zero_zero_int,one_one_int))*.
(d0,A,r3380,rw13520) 39[0:Inp] ||  -> pp(ord_le1442264292teger2(zero_z413810534nteger,one_one_Code_integer))*.
(d0,A,r1333,rw5332) 12[0:Inp] ||  -> pp(monoid_int2(plus_plus_int,zero_zero_int))*.
(d0,A,r1329,rw5316) 11[0:Inp] ||  -> pp(monoid_Code_integer2(plus_p2058578406nteger,zero_z413810534nteger))*.
(d0,A,r1324,rw5296) 10[0:Inp] ||  -> pp(monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r1306,rw5224) 9[0:Inp] ||  -> pp(comm_monoid_int2(plus_plus_int,zero_zero_int))*.
(d0,A,r1302,rw5208) 8[0:Inp] ||  -> pp(comm_m138292217teger2(plus_p2058578406nteger,zero_z413810534nteger))*.
(d0,A,r1297,rw5188) 7[0:Inp] ||  -> pp(comm_monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r1610,rw6440) 17[0:Inp] ||  -> equal(one_one_nat,suc1(zero_zero_nat))**.
(d0,A,r2925,rw11700) 30[0:Inp] ||  -> equal(uminus_uminus_int1(zero_zero_int),zero_zero_int)**.
(d0,A,r2920,rw11680) 29[0:Inp] ||  -> equal(uminus636303014ntegeR(zero_z413810534nteger),zero_z413810534nteger)**.
(d0,A,r3541,rw14164) 42[0:Inp] ||  -> equal(nat1(zero_zero_int),zero_zero_nat)**.
(d0,A,r3085,rw12340) 35[0:Inp] ||  -> equal(zero_n988859829l_int1(fTruE),one_one_int)**.
(d0,A,r2880,rw11520) 28[0:Inp] ||  -> equal(numeral_numeral_int1(onE),one_one_int)**.
(d0,A,r1000,rw3000) 6[0:Inp] || pp(fFalsE)* -> .
(d0,A,r1338,rw4014) 3[0:Inp] ||  -> monoid_literal(plus_plus_literal,zero_zero_literal)*.
(d0,A,r3564,rw10692) 5[0:Inp] ||  -> equal(id_nat,semiri1382578993at_nat)**.
(d0,A,r1400,rw4200) 4[0:Inp] ||  -> equal(poS,numeral_numeral_int)**.
(d0,A,r2871,rw5742) 1[0:Inp] || bot_bot_bool* -> .
(d0,A,r1000,rw2000) 2[0:Inp] ||  -> pp(fTruE)*.