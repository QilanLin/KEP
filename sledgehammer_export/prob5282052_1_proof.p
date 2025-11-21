

From 945 Axiom clauses, 0 were allowed.


A precedence of symbols which satisfies all compatible equal:lr annotations (the actual ordering is in general less restricted):
	[]

SPASS V 3.8ds 
SPASS beiseite: Completion found.
Problem: /Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob5282052_1.p 
SPASS derived 23 clauses, backtracked 0 clauses, performed 0 splits and kept 630 clauses.
SPASS allocated 97405 KBytes.
SPASS spent	0:00:00.35 on the problem.
		0:00:00.02 for the input.
		0:00:00.17 for the FLOTTER CNF translation.
		0:00:00.00 for inferences.
		0:00:00.00 for the backtracking.
		0:00:00.08 for the reduction.


 The saturated set of worked-off clauses is :
(d0,C,r1000,rw8000) 205[0:Inp] || equal(plus_plus_a(y,x),plus_plus_a(x,y))** -> .
(d0,A,r2984,rw1110048) 936[0:Inp] || SkP11(V:nuM,X3:nuM,X11:nuM)* SkP11(X3:nuM,X11:nuM,V:nuM)* SkP11(X3:nuM,V:nuM,X11:nuM)* SkP11(V:nuM,X11:nuM,X3:nuM)* SkP11(X11:nuM,X3:nuM,V:nuM)* SkP11(X11:nuM,V:nuM,X3:nuM)* -> .
(d0,A,r2975,rw1106700) 938[0:Inp] || SkP9(X4:booL,X5:booL,X10:booL)* SkP9(X5:booL,X10:booL,X4:booL)* SkP9(X5:booL,X4:booL,X10:booL)* SkP9(X4:booL,X10:booL,X5:booL)* SkP9(X10:booL,X5:booL,X4:booL)* SkP9(X10:booL,X4:booL,X5:booL)* -> .
(d0,A,r2980,rw1108560) 937[0:Inp] || SkP10(U:naT,Y:naT,X7:naT)* SkP10(Y:naT,X7:naT,U:naT)* SkP10(Y:naT,U:naT,X7:naT)* SkP10(U:naT,X7:naT,Y:naT)* SkP10(X7:naT,Y:naT,U:naT)* SkP10(X7:naT,U:naT,Y:naT)* -> .
(d0,A,r3393,rw1072188) 939[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf288(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool)))* SkP15(X12:fun_nat_bool,X33:fun_nat_bool) SkP15(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3393,rw1072188) 940[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf288(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool)))* SkP15(X12:fun_nat_bool,X33:fun_nat_bool) SkP15(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3393,rw1072188) 941[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf288(X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool,X32:fun_nat_bool)))* SkP15(X33:fun_nat_bool,X12:fun_nat_bool) SkP15(X34:fun_nat_bool,X32:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3393,rw1072188) 942[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf288(X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool,X32:fun_nat_bool)))* SkP15(X33:fun_nat_bool,X12:fun_nat_bool) SkP15(X34:fun_nat_bool,X32:fun_nat_bool) -> pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1053544) 943[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf280(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool),U:naT))* SkP13(X12:fun_nat_bool,X33:fun_nat_bool) SkP13(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1053544) 944[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf280(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool),U:naT))* SkP13(X12:fun_nat_bool,X33:fun_nat_bool) SkP13(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1053544) 945[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf280(X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool,X32:fun_nat_bool),U:naT))* SkP13(X33:fun_nat_bool,X12:fun_nat_bool) SkP13(X34:fun_nat_bool,X32:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1053544) 946[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf280(X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool,X32:fun_nat_bool),U:naT))* SkP13(X33:fun_nat_bool,X12:fun_nat_bool) SkP13(X34:fun_nat_bool,X32:fun_nat_bool) -> pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3397,rw1070055) 928[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf290(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool)))* SkP16(X12:fun_nat_bool,X33:fun_nat_bool) SkP16(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)) pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3397,rw1070055) 929[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf290(X32:fun_nat_bool,X12:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool)))* SkP16(X32:fun_nat_bool,X33:fun_nat_bool) SkP16(X12:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)) pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3397,rw1070055) 930[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf290(X32:fun_nat_bool,X33:fun_nat_bool,X12:fun_nat_bool,X34:fun_nat_bool)))* SkP16(X32:fun_nat_bool,X12:fun_nat_bool) SkP16(X33:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3397,rw1070055) 931[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf290(X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool)))* SkP16(X32:fun_nat_bool,X34:fun_nat_bool) SkP16(X33:fun_nat_bool,X12:fun_nat_bool) -> pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1050210) 932[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf282(X12:fun_nat_bool,X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool),U:naT))* SkP14(X12:fun_nat_bool,X33:fun_nat_bool) SkP14(X32:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)) pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1050210) 933[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf282(X32:fun_nat_bool,X12:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool),U:naT))* SkP14(X32:fun_nat_bool,X33:fun_nat_bool) SkP14(X12:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,U:naT)) pp(aa_nat_bool(X34:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1050210) 934[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf282(X32:fun_nat_bool,X33:fun_nat_bool,X12:fun_nat_bool,X34:fun_nat_bool),U:naT))* SkP14(X32:fun_nat_bool,X12:fun_nat_bool) SkP14(X33:fun_nat_bool,X34:fun_nat_bool) -> pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r3334,rw1050210) 935[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(skf282(X32:fun_nat_bool,X33:fun_nat_bool,X34:fun_nat_bool,X12:fun_nat_bool),U:naT))* SkP14(X32:fun_nat_bool,X34:fun_nat_bool) SkP14(X33:fun_nat_bool,X12:fun_nat_bool) -> pp(aa_nat_bool(X32:fun_nat_bool,U:naT)) pp(aa_nat_bool(X33:fun_nat_bool,U:naT)).
(d0,A,r2193,rw600882) 895[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,U:naT)) -> equal(plus_plus_int2(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(X7:naT,U:naT)),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(U:naT,Y:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(X7:naT,Y:naT)))**.
(d0,A,r2189,rw599786) 896[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,U:naT)) -> equal(plus_plus_nat2(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(X7:naT,U:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(U:naT,Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(X7:naT,Y:naT)))**.
(d0,A,r2746,rw705722) 910[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(X11:nuM,aa_num_num(X25:fun_num_num,V:nuM)))* pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,skf246(X25:fun_num_num)),aa_num_num(X25:fun_num_num,skf247(X25:fun_num_num))))* -> pp(ord_less_eq_num2(X11:nuM,aa_num_num(X25:fun_num_num,X3:nuM)))*.
(d0,A,r3168,rw814176) 897[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_num2(X11:nuM,aa_num_num(X25:fun_num_num,V:nuM)))* pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,skf316(X25:fun_num_num)),aa_num_num(X25:fun_num_num,skf317(X25:fun_num_num))))* -> pp(ord_less_num2(X11:nuM,aa_num_num(X25:fun_num_num,X3:nuM)))*.
(d0,A,r2705,rw695185) 919[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,X3:nuM),X11:nuM))* pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,skf228(X25:fun_num_num)),aa_num_num(X25:fun_num_num,skf229(X25:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,V:nuM),X11:nuM))*.
(d0,A,r2732,rw702124) 913[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_nat2(U:naT,aa_num_nat(X24:fun_num_nat,V:nuM)))* pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,skf240(X24:fun_num_nat)),aa_num_nat(X24:fun_num_nat,skf241(X24:fun_num_nat))))* -> pp(ord_less_eq_nat2(U:naT,aa_num_nat(X24:fun_num_nat,X3:nuM)))*.
(d0,A,r3168,rw814176) 898[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_nat2(U:naT,aa_num_nat(X24:fun_num_nat,V:nuM)))* pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,skf314(X24:fun_num_nat)),aa_num_nat(X24:fun_num_nat,skf315(X24:fun_num_nat))))* -> pp(ord_less_nat2(U:naT,aa_num_nat(X24:fun_num_nat,X3:nuM)))*.
(d0,A,r2701,rw694157) 920[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,X3:nuM),U:naT))* pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,skf226(X24:fun_num_nat)),aa_num_nat(X24:fun_num_nat,skf227(X24:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,V:nuM),U:naT))*.
(d0,A,r2719,rw698783) 916[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_bool2(X4:booL,aa_num_bool(X22:fun_num_bool,V:nuM)))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,skf234(X22:fun_num_bool)),aa_num_bool(X22:fun_num_bool,skf235(X22:fun_num_bool))))* -> pp(ord_less_eq_bool2(X4:booL,aa_num_bool(X22:fun_num_bool,X3:nuM)))*.
(d0,A,r3168,rw814176) 899[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_bool2(X4:booL,aa_num_bool(X22:fun_num_bool,V:nuM)))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,skf312(X22:fun_num_bool)),aa_num_bool(X22:fun_num_bool,skf313(X22:fun_num_bool))))* -> pp(ord_less_bool2(X4:booL,aa_num_bool(X22:fun_num_bool,X3:nuM)))*.
(d0,A,r2697,rw693129) 921[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,X3:nuM),X4:booL))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,skf224(X22:fun_num_bool)),aa_num_bool(X22:fun_num_bool,skf225(X22:fun_num_bool))))* -> pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,V:nuM),X4:booL))*.
(d0,A,r2741,rw704437) 911[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_num2(V:nuM,aa_nat_num(X21:fun_nat_num,U:naT)))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,skf244(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf245(X21:fun_nat_num))))* -> pp(ord_less_eq_num2(V:nuM,aa_nat_num(X21:fun_nat_num,Y:naT)))*.
(d0,A,r3272,rw840904) 900[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_num2(V:nuM,aa_nat_num(X21:fun_nat_num,U:naT)))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,skf310(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf311(X21:fun_nat_num))))* -> pp(ord_less_num2(V:nuM,aa_nat_num(X21:fun_nat_num,Y:naT)))*.
(d0,A,r2692,rw691844) 922[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,Y:naT),V:nuM))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,skf222(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf223(X21:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,U:naT),V:nuM))*.
(d0,A,r1430,rw367510) 905[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,Y:naT),V:nuM))* pp(ord_less_num2(aa_nat_num(X21:fun_nat_num,skf300(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf301(X21:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X21:fun_nat_num,U:naT),V:nuM))*.
(d0,A,r1070,rw274990) 912[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_num2(V:nuM,aa_bool_num(X19:fun_bool_num,X4:booL)))* pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,skf242(X19:fun_bool_num)),aa_bool_num(X19:fun_bool_num,skf243(X19:fun_bool_num))))* -> pp(ord_less_eq_num2(V:nuM,aa_bool_num(X19:fun_bool_num,X5:booL)))*.
(d0,A,r1070,rw274990) 903[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_num2(V:nuM,aa_bool_num(X19:fun_bool_num,X4:booL)))* pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,skf304(X19:fun_bool_num)),aa_bool_num(X19:fun_bool_num,skf305(X19:fun_bool_num))))* -> pp(ord_less_num2(V:nuM,aa_bool_num(X19:fun_bool_num,X5:booL)))*.
(d0,A,r1070,rw274990) 925[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,X5:booL),V:nuM))* pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,skf216(X19:fun_bool_num)),aa_bool_num(X19:fun_bool_num,skf217(X19:fun_bool_num))))* -> pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,X4:booL),V:nuM))*.
(d0,A,r1070,rw274990) 915[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_nat2(U:naT,aa_bool_nat(X18:fun_bool_nat,X4:booL)))* pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,skf236(X18:fun_bool_nat)),aa_bool_nat(X18:fun_bool_nat,skf237(X18:fun_bool_nat))))* -> pp(ord_less_eq_nat2(U:naT,aa_bool_nat(X18:fun_bool_nat,X5:booL)))*.
(d0,A,r1070,rw274990) 904[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_nat2(U:naT,aa_bool_nat(X18:fun_bool_nat,X4:booL)))* pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,skf302(X18:fun_bool_nat)),aa_bool_nat(X18:fun_bool_nat,skf303(X18:fun_bool_nat))))* -> pp(ord_less_nat2(U:naT,aa_bool_nat(X18:fun_bool_nat,X5:booL)))*.
(d0,A,r1070,rw274990) 926[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,X5:booL),U:naT))* pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,skf214(X18:fun_bool_nat)),aa_bool_nat(X18:fun_bool_nat,skf215(X18:fun_bool_nat))))* -> pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,X4:booL),U:naT))*.
(d0,A,r1070,rw274990) 918[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(X10:booL,aa_bool_bool(X15:fun_bool_bool,X4:booL)))* pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,skf230(X15:fun_bool_bool)),aa_bool_bool(X15:fun_bool_bool,skf231(X15:fun_bool_bool))))* -> pp(ord_less_eq_bool2(X10:booL,aa_bool_bool(X15:fun_bool_bool,X5:booL)))*.
(d0,A,r1070,rw274990) 927[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,X5:booL),X10:booL))* pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,skf212(X15:fun_bool_bool)),aa_bool_bool(X15:fun_bool_bool,skf213(X15:fun_bool_bool))))* -> pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,X4:booL),X10:booL))*.
(d0,A,r2714,rw697498) 917[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_bool2(X4:booL,aa_nat_bool(X12:fun_nat_bool,U:naT)))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,skf232(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf233(X12:fun_nat_bool))))* -> pp(ord_less_eq_bool2(X4:booL,aa_nat_bool(X12:fun_nat_bool,Y:naT)))*.
(d0,A,r3272,rw840904) 902[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_bool2(X4:booL,aa_nat_bool(X12:fun_nat_bool,U:naT)))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,skf306(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf307(X12:fun_nat_bool))))* -> pp(ord_less_bool2(X4:booL,aa_nat_bool(X12:fun_nat_bool,Y:naT)))*.
(d0,A,r2683,rw689531) 924[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,Y:naT),X4:booL))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,skf218(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf219(X12:fun_nat_bool))))* -> pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,U:naT),X4:booL))*.
(d0,A,r1430,rw367510) 907[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,Y:naT),X4:booL))* pp(ord_less_bool2(aa_nat_bool(X12:fun_nat_bool,skf296(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf297(X12:fun_nat_bool))))* -> pp(ord_less_bool2(aa_nat_bool(X12:fun_nat_bool,U:naT),X4:booL))*.
(d0,A,r2728,rw701096) 914[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,U:naT)))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf238(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf239(W:fun_nat_nat))))* -> pp(ord_less_eq_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r1430,rw367510) 908[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,U:naT)))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf262(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf263(W:fun_nat_nat))))* -> pp(ord_less_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r3272,rw840904) 901[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,U:naT)))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf308(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf309(W:fun_nat_nat))))* -> pp(ord_less_nat2(X7:naT,aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r2688,rw690816) 923[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,Y:naT),X7:naT))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf220(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf221(W:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),X7:naT))*.
(d0,A,r1430,rw367510) 909[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,Y:naT),X7:naT))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf260(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf261(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),X7:naT))*.
(d0,A,r1430,rw367510) 906[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,Y:naT),X7:naT))* pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf298(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf299(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),X7:naT))*.
(d0,A,r2638,rw672690) 889[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,skf206(X22:fun_num_bool)),aa_num_bool(X22:fun_num_bool,skf207(X22:fun_num_bool))))* SkP5(V:nuM,X22:fun_num_bool,X4:booL)* -> pp(ord_less_eq_bool2(X4:booL,aa_num_bool(X22:fun_num_bool,X3:nuM)))*.
(d0,A,r2593,rw661215) 892[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,skf188(X22:fun_num_bool)),aa_num_bool(X22:fun_num_bool,skf189(X22:fun_num_bool))))* SkP2(X4:booL,X3:nuM,X22:fun_num_bool)* -> pp(ord_less_eq_bool2(aa_num_bool(X22:fun_num_bool,V:nuM),X4:booL))*.
(d0,A,r1070,rw272850) 891[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,skf194(X15:fun_bool_bool)),aa_bool_bool(X15:fun_bool_bool,skf195(X15:fun_bool_bool))))* SkP3(X4:booL,X15:fun_bool_bool,X10:booL)* -> pp(ord_less_eq_bool2(X10:booL,aa_bool_bool(X15:fun_bool_bool,X5:booL)))*.
(d0,A,r1070,rw272850) 894[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,skf176(X15:fun_bool_bool)),aa_bool_bool(X15:fun_bool_bool,skf177(X15:fun_bool_bool))))* SkP0(X10:booL,X5:booL,X15:fun_bool_bool)* -> pp(ord_less_eq_bool2(aa_bool_bool(X15:fun_bool_bool,X4:booL),X10:booL))*.
(d0,A,r2625,rw669375) 890[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,skf200(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf201(X12:fun_nat_bool))))* SkP4(U:naT,X12:fun_nat_bool,X4:booL)* -> pp(ord_less_eq_bool2(X4:booL,aa_nat_bool(X12:fun_nat_bool,Y:naT)))*.
(d0,A,r2580,rw657900) 893[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,skf182(X12:fun_nat_bool)),aa_nat_bool(X12:fun_nat_bool,skf183(X12:fun_nat_bool))))* SkP1(X4:booL,Y:naT,X12:fun_nat_bool)* -> pp(ord_less_eq_bool2(aa_nat_bool(X12:fun_nat_bool,U:naT),X4:booL))*.
(d0,A,r985,rw250190) 1060[0:Rew:180.0,886.1] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(Y:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT))),plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(aTP_Lamm_aa(X:fun_nat_int),set_or601162459st_nat(U:naT,Y:naT))))*.
(d0,A,r980,rw248920) 1061[0:Rew:179.0,887.1] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(Y:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT))),plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(aTP_Lamm_a(W:fun_nat_nat),set_or601162459st_nat(U:naT,Y:naT))))*.
(d0,A,r3047,rw761750) 864[0:Inp] || equal(plus_plus_nat2(times_times_nat2(U:naT,Y:naT),times_times_nat2(X7:naT,X9:naT)),plus_plus_nat2(times_times_nat2(U:naT,X9:naT),times_times_nat2(X7:naT,Y:naT)))* -> equal(U:naT,X7:naT) equal(Y:naT,X9:naT).
(d0,A,r3042,rw760500) 865[0:Inp] || equal(plus_plus_int2(times_times_int(Z:inT,X1:inT),times_times_int(X6:inT,X8:inT)),plus_plus_int2(times_times_int(Z:inT,X8:inT),times_times_int(X6:inT,X1:inT)))* -> equal(Z:inT,X6:inT) equal(X1:inT,X8:inT).
(d0,A,r1430,rw310310) 888[0:Inp] SkP12(X28:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf269(X28:fun_nat_fun_nat_bool)),skf269(X28:fun_nat_fun_nat_bool))) pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf271(X28:fun_nat_fun_nat_bool)),skf270(X28:fun_nat_fun_nat_bool)))* -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,U:naT),Y:naT))*.
(d0,A,r2647,rw566458) 874[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,skf210(X25:fun_num_num)),aa_num_num(X25:fun_num_num,skf211(X25:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,V:nuM),aa_num_num(X25:fun_num_num,X3:nuM)))*.
(d0,A,r2602,rw556828) 880[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,skf192(X25:fun_num_num)),aa_num_num(X25:fun_num_num,skf193(X25:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X25:fun_num_num,V:nuM),aa_num_num(X25:fun_num_num,X3:nuM)))*.
(d0,A,r2643,rw565602) 875[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,skf208(X24:fun_num_nat)),aa_num_nat(X24:fun_num_nat,skf209(X24:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,V:nuM),aa_num_nat(X24:fun_num_nat,X3:nuM)))*.
(d0,A,r2598,rw555972) 881[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,skf190(X24:fun_num_nat)),aa_num_nat(X24:fun_num_nat,skf191(X24:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X24:fun_num_nat,V:nuM),aa_num_nat(X24:fun_num_nat,X3:nuM)))*.
(d0,A,r2634,rw563676) 876[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,skf204(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf205(X21:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,U:naT),aa_nat_num(X21:fun_nat_num,Y:naT)))*.
(d0,A,r2589,rw554046) 882[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,skf186(X21:fun_nat_num)),aa_nat_num(X21:fun_nat_num,skf187(X21:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X21:fun_nat_num,U:naT),aa_nat_num(X21:fun_nat_num,Y:naT)))*.
(d0,A,r1070,rw228980) 878[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,skf198(X19:fun_bool_num)),aa_bool_num(X19:fun_bool_num,skf199(X19:fun_bool_num))))* -> pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,X4:booL),aa_bool_num(X19:fun_bool_num,X5:booL)))*.
(d0,A,r1070,rw228980) 884[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,skf180(X19:fun_bool_num)),aa_bool_num(X19:fun_bool_num,skf181(X19:fun_bool_num))))* -> pp(ord_less_eq_num2(aa_bool_num(X19:fun_bool_num,X4:booL),aa_bool_num(X19:fun_bool_num,X5:booL)))*.
(d0,A,r1070,rw228980) 879[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,skf196(X18:fun_bool_nat)),aa_bool_nat(X18:fun_bool_nat,skf197(X18:fun_bool_nat))))* -> pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,X4:booL),aa_bool_nat(X18:fun_bool_nat,X5:booL)))*.
(d0,A,r1070,rw228980) 885[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,skf178(X18:fun_bool_nat)),aa_bool_nat(X18:fun_bool_nat,skf179(X18:fun_bool_nat))))* -> pp(ord_less_eq_nat2(aa_bool_nat(X18:fun_bool_nat,X4:booL),aa_bool_nat(X18:fun_bool_nat,X5:booL)))*.
(d0,A,r2629,rw562606) 877[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf202(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf203(W:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r2584,rw552976) 883[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,skf184(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf185(W:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r1430,rw306020) 872[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf266(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf267(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r1430,rw306020) 873[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,skf264(W:fun_nat_nat)),aa_nat_nat(W:fun_nat_nat,skf265(W:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),aa_nat_nat(W:fun_nat_nat,Y:naT)))*.
(d0,A,r3325,rw708225) 868[0:Inp] || pp(ord_less_eq_nat2(U:naT,suc1(Y:naT))) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(Y:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,suc1(Y:naT))))**.
(d0,A,r3321,rw707373) 869[0:Inp] || pp(ord_less_eq_nat2(U:naT,suc1(Y:naT))) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(Y:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,suc1(Y:naT))))**.
(d0,A,r985,rw208820) 1059[0:Rew:180.0,863.0] ||  -> pp(ord_less_nat2(suc1(U:naT),Y:naT)) equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(U:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(Y:naT,U:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(Y:naT,suc1(U:naT))))**.
(d0,A,r980,rw207760) 1058[0:Rew:179.0,862.0] ||  -> pp(ord_less_nat2(suc1(U:naT),Y:naT)) equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(U:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(Y:naT,U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(Y:naT,suc1(U:naT))))**.
(d0,A,r2849,rw601139) 854[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(suc1(U:naT),Y:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(U:naT,Y:naT)))**.
(d0,A,r2845,rw600295) 855[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(suc1(U:naT),Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(U:naT,Y:naT)))**.
(d0,A,r2786,rw587846) 856[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(suc1(U:naT),Y:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r2782,rw587002) 857[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(suc1(U:naT),Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r3218,rw675780) 848[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,Y:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(U:naT,Y:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r3213,rw674730) 849[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,Y:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(U:naT,Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r3110,rw653100) 850[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_or1535848064st_nat(U:naT,Y:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r3105,rw652050) 851[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_or1535848064st_nat(U:naT,Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r3397,rw709973) 842[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,skf291(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf291(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* -> SkP16(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3393,rw709137) 841[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,skf289(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf289(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* -> SkP15(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3334,rw696806) 839[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,skf281(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf281(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* -> SkP13(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3334,rw696806) 840[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,skf283(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf283(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* -> SkP14(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3038,rw634942) 831[0:Inp] || equal(U:naT,Y:naT) -> equal(plus_plus_nat2(times_times_nat2(U:naT,X7:naT),times_times_nat2(Y:naT,X9:naT)),plus_plus_nat2(times_times_nat2(U:naT,X9:naT),times_times_nat2(Y:naT,X7:naT)))*.
(d0,A,r3038,rw634942) 832[0:Inp] || equal(U:naT,Y:naT) -> equal(plus_plus_nat2(times_times_nat2(X7:naT,U:naT),times_times_nat2(X9:naT,Y:naT)),plus_plus_nat2(times_times_nat2(X7:naT,Y:naT),times_times_nat2(X9:naT,U:naT)))*.
(d0,A,r3033,rw633897) 829[0:Inp] || equal(Z:inT,X1:inT) -> equal(plus_plus_int2(times_times_int(Z:inT,X6:inT),times_times_int(X1:inT,X8:inT)),plus_plus_int2(times_times_int(Z:inT,X8:inT),times_times_int(X1:inT,X6:inT)))*.
(d0,A,r3033,rw633897) 830[0:Inp] || equal(Z:inT,X1:inT) -> equal(plus_plus_int2(times_times_int(X6:inT,Z:inT),times_times_int(X8:inT,X1:inT)),plus_plus_int2(times_times_int(X6:inT,X1:inT),times_times_int(X8:inT,Z:inT)))*.
(d0,A,r985,rw205865) 1052[0:Rew:180.0,837.0] ||  -> pp(ord_less_nat2(U:naT,Y:naT)) equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(Y:naT,U:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(Y:naT,U:naT)))**.
(d0,A,r980,rw204820) 1053[0:Rew:179.0,838.0] ||  -> pp(ord_less_nat2(U:naT,Y:naT)) equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(Y:naT,U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(Y:naT,U:naT)))**.
(d0,A,r3397,rw703179) 807[0:Inp] ||  -> pp(aa_nat_bool(X12:fun_nat_bool,skf291(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf291(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* SkP16(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3393,rw702351) 806[0:Inp] ||  -> pp(aa_nat_bool(X12:fun_nat_bool,skf289(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf289(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* SkP15(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3334,rw690138) 804[0:Inp] ||  -> pp(aa_nat_bool(X12:fun_nat_bool,skf281(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf281(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* SkP13(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3334,rw690138) 805[0:Inp] ||  -> pp(aa_nat_bool(X12:fun_nat_bool,skf283(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* pp(aa_nat_bool(X32:fun_nat_bool,skf283(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))* SkP14(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3164,rw597996) 824[0:Inp] || equal(plus_plus_nat2(U:naT,times_times_nat2(Y:naT,X7:naT)),plus_plus_nat2(U:naT,times_times_nat2(Y:naT,X9:naT)))* -> equal(X7:naT,X9:naT) equal(Y:naT,zero_zero_nat).
(d0,A,r3159,rw597051) 823[0:Inp] || equal(plus_plus_int2(Z:inT,times_times_int(X1:inT,X6:inT)),plus_plus_int2(Z:inT,times_times_int(X1:inT,X8:inT)))* -> equal(X6:inT,X8:inT) equal(X1:inT,zero_zero_int).
(d0,A,r3312,rw622656) 803[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(U:naT,Y:naT),plus_plus_nat2(times_times_nat2(X7:naT,Y:naT),X9:naT)),plus_plus_nat2(times_times_nat2(plus_plus_nat2(U:naT,X7:naT),Y:naT),X9:naT))**.
(d0,A,r3307,rw621716) 802[0:Inp] ||  -> equal(plus_plus_int2(times_times_int(Z:inT,X1:inT),plus_plus_int2(times_times_int(X6:inT,X1:inT),X8:inT)),plus_plus_int2(times_times_int(plus_plus_int2(Z:inT,X6:inT),X1:inT),X8:inT))**.
(d0,A,r1457,rw247690) 811[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_nat2(X7:naT,X9:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X9:naT,Y:naT)))*.
(d0,A,r1209,rw205530) 808[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,X9:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X9:naT,Y:naT)))*.
(d0,A,r1403,rw238510) 810[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,X9:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X9:naT,Y:naT)))*.
(d0,A,r1367,rw232390) 809[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_nat2(X7:naT,X9:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X9:naT,Y:naT)))*.
(d0,A,r985,rw166465) 1056[0:Rew:848.1,858.1,180.0,858.1] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(U:naT,suc1(Y:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r980,rw165620) 1057[0:Rew:849.1,859.1,179.0,859.1] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> equal(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(U:naT,suc1(Y:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(U:naT,Y:naT)))**.
(d0,A,r985,rw165480) 1055[0:Rew:1052.0,846.0,180.0,846.0] ||  -> pp(ord_less_nat2(U:naT,Y:naT)) equal(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(Y:naT,suc1(U:naT))),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(Y:naT,U:naT)))**.
(d0,A,r980,rw164640) 1054[0:Rew:1053.0,845.0,179.0,845.0] ||  -> pp(ord_less_nat2(U:naT,Y:naT)) equal(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(Y:naT,suc1(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(Y:naT,U:naT)))**.
(d0,A,r1205,rw201235) 742[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_eq_int(X6:inT,X8:inT) -> ord_less_eq_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X8:inT,X1:inT))*.
(d0,A,r1398,rw233466) 746[0:Inp] || ord_less_int(Z:inT,X1:inT) ord_less_eq_int(X6:inT,X8:inT) -> ord_less_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X8:inT,X1:inT))*.
(d0,A,r1362,rw227454) 745[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_int(X6:inT,X8:inT) -> ord_less_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X8:inT,X1:inT))*.
(d0,A,r1452,rw242484) 747[0:Inp] || ord_less_int(Z:inT,X1:inT) ord_less_int(X6:inT,X8:inT) -> ord_less_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X8:inT,X1:inT))*.
(d0,A,r1430,rw218790) 847[0:Inp] SkP12(X28:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf269(X28:fun_nat_fun_nat_bool)),skf269(X28:fun_nat_fun_nat_bool))) -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf270(X28:fun_nat_fun_nat_bool)),skf271(X28:fun_nat_fun_nat_bool)))*.
(d0,A,r2876,rw434276) 822[0:Inp] SkP8(X29:fun_num_fun_num_bool) || pp(aa_num_bool(aa_num_fun_num_bool(X29:fun_num_fun_num_bool,skf257(X29:fun_num_fun_num_bool)),skf256(X29:fun_num_fun_num_bool)))* -> pp(aa_num_bool(aa_num_fun_num_bool(X29:fun_num_fun_num_bool,V:nuM),X3:nuM))*.
(d0,A,r2872,rw433672) 821[0:Inp] SkP7(X28:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf253(X28:fun_nat_fun_nat_bool)),skf252(X28:fun_nat_fun_nat_bool)))* -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,U:naT),Y:naT))*.
(d0,A,r1070,rw161570) 820[0:Inp] SkP6(X27:fun_bo1373903021l_bool) || pp(aa_bool_bool(aa_boo1142376798l_bool(X27:fun_bo1373903021l_bool,skf249(X27:fun_bo1373903021l_bool)),skf248(X27:fun_bo1373903021l_bool)))* -> pp(aa_bool_bool(aa_boo1142376798l_bool(X27:fun_bo1373903021l_bool,X4:booL),X5:booL))*.
(d0,A,r1551,rw231099) 793[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) -> pp(aa_nat_bool(X12:fun_nat_bool,skf277(X12:fun_nat_bool))) pp(aa_nat_bool(X12:fun_nat_bool,skf276(X12:fun_nat_bool,U:naT)))*.
(d0,A,r1551,rw231099) 792[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) -> pp(aa_nat_bool(X12:fun_nat_bool,skf277(X12:fun_nat_bool)))* pp(ord_less_nat2(skf276(X12:fun_nat_bool,U:naT),U:naT))*.
(d0,A,r3438,rw508824) 772[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_eq_num2(X3:nuM,X11:nuM)) -> member_num(X3:nuM,set_or102655269st_num(V:nuM,X11:nuM))*.
(d0,A,r3433,rw508084) 771[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_eq_bool2(X5:booL,X10:booL)) -> member_bool(X5:booL,set_or842601420t_bool(X4:booL,X10:booL))*.
(d0,A,r3442,rw509416) 773[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(Y:naT,X7:naT)) -> member_nat(Y:naT,set_or601162459st_nat(U:naT,X7:naT))*.
(d0,A,r2759,rw405573) 720[0:Inp] || equal(times_times_nat2(U:naT,Y:naT),times_times_nat2(X7:naT,Y:naT))* -> equal(U:naT,X7:naT) equal(Y:naT,zero_zero_nat).
(d0,A,r2463,rw362061) 713[0:Inp] || equal(times_times_nat2(U:naT,Y:naT),times_times_nat2(U:naT,X7:naT))* -> equal(Y:naT,X7:naT) equal(U:naT,zero_zero_nat).
(d0,A,r1776,rw259296) 645[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(U:naT,Y:naT),times_times_nat2(U:naT,X7:naT)),times_times_nat2(U:naT,plus_plus_nat2(Y:naT,X7:naT)))**.
(d0,A,r1843,rw269078) 652[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(U:naT,Y:naT),times_times_nat2(X7:naT,Y:naT)),times_times_nat2(plus_plus_nat2(U:naT,X7:naT),Y:naT))**.
(d0,A,r1771,rw258566) 644[0:Inp] ||  -> equal(plus_plus_int2(times_times_int(Z:inT,X1:inT),times_times_int(Z:inT,X6:inT)),times_times_int(Z:inT,plus_plus_int2(X1:inT,X6:inT)))**.
(d0,A,r1838,rw268348) 651[0:Inp] ||  -> equal(plus_plus_int2(times_times_int(Z:inT,X1:inT),times_times_int(X6:inT,X1:inT)),times_times_int(plus_plus_int2(Z:inT,X6:inT),X1:inT))**.
(d0,A,r1263,rw170505) 1046[0:Rew:962.0,852.0,161.0,852.0] ||  -> equal(groups332228664at_int(aTP_Lamm_ae(X:fun_nat_int),set_or601162459st_nat(U:naT,Y:naT)),groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT),suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),Y:naT)))))**.
(d0,A,r1263,rw170505) 1047[0:Rew:962.0,853.0,161.0,853.0] ||  -> equal(groups1842438620at_nat(aTP_Lamm_ad(W:fun_nat_nat),set_or601162459st_nat(U:naT,Y:naT)),groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT),suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),Y:naT)))))**.
(d0,A,r1263,rw169242) 1044[0:Rew:962.0,843.0,161.0,843.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)),aa_nat_int(X:fun_nat_int,suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)))),aTP_Lamm_ae_2(X:fun_nat_int,U:naT))**.
(d0,A,r1263,rw169242) 1045[0:Rew:962.0,844.0,161.0,844.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)),aa_nat_nat(W:fun_nat_nat,suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)))),aTP_Lamm_ad_2(W:fun_nat_nat,U:naT))**.
(d0,A,r940,rw123140) 1030[0:Rew:315.0,694.0,353.0,694.0,161.0,694.0,353.0,694.0,161.0,694.0,353.0,694.0,161.0,694.0] ||  -> equal(suc1(suc1(plus_plus_nat2(pred_numeral1(V:nuM),plus_plus_nat2(pred_numeral1(X3:nuM),U:naT)))),suc1(plus_plus_nat2(pred_numeral1(plus_plus_num2(V:nuM,X3:nuM)),U:naT)))**.
(d0,A,r1048,rw137288) 794[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(V:nuM)),plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(X3:nuM)),Z:inT)),plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM))),Z:inT))**.
(d0,A,r1681,rw218530) 776[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_nat2(zero_zero_nat,X7:naT)) -> pp(ord_less_nat2(U:naT,plus_plus_nat2(X7:naT,Y:naT)))*.
(d0,A,r2077,rw270010) 787[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,X7:naT),Y:naT))*.
(d0,A,r2063,rw268190) 786[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(X7:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X7:naT,U:naT),Y:naT))*.
(d0,A,r985,rw128050) 1041[0:Rew:180.0,790.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,U:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,suc1(U:naT))))**.
(d0,A,r980,rw127400) 1040[0:Rew:179.0,789.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,suc1(U:naT))))**.
(d0,A,r985,rw127065) 1036[0:Rew:180.0,759.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,suc1(U:naT)),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r980,rw126420) 1035[0:Rew:179.0,758.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,suc1(U:naT)),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r1358,rw173824) 699[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(X11:nuM,V:nuM))* -> pp(ord_less_eq_num2(X11:nuM,X3:nuM))*.
(d0,A,r2261,rw289408) 711[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_num2(X11:nuM,V:nuM))* -> pp(ord_less_num2(X11:nuM,X3:nuM))*.
(d0,A,r2229,rw285312) 708[0:Inp] || pp(ord_less_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(X11:nuM,V:nuM))* -> pp(ord_less_num2(X11:nuM,X3:nuM))*.
(d0,A,r1349,rw172672) 697[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(X10:booL,X4:booL))* -> pp(ord_less_eq_bool2(X10:booL,X5:booL))*.
(d0,A,r2252,rw288256) 709[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_bool2(X10:booL,X4:booL))* -> pp(ord_less_bool2(X10:booL,X5:booL))*.
(d0,A,r2220,rw284160) 706[0:Inp] || pp(ord_less_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(X10:booL,X4:booL))* -> pp(ord_less_bool2(X10:booL,X5:booL))*.
(d0,A,r2319,rw296832) 712[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_nat2(X7:naT,U:naT))* -> pp(ord_less_nat2(X7:naT,Y:naT))*.
(d0,A,r1353,rw173184) 698[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(X7:naT,U:naT))* -> pp(ord_less_eq_nat2(X7:naT,Y:naT))*.
(d0,A,r2256,rw288768) 710[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_nat2(X7:naT,U:naT))* -> pp(ord_less_nat2(X7:naT,Y:naT))*.
(d0,A,r2225,rw284800) 707[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(X7:naT,U:naT))* -> pp(ord_less_nat2(X7:naT,Y:naT))*.
(d0,A,r935,rw119680) 693[0:Inp] ||  -> equal(plus_plus_int2(numeral_numeral_int1(V:nuM),plus_plus_int2(numeral_numeral_int1(X3:nuM),Z:inT)),plus_plus_int2(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)),Z:inT))**.
(d0,A,r917,rw117376) 692[0:Inp] ||  -> equal(plus_plus_int2(numeral_numeral_int1(V:nuM),plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(X3:nuM)),Z:inT)),plus_plus_int2(neg_numeral_sub_int(V:nuM,X3:nuM),Z:inT))**.
(d0,A,r1025,rw131200) 695[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(V:nuM)),plus_plus_int2(numeral_numeral_int1(X3:nuM),Z:inT)),plus_plus_int2(neg_numeral_sub_int(X3:nuM,V:nuM),Z:inT))**.
(d0,A,r1448,rw183896) 630[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(U:naT,X7:naT)))* -> pp(ord_less_nat2(Y:naT,X7:naT)).
(d0,A,r1439,rw182753) 628[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(X7:naT,Y:naT)))* -> pp(ord_less_eq_nat2(U:naT,X7:naT)).
(d0,A,r1412,rw179324) 625[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(X7:naT,Y:naT)))* -> pp(ord_less_nat2(U:naT,X7:naT)).
(d0,A,r1178,rw149606) 619[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(U:naT,X7:naT)))* -> pp(ord_less_eq_nat2(Y:naT,X7:naT)).
(d0,A,r1448,rw183896) 631[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X7:naT,Y:naT)))*.
(d0,A,r1412,rw179324) 626[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> pp(ord_less_nat2(plus_plus_nat2(U:naT,X7:naT),plus_plus_nat2(Y:naT,X7:naT)))*.
(d0,A,r1281,rw162687) 621[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,X7:naT),plus_plus_nat2(Y:naT,X7:naT)))*.
(d0,A,r1178,rw149606) 620[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X7:naT,Y:naT)))*.
(d0,A,r2050,rw260350) 664[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_eq_int(zero_zero_int,X6:inT) -> ord_less_eq_int(Z:inT,plus_plus_int2(X1:inT,X6:inT))*.
(d0,A,r2032,rw258064) 662[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_eq_int(zero_zero_int,X6:inT) -> ord_less_eq_int(Z:inT,plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r1659,rw210693) 637[0:Inp] || ord_less_int(Z:inT,X1:inT) ord_less_eq_int(zero_zero_int,X6:inT) -> ord_less_int(Z:inT,plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r1677,rw212979) 638[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_int(zero_zero_int,X6:inT) -> ord_less_int(Z:inT,plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r2103,rw267081) 667[0:Inp] || ord_less_int(Z:inT,X1:inT) ord_less_int(zero_zero_int,X6:inT) -> ord_less_int(Z:inT,plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r2072,rw263144) 666[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_eq_int(X6:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(Z:inT,X6:inT),X1:inT)*.
(d0,A,r2059,rw261493) 665[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) ord_less_eq_int(X6:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(X6:inT,Z:inT),X1:inT)*.
(d0,A,r922,rw117094) 1025[0:Rew:446.0,557.0,474.0,557.0,268.0,557.0,268.0,557.0,268.0,557.0] ||  -> equal(plus_plus_int2(Z:inT,uminus_uminus_int(plus_plus_int2(X1:inT,X6:inT))),plus_plus_int2(Z:inT,uminus_uminus_int(plus_plus_int2(X6:inT,X1:inT))))*.
(d0,A,r922,rw117094) 1021[0:Rew:474.0,536.0,268.0,536.0,268.0,536.0] ||  -> equal(plus_plus_int2(Z:inT,plus_plus_int2(X1:inT,uminus_uminus_int(plus_plus_int2(Z:inT,X6:inT)))),plus_plus_int2(X1:inT,uminus_uminus_int(X6:inT)))**.
(d0,A,r922,rw117094) 1022[0:Rew:474.0,540.0,268.0,540.0,268.0,540.0] ||  -> equal(plus_plus_int2(Z:inT,plus_plus_int2(X1:inT,uminus_uminus_int(plus_plus_int2(X6:inT,X1:inT)))),plus_plus_int2(Z:inT,uminus_uminus_int(X6:inT)))**.
(d0,A,r1322,rw167894) 624[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(X3:nuM,V:nuM))* -> equal(X3:nuM,V:nuM).
(d0,A,r1317,rw167259) 623[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(Y:naT,U:naT))* -> equal(Y:naT,U:naT).
(d0,A,r985,rw125095) 1033[0:Rew:180.0,722.0,1017.0,722.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,U:naT),groups332228664at_int(X:fun_nat_int,set_ord_lessThan_nat(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(U:naT)))**.
(d0,A,r980,rw124460) 1032[0:Rew:179.0,721.0,1016.0,721.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,U:naT),groups1842438620at_nat(W:fun_nat_nat,set_ord_lessThan_nat(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(U:naT)))**.
(d0,A,r2638,rw332388) 598[0:Inp] pp(X4:booL) || pp(aa_num_bool(X22:fun_num_bool,V:nuM)) -> SkP5(V:nuM,X22:fun_num_bool,X4:booL)*.
(d0,A,r2593,rw326718) 595[0:Inp] pp(X4:booL) || pp(aa_num_bool(X22:fun_num_bool,V:nuM)) -> SkP2(X4:booL,V:nuM,X22:fun_num_bool)*.
(d0,A,r1070,rw134820) 593[0:Inp] pp(X4:booL) || pp(aa_bool_bool(X15:fun_bool_bool,X5:booL)) -> SkP0(X4:booL,X5:booL,X15:fun_bool_bool)*.
(d0,A,r1070,rw134820) 596[0:Inp] pp(X4:booL) || pp(aa_bool_bool(X15:fun_bool_bool,X5:booL)) -> SkP3(X5:booL,X15:fun_bool_bool,X4:booL)*.
(d0,A,r2625,rw330750) 597[0:Inp] pp(X4:booL) || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) -> SkP4(U:naT,X12:fun_nat_bool,X4:booL)*.
(d0,A,r2580,rw325080) 594[0:Inp] pp(X4:booL) || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) -> SkP1(X4:booL,U:naT,X12:fun_nat_bool)*.
(d0,A,r2607,rw328482) 1023[0:Rew:268.0,552.0] || equal(plus_plus_int2(Z:inT,uminus_uminus_int(X1:inT)),X6:inT)* -> equal(Z:inT,plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r2607,rw328482) 1024[0:Rew:268.0,553.1] || equal(Z:inT,plus_plus_int2(X1:inT,X6:inT))* -> equal(plus_plus_int2(Z:inT,uminus_uminus_int(X6:inT)),X1:inT)*.
(d0,A,r1564,rw197064) 583[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM))* -> pp(ord_less_num2(V:nuM,X3:nuM)) equal(V:nuM,X3:nuM).
(d0,A,r1560,rw196560) 582[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* -> pp(ord_less_nat2(U:naT,Y:naT)) equal(U:naT,Y:naT).
(d0,A,r3294,rw415044) 612[0:Inp] || pp(dvd_dvd_nat2(U:naT,Y:naT))* -> equal(times_times_nat2(U:naT,skf278(U:naT,Y:naT)),Y:naT)**.
(d0,A,r3173,rw399798) 604[0:Inp] || pp(dvd_dvd_nat2(U:naT,Y:naT))* -> equal(times_times_nat2(U:naT,skf268(U:naT,Y:naT)),Y:naT)**.
(d0,A,r2562,rw322812) 592[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* -> equal(plus_plus_nat2(U:naT,skf175(U:naT,Y:naT)),Y:naT)**.
(d0,A,r1668,rw210168) 585[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* -> equal(plus_plus_nat2(U:naT,skf159(U:naT,Y:naT)),Y:naT)**.
(d0,A,r1600,rw201600) 584[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* -> equal(plus_plus_nat2(U:naT,skf158(U:naT,Y:naT)),Y:naT)**.
(d0,A,r1214,rw152964) 586[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* -> equal(plus_plus_nat2(U:naT,skf160(U:naT,Y:naT)),Y:naT)**.
(d0,A,r913,rw114125) 472[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(X7:naT,Y:naT))* -> equal(U:naT,X7:naT).
(d0,A,r904,rw113000) 468[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(U:naT,X7:naT))* -> equal(Y:naT,X7:naT).
(d0,A,r2759,rw344875) 555[0:Inp] || equal(U:naT,Y:naT) -> equal(times_times_nat2(U:naT,X7:naT),times_times_nat2(Y:naT,X7:naT))*.
(d0,A,r2463,rw307875) 548[0:Inp] || equal(U:naT,Y:naT) -> equal(times_times_nat2(X7:naT,U:naT),times_times_nat2(X7:naT,Y:naT))*.
(d0,A,r913,rw114125) 473[0:Inp] || equal(U:naT,Y:naT) -> equal(plus_plus_nat2(U:naT,X7:naT),plus_plus_nat2(Y:naT,X7:naT))*.
(d0,A,r904,rw113000) 469[0:Inp] || equal(U:naT,Y:naT) -> equal(plus_plus_nat2(X7:naT,U:naT),plus_plus_nat2(X7:naT,Y:naT))*.
(d0,A,r2764,rw345500) 556[0:Inp] ||  -> equal(times_times_nat2(U:naT,times_times_nat2(Y:naT,X7:naT)),times_times_nat2(Y:naT,times_times_nat2(U:naT,X7:naT)))*.
(d0,A,r962,rw120250) 479[0:Inp] ||  -> equal(plus_plus_nat2(U:naT,plus_plus_nat2(Y:naT,X7:naT)),plus_plus_nat2(Y:naT,plus_plus_nat2(U:naT,X7:naT)))*.
(d0,A,r2346,rw293250) 538[0:Inp] ||  -> equal(times_times_nat2(times_times_nat2(U:naT,Y:naT),X7:naT),times_times_nat2(U:naT,times_times_nat2(Y:naT,X7:naT)))**.
(d0,A,r926,rw115750) 475[0:Inp] ||  -> equal(plus_plus_nat2(plus_plus_nat2(U:naT,Y:naT),X7:naT),plus_plus_nat2(U:naT,plus_plus_nat2(Y:naT,X7:naT)))**.
(d0,A,r2777,rw347125) 558[0:Inp] ||  -> equal(minus_minus_nat2(minus_minus_nat2(U:naT,Y:naT),X7:naT),minus_minus_nat2(U:naT,plus_plus_nat2(Y:naT,X7:naT)))**.
(d0,A,r2387,rw298375) 541[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(X7:naT,Y:naT)),minus_minus_nat2(U:naT,X7:naT))**.
(d0,A,r2086,rw260750) 537[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(U:naT,X7:naT)),minus_minus_nat2(Y:naT,X7:naT))**.
(d0,A,r1434,rw179250) 511[0:Inp] || ord_less_eq_int(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(X6:inT,X1:inT))* -> ord_less_eq_int(Z:inT,X6:inT).
(d0,A,r1174,rw146750) 495[0:Inp] || ord_less_eq_int(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(Z:inT,X6:inT))* -> ord_less_eq_int(X1:inT,X6:inT).
(d0,A,r1443,rw180375) 513[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(Z:inT,X6:inT))* -> ord_less_int(X1:inT,X6:inT).
(d0,A,r1407,rw175875) 508[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(X6:inT,X1:inT))* -> ord_less_int(Z:inT,X6:inT).
(d0,A,r908,rw113500) 470[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(X6:inT,X1:inT))* -> equal(Z:inT,X6:inT).
(d0,A,r900,rw112500) 466[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(Z:inT,X6:inT))* -> equal(X1:inT,X6:inT).
(d0,A,r1277,rw159625) 499[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) -> ord_less_eq_int(plus_plus_int2(Z:inT,X6:inT),plus_plus_int2(X1:inT,X6:inT))*.
(d0,A,r1174,rw146750) 496[0:Inp] || ord_less_eq_int(Z:inT,X1:inT) -> ord_less_eq_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r1443,rw180375) 514[0:Inp] || ord_less_int(Z:inT,X1:inT) -> ord_less_int(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r1407,rw175875) 509[0:Inp] || ord_less_int(Z:inT,X1:inT) -> ord_less_int(plus_plus_int2(Z:inT,X6:inT),plus_plus_int2(X1:inT,X6:inT))*.
(d0,A,r908,rw113500) 471[0:Inp] || equal(Z:inT,X1:inT) -> equal(plus_plus_int2(Z:inT,X6:inT),plus_plus_int2(X1:inT,X6:inT))*.
(d0,A,r900,rw112500) 467[0:Inp] || equal(Z:inT,X1:inT) -> equal(plus_plus_int2(X6:inT,Z:inT),plus_plus_int2(X6:inT,X1:inT))*.
(d0,A,r967,rw120875) 480[0:Inp] ||  -> equal(plus_plus_int2(Z:inT,plus_plus_int2(X1:inT,X6:inT)),plus_plus_int2(X1:inT,plus_plus_int2(Z:inT,X6:inT)))*.
(d0,A,r922,rw115250) 474[0:Inp] ||  -> equal(plus_plus_int2(plus_plus_int2(Z:inT,X1:inT),X6:inT),plus_plus_int2(Z:inT,plus_plus_int2(X1:inT,X6:inT)))**.
(d0,A,r2378,rw297250) 539[0:Inp] ||  -> pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_nat2(Y:naT,U:naT))* equal(Y:naT,U:naT).
(d0,A,r3397,rw421228) 455[0:Inp] ||  -> pp(ord_less_nat2(skf291(X12:fun_nat_bool,X32:fun_nat_bool,U:naT),U:naT))* SkP16(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r3393,rw420732) 454[0:Inp] ||  -> pp(ord_less_nat2(skf289(X12:fun_nat_bool,X32:fun_nat_bool,U:naT),U:naT))* SkP15(X12:fun_nat_bool,X32:fun_nat_bool).
(d0,A,r2638,rw327112) 430[0:Inp] ||  -> pp(X4:booL) pp(aa_num_bool(X22:fun_num_bool,V:nuM)) SkP5(V:nuM,X22:fun_num_bool,X4:booL)*.
(d0,A,r2593,rw321532) 427[0:Inp] ||  -> pp(X4:booL) pp(aa_num_bool(X22:fun_num_bool,V:nuM)) SkP2(X4:booL,V:nuM,X22:fun_num_bool)*.
(d0,A,r1070,rw132680) 425[0:Inp] ||  -> pp(X4:booL) pp(aa_bool_bool(X15:fun_bool_bool,X5:booL)) SkP0(X4:booL,X5:booL,X15:fun_bool_bool)*.
(d0,A,r1070,rw132680) 428[0:Inp] ||  -> pp(X4:booL) pp(aa_bool_bool(X15:fun_bool_bool,X5:booL)) SkP3(X5:booL,X15:fun_bool_bool,X4:booL)*.
(d0,A,r2625,rw325500) 429[0:Inp] ||  -> pp(X4:booL) pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) SkP4(U:naT,X12:fun_nat_bool,X4:booL)*.
(d0,A,r2580,rw319920) 426[0:Inp] ||  -> pp(X4:booL) pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) SkP1(X4:booL,U:naT,X12:fun_nat_bool)*.
(d0,A,r2310,rw261030) 819[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(comp_nat_int_nat(X:fun_nat_int,suC),set_or562006527an_nat(zero_zero_nat,U:naT))),groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(zero_zero_nat,suc1(U:naT))))**.
(d0,A,r2306,rw260578) 818[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(comp_nat_nat_nat(W:fun_nat_nat,suC),set_or562006527an_nat(zero_zero_nat,U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(zero_zero_nat,suc1(U:naT))))**.
(d0,A,r1996,rw223552) 798[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int)* ord_less_eq_int(X1:inT,zero_zero_int)* equal(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)** -> equal(X1:inT,zero_zero_int).
(d0,A,r1996,rw223552) 799[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int)* ord_less_eq_int(X1:inT,zero_zero_int)* equal(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)** -> equal(Z:inT,zero_zero_int).
(d0,A,r1964,rw219968) 796[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT)* ord_less_eq_int(zero_zero_int,X1:inT)* equal(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)** -> equal(X1:inT,zero_zero_int).
(d0,A,r1964,rw219968) 797[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT)* ord_less_eq_int(zero_zero_int,X1:inT)* equal(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)** -> equal(Z:inT,zero_zero_int).
(d0,A,r2207,rw244977) 1019[0:Rew:175.0,817.0,175.0,817.0] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(comp_nat_int_nat(X:fun_nat_int,suC),set_ord_atMost_nat(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r2202,rw244422) 1018[0:Rew:175.0,816.0,175.0,816.0] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(comp_nat_nat_nat(W:fun_nat_nat,suC),set_ord_atMost_nat(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r2499,rw274890) 762[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(aTP_Lamm_aa(X:fun_nat_int),set_ord_atMost_nat(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r2494,rw274340) 761[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(aTP_Lamm_a(W:fun_nat_nat),set_ord_atMost_nat(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(suc1(U:naT))))**.
(d0,A,r2935,rw319915) 726[0:Inp] ||  -> equal(plus_plus_int2(aa_nat_int(X:fun_nat_int,zero_zero_nat),groups332228664at_int(aTP_Lamm_aa(X:fun_nat_int),set_ord_lessThan_nat(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(U:naT)))**.
(d0,A,r2930,rw319370) 725[0:Inp] ||  -> equal(plus_plus_nat2(aa_nat_nat(W:fun_nat_nat,zero_zero_nat),groups1842438620at_nat(aTP_Lamm_a(W:fun_nat_nat),set_ord_lessThan_nat(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(U:naT)))**.
(d0,A,r3384,rw365472) 691[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(groups1842438620at_nat(W:fun_nat_nat,set_or562006527an_nat(Y:naT,suc1(U:naT))),zero_zero_nat)**.
(d0,A,r3379,rw364932) 690[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(groups332228664at_int(X:fun_nat_int,set_or562006527an_nat(Y:naT,suc1(U:naT))),zero_zero_int)**.
(d0,A,r1295,rw138565) 1034[0:MRR:743.0,106.0] pp(X4:booL) || pp(ord_less_eq_bool2(X4:booL,X5:booL))* -> pp(ord_less_eq_bool2(X10:booL,X5:booL))*.
(d0,A,r3132,rw335124) 603[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(groups1842438620at_nat(W:fun_nat_nat,set_or601162459st_nat(Y:naT,U:naT)),zero_zero_nat)**.
(d0,A,r3128,rw334696) 602[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> equal(groups332228664at_int(X:fun_nat_int,set_or601162459st_nat(Y:naT,U:naT)),zero_zero_int)**.
(d0,A,r1847,rw195782) 1029[0:MRR:661.2,189.0] || pp(ord_less_eq_bool2(X4:booL,X5:booL))* -> pp(X5:booL) pp(ord_less_eq_bool2(X4:booL,X10:booL))*.
(d0,A,r1416,rw150096) 1037[0:MRR:775.0,19.0] || pp(ord_less_nat2(U:naT,Y:naT)) -> pp(ord_less_nat2(U:naT,plus_plus_nat2(X7:naT,Y:naT)))*.
(d0,A,r1416,rw150096) 1038[0:MRR:783.0,19.0] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(U:naT,plus_plus_nat2(X7:naT,Y:naT)))*.
(d0,A,r1416,rw150096) 1039[0:MRR:785.0,19.0] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(U:naT,plus_plus_nat2(Y:naT,X7:naT)))*.
(d0,A,r3438,rw360990) 461[0:Inp] || member_num(V:nuM,set_or102655269st_num(X3:nuM,X11:nuM))* -> pp(ord_less_eq_num2(X3:nuM,V:nuM)).
(d0,A,r3438,rw360990) 462[0:Inp] || member_num(V:nuM,set_or102655269st_num(X3:nuM,X11:nuM))* -> pp(ord_less_eq_num2(V:nuM,X11:nuM)).
(d0,A,r3433,rw360465) 459[0:Inp] || member_bool(X4:booL,set_or842601420t_bool(X5:booL,X10:booL))* -> pp(ord_less_eq_bool2(X5:booL,X4:booL)).
(d0,A,r3433,rw360465) 460[0:Inp] || member_bool(X4:booL,set_or842601420t_bool(X5:booL,X10:booL))* -> pp(ord_less_eq_bool2(X4:booL,X10:booL)).
(d0,A,r3442,rw361410) 463[0:Inp] || member_nat(U:naT,set_or601162459st_nat(Y:naT,X7:naT))* -> pp(ord_less_eq_nat2(Y:naT,U:naT)).
(d0,A,r3442,rw361410) 464[0:Inp] || member_nat(U:naT,set_or601162459st_nat(Y:naT,X7:naT))* -> pp(ord_less_eq_nat2(U:naT,X7:naT)).
(d0,A,r3294,rw345870) 451[0:Inp] || equal(U:naT,times_times_nat2(Y:naT,X7:naT))* -> pp(dvd_dvd_nat2(Y:naT,U:naT))*.
(d0,A,r1600,rw168000) 398[0:Inp] || equal(U:naT,plus_plus_nat2(Y:naT,X7:naT))* -> pp(ord_less_eq_nat2(Y:naT,U:naT))*.
(d0,A,r2984,rw307352) 280[0:Inp] ||  -> pp(ord_less_eq_num2(V:nuM,X3:nuM))* SkP11(X11:nuM,X3:nuM,V:nuM)*.
(d0,A,r2984,rw307352) 281[0:Inp] ||  -> pp(ord_less_eq_num2(V:nuM,X3:nuM))* SkP11(X3:nuM,V:nuM,X11:nuM)*.
(d0,A,r2975,rw306425) 276[0:Inp] ||  -> pp(ord_less_eq_bool2(X4:booL,X5:booL))* SkP9(X10:booL,X5:booL,X4:booL)*.
(d0,A,r2975,rw306425) 277[0:Inp] ||  -> pp(ord_less_eq_bool2(X4:booL,X5:booL))* SkP9(X5:booL,X4:booL,X10:booL)*.
(d0,A,r2980,rw306940) 278[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,Y:naT))* SkP10(X7:naT,Y:naT,U:naT)*.
(d0,A,r2980,rw306940) 279[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,Y:naT))* SkP10(Y:naT,U:naT,X7:naT)*.
(d0,A,r1263,rw116196) 1011[0:Rew:18.0,770.1] || pp(aa_nat_bool(X12:fun_nat_bool,zero_zero_nat)) pp(aa_nat_bool(X12:fun_nat_bool,suc1(zero_zero_nat))) -> pp(aa_nat_bool(X12:fun_nat_bool,zero_n1672634641l_nat1(X4:booL)))*.
(d0,A,r2045,rw188140) 784[0:Inp] || pp(ord_less_eq_nat2(U:naT,zero_zero_nat)) pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,U:naT),zero_zero_nat))*.
(d0,A,r1263,rw114933) 1010[0:Rew:962.0,769.0,161.0,769.0] ||  -> equal(groups332228664at_int(aTP_Lamm_ae(X:fun_nat_int),set_ord_atMost_nat(U:naT)),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)))))**.
(d0,A,r1263,rw114933) 1009[0:Rew:962.0,768.0,161.0,768.0] ||  -> equal(groups1842438620at_nat(aTP_Lamm_ad(W:fun_nat_nat),set_ord_atMost_nat(U:naT)),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(suc1(times_times_nat2(suc1(suc1(zero_zero_nat)),U:naT)))))**.
(d0,A,r1263,rw113670) 1006[0:Rew:18.0,687.1] pp(X4:booL) || pp(aa_nat_bool(X12:fun_nat_bool,suc1(zero_zero_nat))) -> pp(aa_nat_bool(X12:fun_nat_bool,zero_n1672634641l_nat1(X4:booL)))*.
(d0,A,r1263,rw113670) 1005[0:Rew:18.0,686.2] pp(X4:booL) || pp(aa_nat_bool(X12:fun_nat_bool,zero_n1672634641l_nat1(X4:booL)))* -> pp(aa_nat_bool(X12:fun_nat_bool,suc1(zero_zero_nat))).
(d0,A,r1156,rw102884) 994[0:Rew:315.0,392.0,353.0,392.0,161.0,392.0,161.0,392.0,161.0,392.0] ||  -> equal(suc1(suc1(plus_plus_nat2(pred_numeral1(V:nuM),pred_numeral1(X3:nuM)))),suc1(pred_numeral1(plus_plus_num2(V:nuM,X3:nuM))))**.
(d0,A,r1928,rw171592) 659[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT) ord_less_eq_int(zero_zero_int,X1:inT) -> ord_less_eq_int(zero_zero_int,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r1749,rw155661) 642[0:Inp] || ord_less_int(zero_zero_int,Z:inT) ord_less_eq_int(zero_zero_int,X1:inT) -> ord_less_int(zero_zero_int,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r1650,rw146850) 636[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT) ord_less_int(zero_zero_int,X1:inT) -> ord_less_int(zero_zero_int,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r1910,rw169990) 658[0:Inp] || ord_less_int(zero_zero_int,Z:inT) ord_less_int(zero_zero_int,X1:inT) -> ord_less_int(zero_zero_int,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r2041,rw181649) 663[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int) ord_less_eq_int(X1:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)*.
(d0,A,r1708,rw152012) 640[0:Inp] || ord_less_int(Z:inT,zero_zero_int) ord_less_eq_int(X1:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)*.
(d0,A,r1686,rw150054) 639[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int) ord_less_int(X1:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)*.
(d0,A,r1973,rw175597) 660[0:Inp] || ord_less_int(Z:inT,zero_zero_int) ord_less_int(X1:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)*.
(d0,A,r3263,rw287144) 610[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,zero_n1672634641l_nat1(X4:booL)))* -> pp(X4:booL) pp(aa_nat_bool(X12:fun_nat_bool,zero_zero_nat)).
(d0,A,r3263,rw287144) 611[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,zero_zero_nat)) -> pp(X4:booL) pp(aa_nat_bool(X12:fun_nat_bool,zero_n1672634641l_nat1(X4:booL)))*.
(d0,A,r1129,rw99352) 577[0:Inp] || equal(numeral_numeral_int1(V:nuM),uminus_uminus_int(numeral_numeral_int1(X3:nuM))) -> ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)))*.
(d0,A,r1142,rw100496) 579[0:Inp] || equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),numeral_numeral_int1(X3:nuM)) -> ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)))*.
(d0,A,r1129,rw99352) 578[0:Inp] || ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)))* -> equal(numeral_numeral_int1(V:nuM),uminus_uminus_int(numeral_numeral_int1(X3:nuM))).
(d0,A,r1142,rw100496) 580[0:Inp] || ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)))* -> equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),numeral_numeral_int1(X3:nuM)).
(d0,A,r2157,rw189816) 591[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,X1:inT),zero_zero_int)* -> ord_less_int(X1:inT,zero_zero_int) ord_less_int(Z:inT,zero_zero_int).
(d0,A,r3303,rw290664) 613[0:Inp] || equal(times_times_nat2(U:naT,Y:naT),zero_zero_nat)** -> equal(U:naT,zero_zero_nat) equal(Y:naT,zero_zero_nat).
(d0,A,r2876,rw250212) 565[0:Inp] || pp(aa_num_bool(aa_num_fun_num_bool(X29:fun_num_fun_num_bool,skf258(X29:fun_num_fun_num_bool)),skf259(X29:fun_num_fun_num_bool)))* -> SkP8(X29:fun_num_fun_num_bool).
(d0,A,r2876,rw250212) 564[0:Inp] SkP8(X29:fun_num_fun_num_bool) ||  -> pp(aa_num_bool(aa_num_fun_num_bool(X29:fun_num_fun_num_bool,skf256(X29:fun_num_fun_num_bool)),skf257(X29:fun_num_fun_num_bool)))*.
(d0,A,r2872,rw249864) 563[0:Inp] || pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf254(X28:fun_nat_fun_nat_bool)),skf255(X28:fun_nat_fun_nat_bool)))* -> SkP7(X28:fun_nat_fun_nat_bool).
(d0,A,r1430,rw124410) 570[0:Inp] || pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf272(X28:fun_nat_fun_nat_bool)),skf273(X28:fun_nat_fun_nat_bool)))* -> SkP12(X28:fun_nat_fun_nat_bool).
(d0,A,r2872,rw249864) 562[0:Inp] SkP7(X28:fun_nat_fun_nat_bool) ||  -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X28:fun_nat_fun_nat_bool,skf252(X28:fun_nat_fun_nat_bool)),skf253(X28:fun_nat_fun_nat_bool)))*.
(d0,A,r1070,rw93090) 561[0:Inp] || pp(aa_bool_bool(aa_boo1142376798l_bool(X27:fun_bo1373903021l_bool,skf250(X27:fun_bo1373903021l_bool)),skf251(X27:fun_bo1373903021l_bool)))* -> SkP6(X27:fun_bo1373903021l_bool).
(d0,A,r1070,rw93090) 560[0:Inp] SkP6(X27:fun_bo1373903021l_bool) ||  -> pp(aa_bool_bool(aa_boo1142376798l_bool(X27:fun_bo1373903021l_bool,skf248(X27:fun_bo1373903021l_bool)),skf249(X27:fun_bo1373903021l_bool)))*.
(d0,A,r1551,rw134937) 571[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT)) pp(ord_less_nat2(U:naT,skf275(X12:fun_nat_bool)))* -> .
(d0,A,r2445,rw212715) 544[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_bool2(X5:booL,skf163(X4:booL)))* -> .
(d0,A,r2521,rw219327) 549[0:Inp] || pp(ord_less_eq_bool2(X4:booL,X5:booL)) pp(ord_less_bool2(skf172(X5:booL),X4:booL))* -> .
(d0,A,r1555,rw135285) 524[0:Inp] pp(X4:booL) pp(X5:booL) || pp(ord_less_bool2(X5:booL,X4:booL))* -> .
(d0,A,r2454,rw213498) 546[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_num2(X3:nuM,skf165(V:nuM)))* -> .
(d0,A,r2530,rw220110) 551[0:Inp] || pp(ord_less_eq_num2(V:nuM,X3:nuM)) pp(ord_less_num2(skf174(X3:nuM),V:nuM))* -> .
(d0,A,r1151,rw100137) 1002[0:Rew:391.0,581.0,446.0,581.0,268.0,581.0] ||  -> equal(uminus_uminus_int(numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM))),uminus_uminus_int(numeral_numeral_int1(plus_plus_num2(X3:nuM,V:nuM))))*.
(d0,A,r3429,rw298323) 574[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_nat2(Y:naT,skf295(U:naT)))* -> .
(d0,A,r2449,rw213063) 545[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_nat2(Y:naT,skf164(U:naT)))* -> .
(d0,A,r3370,rw293190) 573[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_nat2(skf286(Y:naT),U:naT))* -> .
(d0,A,r2526,rw219762) 550[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) pp(ord_less_nat2(skf173(Y:naT),U:naT))* -> .
(d0,A,r3559,rw309633) 575[0:Inp] || pp(ord_less_eq_nat2(suc1(U:naT),suc1(Y:naT)))* -> pp(ord_less_eq_nat2(U:naT,Y:naT)).
(d0,A,r1394,rw121278) 506[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,Y:naT),Y:naT))* -> pp(ord_less_eq_nat2(U:naT,zero_zero_nat)).
(d0,A,r1380,rw120060) 504[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,Y:naT),U:naT))* -> pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)).
(d0,A,r1578,rw137286) 526[0:Inp] || pp(ord_less_nat2(zero_zero_nat,U:naT)) -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(U:naT,Y:naT)))*.
(d0,A,r1528,rw132936) 523[0:Inp] || pp(ord_less_nat2(zero_zero_nat,U:naT)) -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(Y:naT,U:naT)))*.
(d0,A,r1578,rw137286) 525[0:Inp] || pp(ord_less_nat2(U:naT,plus_plus_nat2(Y:naT,U:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Y:naT)).
(d0,A,r1528,rw132936) 522[0:Inp] || pp(ord_less_nat2(U:naT,plus_plus_nat2(U:naT,Y:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Y:naT)).
(d0,A,r3559,rw309633) 576[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(suc1(U:naT),suc1(Y:naT)))*.
(d0,A,r1394,rw121278) 507[0:Inp] || pp(ord_less_eq_nat2(U:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(U:naT,Y:naT),Y:naT))*.
(d0,A,r1380,rw120060) 505[0:Inp] || pp(ord_less_eq_nat2(U:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,U:naT),Y:naT))*.
(d0,A,r1551,rw133386) 414[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,skf162(X12:fun_nat_bool)))* -> pp(aa_nat_bool(X12:fun_nat_bool,U:naT))*.
(d0,A,r1551,rw133386) 413[0:Inp] || pp(ord_less_nat2(U:naT,skf162(X12:fun_nat_bool)))* -> pp(aa_nat_bool(X12:fun_nat_bool,U:naT)).
(d0,A,r1551,rw133386) 449[0:Inp] || pp(aa_nat_bool(X12:fun_nat_bool,U:naT))* -> pp(aa_nat_bool(X12:fun_nat_bool,skf275(X12:fun_nat_bool)))*.
(d0,A,r1484,rw127624) 395[0:Inp] || pp(ord_less_bool2(X4:booL,X5:booL)) pp(ord_less_eq_bool2(X5:booL,X4:booL))* -> .
(d0,A,r2121,rw182406) 408[0:Inp] pp(X4:booL) || pp(ord_less_eq_bool2(X4:booL,X5:booL))* -> pp(X5:booL).
(d0,A,r2467,rw212162) 416[0:Inp] || pp(ord_less_bool2(X4:booL,skf166(X5:booL)))* -> pp(ord_less_eq_bool2(X4:booL,X5:booL)).
(d0,A,r2503,rw215258) 419[0:Inp] || pp(ord_less_bool2(skf169(X4:booL),X5:booL))* -> pp(ord_less_eq_bool2(X4:booL,X5:booL)).
(d0,A,r1493,rw128398) 397[0:Inp] || pp(ord_less_num2(V:nuM,X3:nuM)) pp(ord_less_eq_num2(X3:nuM,V:nuM))* -> .
(d0,A,r2476,rw212936) 418[0:Inp] || pp(ord_less_num2(V:nuM,skf168(X3:nuM)))* -> pp(ord_less_eq_num2(V:nuM,X3:nuM)).
(d0,A,r2512,rw216032) 421[0:Inp] || pp(ord_less_num2(skf171(V:nuM),X3:nuM))* -> pp(ord_less_eq_num2(V:nuM,X3:nuM)).
(d0,A,r1151,rw98986) 391[0:Inp] ||  -> equal(plus_plus_int2(numeral_numeral_int1(V:nuM),numeral_numeral_int1(X3:nuM)),numeral_numeral_int1(plus_plus_num2(V:nuM,X3:nuM)))**.
(d0,A,r2890,rw248540) 992[0:Rew:268.0,385.0] ||  -> equal(plus_plus_int2(numeral_numeral_int1(V:nuM),uminus_uminus_int(numeral_numeral_int1(X3:nuM))),neg_numeral_sub_int(V:nuM,X3:nuM))**.
(d0,A,r1286,rw110596) 394[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int(numeral_numeral_int1(V:nuM)),numeral_numeral_int1(X3:nuM)),neg_numeral_sub_int(X3:nuM,V:nuM))**.
(d0,A,r2998,rw257828) 442[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),zero_zero_int)** -> equal(Z:inT,uminus_uminus_int(X1:inT)).
(d0,A,r2885,rw248110) 436[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),zero_zero_int)** -> equal(uminus_uminus_int(Z:inT),X1:inT).
(d0,A,r2998,rw257828) 441[0:Inp] || equal(Z:inT,uminus_uminus_int(X1:inT)) -> equal(plus_plus_int2(Z:inT,X1:inT),zero_zero_int)**.
(d0,A,r2921,rw251206) 438[0:Inp] || equal(Z:inT,uminus_uminus_int(X1:inT)) -> equal(plus_plus_int2(X1:inT,Z:inT),zero_zero_int)**.
(d0,A,r1097,rw94342) 390[0:Inp] neg_nu841131049um_int(Z:inT) neg_nu841131049um_int(X1:inT) ||  -> neg_nu841131049um_int(plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r2890,rw248540) 980[0:Rew:268.0,287.0,268.0,287.0] ||  -> equal(uminus_uminus_int(plus_plus_int2(Z:inT,uminus_uminus_int(X1:inT))),plus_plus_int2(X1:inT,uminus_uminus_int(Z:inT)))**.
(d0,A,r3092,rw265912) 446[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int(Z:inT),uminus_uminus_int(X1:inT)),uminus_uminus_int(plus_plus_int2(X1:inT,Z:inT)))**.
(d0,A,r2427,rw208722) 415[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* pp(ord_less_nat2(Y:naT,U:naT))* -> .
(d0,A,r1488,rw127968) 396[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) pp(ord_less_eq_nat2(Y:naT,U:naT))* -> .
(d0,A,r3424,rw294464) 458[0:Inp] || pp(ord_less_nat2(U:naT,skf294(Y:naT)))* -> pp(ord_less_nat2(U:naT,Y:naT)).
(d0,A,r2472,rw212592) 417[0:Inp] || pp(ord_less_nat2(U:naT,skf167(Y:naT)))* -> pp(ord_less_eq_nat2(U:naT,Y:naT)).
(d0,A,r3388,rw291368) 453[0:Inp] || pp(ord_less_nat2(skf287(U:naT),Y:naT))* -> pp(ord_less_nat2(U:naT,Y:naT)).
(d0,A,r2508,rw215688) 420[0:Inp] || pp(ord_less_nat2(skf170(U:naT),Y:naT))* -> pp(ord_less_eq_nat2(U:naT,Y:naT)).
(d0,A,r3285,rw282510) 450[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(suc1(U:naT),Y:naT))*.
(d0,A,r3361,rw289046) 452[0:Inp] || pp(ord_less_eq_nat2(U:naT,Y:naT))* -> equal(minus_minus_nat2(U:naT,Y:naT),zero_zero_nat).
(d0,A,r3415,rw293690) 456[0:Inp] ||  -> equal(plus_plus_int2(semiri501196819t_int1(U:naT),semiri501196819t_int1(Y:naT)),semiri501196819t_int1(plus_plus_nat2(U:naT,Y:naT)))**.
(d0,A,r2935,rw252410) 1017[0:Rew:726.0,767.0] ||  -> equal(groups332228664at_int(X:fun_nat_int,set_ord_lessThan_nat(suc1(U:naT))),groups332228664at_int(X:fun_nat_int,set_ord_atMost_nat(U:naT)))**.
(d0,A,r2930,rw251980) 1016[0:Rew:725.0,766.0] ||  -> equal(groups1842438620at_nat(W:fun_nat_nat,set_ord_lessThan_nat(suc1(U:naT))),groups1842438620at_nat(W:fun_nat_nat,set_ord_atMost_nat(U:naT)))**.
(d0,A,r1555,rw132175) 346[0:Inp] || pp(ord_less_bool2(X4:booL,X5:booL))* -> pp(X5:booL) pp(X4:booL).
(d0,A,r1555,rw132175) 345[0:Inp] || pp(ord_less_bool2(X4:booL,X5:booL)) -> pp(ord_less_eq_bool2(X4:booL,X5:booL))*.
(d0,A,r1555,rw132175) 1031[0:MRR:701.1,189.1] pp(X4:booL) ||  -> pp(X5:booL) pp(ord_less_bool2(X5:booL,X4:booL))*.
(d0,A,r1564,rw132940) 350[0:Inp] || pp(ord_less_num2(V:nuM,X3:nuM))* equal(V:nuM,X3:nuM) -> .
(d0,A,r1564,rw132940) 349[0:Inp] || pp(ord_less_num2(V:nuM,X3:nuM)) -> pp(ord_less_eq_num2(V:nuM,X3:nuM))*.
(d0,A,r1389,rw118065) 334[0:Inp] || ord_less_eq_int(plus_plus_int2(Z:inT,X1:inT),X1:inT)* -> ord_less_eq_int(Z:inT,zero_zero_int).
(d0,A,r1376,rw116960) 330[0:Inp] || ord_less_eq_int(plus_plus_int2(Z:inT,X1:inT),Z:inT)* -> ord_less_eq_int(X1:inT,zero_zero_int).
(d0,A,r1515,rw128775) 339[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,X1:inT),X1:inT)* -> ord_less_int(Z:inT,zero_zero_int).
(d0,A,r1501,rw127585) 337[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,X1:inT),Z:inT)* -> ord_less_int(X1:inT,zero_zero_int).
(d0,A,r1111,rw94435) 301[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),X1:inT)** -> equal(Z:inT,zero_zero_int).
(d0,A,r1088,rw92480) 293[0:Inp] || equal(plus_plus_int2(Z:inT,X1:inT),Z:inT)** -> equal(X1:inT,zero_zero_int).
(d0,A,r1340,rw113900) 329[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT) -> ord_less_eq_int(X1:inT,plus_plus_int2(Z:inT,X1:inT))*.
(d0,A,r1326,rw112710) 327[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT) -> ord_less_eq_int(X1:inT,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r1573,rw133705) 352[0:Inp] || ord_less_int(zero_zero_int,Z:inT) -> ord_less_int(X1:inT,plus_plus_int2(Z:inT,X1:inT))*.
(d0,A,r1524,rw129540) 342[0:Inp] || ord_less_int(zero_zero_int,Z:inT) -> ord_less_int(X1:inT,plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r1340,rw113900) 328[0:Inp] || ord_less_eq_int(Z:inT,plus_plus_int2(X1:inT,Z:inT))* -> ord_less_eq_int(zero_zero_int,X1:inT).
(d0,A,r1326,rw112710) 326[0:Inp] || ord_less_eq_int(Z:inT,plus_plus_int2(Z:inT,X1:inT))* -> ord_less_eq_int(zero_zero_int,X1:inT).
(d0,A,r1573,rw133705) 351[0:Inp] || ord_less_int(Z:inT,plus_plus_int2(X1:inT,Z:inT))* -> ord_less_int(zero_zero_int,X1:inT).
(d0,A,r1524,rw129540) 341[0:Inp] || ord_less_int(Z:inT,plus_plus_int2(Z:inT,X1:inT))* -> ord_less_int(zero_zero_int,X1:inT).
(d0,A,r1389,rw118065) 335[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(Z:inT,X1:inT),X1:inT)*.
(d0,A,r1376,rw116960) 331[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(X1:inT,Z:inT),X1:inT)*.
(d0,A,r1515,rw128775) 340[0:Inp] || ord_less_int(Z:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(Z:inT,X1:inT),X1:inT)*.
(d0,A,r1501,rw127585) 338[0:Inp] || ord_less_int(Z:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(X1:inT,Z:inT),X1:inT)*.
(d0,A,r1111,rw94435) 302[0:Inp] || equal(Z:inT,zero_zero_int) -> equal(plus_plus_int2(Z:inT,X1:inT),X1:inT)**.
(d0,A,r1088,rw92480) 294[0:Inp] || equal(Z:inT,zero_zero_int) -> equal(plus_plus_int2(X1:inT,Z:inT),X1:inT)**.
(d0,A,r3092,rw262820) 996[0:Rew:446.0,447.0] ||  -> equal(uminus_uminus_int(plus_plus_int2(Z:inT,X1:inT)),uminus_uminus_int(plus_plus_int2(X1:inT,Z:inT)))*.
(d0,A,r3375,rw286875) 384[0:Inp] ||  -> equal(times_times_int(Z:inT,uminus_uminus_int(X1:inT)),uminus_uminus_int(times_times_int(Z:inT,X1:inT)))**.
(d0,A,r3330,rw283050) 382[0:Inp] ||  -> equal(times_times_int(uminus_uminus_int(Z:inT),X1:inT),uminus_uminus_int(times_times_int(Z:inT,X1:inT)))**.
(d0,A,r1560,rw132600) 348[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT))* equal(U:naT,Y:naT) -> .
(d0,A,r1560,rw132600) 347[0:Inp] || pp(ord_less_nat2(U:naT,Y:naT)) -> pp(ord_less_eq_nat2(U:naT,Y:naT))*.
(d0,A,r3564,rw302940) 388[0:Inp] || equal(suc1(U:naT),suc1(Y:naT))* -> equal(U:naT,Y:naT).
(d0,A,r1115,rw94775) 303[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),Y:naT)** -> equal(U:naT,zero_zero_nat).
(d0,A,r1093,rw92905) 295[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),U:naT)** -> equal(Y:naT,zero_zero_nat).
(d0,A,r3564,rw302940) 389[0:Inp] || equal(U:naT,Y:naT) -> equal(suc1(U:naT),suc1(Y:naT))*.
(d0,A,r1115,rw94775) 304[0:Inp] || equal(U:naT,zero_zero_nat) -> equal(plus_plus_nat2(U:naT,Y:naT),Y:naT)**.
(d0,A,r1093,rw92905) 296[0:Inp] || equal(U:naT,zero_zero_nat) -> equal(plus_plus_nat2(Y:naT,U:naT),Y:naT)**.
(d0,A,r1200,rw102000) 315[0:Inp] ||  -> equal(plus_plus_nat2(U:naT,suc1(Y:naT)),suc1(plus_plus_nat2(U:naT,Y:naT)))**.
(d0,A,r1645,rw139825) 353[0:Inp] ||  -> equal(plus_plus_nat2(suc1(U:naT),Y:naT),suc1(plus_plus_nat2(U:naT,Y:naT)))**.
(d0,A,r2768,rw235280) 375[0:Inp] ||  -> equal(minus_minus_nat2(suc1(U:naT),suc1(Y:naT)),minus_minus_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw85000) 982[0:Rew:292.0,207.0] ||  -> equal(aa_nat_int(aTP_Lamm_aa(X:fun_nat_int),U:naT),aa_nat_int(X:fun_nat_int,suc1(U:naT)))**.
(d0,A,r1000,rw85000) 981[0:Rew:291.0,206.0] ||  -> equal(aa_nat_nat(aTP_Lamm_a(W:fun_nat_nat),U:naT),aa_nat_nat(W:fun_nat_nat,suc1(U:naT)))**.
(d0,A,r1870,rw157080) 235[0:Inp] ||  -> pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_eq_bool2(X5:booL,X4:booL))*.
(d0,A,r1484,rw124656) 228[0:Inp] ||  -> pp(ord_less_eq_bool2(X4:booL,X5:booL))* pp(ord_less_bool2(X5:booL,X4:booL)).
(d0,A,r1000,rw84000) 222[0:Inp] ||  -> equal(aa_bool_bool(ord_less_bool1(X4:booL),X5:booL),ord_less_bool2(X4:booL,X5:booL))**.
(d0,A,r1000,rw84000) 225[0:Inp] ||  -> equal(aa_bool_bool(ord_less_eq_bool1(X4:booL),X5:booL),ord_less_eq_bool2(X4:booL,X5:booL))**.
(d0,A,r1879,rw157836) 240[0:Inp] || equal(V:nuM,X3:nuM) -> pp(ord_less_eq_num2(X3:nuM,V:nuM))*.
(d0,A,r1879,rw157836) 239[0:Inp] ||  -> pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_eq_num2(X3:nuM,V:nuM))*.
(d0,A,r1493,rw125412) 230[0:Inp] ||  -> pp(ord_less_eq_num2(V:nuM,X3:nuM))* pp(ord_less_num2(X3:nuM,V:nuM)).
(d0,A,r1000,rw84000) 217[0:Inp] ||  -> equal(aa_num_num(plus_plus_num(V:nuM),X3:nuM),plus_plus_num2(V:nuM,X3:nuM))**.
(d0,A,r1000,rw84000) 221[0:Inp] ||  -> equal(aa_num_bool(ord_less_num1(V:nuM),X3:nuM),ord_less_num2(V:nuM,X3:nuM))**.
(d0,A,r1000,rw84000) 224[0:Inp] ||  -> equal(aa_num_bool(ord_less_eq_num1(V:nuM),X3:nuM),ord_less_eq_num2(V:nuM,X3:nuM))**.
(d0,A,r1000,rw84000) 212[0:Inp] ||  -> equal(aa_nat_bool(monoid_nat(X2:fun_nat_fun_nat_nat),U:naT),monoid_nat2(X2:fun_nat_fun_nat_nat,U:naT))**.
(d0,A,r1000,rw84000) 213[0:Inp] ||  -> equal(aa_nat_bool(comm_monoid_nat(X2:fun_nat_fun_nat_nat),U:naT),comm_monoid_nat2(X2:fun_nat_fun_nat_nat,U:naT))**.
(d0,A,r2890,rw242760) 268[0:Inp] ||  -> equal(minus_minus_int(Z:inT,X1:inT),plus_plus_int2(Z:inT,uminus_uminus_int(X1:inT)))**.
(d0,A,r985,rw82740) 975[0:Rew:268.0,972.0] ||  -> equal(plus_plus_int2(Z:inT,plus_plus_int2(X1:inT,uminus_uminus_int(Z:inT))),X1:inT)**.
(d0,A,r3101,rw260484) 283[0:Inp] ||  -> equal(plus_plus_int2(Z:inT,plus_plus_int2(uminus_uminus_int(Z:inT),X1:inT)),X1:inT)**.
(d0,A,r1000,rw84000) 974[0:Rew:204.0,209.0] ||  -> equal(aa_int_int(aTP_Lamm_ac(Z:inT),X1:inT),plus_plus_int2(X1:inT,Z:inT))**.
(d0,A,r1000,rw84000) 215[0:Inp] ||  -> equal(aa_int_int(plus_plus_int1(Z:inT),X1:inT),plus_plus_int2(Z:inT,X1:inT))**.
(d0,A,r985,rw82740) 984[0:Rew:180.0,976.0] ||  -> equal(plus_plus_int2(uminus_uminus_int(Z:inT),plus_plus_int2(X1:inT,Z:inT)),X1:inT)**.
(d0,A,r1874,rw157416) 238[0:Inp] || equal(U:naT,Y:naT) -> pp(ord_less_eq_nat2(Y:naT,U:naT))*.
(d0,A,r1874,rw157416) 237[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_eq_nat2(Y:naT,U:naT))*.
(d0,A,r1488,rw124992) 229[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,Y:naT))* pp(ord_less_nat2(Y:naT,U:naT)).
(d0,A,r1000,rw84000) 973[0:Rew:203.0,208.0] ||  -> equal(aa_nat_nat(aTP_Lamm_ab(U:naT),Y:naT),plus_plus_nat2(Y:naT,U:naT))**.
(d0,A,r1000,rw84000) 214[0:Inp] ||  -> equal(aa_nat_bool(dvd_dvd_nat1(U:naT),Y:naT),dvd_dvd_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw84000) 216[0:Inp] ||  -> equal(aa_nat_nat(plus_plus_nat1(U:naT),Y:naT),plus_plus_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw84000) 218[0:Inp] ||  -> equal(aa_nat_nat(minus_minus_nat(U:naT),Y:naT),minus_minus_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw84000) 219[0:Inp] ||  -> equal(aa_nat_nat(times_times_nat(U:naT),Y:naT),times_times_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw84000) 220[0:Inp] ||  -> equal(aa_nat_bool(ord_less_nat1(U:naT),Y:naT),ord_less_nat2(U:naT,Y:naT))**.
(d0,A,r1000,rw84000) 223[0:Inp] ||  -> equal(aa_nat_bool(ord_less_eq_nat1(U:naT),Y:naT),ord_less_eq_nat2(U:naT,Y:naT))**.
(d0,A,r3595,rw301980) 292[0:Inp] ||  -> equal(aTP_Lamm_aa_2(X:fun_nat_int,U:naT),aa_nat_int(X:fun_nat_int,suc1(U:naT)))**.
(d0,A,r1000,rw84000) 211[0:Inp] ||  -> equal(aa_nat_int(aTP_Lamm_ae(X:fun_nat_int),U:naT),aTP_Lamm_ae_2(X:fun_nat_int,U:naT))**.
(d0,A,r3591,rw301644) 291[0:Inp] ||  -> equal(aTP_Lamm_a_2(W:fun_nat_nat,U:naT),aa_nat_nat(W:fun_nat_nat,suc1(U:naT)))**.
(d0,A,r1000,rw84000) 210[0:Inp] ||  -> equal(aa_nat_nat(aTP_Lamm_ad(W:fun_nat_nat),U:naT),aTP_Lamm_ad_2(W:fun_nat_nat,U:naT))**.
(d0,A,r3334,rw276722) 200[0:Inp] ||  -> pp(ord_less_nat2(U:naT,skf281(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))*.
(d0,A,r3334,rw276722) 201[0:Inp] ||  -> pp(ord_less_nat2(U:naT,skf283(X12:fun_nat_bool,X32:fun_nat_bool,U:naT)))*.
(d0,A,r985,rw81755) 180[0:Inp] ||  -> equal(plus_plus_int2(Z:inT,X1:inT),plus_plus_int2(X1:inT,Z:inT))*.
(d0,A,r3586,rw297638) 204[0:Inp] ||  -> equal(aTP_Lamm_ac_2(Z:inT,X1:inT),plus_plus_int2(X1:inT,Z:inT))**.
(d0,A,r1758,rw145914) 188[0:Inp] ||  -> equal(times_times_nat2(U:naT,Y:naT),times_times_nat2(Y:naT,U:naT))*.
(d0,A,r980,rw81340) 179[0:Inp] ||  -> equal(plus_plus_nat2(U:naT,Y:naT),plus_plus_nat2(Y:naT,U:naT))*.
(d0,A,r3582,rw297306) 203[0:Inp] ||  -> equal(aTP_Lamm_ab_2(U:naT,Y:naT),plus_plus_nat2(Y:naT,U:naT))**.
(d0,A,r1632,rw135456) 187[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(U:naT,Y:naT),Y:naT),U:naT)**.
(d0,A,r1537,rw127571) 185[0:Inp] ||  -> equal(minus_minus_nat2(plus_plus_nat2(U:naT,Y:naT),U:naT),Y:naT)**.
(d0,A,r1416,rw96288) 1012[0:MRR:774.1,19.0] || pp(ord_less_nat2(zero_zero_nat,U:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(U:naT,Y:naT)))*.
(d0,A,r1416,rw96288) 1013[0:MRR:779.0,19.0] || pp(ord_less_nat2(zero_zero_nat,U:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(Y:naT,U:naT)))*.
(d0,A,r980,rw65660) 995[0:Rew:994.0,989.0] ||  -> equal(suc1(pred_numeral1(plus_plus_num2(V:nuM,V:nuM))),suc1(pred_numeral1(bit01(V:nuM))))**.
(d0,A,r1308,rw86328) 324[0:Inp] || ord_less_eq_int(plus_plus_int2(Z:inT,Z:inT),zero_zero_int)* -> ord_less_eq_int(Z:inT,zero_zero_int).
(d0,A,r1542,rw101772) 343[0:Inp] || ord_less_int(plus_plus_int2(Z:inT,Z:inT),zero_zero_int)* -> ord_less_int(Z:inT,zero_zero_int).
(d0,A,r1160,rw76560) 313[0:Inp] || equal(plus_plus_int2(Z:inT,Z:inT),zero_zero_int)** -> equal(Z:inT,zero_zero_int).
(d0,A,r1290,rw85140) 322[0:Inp] || ord_less_eq_int(zero_zero_int,plus_plus_int2(Z:inT,Z:inT))* -> ord_less_eq_int(zero_zero_int,Z:inT).
(d0,A,r1385,rw91410) 332[0:Inp] || ord_less_int(zero_zero_int,plus_plus_int2(Z:inT,Z:inT))* -> ord_less_int(zero_zero_int,Z:inT).
(d0,A,r1290,rw85140) 323[0:Inp] || ord_less_eq_int(zero_zero_int,Z:inT) -> ord_less_eq_int(zero_zero_int,plus_plus_int2(Z:inT,Z:inT))*.
(d0,A,r1385,rw91410) 333[0:Inp] || ord_less_int(zero_zero_int,Z:inT) -> ord_less_int(zero_zero_int,plus_plus_int2(Z:inT,Z:inT))*.
(d0,A,r1308,rw86328) 325[0:Inp] || ord_less_eq_int(Z:inT,zero_zero_int) -> ord_less_eq_int(plus_plus_int2(Z:inT,Z:inT),zero_zero_int)*.
(d0,A,r1542,rw101772) 344[0:Inp] || ord_less_int(Z:inT,zero_zero_int) -> ord_less_int(plus_plus_int2(Z:inT,Z:inT),zero_zero_int)*.
(d0,A,r1120,rw73920) 305[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),zero_zero_nat)** -> equal(U:naT,zero_zero_nat).
(d0,A,r1120,rw73920) 306[0:Inp] || equal(plus_plus_nat2(U:naT,Y:naT),zero_zero_nat)** -> equal(Y:naT,zero_zero_nat).
(d0,A,r3303,rw217998) 378[0:Inp] || equal(U:naT,zero_zero_nat) -> equal(times_times_nat2(U:naT,Y:naT),zero_zero_nat)**.
(d0,A,r3303,rw217998) 379[0:Inp] || equal(U:naT,zero_zero_nat) -> equal(times_times_nat2(Y:naT,U:naT),zero_zero_nat)**.
(d0,A,r1151,rw74815) 993[0:Rew:391.0,373.0] ||  -> equal(numeral_numeral_int1(plus_plus_num2(V:nuM,V:nuM)),numeral_numeral_int1(bit01(V:nuM)))**.
(d0,A,r1847,rw118208) 189[0:Inp] pp(X4:booL) ||  -> pp(ord_less_eq_bool2(X5:booL,X4:booL))*.
(d0,A,r3177,rw203328) 199[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(U:naT,Y:naT),Y:naT))* -> .
(d0,A,r1506,rw96384) 1001[0:MRR:518.1,56.0] || pp(ord_less_nat2(plus_plus_nat2(U:naT,Y:naT),U:naT))* -> .
(d0,A,r1847,rw116361) 106[0:Inp] ||  -> pp(X4:booL) pp(ord_less_eq_bool2(X4:booL,X5:booL))*.
(d0,A,r1052,rw66276) 104[0:Inp] ||  -> equal(neg_numeral_dbl_int(Z:inT),plus_plus_int2(Z:inT,Z:inT))**.
(d0,A,r3155,rw198765) 155[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,plus_plus_nat2(Y:naT,U:naT)))*.
(d0,A,r1331,rw83853) 999[0:MRR:501.0,19.0] ||  -> pp(ord_less_eq_nat2(U:naT,plus_plus_nat2(U:naT,Y:naT)))*.
(d0,A,r1187,rw58163) 497[0:Inp] || equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),one_one_int) -> ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(onE,V:nuM)))*.
(d0,A,r1187,rw58163) 498[0:Inp] || ring_1_iszero_int(numeral_numeral_int1(plus_plus_num2(onE,V:nuM)))* -> equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),one_one_int).
(d0,A,r1147,rw55056) 968[0:Rew:149.0,493.1] || equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),one_one_int)** -> ring_1_iszero_int(numeral_numeral_int1(inc1(V:nuM))).
(d0,A,r1147,rw55056) 969[0:Rew:149.0,494.0] || ring_1_iszero_int(numeral_numeral_int1(inc1(V:nuM))) -> equal(uminus_uminus_int(numeral_numeral_int1(V:nuM)),one_one_int)**.
(d0,A,r1430,rw67210) 336[0:Inp] || pp(ord_less_nat2(zero_zero_nat,U:naT))* equal(U:naT,zero_zero_nat) -> .
(d0,A,r1371,rw63066) 227[0:Inp] || equal(U:naT,zero_zero_nat) -> pp(ord_less_eq_nat2(U:naT,zero_zero_nat))*.
(d0,A,r1371,rw63066) 226[0:Inp] || pp(ord_less_eq_nat2(U:naT,zero_zero_nat))* -> equal(U:naT,zero_zero_nat).
(d0,A,r3231,rw148626) 285[0:Inp] ||  -> equal(plus_plus_int2(one_one_int,semiri501196819t_int1(U:naT)),semiri501196819t_int1(suc1(U:naT)))**.
(d0,A,r1000,rw45000) 964[0:Rew:161.0,96.0] ||  -> equal(aa_num_nat(numeral_numeral_nat,V:nuM),suc1(pred_numeral1(V:nuM)))**.
(d0,A,r1214,rw54630) 181[0:Inp] || equal(zero_zero_nat,U:naT)* -> equal(U:naT,zero_zero_nat).
(d0,A,r1430,rw64350) 183[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,U:naT))* equal(U:naT,zero_zero_nat).
(d0,A,r2876,rw126544) 148[0:Inp] ||  -> pp(ord_less_eq_num2(skf258(X29:fun_num_fun_num_bool),skf259(X29:fun_num_fun_num_bool)))*.
(d0,A,r2872,rw126368) 147[0:Inp] ||  -> pp(ord_less_eq_nat2(skf254(X28:fun_nat_fun_nat_bool),skf255(X28:fun_nat_fun_nat_bool)))*.
(d0,A,r1430,rw62920) 156[0:Inp] ||  -> pp(ord_less_nat2(skf272(X28:fun_nat_fun_nat_bool),skf273(X28:fun_nat_fun_nat_bool)))*.
(d0,A,r1070,rw47080) 146[0:Inp] ||  -> pp(ord_less_eq_bool2(skf250(X27:fun_bo1373903021l_bool),skf251(X27:fun_bo1373903021l_bool)))*.
(d0,A,r3168,rw139392) 173[0:Inp] ||  -> pp(ord_less_eq_num2(skf316(X25:fun_num_num),skf317(X25:fun_num_num)))*.
(d0,A,r2746,rw120824) 145[0:Inp] ||  -> pp(ord_less_eq_num2(skf246(X25:fun_num_num),skf247(X25:fun_num_num)))*.
(d0,A,r2705,rw119020) 136[0:Inp] ||  -> pp(ord_less_eq_num2(skf228(X25:fun_num_num),skf229(X25:fun_num_num)))*.
(d0,A,r2647,rw116468) 127[0:Inp] ||  -> pp(ord_less_eq_num2(skf210(X25:fun_num_num),skf211(X25:fun_num_num)))*.
(d0,A,r2602,rw114488) 118[0:Inp] ||  -> pp(ord_less_eq_num2(skf192(X25:fun_num_num),skf193(X25:fun_num_num)))*.
(d0,A,r3168,rw139392) 172[0:Inp] ||  -> pp(ord_less_eq_num2(skf314(X24:fun_num_nat),skf315(X24:fun_num_nat)))*.
(d0,A,r2732,rw120208) 142[0:Inp] ||  -> pp(ord_less_eq_num2(skf240(X24:fun_num_nat),skf241(X24:fun_num_nat)))*.
(d0,A,r2701,rw118844) 135[0:Inp] ||  -> pp(ord_less_eq_num2(skf226(X24:fun_num_nat),skf227(X24:fun_num_nat)))*.
(d0,A,r2643,rw116292) 126[0:Inp] ||  -> pp(ord_less_eq_num2(skf208(X24:fun_num_nat),skf209(X24:fun_num_nat)))*.
(d0,A,r2598,rw114312) 117[0:Inp] ||  -> pp(ord_less_eq_num2(skf190(X24:fun_num_nat),skf191(X24:fun_num_nat)))*.
(d0,A,r3168,rw139392) 171[0:Inp] ||  -> pp(ord_less_eq_num2(skf312(X22:fun_num_bool),skf313(X22:fun_num_bool)))*.
(d0,A,r2719,rw119636) 139[0:Inp] ||  -> pp(ord_less_eq_num2(skf234(X22:fun_num_bool),skf235(X22:fun_num_bool)))*.
(d0,A,r2697,rw118668) 134[0:Inp] ||  -> pp(ord_less_eq_num2(skf224(X22:fun_num_bool),skf225(X22:fun_num_bool)))*.
(d0,A,r2638,rw116072) 125[0:Inp] ||  -> pp(ord_less_eq_num2(skf206(X22:fun_num_bool),skf207(X22:fun_num_bool)))*.
(d0,A,r2593,rw114092) 116[0:Inp] ||  -> pp(ord_less_eq_num2(skf188(X22:fun_num_bool),skf189(X22:fun_num_bool)))*.
(d0,A,r3272,rw143968) 170[0:Inp] ||  -> pp(ord_less_eq_nat2(skf310(X21:fun_nat_num),skf311(X21:fun_nat_num)))*.
(d0,A,r2741,rw120604) 144[0:Inp] ||  -> pp(ord_less_eq_nat2(skf244(X21:fun_nat_num),skf245(X21:fun_nat_num)))*.
(d0,A,r2692,rw118448) 133[0:Inp] ||  -> pp(ord_less_eq_nat2(skf222(X21:fun_nat_num),skf223(X21:fun_nat_num)))*.
(d0,A,r2634,rw115896) 124[0:Inp] ||  -> pp(ord_less_eq_nat2(skf204(X21:fun_nat_num),skf205(X21:fun_nat_num)))*.
(d0,A,r2589,rw113916) 115[0:Inp] ||  -> pp(ord_less_eq_nat2(skf186(X21:fun_nat_num),skf187(X21:fun_nat_num)))*.
(d0,A,r1430,rw62920) 165[0:Inp] ||  -> pp(ord_less_nat2(skf300(X21:fun_nat_num),skf301(X21:fun_nat_num)))*.
(d0,A,r1070,rw47080) 112[0:Inp] ||  -> pp(ord_less_eq_bool2(skf180(X19:fun_bool_num),skf181(X19:fun_bool_num)))*.
(d0,A,r1070,rw47080) 121[0:Inp] ||  -> pp(ord_less_eq_bool2(skf198(X19:fun_bool_num),skf199(X19:fun_bool_num)))*.
(d0,A,r1070,rw47080) 130[0:Inp] ||  -> pp(ord_less_eq_bool2(skf216(X19:fun_bool_num),skf217(X19:fun_bool_num)))*.
(d0,A,r1070,rw47080) 143[0:Inp] ||  -> pp(ord_less_eq_bool2(skf242(X19:fun_bool_num),skf243(X19:fun_bool_num)))*.
(d0,A,r1070,rw47080) 167[0:Inp] ||  -> pp(ord_less_eq_bool2(skf304(X19:fun_bool_num),skf305(X19:fun_bool_num)))*.
(d0,A,r1070,rw47080) 111[0:Inp] ||  -> pp(ord_less_eq_bool2(skf178(X18:fun_bool_nat),skf179(X18:fun_bool_nat)))*.
(d0,A,r1070,rw47080) 120[0:Inp] ||  -> pp(ord_less_eq_bool2(skf196(X18:fun_bool_nat),skf197(X18:fun_bool_nat)))*.
(d0,A,r1070,rw47080) 129[0:Inp] ||  -> pp(ord_less_eq_bool2(skf214(X18:fun_bool_nat),skf215(X18:fun_bool_nat)))*.
(d0,A,r1070,rw47080) 140[0:Inp] ||  -> pp(ord_less_eq_bool2(skf236(X18:fun_bool_nat),skf237(X18:fun_bool_nat)))*.
(d0,A,r1070,rw47080) 166[0:Inp] ||  -> pp(ord_less_eq_bool2(skf302(X18:fun_bool_nat),skf303(X18:fun_bool_nat)))*.
(d0,A,r1070,rw47080) 110[0:Inp] ||  -> pp(ord_less_eq_bool2(skf176(X15:fun_bool_bool),skf177(X15:fun_bool_bool)))*.
(d0,A,r1070,rw47080) 119[0:Inp] ||  -> pp(ord_less_eq_bool2(skf194(X15:fun_bool_bool),skf195(X15:fun_bool_bool)))*.
(d0,A,r1070,rw47080) 128[0:Inp] ||  -> pp(ord_less_eq_bool2(skf212(X15:fun_bool_bool),skf213(X15:fun_bool_bool)))*.
(d0,A,r1070,rw47080) 137[0:Inp] ||  -> pp(ord_less_eq_bool2(skf230(X15:fun_bool_bool),skf231(X15:fun_bool_bool)))*.
(d0,A,r3272,rw143968) 168[0:Inp] ||  -> pp(ord_less_eq_nat2(skf306(X12:fun_nat_bool),skf307(X12:fun_nat_bool)))*.
(d0,A,r2714,rw119416) 138[0:Inp] ||  -> pp(ord_less_eq_nat2(skf232(X12:fun_nat_bool),skf233(X12:fun_nat_bool)))*.
(d0,A,r2683,rw118052) 131[0:Inp] ||  -> pp(ord_less_eq_nat2(skf218(X12:fun_nat_bool),skf219(X12:fun_nat_bool)))*.
(d0,A,r2625,rw115500) 122[0:Inp] ||  -> pp(ord_less_eq_nat2(skf200(X12:fun_nat_bool),skf201(X12:fun_nat_bool)))*.
(d0,A,r2580,rw113520) 113[0:Inp] ||  -> pp(ord_less_eq_nat2(skf182(X12:fun_nat_bool),skf183(X12:fun_nat_bool)))*.
(d0,A,r1430,rw62920) 163[0:Inp] ||  -> pp(ord_less_nat2(skf296(X12:fun_nat_bool),skf297(X12:fun_nat_bool)))*.
(d0,A,r1000,rw44000) 176[0:Inp] ||  -> equal(X4:booL,fFalsE)* equal(X4:booL,fTruE).
(d0,A,r1000,rw44000) 97[0:Inp] ||  -> equal(aa_boo1142376798l_bool(ord_less_bool,X4:booL),ord_less_bool1(X4:booL))**.
(d0,A,r1000,rw44000) 102[0:Inp] ||  -> equal(aa_boo1142376798l_bool(ord_less_eq_bool,X4:booL),ord_less_eq_bool1(X4:booL))**.
(d0,A,r1000,rw44000) 103[0:Inp] ||  -> equal(aa_bool_nat(zero_n1356753679ol_nat,X4:booL),zero_n1672634641l_nat1(X4:booL))**.
(d0,A,r3083,rw135652) 150[0:Inp] ||  -> equal(plus_plus_int2(Z:inT,uminus_uminus_int(Z:inT)),zero_zero_int)**.
(d0,A,r1000,rw44000) 91[0:Inp] ||  -> equal(aa_int_fun_int_int(plus_plus_int,Z:inT),plus_plus_int1(Z:inT))**.
(d0,A,r1214,rw53416) 105[0:Inp] || equal(skf160(U:naT,Y:naT),zero_zero_nat)** -> .
(d0,A,r3272,rw143968) 169[0:Inp] ||  -> pp(ord_less_eq_nat2(skf308(W:fun_nat_nat),skf309(W:fun_nat_nat)))*.
(d0,A,r2728,rw120032) 141[0:Inp] ||  -> pp(ord_less_eq_nat2(skf238(W:fun_nat_nat),skf239(W:fun_nat_nat)))*.
(d0,A,r2688,rw118272) 132[0:Inp] ||  -> pp(ord_less_eq_nat2(skf220(W:fun_nat_nat),skf221(W:fun_nat_nat)))*.
(d0,A,r2629,rw115676) 123[0:Inp] ||  -> pp(ord_less_eq_nat2(skf202(W:fun_nat_nat),skf203(W:fun_nat_nat)))*.
(d0,A,r2584,rw113696) 114[0:Inp] ||  -> pp(ord_less_eq_nat2(skf184(W:fun_nat_nat),skf185(W:fun_nat_nat)))*.
(d0,A,r1430,rw62920) 151[0:Inp] ||  -> pp(ord_less_nat2(skf260(W:fun_nat_nat),skf261(W:fun_nat_nat)))*.
(d0,A,r1430,rw62920) 152[0:Inp] ||  -> pp(ord_less_nat2(skf262(W:fun_nat_nat),skf263(W:fun_nat_nat)))*.
(d0,A,r1430,rw62920) 153[0:Inp] ||  -> pp(ord_less_nat2(skf264(W:fun_nat_nat),skf265(W:fun_nat_nat)))*.
(d0,A,r1430,rw62920) 154[0:Inp] ||  -> pp(ord_less_nat2(skf266(W:fun_nat_nat),skf267(W:fun_nat_nat)))*.
(d0,A,r1430,rw62920) 164[0:Inp] ||  -> pp(ord_less_nat2(skf298(W:fun_nat_nat),skf299(W:fun_nat_nat)))*.
(d0,A,r3447,rw151668) 161[0:Inp] ||  -> equal(numeral_numeral_nat1(V:nuM),suc1(pred_numeral1(V:nuM)))**.
(d0,A,r2962,rw130328) 149[0:Inp] ||  -> equal(plus_plus_num2(V:nuM,onE),inc1(V:nuM))**.
(d0,A,r1000,rw44000) 86[0:Inp] ||  -> equal(aa_num_num(inC,V:nuM),inc1(V:nuM))**.
(d0,A,r1000,rw44000) 87[0:Inp] ||  -> equal(aa_num_num(bit0,V:nuM),bit01(V:nuM))**.
(d0,A,r1000,rw44000) 88[0:Inp] ||  -> equal(aa_num_nat(pred_numeral,V:nuM),pred_numeral1(V:nuM))**.
(d0,A,r1000,rw44000) 94[0:Inp] ||  -> equal(aa_num_fun_num_bool(ord_less_num,V:nuM),ord_less_num1(V:nuM))**.
(d0,A,r1000,rw44000) 95[0:Inp] ||  -> equal(aa_num_int(numeral_numeral_int,V:nuM),numeral_numeral_int1(V:nuM))**.
(d0,A,r1000,rw44000) 99[0:Inp] ||  -> equal(aa_num_fun_num_bool(ord_less_eq_num,V:nuM),ord_less_eq_num1(V:nuM))**.
(d0,A,r3406,rw149864) 160[0:Inp] || pp(ord_less_nat2(U:naT,skf293(U:naT)))* -> .
(d0,A,r3402,rw149688) 159[0:Inp] || pp(ord_less_nat2(U:naT,skf292(U:naT)))* -> .
(d0,A,r3366,rw148104) 158[0:Inp] || pp(ord_less_nat2(skf285(U:naT),U:naT))* -> .
(d0,A,r3357,rw147708) 157[0:Inp] || pp(ord_less_nat2(skf284(U:naT),U:naT))* -> .
(d0,A,r1263,rw55572) 955[0:Rew:18.0,57.0] ||  -> equal(times_times_nat2(U:naT,suc1(zero_zero_nat)),U:naT)**.
(d0,A,r3568,rw156992) 175[0:Inp] ||  -> equal(set_or601162459st_nat(zero_zero_nat,U:naT),set_ord_atMost_nat(U:naT))**.
(d0,A,r1000,rw44000) 85[0:Inp] ||  -> equal(aa_nat_nat(suC,U:naT),suc1(U:naT))**.
(d0,A,r1000,rw44000) 90[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(dvd_dvd_nat,U:naT),dvd_dvd_nat1(U:naT))**.
(d0,A,r1000,rw44000) 92[0:Inp] ||  -> equal(aa_nat_fun_nat_nat(plus_plus_nat,U:naT),plus_plus_nat1(U:naT))**.
(d0,A,r1000,rw44000) 93[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_nat,U:naT),ord_less_nat1(U:naT))**.
(d0,A,r1000,rw44000) 98[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_eq_nat,U:naT),ord_less_eq_nat1(U:naT))**.
(d0,A,r1000,rw44000) 100[0:Inp] ||  -> equal(aa_nat_int(semiri2019852685at_int,U:naT),semiri501196819t_int1(U:naT))**.
(d0,A,r1263,rw55572) 954[0:Rew:18.0,55.0] ||  -> equal(times_times_nat2(suc1(zero_zero_nat),U:naT),U:naT)**.
(d0,A,r2315,rw99545) 65[0:Inp] ||  -> equal(uminus_uminus_int(uminus_uminus_int(Z:inT)),Z:inT)**.
(d0,A,r971,rw41753) 40[0:Inp] ||  -> equal(plus_plus_int2(Z:inT,zero_zero_int),Z:inT)**.
(d0,A,r989,rw42527) 42[0:Inp] ||  -> equal(plus_plus_int2(zero_zero_int,Z:inT),Z:inT)**.
(d0,A,r1250,rw53750) 51[0:Inp] || pp(ord_less_nat2(U:naT,U:naT))* -> .
(d0,A,r3334,rw143362) 84[0:Inp] ||  -> pp(ord_less_nat2(U:naT,skf279(U:naT)))*.
(d0,A,r2809,rw120787) 72[0:Inp] ||  -> pp(ord_less_nat2(U:naT,suc1(U:naT)))*.
(d0,A,r3290,rw141470) 83[0:Inp] ||  -> equal(minus_minus_nat2(U:naT,U:naT),zero_zero_nat)**.
(d0,A,r2153,rw92579) 62[0:Inp] ||  -> equal(minus_minus_nat2(U:naT,zero_zero_nat),U:naT)**.
(d0,A,r976,rw41968) 41[0:Inp] ||  -> equal(plus_plus_nat2(U:naT,zero_zero_nat),U:naT)**.
(d0,A,r1000,rw43000) 958[0:Rew:17.0,89.0] ||  -> equal(aa_nat_nat(id_nat,U:naT),U:naT)**.
(d0,A,r994,rw42742) 43[0:Inp] ||  -> equal(plus_plus_nat2(zero_zero_nat,U:naT),U:naT)**.
(d0,A,r2440,rw102480) 34[0:Inp] ||  -> inj_on_int_int(aTP_Lamm_ac(Z:inT),X14:set_int)*.
(d0,A,r2436,rw102312) 33[0:Inp] ||  -> inj_on_nat_nat(aTP_Lamm_ab(U:naT),X13:set_nat)*.
(d0,A,r1070,rw44940) 12[0:Inp] ||  -> pp(ord_less_eq_bool2(X4:booL,X4:booL))*.
(d0,A,r1079,rw45318) 14[0:Inp] ||  -> pp(ord_less_eq_num2(V:nuM,V:nuM))*.
(d0,A,r1075,rw45150) 13[0:Inp] ||  -> pp(ord_less_eq_nat2(U:naT,U:naT))*.
(d0,A,r1254,rw52668) 17[0:Inp] ||  -> equal(id_nat1(U:naT),U:naT)**.
(d0,A,r1000,rw42000) 959[0:Rew:958.0,101.0,10.0,101.0] ||  -> equal(semiri1184971631t_nat1(U:naT),U:naT)**.
(d0,A,r2800,rw67200) 70[0:Inp] || equal(numeral_numeral_int1(V:nuM),zero_zero_int)** -> .
(d0,A,r1551,rw37224) 56[0:Inp] || pp(ord_less_nat2(U:naT,zero_zero_nat))* -> .
(d0,A,r1497,rw35928) 54[0:Inp] || equal(suc1(U:naT),zero_zero_nat)** -> .
(d0,A,r3276,rw78624) 82[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,suc1(U:naT)))*.
(d0,A,r2234,rw53616) 64[0:Inp] ||  -> equal(times_times_nat2(U:naT,zero_zero_nat),zero_zero_nat)**.
(d0,A,r2184,rw52416) 63[0:Inp] ||  -> equal(times_times_nat2(zero_zero_nat,U:naT),zero_zero_nat)**.
(d0,A,r3168,rw72864) 35[0:Inp] ||  -> pp(ord_less_eq_num2(onE,V:nuM))*.
(d0,A,r1416,rw32568) 19[0:Inp] ||  -> pp(ord_less_eq_nat2(zero_zero_nat,U:naT))*.
(d0,A,r1263,rw10104) 962[0:Rew:161.0,961.0] ||  -> equal(suc1(pred_numeral1(bit01(onE))),suc1(suc1(zero_zero_nat)))**.
(d0,A,r2270,rw15890) 193[0:Inp] ||  -> equal(plus_plus_int2(one_one_int,one_one_int),numeral_numeral_int1(bit01(onE)))**.
(d0,A,r1263,rw7578) 952[0:Rew:18.0,79.0] || pp(ord_less_eq_nat2(suc1(zero_zero_nat),zero_zero_nat))* -> .
(d0,A,r1263,rw7578) 965[0:Rew:161.0,951.0] ||  -> equal(suc1(pred_numeral1(onE)),suc1(zero_zero_nat))**.
(d0,A,r1263,rw6315) 950[0:Rew:18.0,32.0] ||  -> equal(zero_n1672634641l_nat1(fTruE),suc1(zero_zero_nat))**.
(d0,A,r1263,rw6315) 947[0:Rew:18.0,39.0] ||  -> equal(plus_plus_nat1(suc1(zero_zero_nat)),suC)**.
(d0,A,r3254,rw16270) 80[0:Inp] ||  -> equal(neg_numeral_sub_int(onE,onE),zero_zero_int)**.
(d0,A,r1232,rw4928) 16[0:Inp] ||  -> pp(monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r1223,rw4892) 15[0:Inp] ||  -> pp(comm_monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r1263,rw5052) 18[0:Inp] ||  -> equal(one_one_nat,suc1(zero_zero_nat))**.
(d0,A,r3245,rw12980) 36[0:Inp] ||  -> equal(uminus_uminus_int(zero_zero_int),zero_zero_int)**.
(d0,A,r1919,rw7676) 25[0:Inp] ||  -> equal(numeral_numeral_int1(onE),one_one_int)**.
(d0,A,r1000,rw3000) 11[0:Inp] || pp(fFalsE)* -> .
(d0,A,r1227,rw3681) 8[0:Inp] ||  -> monoid_int(plus_plus_int,zero_zero_int)*.
(d0,A,r1218,rw3654) 7[0:Inp] ||  -> comm_monoid_int(plus_plus_int,zero_zero_int)*.
(d0,A,r3550,rw10650) 10[0:Inp] ||  -> equal(semiri1382578993at_nat,id_nat)**.
(d0,A,r3227,rw9681) 9[0:Inp] ||  -> equal(poS,numeral_numeral_int)**.
(d0,A,r1569,rw3138) 1[0:Inp] || bot_bot_bool* -> .
(d0,A,r1000,rw2000) 6[0:Inp] ||  -> pp(fTruE)*.
(d0,A,r2342,rw4684) 5[0:Inp] ||  -> abel_semigroup_int(plus_plus_int)*.
(d0,A,r2337,rw4674) 4[0:Inp] ||  -> abel_semigroup_nat(plus_plus_nat)*.
(d0,A,r2301,rw4602) 3[0:Inp] ||  -> semigroup_int(plus_plus_int)*.
(d0,A,r2297,rw4594) 2[0:Inp] ||  -> semigroup_nat(plus_plus_nat)*.