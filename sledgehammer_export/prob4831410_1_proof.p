

From 1804 Axiom clauses, 2 were allowed.


A precedence of symbols which satisfies all compatible equal:lr annotations (the actual ordering is in general less restricted):
	[]

SPASS V 3.8ds 
SPASS beiseite: Completion found.
Problem: /Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4831410_1.p 
SPASS derived 19 clauses, backtracked 0 clauses, performed 0 splits and kept 1182 clauses.
SPASS allocated 105910 KBytes.
SPASS spent	0:00:01.11 on the problem.
		0:00:00.02 for the input.
		0:00:00.68 for the FLOTTER CNF translation.
		0:00:00.00 for inferences.
		0:00:00.00 for the backtracking.
		0:00:00.23 for the reduction.


 The saturated set of worked-off clauses is :
(d0,C,r0,rw0) 158[0:Inp] || equal(plus_plus_a(x,zero_zero_a),x)** -> .
(d0,A,r0,rw0) 1777[0:Inp] || SkP0(U:nuM,X2:nuM,X9:nuM)* SkP0(X2:nuM,X9:nuM,U:nuM)* SkP0(X2:nuM,U:nuM,X9:nuM)* SkP0(U:nuM,X9:nuM,X2:nuM)* SkP0(X9:nuM,X2:nuM,U:nuM)* SkP0(X9:nuM,U:nuM,X2:nuM)* -> .
(d0,A,r0,rw0) 1775[0:Inp] || SkP2(W:inT,X1:inT,X4:inT)* SkP2(X1:inT,X4:inT,W:inT)* SkP2(X1:inT,W:inT,X4:inT)* SkP2(W:inT,X4:inT,X1:inT)* SkP2(X4:inT,X1:inT,W:inT)* SkP2(X4:inT,W:inT,X1:inT)* -> .
(d0,A,r0,rw0) 1776[0:Inp] || SkP1(Y:naT,Z:naT,X3:naT)* SkP1(Z:naT,X3:naT,Y:naT)* SkP1(Z:naT,Y:naT,X3:naT)* SkP1(Y:naT,X3:naT,Z:naT)* SkP1(X3:naT,Z:naT,Y:naT)* SkP1(X3:naT,Y:naT,Z:naT)* -> .
(d0,A,r0,rw0) 1778[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf649(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool)))* SkP20(X30:fun_int_bool,X39:fun_int_bool) SkP20(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1779[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf649(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool)))* SkP20(X30:fun_int_bool,X39:fun_int_bool) SkP20(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1780[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf649(X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool,X34:fun_int_bool)))* SkP20(X39:fun_int_bool,X30:fun_int_bool) SkP20(X40:fun_int_bool,X34:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1781[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf649(X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool,X34:fun_int_bool)))* SkP20(X39:fun_int_bool,X30:fun_int_bool) SkP20(X40:fun_int_bool,X34:fun_int_bool) -> pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1790[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(skf625(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool),W:inT))* SkP14(X30:fun_int_bool,X39:fun_int_bool) SkP14(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1791[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(skf625(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool),W:inT))* SkP14(X30:fun_int_bool,X39:fun_int_bool) SkP14(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1792[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(skf625(X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool,X34:fun_int_bool),W:inT))* SkP14(X39:fun_int_bool,X30:fun_int_bool) SkP14(X40:fun_int_bool,X34:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1793[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(ord_less_int2(skf625(X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool,X34:fun_int_bool),W:inT))* SkP14(X39:fun_int_bool,X30:fun_int_bool) SkP14(X40:fun_int_bool,X34:fun_int_bool) -> pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1782[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf647(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool)))* SkP19(X25:fun_nat_bool,X37:fun_nat_bool) SkP19(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1783[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf647(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool)))* SkP19(X25:fun_nat_bool,X37:fun_nat_bool) SkP19(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1784[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf647(X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool,X33:fun_nat_bool)))* SkP19(X37:fun_nat_bool,X25:fun_nat_bool) SkP19(X38:fun_nat_bool,X33:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1785[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf647(X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool,X33:fun_nat_bool)))* SkP19(X37:fun_nat_bool,X25:fun_nat_bool) SkP19(X38:fun_nat_bool,X33:fun_nat_bool) -> pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1794[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf623(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool),Y:naT))* SkP13(X25:fun_nat_bool,X37:fun_nat_bool) SkP13(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1795[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf623(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool),Y:naT))* SkP13(X25:fun_nat_bool,X37:fun_nat_bool) SkP13(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1796[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf623(X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool,X33:fun_nat_bool),Y:naT))* SkP13(X37:fun_nat_bool,X25:fun_nat_bool) SkP13(X38:fun_nat_bool,X33:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1797[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf623(X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool,X33:fun_nat_bool),Y:naT))* SkP13(X37:fun_nat_bool,X25:fun_nat_bool) SkP13(X38:fun_nat_bool,X33:fun_nat_bool) -> pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1786[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf645(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool)))* SkP18(X31:fun_num_bool,X35:fun_num_bool) SkP18(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1787[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf645(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool)))* SkP18(X31:fun_num_bool,X35:fun_num_bool) SkP18(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1788[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf645(X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool,X32:fun_num_bool)))* SkP18(X35:fun_num_bool,X31:fun_num_bool) SkP18(X36:fun_num_bool,X32:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1789[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf645(X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool,X32:fun_num_bool)))* SkP18(X35:fun_num_bool,X31:fun_num_bool) SkP18(X36:fun_num_bool,X32:fun_num_bool) -> pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1798[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(skf621(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool),U:nuM))* SkP12(X31:fun_num_bool,X35:fun_num_bool) SkP12(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1799[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(skf621(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool),U:nuM))* SkP12(X31:fun_num_bool,X35:fun_num_bool) SkP12(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1800[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(skf621(X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool,X32:fun_num_bool),U:nuM))* SkP12(X35:fun_num_bool,X31:fun_num_bool) SkP12(X36:fun_num_bool,X32:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1801[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(ord_less_num2(skf621(X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool,X32:fun_num_bool),U:nuM))* SkP12(X35:fun_num_bool,X31:fun_num_bool) SkP12(X36:fun_num_bool,X32:fun_num_bool) -> pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1751[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf655(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool)))* SkP23(X30:fun_int_bool,X39:fun_int_bool) SkP23(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)) pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1752[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf655(X34:fun_int_bool,X30:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool)))* SkP23(X34:fun_int_bool,X39:fun_int_bool) SkP23(X30:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)) pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1753[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf655(X34:fun_int_bool,X39:fun_int_bool,X30:fun_int_bool,X40:fun_int_bool)))* SkP23(X34:fun_int_bool,X30:fun_int_bool) SkP23(X39:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1754[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,skf655(X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool)))* SkP23(X34:fun_int_bool,X40:fun_int_bool) SkP23(X39:fun_int_bool,X30:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1763[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(skf631(X30:fun_int_bool,X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool),W:inT))* SkP17(X30:fun_int_bool,X39:fun_int_bool) SkP17(X34:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)) pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1764[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(skf631(X34:fun_int_bool,X30:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool),W:inT))* SkP17(X34:fun_int_bool,X39:fun_int_bool) SkP17(X30:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X39:fun_int_bool,W:inT)) pp(aa_int_bool(X40:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1765[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(skf631(X34:fun_int_bool,X39:fun_int_bool,X30:fun_int_bool,X40:fun_int_bool),W:inT))* SkP17(X34:fun_int_bool,X30:fun_int_bool) SkP17(X39:fun_int_bool,X40:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1766[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(skf631(X34:fun_int_bool,X39:fun_int_bool,X40:fun_int_bool,X30:fun_int_bool),W:inT))* SkP17(X34:fun_int_bool,X40:fun_int_bool) SkP17(X39:fun_int_bool,X30:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,W:inT)) pp(aa_int_bool(X39:fun_int_bool,W:inT)).
(d0,A,r0,rw0) 1755[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf653(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool)))* SkP22(X25:fun_nat_bool,X37:fun_nat_bool) SkP22(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1756[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf653(X33:fun_nat_bool,X25:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool)))* SkP22(X33:fun_nat_bool,X37:fun_nat_bool) SkP22(X25:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1757[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf653(X33:fun_nat_bool,X37:fun_nat_bool,X25:fun_nat_bool,X38:fun_nat_bool)))* SkP22(X33:fun_nat_bool,X25:fun_nat_bool) SkP22(X37:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1758[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf653(X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool)))* SkP22(X33:fun_nat_bool,X38:fun_nat_bool) SkP22(X37:fun_nat_bool,X25:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1767[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf629(X25:fun_nat_bool,X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool),Y:naT))* SkP16(X25:fun_nat_bool,X37:fun_nat_bool) SkP16(X33:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1768[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf629(X33:fun_nat_bool,X25:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool),Y:naT))* SkP16(X33:fun_nat_bool,X37:fun_nat_bool) SkP16(X25:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X38:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1769[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf629(X33:fun_nat_bool,X37:fun_nat_bool,X25:fun_nat_bool,X38:fun_nat_bool),Y:naT))* SkP16(X33:fun_nat_bool,X25:fun_nat_bool) SkP16(X37:fun_nat_bool,X38:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1770[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(skf629(X33:fun_nat_bool,X37:fun_nat_bool,X38:fun_nat_bool,X25:fun_nat_bool),Y:naT))* SkP16(X33:fun_nat_bool,X38:fun_nat_bool) SkP16(X37:fun_nat_bool,X25:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X37:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1759[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf651(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool)))* SkP21(X31:fun_num_bool,X35:fun_num_bool) SkP21(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)) pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1760[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf651(X32:fun_num_bool,X31:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool)))* SkP21(X32:fun_num_bool,X35:fun_num_bool) SkP21(X31:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)) pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1761[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf651(X32:fun_num_bool,X35:fun_num_bool,X31:fun_num_bool,X36:fun_num_bool)))* SkP21(X32:fun_num_bool,X31:fun_num_bool) SkP21(X35:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1762[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(U:nuM,skf651(X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool)))* SkP21(X32:fun_num_bool,X36:fun_num_bool) SkP21(X35:fun_num_bool,X31:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1771[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(skf627(X31:fun_num_bool,X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool),U:nuM))* SkP15(X31:fun_num_bool,X35:fun_num_bool) SkP15(X32:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)) pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1772[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(skf627(X32:fun_num_bool,X31:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool),U:nuM))* SkP15(X32:fun_num_bool,X35:fun_num_bool) SkP15(X31:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X35:fun_num_bool,U:nuM)) pp(aa_num_bool(X36:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1773[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(skf627(X32:fun_num_bool,X35:fun_num_bool,X31:fun_num_bool,X36:fun_num_bool),U:nuM))* SkP15(X32:fun_num_bool,X31:fun_num_bool) SkP15(X35:fun_num_bool,X36:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1774[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_num2(skf627(X32:fun_num_bool,X35:fun_num_bool,X36:fun_num_bool,X31:fun_num_bool),U:nuM))* SkP15(X32:fun_num_bool,X36:fun_num_bool) SkP15(X35:fun_num_bool,X31:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,U:nuM)) pp(aa_num_bool(X35:fun_num_bool,U:nuM)).
(d0,A,r0,rw0) 1802[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(W:inT,X4:inT)) pp(ord_less_int2(X4:inT,skf610(X30:fun_int_bool,X1:inT,W:inT)))* -> pp(aa_int_bool(X30:fun_int_bool,X1:inT)) pp(aa_int_bool(X30:fun_int_bool,X4:inT)).
(d0,A,r0,rw0) 1803[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(Y:naT,X3:naT))* pp(ord_less_nat2(X3:naT,skf608(X25:fun_nat_bool,Z:naT,Y:naT)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Z:naT)) pp(aa_nat_bool(X25:fun_nat_bool,X3:naT)).
(d0,A,r0,rw0) 1677[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,X1:inT))* pp(aa_int_bool(X30:fun_int_bool,skf611(X30:fun_int_bool,X4:inT,W:inT)))* -> pp(aa_int_bool(X30:fun_int_bool,X1:inT)) pp(ord_less_eq_int2(X4:inT,skf610(X30:fun_int_bool,X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1678[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,Z:naT)) pp(aa_nat_bool(X25:fun_nat_bool,skf609(X25:fun_nat_bool,X3:naT,Y:naT)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Z:naT)) pp(ord_less_eq_nat2(X3:naT,skf608(X25:fun_nat_bool,Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1675[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,X1:inT))* -> pp(aa_int_bool(X30:fun_int_bool,X1:inT)) pp(ord_less_eq_int2(X4:inT,skf610(X30:fun_int_bool,X1:inT,W:inT)))* pp(ord_less_int2(skf611(X30:fun_int_bool,X4:inT,W:inT),X4:inT))*.
(d0,A,r0,rw0) 1676[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,Z:naT)) pp(ord_less_eq_nat2(X3:naT,skf608(X25:fun_nat_bool,Z:naT,Y:naT)))* pp(ord_less_nat2(skf609(X25:fun_nat_bool,X3:naT,Y:naT),X3:naT))*.
(d0,A,r0,rw0) 1805[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,X21:inT)) equal(plus_plus_int2(X21:inT,X7:inT),one_one_int) -> pp(ord_less_eq_int2(plus_plus_int2(times_times_int2(X21:inT,X4:inT),times_times_int2(X7:inT,W:inT)),X1:inT))*.
(d0,A,r0,rw0) 1804[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,X21:inT)) equal(plus_plus_int2(X21:inT,X7:inT),one_one_int) -> pp(ord_less_int2(plus_plus_int2(times_times_int2(X21:inT,X4:inT),times_times_int2(X7:inT,W:inT)),X1:inT))*.
(d0,A,r0,rw0) 1891[0:Rew:351.0,1615.1] || SkP24(X25:fun_nat_bool,Y:naT) -> pp(aa_nat_bool(X25:fun_nat_bool,divide_divide_nat2(Z:naT,Y:naT))) equal(plus_plus_nat2(skf670(X25:fun_nat_bool,Y:naT,Z:naT),times_times_nat2(Y:naT,skf671(X25:fun_nat_bool,Y:naT,Z:naT))),Z:naT)**.
(d0,A,r0,rw0) 1688[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_int2(X4:inT,aa_int_int(X20:fun_int_int,W:inT)))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf576(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf577(X20:fun_int_int))))* -> pp(ord_less_int2(X4:inT,aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1706[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X4:inT,aa_int_int(X20:fun_int_int,W:inT)))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf444(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf445(X20:fun_int_int))))* -> pp(ord_less_eq_int2(X4:inT,aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1733[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_int2(X4:inT,aa_int_int(X20:fun_int_int,W:inT)))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf378(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf379(X20:fun_int_int))))* -> pp(ord_less_int2(X4:inT,aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1715[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X4:inT,aa_int_int(X20:fun_int_int,W:inT)))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf414(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf415(X20:fun_int_int))))* -> pp(ord_less_int2(X4:inT,aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1679[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,X1:inT),X4:inT))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf594(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf595(X20:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X20:fun_int_int,W:inT),X4:inT))*.
(d0,A,r0,rw0) 1697[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,X1:inT),X4:inT))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf462(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf463(X20:fun_int_int))))* -> pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,W:inT),X4:inT))*.
(d0,A,r0,rw0) 1724[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,X1:inT),X4:inT))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf396(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf397(X20:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X20:fun_int_int,W:inT),X4:inT))*.
(d0,A,r0,rw0) 1742[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,X1:inT),X4:inT))* pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf360(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf361(X20:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X20:fun_int_int,W:inT),X4:inT))*.
(d0,A,r0,rw0) 1689[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_int2(W:inT,aa_nat_int(X19:fun_nat_int,Y:naT)))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf574(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf575(X19:fun_nat_int))))* -> pp(ord_less_int2(W:inT,aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1707[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(W:inT,aa_nat_int(X19:fun_nat_int,Y:naT)))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf442(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf443(X19:fun_nat_int))))* -> pp(ord_less_eq_int2(W:inT,aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1716[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(W:inT,aa_nat_int(X19:fun_nat_int,Y:naT)))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf412(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf413(X19:fun_nat_int))))* -> pp(ord_less_int2(W:inT,aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1736[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_int2(W:inT,aa_nat_int(X19:fun_nat_int,Y:naT)))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf372(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf373(X19:fun_nat_int))))* -> pp(ord_less_int2(W:inT,aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1682[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Z:naT),W:inT))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf588(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf589(X19:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Y:naT),W:inT))*.
(d0,A,r0,rw0) 1700[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,Z:naT),W:inT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf456(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf457(X19:fun_nat_int))))* -> pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,Y:naT),W:inT))*.
(d0,A,r0,rw0) 1727[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Z:naT),W:inT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf390(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf391(X19:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Y:naT),W:inT))*.
(d0,A,r0,rw0) 1743[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,Z:naT),W:inT))* pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf358(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf359(X19:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Y:naT),W:inT))*.
(d0,A,r0,rw0) 1690[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_int2(W:inT,aa_num_int(X18:fun_num_int,U:nuM)))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf572(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf573(X18:fun_num_int))))* -> pp(ord_less_int2(W:inT,aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1708[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_int2(W:inT,aa_num_int(X18:fun_num_int,U:nuM)))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf440(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf441(X18:fun_num_int))))* -> pp(ord_less_eq_int2(W:inT,aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1717[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_int2(W:inT,aa_num_int(X18:fun_num_int,U:nuM)))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf410(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf411(X18:fun_num_int))))* -> pp(ord_less_int2(W:inT,aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1739[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_int2(W:inT,aa_num_int(X18:fun_num_int,U:nuM)))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf366(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf367(X18:fun_num_int))))* -> pp(ord_less_int2(W:inT,aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1685[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,X2:nuM),W:inT))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf582(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf583(X18:fun_num_int))))* -> pp(ord_less_int2(aa_num_int(X18:fun_num_int,U:nuM),W:inT))*.
(d0,A,r0,rw0) 1703[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,X2:nuM),W:inT))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf450(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf451(X18:fun_num_int))))* -> pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,U:nuM),W:inT))*.
(d0,A,r0,rw0) 1730[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,X2:nuM),W:inT))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf384(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf385(X18:fun_num_int))))* -> pp(ord_less_int2(aa_num_int(X18:fun_num_int,U:nuM),W:inT))*.
(d0,A,r0,rw0) 1744[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,X2:nuM),W:inT))* pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf356(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf357(X18:fun_num_int))))* -> pp(ord_less_int2(aa_num_int(X18:fun_num_int,U:nuM),W:inT))*.
(d0,A,r0,rw0) 1691[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,W:inT)))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf570(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf571(X17:fun_int_nat))))* -> pp(ord_less_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1709[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,W:inT)))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf438(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf439(X17:fun_int_nat))))* -> pp(ord_less_eq_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1718[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,W:inT)))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf408(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf409(X17:fun_int_nat))))* -> pp(ord_less_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1734[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,W:inT)))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf376(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf377(X17:fun_int_nat))))* -> pp(ord_less_nat2(Y:naT,aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1680[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,X1:inT),Y:naT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf592(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf593(X17:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,W:inT),Y:naT))*.
(d0,A,r0,rw0) 1698[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,X1:inT),Y:naT))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf460(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf461(X17:fun_int_nat))))* -> pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,W:inT),Y:naT))*.
(d0,A,r0,rw0) 1725[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,X1:inT),Y:naT))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf394(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf395(X17:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,W:inT),Y:naT))*.
(d0,A,r0,rw0) 1745[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,X1:inT),Y:naT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf354(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf355(X17:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,W:inT),Y:naT))*.
(d0,A,r0,rw0) 1692[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Y:naT)))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf568(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf569(X15:fun_nat_nat))))* -> pp(ord_less_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1710[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Y:naT)))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf436(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf437(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1737[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Y:naT)))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf370(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf371(X15:fun_nat_nat))))* -> pp(ord_less_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1719[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Y:naT)))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf406(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf407(X15:fun_nat_nat))))* -> pp(ord_less_nat2(X3:naT,aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1683[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Z:naT),X3:naT))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf586(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf587(X15:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),X3:naT))*.
(d0,A,r0,rw0) 1701[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Z:naT),X3:naT))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf454(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf455(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),X3:naT))*.
(d0,A,r0,rw0) 1728[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Z:naT),X3:naT))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf388(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf389(X15:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),X3:naT))*.
(d0,A,r0,rw0) 1746[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Z:naT),X3:naT))* pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf352(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf353(X15:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),X3:naT))*.
(d0,A,r0,rw0) 1693[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,U:nuM)))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf566(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf567(X14:fun_num_nat))))* -> pp(ord_less_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1711[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,U:nuM)))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf434(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf435(X14:fun_num_nat))))* -> pp(ord_less_eq_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1720[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,U:nuM)))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf404(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf405(X14:fun_num_nat))))* -> pp(ord_less_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1740[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,U:nuM)))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf364(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf365(X14:fun_num_nat))))* -> pp(ord_less_nat2(Y:naT,aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1686[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,X2:nuM),Y:naT))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf580(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf581(X14:fun_num_nat))))* -> pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),Y:naT))*.
(d0,A,r0,rw0) 1704[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,X2:nuM),Y:naT))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf448(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf449(X14:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),Y:naT))*.
(d0,A,r0,rw0) 1731[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,X2:nuM),Y:naT))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf382(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf383(X14:fun_num_nat))))* -> pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),Y:naT))*.
(d0,A,r0,rw0) 1747[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,X2:nuM),Y:naT))* pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf350(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf351(X14:fun_num_nat))))* -> pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),Y:naT))*.
(d0,A,r0,rw0) 1694[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_num2(U:nuM,aa_int_num(X13:fun_int_num,W:inT)))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf564(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf565(X13:fun_int_num))))* -> pp(ord_less_num2(U:nuM,aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1712[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(U:nuM,aa_int_num(X13:fun_int_num,W:inT)))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf432(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf433(X13:fun_int_num))))* -> pp(ord_less_eq_num2(U:nuM,aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1721[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(U:nuM,aa_int_num(X13:fun_int_num,W:inT)))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf402(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf403(X13:fun_int_num))))* -> pp(ord_less_num2(U:nuM,aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1735[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_num2(U:nuM,aa_int_num(X13:fun_int_num,W:inT)))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf374(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf375(X13:fun_int_num))))* -> pp(ord_less_num2(U:nuM,aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1681[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,X1:inT),U:nuM))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf590(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf591(X13:fun_int_num))))* -> pp(ord_less_num2(aa_int_num(X13:fun_int_num,W:inT),U:nuM))*.
(d0,A,r0,rw0) 1699[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,X1:inT),U:nuM))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf458(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf459(X13:fun_int_num))))* -> pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,W:inT),U:nuM))*.
(d0,A,r0,rw0) 1726[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,X1:inT),U:nuM))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf392(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf393(X13:fun_int_num))))* -> pp(ord_less_num2(aa_int_num(X13:fun_int_num,W:inT),U:nuM))*.
(d0,A,r0,rw0) 1748[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,X1:inT),U:nuM))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf348(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf349(X13:fun_int_num))))* -> pp(ord_less_num2(aa_int_num(X13:fun_int_num,W:inT),U:nuM))*.
(d0,A,r0,rw0) 1695[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Y:naT)))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf562(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf563(X12:fun_nat_num))))* -> pp(ord_less_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1713[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Y:naT)))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf430(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf431(X12:fun_nat_num))))* -> pp(ord_less_eq_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1722[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Y:naT)))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf400(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf401(X12:fun_nat_num))))* -> pp(ord_less_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1738[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Y:naT)))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf368(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf369(X12:fun_nat_num))))* -> pp(ord_less_num2(U:nuM,aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1684[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Z:naT),U:nuM))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf584(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf585(X12:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Y:naT),U:nuM))*.
(d0,A,r0,rw0) 1702[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,Z:naT),U:nuM))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf452(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf453(X12:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,Y:naT),U:nuM))*.
(d0,A,r0,rw0) 1729[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Z:naT),U:nuM))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf386(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf387(X12:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Y:naT),U:nuM))*.
(d0,A,r0,rw0) 1749[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,Z:naT),U:nuM))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf346(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf347(X12:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Y:naT),U:nuM))*.
(d0,A,r0,rw0) 1696[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X9:nuM,aa_num_num(X8:fun_num_num,U:nuM)))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf560(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf561(X8:fun_num_num))))* -> pp(ord_less_num2(X9:nuM,aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1714[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X9:nuM,aa_num_num(X8:fun_num_num,U:nuM)))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf428(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf429(X8:fun_num_num))))* -> pp(ord_less_eq_num2(X9:nuM,aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1741[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X9:nuM,aa_num_num(X8:fun_num_num,U:nuM)))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf362(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf363(X8:fun_num_num))))* -> pp(ord_less_num2(X9:nuM,aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1723[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X9:nuM,aa_num_num(X8:fun_num_num,U:nuM)))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf398(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf399(X8:fun_num_num))))* -> pp(ord_less_num2(X9:nuM,aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1687[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,X2:nuM),X9:nuM))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf578(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf579(X8:fun_num_num))))* -> pp(ord_less_num2(aa_num_num(X8:fun_num_num,U:nuM),X9:nuM))*.
(d0,A,r0,rw0) 1705[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,X2:nuM),X9:nuM))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf446(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf447(X8:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,U:nuM),X9:nuM))*.
(d0,A,r0,rw0) 1732[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,X2:nuM),X9:nuM))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf380(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf381(X8:fun_num_num))))* -> pp(ord_less_num2(aa_num_num(X8:fun_num_num,U:nuM),X9:nuM))*.
(d0,A,r0,rw0) 1750[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,X2:nuM),X9:nuM))* pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf344(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf345(X8:fun_num_num))))* -> pp(ord_less_num2(aa_num_num(X8:fun_num_num,U:nuM),X9:nuM))*.
(d0,A,r0,rw0) 1659[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(aa_nat_bool(X25:fun_nat_bool,divide_divide_nat2(X3:naT,Z:naT)))* equal(X3:naT,plus_plus_nat2(times_times_nat2(Z:naT,X6:naT),Y:naT))* -> pp(aa_nat_bool(X25:fun_nat_bool,X6:naT))* equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 1610[0:Inp] || equal(plus_plus_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X7:inT)),plus_plus_int2(times_times_int2(W:inT,X7:inT),times_times_int2(X4:inT,X1:inT)))* -> equal(W:inT,X4:inT) equal(X1:inT,X7:inT).
(d0,A,r0,rw0) 1611[0:Inp] || equal(plus_plus_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(X3:naT,X6:naT)),plus_plus_nat2(times_times_nat2(Y:naT,X6:naT),times_times_nat2(X3:naT,Z:naT)))* -> equal(Y:naT,X3:naT) equal(Z:naT,X6:naT).
(d0,A,r0,rw0) 1671[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X7:inT)) -> pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1673[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1665[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1667[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1669[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X7:inT)) pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1663[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X7:inT)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X7:inT)) -> pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1660[0:Inp] SkP8(X24:fun_int_fun_int_bool) || pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf519(X24:fun_int_fun_int_bool)),skf519(X24:fun_int_fun_int_bool))) pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf521(X24:fun_int_fun_int_bool)),skf520(X24:fun_int_fun_int_bool)))* -> pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1661[0:Inp] SkP7(X23:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf514(X23:fun_nat_fun_nat_bool)),skf514(X23:fun_nat_fun_nat_bool))) pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf516(X23:fun_nat_fun_nat_bool)),skf515(X23:fun_nat_fun_nat_bool)))* -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 1662[0:Inp] SkP6(X22:fun_num_fun_num_bool) || pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf509(X22:fun_num_fun_num_bool)),skf509(X22:fun_num_fun_num_bool))) pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf511(X22:fun_num_fun_num_bool)),skf510(X22:fun_num_fun_num_bool)))* -> pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,U:nuM),X2:nuM))*.
(d0,A,r0,rw0) 1623[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf558(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf559(X20:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X20:fun_int_int,W:inT),aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1632[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(aa_int_int(X20:fun_int_int,skf540(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf541(X20:fun_int_int))))* -> pp(ord_less_int2(aa_int_int(X20:fun_int_int,W:inT),aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1641[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf498(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf499(X20:fun_int_int))))* -> pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,W:inT),aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1650[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,skf480(X20:fun_int_int)),aa_int_int(X20:fun_int_int,skf481(X20:fun_int_int))))* -> pp(ord_less_eq_int2(aa_int_int(X20:fun_int_int,W:inT),aa_int_int(X20:fun_int_int,X1:inT)))*.
(d0,A,r0,rw0) 1626[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf552(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf553(X19:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Y:naT),aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1635[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,skf534(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf535(X19:fun_nat_int))))* -> pp(ord_less_int2(aa_nat_int(X19:fun_nat_int,Y:naT),aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1644[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf492(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf493(X19:fun_nat_int))))* -> pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,Y:naT),aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1653[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,skf474(X19:fun_nat_int)),aa_nat_int(X19:fun_nat_int,skf475(X19:fun_nat_int))))* -> pp(ord_less_eq_int2(aa_nat_int(X19:fun_nat_int,Y:naT),aa_nat_int(X19:fun_nat_int,Z:naT)))*.
(d0,A,r0,rw0) 1629[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf546(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf547(X18:fun_num_int))))* -> pp(ord_less_int2(aa_num_int(X18:fun_num_int,U:nuM),aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1638[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_int2(aa_num_int(X18:fun_num_int,skf528(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf529(X18:fun_num_int))))* -> pp(ord_less_int2(aa_num_int(X18:fun_num_int,U:nuM),aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1647[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf486(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf487(X18:fun_num_int))))* -> pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,U:nuM),aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1656[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,skf468(X18:fun_num_int)),aa_num_int(X18:fun_num_int,skf469(X18:fun_num_int))))* -> pp(ord_less_eq_int2(aa_num_int(X18:fun_num_int,U:nuM),aa_num_int(X18:fun_num_int,X2:nuM)))*.
(d0,A,r0,rw0) 1624[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf556(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf557(X17:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,W:inT),aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1633[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,skf538(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf539(X17:fun_int_nat))))* -> pp(ord_less_nat2(aa_int_nat(X17:fun_int_nat,W:inT),aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1642[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf496(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf497(X17:fun_int_nat))))* -> pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,W:inT),aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1651[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,skf478(X17:fun_int_nat)),aa_int_nat(X17:fun_int_nat,skf479(X17:fun_int_nat))))* -> pp(ord_less_eq_nat2(aa_int_nat(X17:fun_int_nat,W:inT),aa_int_nat(X17:fun_int_nat,X1:inT)))*.
(d0,A,r0,rw0) 1627[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf550(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf551(X15:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1636[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf532(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf533(X15:fun_nat_nat))))* -> pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1645[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf490(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf491(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1654[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,skf472(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf473(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1622[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf672(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf673(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),aa_nat_nat(X15:fun_nat_nat,Z:naT)))*.
(d0,A,r0,rw0) 1630[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf544(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf545(X14:fun_num_nat))))* -> pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1639[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,skf526(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf527(X14:fun_num_nat))))* -> pp(ord_less_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1648[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf484(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf485(X14:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1657[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,skf466(X14:fun_num_nat)),aa_num_nat(X14:fun_num_nat,skf467(X14:fun_num_nat))))* -> pp(ord_less_eq_nat2(aa_num_nat(X14:fun_num_nat,U:nuM),aa_num_nat(X14:fun_num_nat,X2:nuM)))*.
(d0,A,r0,rw0) 1625[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf554(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf555(X13:fun_int_num))))* -> pp(ord_less_num2(aa_int_num(X13:fun_int_num,W:inT),aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1634[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_num2(aa_int_num(X13:fun_int_num,skf536(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf537(X13:fun_int_num))))* -> pp(ord_less_num2(aa_int_num(X13:fun_int_num,W:inT),aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1643[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf494(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf495(X13:fun_int_num))))* -> pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,W:inT),aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1652[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,skf476(X13:fun_int_num)),aa_int_num(X13:fun_int_num,skf477(X13:fun_int_num))))* -> pp(ord_less_eq_num2(aa_int_num(X13:fun_int_num,W:inT),aa_int_num(X13:fun_int_num,X1:inT)))*.
(d0,A,r0,rw0) 1628[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf548(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf549(X12:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Y:naT),aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1637[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,skf530(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf531(X12:fun_nat_num))))* -> pp(ord_less_num2(aa_nat_num(X12:fun_nat_num,Y:naT),aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1646[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf488(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf489(X12:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,Y:naT),aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1655[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,skf470(X12:fun_nat_num)),aa_nat_num(X12:fun_nat_num,skf471(X12:fun_nat_num))))* -> pp(ord_less_eq_num2(aa_nat_num(X12:fun_nat_num,Y:naT),aa_nat_num(X12:fun_nat_num,Z:naT)))*.
(d0,A,r0,rw0) 1631[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf542(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf543(X8:fun_num_num))))* -> pp(ord_less_num2(aa_num_num(X8:fun_num_num,U:nuM),aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1640[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_num2(aa_num_num(X8:fun_num_num,skf524(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf525(X8:fun_num_num))))* -> pp(ord_less_num2(aa_num_num(X8:fun_num_num,U:nuM),aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1649[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf482(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf483(X8:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,U:nuM),aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1658[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,skf464(X8:fun_num_num)),aa_num_num(X8:fun_num_num,skf465(X8:fun_num_num))))* -> pp(ord_less_eq_num2(aa_num_num(X8:fun_num_num,U:nuM),aa_num_num(X8:fun_num_num,X2:nuM)))*.
(d0,A,r0,rw0) 1614[0:Inp] || pp(ord_less_nat2(aa_nat_nat(X15:fun_nat_nat,skf674(X15:fun_nat_nat)),aa_nat_nat(X15:fun_nat_nat,skf675(X15:fun_nat_nat))))* -> pp(ord_less_eq_nat2(plus_plus_nat2(aa_nat_nat(X15:fun_nat_nat,Y:naT),Z:naT),aa_nat_nat(X15:fun_nat_nat,plus_plus_nat2(Y:naT,Z:naT))))*.
(d0,A,r0,rw0) 1607[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_int2(W:inT,X1:inT))* -> pp(aa_int_bool(X30:fun_int_bool,X1:inT)) pp(ord_less_eq_int2(skf610(X30:fun_int_bool,X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1608[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,Z:naT)) pp(ord_less_eq_nat2(skf608(X25:fun_nat_bool,Z:naT,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 1566[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,skf626(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf626(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* -> SkP14(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1569[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,skf632(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf632(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* -> SkP17(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1572[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,skf650(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf650(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* -> SkP20(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1575[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,skf656(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf656(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* -> SkP23(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1571[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf648(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf648(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* -> SkP19(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1574[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf654(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf654(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* -> SkP22(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1565[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf624(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf624(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* -> SkP13(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1568[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf630(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf630(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* -> SkP16(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1564[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,skf622(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf622(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* -> SkP12(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1567[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,skf628(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf628(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* -> SkP15(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1570[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,skf646(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf646(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* -> SkP18(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1573[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,skf652(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf652(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* -> SkP21(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1578[0:Inp] || equal(W:inT,X1:inT) -> equal(plus_plus_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X7:inT)),plus_plus_int2(times_times_int2(W:inT,X7:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1579[0:Inp] || equal(W:inT,X1:inT) -> equal(plus_plus_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X7:inT,X1:inT)),plus_plus_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X7:inT,W:inT)))*.
(d0,A,r0,rw0) 1576[0:Inp] || equal(Y:naT,Z:naT) -> equal(plus_plus_nat2(times_times_nat2(Y:naT,X3:naT),times_times_nat2(Z:naT,X6:naT)),plus_plus_nat2(times_times_nat2(Y:naT,X6:naT),times_times_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1577[0:Inp] || equal(Y:naT,Z:naT) -> equal(plus_plus_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X6:naT,Z:naT)),plus_plus_nat2(times_times_nat2(X3:naT,Z:naT),times_times_nat2(X6:naT,Y:naT)))*.
(d0,A,r0,rw0) 1423[0:Inp] ||  -> pp(aa_int_bool(X30:fun_int_bool,skf626(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf626(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* SkP14(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1426[0:Inp] ||  -> pp(aa_int_bool(X30:fun_int_bool,skf632(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf632(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* SkP17(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1429[0:Inp] ||  -> pp(aa_int_bool(X30:fun_int_bool,skf650(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf650(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* SkP20(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1432[0:Inp] ||  -> pp(aa_int_bool(X30:fun_int_bool,skf656(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* pp(aa_int_bool(X34:fun_int_bool,skf656(X30:fun_int_bool,X34:fun_int_bool,W:inT)))* SkP23(X30:fun_int_bool,X34:fun_int_bool).
(d0,A,r0,rw0) 1428[0:Inp] ||  -> pp(aa_nat_bool(X25:fun_nat_bool,skf648(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf648(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* SkP19(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1431[0:Inp] ||  -> pp(aa_nat_bool(X25:fun_nat_bool,skf654(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf654(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* SkP22(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1422[0:Inp] ||  -> pp(aa_nat_bool(X25:fun_nat_bool,skf624(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf624(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* SkP13(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1425[0:Inp] ||  -> pp(aa_nat_bool(X25:fun_nat_bool,skf630(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* pp(aa_nat_bool(X33:fun_nat_bool,skf630(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))* SkP16(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 1421[0:Inp] ||  -> pp(aa_num_bool(X31:fun_num_bool,skf622(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf622(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP12(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1424[0:Inp] ||  -> pp(aa_num_bool(X31:fun_num_bool,skf628(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf628(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP15(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1427[0:Inp] ||  -> pp(aa_num_bool(X31:fun_num_bool,skf646(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf646(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP18(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1430[0:Inp] ||  -> pp(aa_num_bool(X31:fun_num_bool,skf652(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* pp(aa_num_bool(X32:fun_num_bool,skf652(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP21(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1889[0:MRR:1668.3,22.0] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,X6:naT)) pp(ord_less_nat2(zero_zero_nat,X3:naT)) -> pp(ord_less_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1890[0:MRR:1670.1,22.0] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(X3:naT,X6:naT)) pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1604[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT))* pp(aa_int_bool(X34:fun_int_bool,skf616(X34:fun_int_bool,X30:fun_int_bool)))* SkP11(W:inT,X30:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,order_Greatest_int(X30:fun_int_bool))).
(d0,A,r0,rw0) 1605[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))* pp(aa_nat_bool(X33:fun_nat_bool,skf614(X33:fun_nat_bool,X25:fun_nat_bool)))* SkP10(Y:naT,X25:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,order_Greatest_nat(X25:fun_nat_bool))).
(d0,A,r0,rw0) 1606[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM))* pp(aa_num_bool(X32:fun_num_bool,skf612(X32:fun_num_bool,X31:fun_num_bool)))* SkP9(U:nuM,X31:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,order_Greatest_num(X31:fun_num_bool))).
(d0,A,r0,rw0) 1593[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT))* SkP11(W:inT,X30:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,order_Greatest_int(X30:fun_int_bool))) pp(aa_int_bool(X30:fun_int_bool,skf616(X34:fun_int_bool,X30:fun_int_bool)))*.
(d0,A,r0,rw0) 1594[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))* SkP10(Y:naT,X25:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,order_Greatest_nat(X25:fun_nat_bool))) pp(aa_nat_bool(X25:fun_nat_bool,skf614(X33:fun_nat_bool,X25:fun_nat_bool)))*.
(d0,A,r0,rw0) 1595[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM))* SkP9(U:nuM,X31:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,order_Greatest_num(X31:fun_num_bool))) pp(aa_num_bool(X31:fun_num_bool,skf612(X32:fun_num_bool,X31:fun_num_bool)))*.
(d0,A,r0,rw0) 1563[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT))* SkP11(W:inT,X30:fun_int_bool) -> pp(aa_int_bool(X34:fun_int_bool,order_Greatest_int(X30:fun_int_bool))) SkP11(skf616(X34:fun_int_bool,X30:fun_int_bool),X30:fun_int_bool)*.
(d0,A,r0,rw0) 1562[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))* SkP10(Y:naT,X25:fun_nat_bool) -> pp(aa_nat_bool(X33:fun_nat_bool,order_Greatest_nat(X25:fun_nat_bool))) SkP10(skf614(X33:fun_nat_bool,X25:fun_nat_bool),X25:fun_nat_bool)*.
(d0,A,r0,rw0) 1561[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM))* SkP9(U:nuM,X31:fun_num_bool) -> pp(aa_num_bool(X32:fun_num_bool,order_Greatest_num(X31:fun_num_bool))) SkP9(skf612(X32:fun_num_bool,X31:fun_num_bool),X31:fun_num_bool)*.
(d0,A,r0,rw0) 1542[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf671(X25:fun_nat_bool,Y:naT,Z:naT)))* SkP24(X25:fun_nat_bool,Y:naT) -> pp(aa_nat_bool(X25:fun_nat_bool,divide_divide_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1505[0:Inp] || equal(plus_plus_int2(W:inT,times_times_int2(X1:inT,X4:inT)),plus_plus_int2(W:inT,times_times_int2(X1:inT,X7:inT)))* -> equal(X4:inT,X7:inT) equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1504[0:Inp] || equal(plus_plus_nat2(Y:naT,times_times_nat2(Z:naT,X3:naT)),plus_plus_nat2(Y:naT,times_times_nat2(Z:naT,X6:naT)))* -> equal(X3:naT,X6:naT) equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 1454[0:Inp] || SkP24(X25:fun_nat_bool,Y:naT) -> pp(aa_nat_bool(X25:fun_nat_bool,divide_divide_nat2(Z:naT,Y:naT))) pp(ord_less_nat2(skf670(X25:fun_nat_bool,Y:naT,Z:naT),Y:naT))*.
(d0,A,r0,rw0) 1434[0:Inp] ||  -> equal(plus_plus_int2(times_times_int2(W:inT,X1:inT),plus_plus_int2(times_times_int2(X4:inT,X1:inT),X7:inT)),plus_plus_int2(times_times_int2(plus_plus_int2(W:inT,X4:inT),X1:inT),X7:inT))**.
(d0,A,r0,rw0) 1433[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(Y:naT,Z:naT),plus_plus_nat2(times_times_nat2(X3:naT,Z:naT),X6:naT)),plus_plus_nat2(times_times_nat2(plus_plus_nat2(Y:naT,X3:naT),Z:naT),X6:naT))**.
(d0,A,r0,rw0) 1599[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(aa_nat_bool(X25:fun_nat_bool,Z:naT)) pp(ord_less_nat2(Z:naT,skf676(X25:fun_nat_bool,Y:naT)))* -> pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)).
(d0,A,r0,rw0) 1466[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X7:inT)) -> pp(ord_less_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1470[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X7:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1458[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,X7:inT)) -> pp(ord_less_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1460[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,X7:inT)) -> pp(ord_less_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X7:inT,X1:inT)))*.
(d0,A,r0,rw0) 1465[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(X3:naT,X6:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1469[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,X6:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1545[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,X6:naT)) -> pp(ord_less_eq_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1888[0:MRR:1666.1,1666.3,22.0,22.0] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(X3:naT,X6:naT)) -> pp(ord_less_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1457[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(X3:naT,X6:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1459[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,X6:naT))* -> pp(ord_less_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X6:naT,Z:naT)))*.
(d0,A,r0,rw0) 1530[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X1:inT,W:inT)) -> pp(ord_less_eq_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1533[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X1:inT,W:inT)) -> pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1455[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* equal(plus_plus_nat2(X3:naT,Z:naT),plus_plus_nat2(Y:naT,X6:naT))* -> pp(ord_less_nat2(X3:naT,X6:naT))*.
(d0,A,r0,rw0) 1435[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT)))* -> pp(ord_less_int2(W:inT,X4:inT)) pp(ord_less_int2(X4:inT,W:inT)).
(d0,A,r0,rw0) 1439[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)) pp(ord_less_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1402[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(X1:inT,times_times_int2(X4:inT,W:inT)),W:inT),plus_plus_int2(X4:inT,divide_divide_int2(X1:inT,W:inT)))**.
(d0,A,r0,rw0) 1404[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(X1:inT,times_times_int2(W:inT,X4:inT)),W:inT),plus_plus_int2(X4:inT,divide_divide_int2(X1:inT,W:inT)))**.
(d0,A,r0,rw0) 1406[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(times_times_int2(X1:inT,W:inT),X4:inT),W:inT),plus_plus_int2(X1:inT,divide_divide_int2(X4:inT,W:inT)))**.
(d0,A,r0,rw0) 1408[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(times_times_int2(W:inT,X1:inT),X4:inT),W:inT),plus_plus_int2(X1:inT,divide_divide_int2(X4:inT,W:inT)))**.
(d0,A,r0,rw0) 1401[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(Z:naT,times_times_nat2(X3:naT,Y:naT)),Y:naT),plus_plus_nat2(X3:naT,divide_divide_nat2(Z:naT,Y:naT)))**.
(d0,A,r0,rw0) 1403[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(Z:naT,times_times_nat2(Y:naT,X3:naT)),Y:naT),plus_plus_nat2(X3:naT,divide_divide_nat2(Z:naT,Y:naT)))**.
(d0,A,r0,rw0) 1405[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(times_times_nat2(Z:naT,Y:naT),X3:naT),Y:naT),plus_plus_nat2(Z:naT,divide_divide_nat2(X3:naT,Y:naT)))**.
(d0,A,r0,rw0) 1407[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(times_times_nat2(Y:naT,Z:naT),X3:naT),Y:naT),plus_plus_nat2(Z:naT,divide_divide_nat2(X3:naT,Y:naT)))**.
(d0,A,r0,rw0) 1289[0:Inp] || equal(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))* -> equal(W:inT,X1:inT) equal(W:inT,uminus_uminus_int1(X1:inT)).
(d0,A,r0,rw0) 1596[0:Inp] SkP8(X24:fun_int_fun_int_bool) || pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf519(X24:fun_int_fun_int_bool)),skf519(X24:fun_int_fun_int_bool))) -> pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf520(X24:fun_int_fun_int_bool)),skf521(X24:fun_int_fun_int_bool)))*.
(d0,A,r0,rw0) 1597[0:Inp] SkP7(X23:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf514(X23:fun_nat_fun_nat_bool)),skf514(X23:fun_nat_fun_nat_bool))) -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf515(X23:fun_nat_fun_nat_bool)),skf516(X23:fun_nat_fun_nat_bool)))*.
(d0,A,r0,rw0) 1598[0:Inp] SkP6(X22:fun_num_fun_num_bool) || pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf509(X22:fun_num_fun_num_bool)),skf509(X22:fun_num_fun_num_bool))) -> pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf510(X22:fun_num_fun_num_bool)),skf511(X22:fun_num_fun_num_bool)))*.
(d0,A,r0,rw0) 1475[0:Inp] SkP5(X24:fun_int_fun_int_bool) || pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf425(X24:fun_int_fun_int_bool)),skf424(X24:fun_int_fun_int_bool)))* -> pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1474[0:Inp] SkP4(X23:fun_nat_fun_nat_bool) || pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf421(X23:fun_nat_fun_nat_bool)),skf420(X23:fun_nat_fun_nat_bool)))* -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 1473[0:Inp] SkP3(X22:fun_num_fun_num_bool) || pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf417(X22:fun_num_fun_num_bool)),skf416(X22:fun_num_fun_num_bool)))* -> pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,U:nuM),X2:nuM))*.
(d0,A,r0,rw0) 1493[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1502[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1510[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_eq_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1516[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_eq_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1519[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1524[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X4:inT,X1:inT)).
(d0,A,r0,rw0) 1491[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1500[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1507[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_eq_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1513[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_eq_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1518[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1523[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1480[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,zero_zero_int)) -> pp(ord_less_eq_int2(times_times_int2(X1:inT,X4:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1483[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,zero_zero_int)) -> pp(ord_less_eq_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1487[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,zero_zero_int)) -> pp(ord_less_int2(times_times_int2(X1:inT,X4:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1496[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,zero_zero_int)) -> pp(ord_less_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1511[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,zero_zero_int))* -> pp(ord_less_eq_int2(times_times_int2(X1:inT,X4:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1517[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X4:inT,zero_zero_int))* -> pp(ord_less_eq_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1477[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1479[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_eq_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1485[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1486[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1509[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT))* -> pp(ord_less_eq_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1515[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT))* -> pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1506[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),times_times_nat2(X3:naT,Y:naT)))* -> pp(ord_less_eq_nat2(Z:naT,X3:naT)).
(d0,A,r0,rw0) 1512[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_eq_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)))* -> pp(ord_less_eq_nat2(Z:naT,X3:naT)).
(d0,A,r0,rw0) 1543[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_nat2(divide_divide_nat2(Z:naT,Y:naT),X3:naT))* -> pp(ord_less_nat2(Z:naT,times_times_nat2(X3:naT,Y:naT))).
(d0,A,r0,rw0) 1540[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),X3:naT)) -> pp(ord_less_eq_nat2(Z:naT,divide_divide_nat2(X3:naT,Y:naT)))*.
(d0,A,r0,rw0) 1539[0:Inp] || pp(ord_less_eq_nat2(Y:naT,divide_divide_nat2(Z:naT,X3:naT)))* pp(ord_less_nat2(zero_zero_nat,X3:naT)) -> pp(ord_less_eq_nat2(times_times_nat2(Y:naT,X3:naT),Z:naT)).
(d0,A,r0,rw0) 1484[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(zero_zero_nat,X3:naT)) -> pp(ord_less_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1488[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(zero_zero_nat,X3:naT)) -> pp(ord_less_nat2(times_times_nat2(Y:naT,X3:naT),times_times_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1541[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_eq_nat2(divide_divide_nat2(X3:naT,Z:naT),divide_divide_nat2(X3:naT,Y:naT)))*.
(d0,A,r0,rw0) 1436[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT)))* -> pp(ord_less_int2(W:inT,X4:inT)) pp(ord_less_int2(X1:inT,zero_zero_int)).
(d0,A,r0,rw0) 1440[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)) pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1437[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT)))* -> pp(ord_less_int2(X4:inT,W:inT)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1441[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X4:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1443[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(X4:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1445[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(X4:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1447[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(X4:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1449[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(X4:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1444[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(zero_zero_int,X4:inT)) pp(ord_less_int2(times_times_int2(X1:inT,X4:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1446[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(zero_zero_int,X4:inT)) pp(ord_less_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1448[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(zero_zero_int,X4:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,X4:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1450[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(zero_zero_int,X4:inT))* pp(ord_less_eq_int2(times_times_int2(X4:inT,X1:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1330[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) pp(ord_less_eq_num2(skf618(U:nuM,X31:fun_num_bool),U:nuM))* -> equal(order_Greatest_num(X31:fun_num_bool),U:nuM).
(d0,A,r0,rw0) 1332[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) pp(ord_less_eq_int2(skf620(W:inT,X30:fun_int_bool),W:inT))* -> equal(order_Greatest_int(X30:fun_int_bool),W:inT).
(d0,A,r0,rw0) 1331[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_eq_nat2(skf619(Y:naT,X25:fun_nat_bool),Y:naT))* -> equal(order_Greatest_nat(X25:fun_nat_bool),Y:naT).
(d0,A,r0,rw0) 1329[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,skf508(X25:fun_nat_bool))) pp(aa_nat_bool(X25:fun_nat_bool,skf507(X25:fun_nat_bool,Y:naT)))*.
(d0,A,r0,rw0) 1328[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,skf508(X25:fun_nat_bool)))* pp(ord_less_nat2(skf507(X25:fun_nat_bool,Y:naT),Y:naT))*.
(d0,A,r0,rw0) 1417[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT))* equal(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT))* -> equal(Z:naT,X3:naT).
(d0,A,r0,rw0) 1420[0:Inp] || pp(dvd_dvd_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)))* -> pp(dvd_dvd_nat2(Z:naT,X3:naT)) equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 1419[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> equal(divide_divide_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)),divide_divide_nat2(Z:naT,X3:naT))**.
(d0,A,r0,rw0) 1254[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM)) -> pp(aa_num_bool(X31:fun_num_bool,skf618(U:nuM,X31:fun_num_bool)))* equal(order_Greatest_num(X31:fun_num_bool),U:nuM).
(d0,A,r0,rw0) 1256[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT)) -> pp(aa_int_bool(X30:fun_int_bool,skf620(W:inT,X30:fun_int_bool)))* equal(order_Greatest_int(X30:fun_int_bool),W:inT).
(d0,A,r0,rw0) 1255[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,skf619(Y:naT,X25:fun_nat_bool)))* equal(order_Greatest_nat(X25:fun_nat_bool),Y:naT).
(d0,A,r0,rw0) 1210[0:Inp] || equal(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT))* -> equal(W:inT,X4:inT) equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1212[0:Inp] || equal(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT))* -> equal(X1:inT,X4:inT) equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1232[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)),divide_divide_int2(X1:inT,X4:inT))**.
(d0,A,r0,rw0) 1234[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)),divide_divide_int2(X1:inT,X4:inT))**.
(d0,A,r0,rw0) 1209[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),times_times_nat2(X3:naT,Z:naT))* -> equal(Y:naT,X3:naT) equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 1211[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT))* -> equal(Z:naT,X3:naT) equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 1231[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)),divide_divide_nat2(Z:naT,X3:naT))**.
(d0,A,r0,rw0) 1233[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(times_times_nat2(Z:naT,Y:naT),times_times_nat2(X3:naT,Y:naT)),divide_divide_nat2(Z:naT,X3:naT))**.
(d0,A,r0,rw0) 1126[0:Inp] ||  -> equal(plus_plus_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)),times_times_int2(W:inT,plus_plus_int2(X1:inT,X4:inT)))**.
(d0,A,r0,rw0) 1124[0:Inp] ||  -> equal(plus_plus_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT)),times_times_int2(plus_plus_int2(W:inT,X4:inT),X1:inT))**.
(d0,A,r0,rw0) 1125[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)),times_times_nat2(Y:naT,plus_plus_nat2(Z:naT,X3:naT)))**.
(d0,A,r0,rw0) 1123[0:Inp] ||  -> equal(plus_plus_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(X3:naT,Z:naT)),times_times_nat2(plus_plus_nat2(Y:naT,X3:naT),Z:naT))**.
(d0,A,r0,rw0) 1620[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)) pp(aa_nat_bool(X25:fun_nat_bool,one_one_nat)) pp(aa_nat_bool(X25:fun_nat_bool,plus_plus_nat2(skf685(X25:fun_nat_bool),numeral_numeral_nat1(bit01(onE)))))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))*.
(d0,A,r0,rw0) 1600[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1438[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(X4:inT,X1:inT)))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1442[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1315[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(W:inT,plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1319[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_eq_int2(W:inT,plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1323[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_eq_int2(W:inT,plus_plus_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1307[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(W:inT,plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1309[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(zero_zero_int,X4:inT)) -> pp(ord_less_int2(W:inT,plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1317[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X4:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1321[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_eq_int2(X4:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(W:inT,X4:inT),X1:inT))*.
(d0,A,r0,rw0) 1399[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),times_times_int2(X4:inT,W:inT)))*.
(d0,A,r0,rw0) 1400[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 1306[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(zero_zero_nat,X3:naT)) -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1316[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X3:naT,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 1320[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(X3:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,X3:naT),Z:naT))*.
(d0,A,r0,rw0) 1294[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) -> pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)) pp(aa_nat_bool(X25:fun_nat_bool,skf676(X25:fun_nat_bool,Y:naT)))*.
(d0,A,r0,rw0) 1291[0:Inp] ||  -> equal(bit11(plus_plus_num2(plus_plus_num2(U:nuM,X2:nuM),bit01(times_times_num2(U:nuM,X2:nuM)))),times_times_num2(bit11(U:nuM),bit11(X2:nuM)))**.
(d0,A,r0,rw0) 1875[0:Rew:372.0,1292.1] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(Z:naT,plus_plus_nat2(Y:naT,times_times_nat2(Y:naT,divide_divide_nat2(Z:naT,Y:naT)))))*.
(d0,A,r0,rw0) 1173[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X9:nuM,U:nuM))* -> pp(ord_less_eq_num2(X9:nuM,X2:nuM))*.
(d0,A,r0,rw0) 1182[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X9:nuM,U:nuM))* -> pp(ord_less_num2(X9:nuM,X2:nuM))*.
(d0,A,r0,rw0) 1170[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X9:nuM,U:nuM))* -> pp(ord_less_num2(X9:nuM,X2:nuM))*.
(d0,A,r0,rw0) 1194[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X9:nuM,U:nuM))* -> pp(ord_less_num2(X9:nuM,X2:nuM))*.
(d0,A,r0,rw0) 1175[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X4:inT,W:inT))* -> pp(ord_less_eq_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 1184[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_int2(X4:inT,W:inT))* -> pp(ord_less_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 1172[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_int2(X4:inT,W:inT))* -> pp(ord_less_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 1196[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X4:inT,W:inT))* -> pp(ord_less_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 1174[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(X3:naT,Y:naT))* -> pp(ord_less_eq_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 1183[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(X3:naT,Y:naT))* -> pp(ord_less_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 1171[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(X3:naT,Y:naT))* -> pp(ord_less_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 1195[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(X3:naT,Y:naT))* -> pp(ord_less_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 1241[0:Inp] ||  -> equal(times_times_nat2(numeral_numeral_nat1(U:nuM),times_times_nat2(numeral_numeral_nat1(X2:nuM),Y:naT)),times_times_nat2(numeral_numeral_nat1(times_times_num2(U:nuM,X2:nuM)),Y:naT))**.
(d0,A,r0,rw0) 1242[0:Inp] ||  -> equal(times_times_int2(numeral_numeral_int1(U:nuM),times_times_int2(numeral_numeral_int1(X2:nuM),W:inT)),times_times_int2(numeral_numeral_int1(times_times_num2(U:nuM,X2:nuM)),W:inT))**.
(d0,A,r0,rw0) 1243[0:Inp] ||  -> equal(plus_plus_nat2(numeral_numeral_nat1(U:nuM),plus_plus_nat2(numeral_numeral_nat1(X2:nuM),Y:naT)),plus_plus_nat2(numeral_numeral_nat1(plus_plus_num2(U:nuM,X2:nuM)),Y:naT))**.
(d0,A,r0,rw0) 1244[0:Inp] ||  -> equal(plus_plus_int2(numeral_numeral_int1(U:nuM),plus_plus_int2(numeral_numeral_int1(X2:nuM),W:inT)),plus_plus_int2(numeral_numeral_int1(plus_plus_num2(U:nuM,X2:nuM)),W:inT))**.
(d0,A,r0,rw0) 1871[0:Rew:352.0,1238.0] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(X1:inT,W:inT),W:inT),plus_plus_int2(one_one_int,divide_divide_int2(X1:inT,W:inT)))**.
(d0,A,r0,rw0) 1873[0:Rew:352.0,1240.0] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(plus_plus_int2(W:inT,X1:inT),W:inT),plus_plus_int2(one_one_int,divide_divide_int2(X1:inT,W:inT)))**.
(d0,A,r0,rw0) 1870[0:Rew:351.0,1237.0] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(Z:naT,Y:naT),Y:naT),plus_plus_nat2(one_one_nat,divide_divide_nat2(Z:naT,Y:naT)))**.
(d0,A,r0,rw0) 1872[0:Rew:351.0,1239.0] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(plus_plus_nat2(Y:naT,Z:naT),Y:naT),plus_plus_nat2(one_one_nat,divide_divide_nat2(Z:naT,Y:naT)))**.
(d0,A,r0,rw0) 1120[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,U:nuM))* SkP9(X2:nuM,X31:fun_num_bool)* -> pp(ord_less_eq_num2(U:nuM,X2:nuM))*.
(d0,A,r0,rw0) 1122[0:Inp] || pp(aa_int_bool(X30:fun_int_bool,W:inT))* SkP11(X1:inT,X30:fun_int_bool)* -> pp(ord_less_eq_int2(W:inT,X1:inT))*.
(d0,A,r0,rw0) 1121[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))* SkP10(Z:naT,X25:fun_nat_bool)* -> pp(ord_less_eq_nat2(Y:naT,Z:naT))*.
(d0,A,r0,rw0) 1040[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(W:inT,X4:inT)))* -> pp(ord_less_eq_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1044[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(X4:inT,X1:inT)))* -> pp(ord_less_eq_int2(W:inT,X4:inT)).
(d0,A,r0,rw0) 1048[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(W:inT,X4:inT)))* -> pp(ord_less_int2(X1:inT,X4:inT)).
(d0,A,r0,rw0) 1052[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(X4:inT,X1:inT)))* -> pp(ord_less_int2(W:inT,X4:inT)).
(d0,A,r0,rw0) 1041[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1045[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(plus_plus_int2(W:inT,X4:inT),plus_plus_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1049[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_int2(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X4:inT,X1:inT)))*.
(d0,A,r0,rw0) 1053[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_int2(plus_plus_int2(W:inT,X4:inT),plus_plus_int2(X1:inT,X4:inT)))*.
(d0,A,r0,rw0) 1038[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(Y:naT,X3:naT)))* -> pp(ord_less_eq_nat2(Z:naT,X3:naT)).
(d0,A,r0,rw0) 1042[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(X3:naT,Z:naT)))* -> pp(ord_less_eq_nat2(Y:naT,X3:naT)).
(d0,A,r0,rw0) 1046[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(Y:naT,X3:naT)))* -> pp(ord_less_nat2(Z:naT,X3:naT)).
(d0,A,r0,rw0) 1050[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(X3:naT,Z:naT)))* -> pp(ord_less_nat2(Y:naT,X3:naT)).
(d0,A,r0,rw0) 1157[0:Inp] || pp(ord_less_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(X3:naT,Z:naT)))* -> pp(ord_less_nat2(Y:naT,X3:naT)).
(d0,A,r0,rw0) 1159[0:Inp] || pp(ord_less_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)))* -> pp(ord_less_nat2(Z:naT,X3:naT)).
(d0,A,r0,rw0) 1161[0:Inp] || pp(ord_less_nat2(Y:naT,times_times_nat2(Z:naT,X3:naT))) -> pp(ord_less_nat2(divide_divide_nat2(Y:naT,X3:naT),Z:naT))*.
(d0,A,r0,rw0) 1039[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1043[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,X3:naT),plus_plus_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1047[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_nat2(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1051[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_nat2(plus_plus_nat2(Y:naT,X3:naT),plus_plus_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1154[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1155[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(times_times_nat2(Y:naT,X3:naT),times_times_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1169[0:Inp] || pp(dvd_dvd_nat2(Y:naT,Z:naT)) -> pp(dvd_dvd_nat2(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1054[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X2:nuM,U:nuM))* -> equal(X2:nuM,U:nuM).
(d0,A,r0,rw0) 1056[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X1:inT,W:inT))* -> equal(X1:inT,W:inT).
(d0,A,r0,rw0) 1055[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(Z:naT,Y:naT))* -> equal(Z:naT,Y:naT).
(d0,A,r0,rw0) 967[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* -> pp(ord_less_num2(U:nuM,X2:nuM)) equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 969[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(W:inT,X1:inT))* equal(W:inT,X1:inT).
(d0,A,r0,rw0) 1023[0:Inp] || equal(W:inT,uminus_uminus_int1(X1:inT)) -> equal(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))*.
(d0,A,r0,rw0) 968[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* -> pp(ord_less_nat2(Y:naT,Z:naT)) equal(Y:naT,Z:naT).
(d0,A,r0,rw0) 964[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* -> equal(plus_plus_nat2(Y:naT,skf341(Y:naT,Z:naT)),Z:naT)**.
(d0,A,r0,rw0) 965[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* -> equal(plus_plus_nat2(Y:naT,skf342(Y:naT,Z:naT)),Z:naT)**.
(d0,A,r0,rw0) 966[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* -> equal(plus_plus_nat2(Y:naT,skf343(Y:naT,Z:naT)),Z:naT)**.
(d0,A,r0,rw0) 1033[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* -> equal(plus_plus_nat2(Y:naT,skf678(Z:naT,Y:naT)),Z:naT)**.
(d0,A,r0,rw0) 781[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(W:inT,X4:inT))* -> equal(X1:inT,X4:inT).
(d0,A,r0,rw0) 785[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(X4:inT,X1:inT))* -> equal(W:inT,X4:inT).
(d0,A,r0,rw0) 782[0:Inp] || equal(W:inT,X1:inT) -> equal(plus_plus_int2(X4:inT,W:inT),plus_plus_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 786[0:Inp] || equal(W:inT,X1:inT) -> equal(plus_plus_int2(W:inT,X4:inT),plus_plus_int2(X1:inT,X4:inT))*.
(d0,A,r0,rw0) 890[0:Inp] || equal(W:inT,X1:inT) -> equal(times_times_int2(W:inT,X4:inT),times_times_int2(X1:inT,X4:inT))*.
(d0,A,r0,rw0) 894[0:Inp] || equal(W:inT,X1:inT) -> equal(times_times_int2(X4:inT,W:inT),times_times_int2(X4:inT,X1:inT))*.
(d0,A,r0,rw0) 792[0:Inp] ||  -> equal(plus_plus_int2(W:inT,plus_plus_int2(X1:inT,X4:inT)),plus_plus_int2(X1:inT,plus_plus_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 896[0:Inp] ||  -> equal(times_times_int2(W:inT,times_times_int2(X1:inT,X4:inT)),times_times_int2(X1:inT,times_times_int2(W:inT,X4:inT)))*.
(d0,A,r0,rw0) 798[0:Inp] ||  -> equal(plus_plus_int2(plus_plus_int2(W:inT,X1:inT),X4:inT),plus_plus_int2(W:inT,plus_plus_int2(X1:inT,X4:inT)))**.
(d0,A,r0,rw0) 898[0:Inp] ||  -> equal(times_times_int2(times_times_int2(W:inT,X1:inT),X4:inT),times_times_int2(W:inT,times_times_int2(X1:inT,X4:inT)))**.
(d0,A,r0,rw0) 779[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(Y:naT,X3:naT))* -> equal(Z:naT,X3:naT).
(d0,A,r0,rw0) 783[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(X3:naT,Z:naT))* -> equal(Y:naT,X3:naT).
(d0,A,r0,rw0) 780[0:Inp] || equal(Y:naT,Z:naT) -> equal(plus_plus_nat2(X3:naT,Y:naT),plus_plus_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 784[0:Inp] || equal(Y:naT,Z:naT) -> equal(plus_plus_nat2(Y:naT,X3:naT),plus_plus_nat2(Z:naT,X3:naT))*.
(d0,A,r0,rw0) 888[0:Inp] || equal(Y:naT,Z:naT) -> equal(times_times_nat2(Y:naT,X3:naT),times_times_nat2(Z:naT,X3:naT))*.
(d0,A,r0,rw0) 892[0:Inp] || equal(Y:naT,Z:naT) -> equal(times_times_nat2(X3:naT,Y:naT),times_times_nat2(X3:naT,Z:naT))*.
(d0,A,r0,rw0) 791[0:Inp] ||  -> equal(plus_plus_nat2(Y:naT,plus_plus_nat2(Z:naT,X3:naT)),plus_plus_nat2(Z:naT,plus_plus_nat2(Y:naT,X3:naT)))*.
(d0,A,r0,rw0) 895[0:Inp] ||  -> equal(times_times_nat2(Y:naT,times_times_nat2(Z:naT,X3:naT)),times_times_nat2(Z:naT,times_times_nat2(Y:naT,X3:naT)))*.
(d0,A,r0,rw0) 797[0:Inp] ||  -> equal(plus_plus_nat2(plus_plus_nat2(Y:naT,Z:naT),X3:naT),plus_plus_nat2(Y:naT,plus_plus_nat2(Z:naT,X3:naT)))**.
(d0,A,r0,rw0) 897[0:Inp] ||  -> equal(times_times_nat2(times_times_nat2(Y:naT,Z:naT),X3:naT),times_times_nat2(Y:naT,times_times_nat2(Z:naT,X3:naT)))**.
(d0,A,r0,rw0) 954[0:Inp] ||  -> equal(divide_divide_nat2(divide_divide_nat2(Y:naT,Z:naT),X3:naT),divide_divide_nat2(Y:naT,times_times_nat2(Z:naT,X3:naT)))**.
(d0,A,r0,rw0) 852[0:Inp] ||  -> pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X2:nuM,U:nuM))* equal(X2:nuM,U:nuM).
(d0,A,r0,rw0) 930[0:Inp] || equal(W:inT,X1:inT) -> equal(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))*.
(d0,A,r0,rw0) 854[0:Inp] ||  -> pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_int2(X1:inT,W:inT))* equal(X1:inT,W:inT).
(d0,A,r0,rw0) 853[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(Z:naT,Y:naT))* equal(Z:naT,Y:naT).
(d0,A,r0,rw0) 727[0:Inp] ||  -> pp(ord_less_nat2(skf648(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT),Y:naT))* SkP19(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 729[0:Inp] ||  -> pp(ord_less_nat2(skf654(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT),Y:naT))* SkP22(X25:fun_nat_bool,X33:fun_nat_bool).
(d0,A,r0,rw0) 721[0:Inp] ||  -> pp(ord_less_num2(U:nuM,skf622(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP12(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 722[0:Inp] ||  -> pp(ord_less_num2(U:nuM,skf628(X31:fun_num_bool,X32:fun_num_bool,U:nuM)))* SkP15(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 726[0:Inp] ||  -> pp(ord_less_num2(skf646(X31:fun_num_bool,X32:fun_num_bool,U:nuM),U:nuM))* SkP18(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 728[0:Inp] ||  -> pp(ord_less_num2(skf652(X31:fun_num_bool,X32:fun_num_bool,U:nuM),U:nuM))* SkP21(X31:fun_num_bool,X32:fun_num_bool).
(d0,A,r0,rw0) 1621[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> equal(divide_divide_int2(plus_plus_int2(one_one_int,times_times_int2(numeral_numeral_int1(bit01(onE)),X1:inT)),times_times_int2(numeral_numeral_int1(bit01(onE)),W:inT)),divide_divide_int2(plus_plus_int2(X1:inT,one_one_int),W:inT))**.
(d0,A,r0,rw0) 1609[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> equal(divide_divide_int2(plus_plus_int2(one_one_int,times_times_int2(numeral_numeral_int1(bit01(onE)),X1:inT)),times_times_int2(numeral_numeral_int1(bit01(onE)),W:inT)),divide_divide_int2(X1:inT,W:inT))**.
(d0,A,r0,rw0) 1602[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(X1:inT,one_one_int)) pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),one_one_int))*.
(d0,A,r0,rw0) 1559[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(X1:inT,zero_zero_int))* equal(plus_plus_int2(X1:inT,W:inT),zero_zero_int)** -> equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1560[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(X1:inT,zero_zero_int))* equal(plus_plus_int2(X1:inT,W:inT),zero_zero_int)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1555[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(zero_zero_int,X1:inT))* equal(plus_plus_int2(X1:inT,W:inT),zero_zero_int)** -> equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1556[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(zero_zero_int,X1:inT))* equal(plus_plus_int2(X1:inT,W:inT),zero_zero_int)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1867[0:Rew:389.0,1413.0,336.0,1413.0] || pp(aa_num_bool(X31:fun_num_bool,onE)) pp(aa_num_bool(X31:fun_num_bool,plus_plus_num2(onE,skf669(X31:fun_num_bool))))* -> pp(aa_num_bool(X31:fun_num_bool,U:nuM))*.
(d0,A,r0,rw0) 1341[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(W:inT,times_times_int2(X1:inT,W:inT)))* -> pp(ord_less_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1347[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(W:inT,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1353[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(W:inT,times_times_int2(X1:inT,W:inT)))* -> pp(ord_less_eq_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1359[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(W:inT,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_eq_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1337[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),W:inT))* -> pp(ord_less_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1343[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1349[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),W:inT))* -> pp(ord_less_eq_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1355[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_eq_int2(X1:inT,one_one_int)).
(d0,A,r0,rw0) 1354[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,times_times_int2(W:inT,X1:inT)))*.
(d0,A,r0,rw0) 1360[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1340[0:Inp] || pp(ord_less_int2(W:inT,times_times_int2(X1:inT,W:inT)))* pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1346[0:Inp] || pp(ord_less_int2(W:inT,times_times_int2(W:inT,X1:inT)))* pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1352[0:Inp] || pp(ord_less_eq_int2(W:inT,times_times_int2(X1:inT,W:inT)))* pp(ord_less_int2(zero_zero_int,W:inT))* -> pp(ord_less_eq_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1358[0:Inp] || pp(ord_less_eq_int2(W:inT,times_times_int2(W:inT,X1:inT)))* pp(ord_less_int2(zero_zero_int,W:inT))* -> pp(ord_less_eq_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1338[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),W:inT))* -> pp(ord_less_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1344[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1350[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),W:inT))* -> pp(ord_less_eq_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1356[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_eq_int2(one_one_int,X1:inT)).
(d0,A,r0,rw0) 1351[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1357[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1336[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1416[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(zero_zero_nat,divide_divide_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1414[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_nat2(one_one_nat,Z:naT)) -> pp(ord_less_nat2(divide_divide_nat2(Y:naT,Z:naT),Y:naT))*.
(d0,A,r0,rw0) 1295[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)) pp(aa_nat_bool(X25:fun_nat_bool,skf677(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))*.
(d0,A,r0,rw0) 1296[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)) pp(ord_less_nat2(Y:naT,skf677(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 1259[0:Inp] || pp(ord_less_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(X1:inT,times_times_int2(W:inT,X1:inT)))*.
(d0,A,r0,rw0) 1263[0:Inp] || pp(ord_less_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(X1:inT,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1267[0:Inp] || pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_int2(X1:inT,zero_zero_int))* pp(ord_less_eq_int2(X1:inT,times_times_int2(W:inT,X1:inT)))*.
(d0,A,r0,rw0) 1271[0:Inp] || pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_int2(X1:inT,zero_zero_int))* pp(ord_less_eq_int2(X1:inT,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1260[0:Inp] || pp(ord_less_int2(W:inT,one_one_int)) -> pp(ord_less_int2(X1:inT,times_times_int2(W:inT,X1:inT)))* pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1264[0:Inp] || pp(ord_less_int2(W:inT,one_one_int)) -> pp(ord_less_int2(X1:inT,times_times_int2(X1:inT,W:inT)))* pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1268[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) -> pp(ord_less_eq_int2(X1:inT,times_times_int2(W:inT,X1:inT)))* pp(ord_less_int2(zero_zero_int,X1:inT))*.
(d0,A,r0,rw0) 1272[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) -> pp(ord_less_eq_int2(X1:inT,times_times_int2(X1:inT,W:inT)))* pp(ord_less_int2(zero_zero_int,X1:inT))*.
(d0,A,r0,rw0) 1257[0:Inp] || pp(ord_less_int2(W:inT,one_one_int)) -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1261[0:Inp] || pp(ord_less_int2(W:inT,one_one_int)) -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1265[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) -> pp(ord_less_int2(X1:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1269[0:Inp] || pp(ord_less_eq_int2(W:inT,one_one_int)) -> pp(ord_less_int2(X1:inT,zero_zero_int))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1258[0:Inp] || pp(ord_less_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(zero_zero_int,X1:inT)) pp(ord_less_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1262[0:Inp] || pp(ord_less_int2(one_one_int,W:inT)) -> pp(ord_less_eq_int2(zero_zero_int,X1:inT)) pp(ord_less_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1266[0:Inp] || pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_int2(zero_zero_int,X1:inT))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 1270[0:Inp] || pp(ord_less_eq_int2(one_one_int,W:inT)) -> pp(ord_less_int2(zero_zero_int,X1:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 1229[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT)),zero_zero_int))* -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1230[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT)),zero_zero_int))* -> equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1226[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(W:inT,times_times_int2(X1:inT,W:inT)))* pp(ord_less_int2(zero_zero_int,W:inT))*.
(d0,A,r0,rw0) 1228[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_eq_int2(W:inT,times_times_int2(W:inT,X1:inT)))* pp(ord_less_int2(zero_zero_int,W:inT))*.
(d0,A,r0,rw0) 1225[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),W:inT))*.
(d0,A,r0,rw0) 1227[0:Inp] ||  -> pp(ord_less_int2(W:inT,zero_zero_int))* pp(ord_less_int2(zero_zero_int,W:inT))* pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),W:inT))*.
(d0,A,r0,rw0) 1246[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT))* equal(divide_divide_nat2(Y:naT,Z:naT),Y:naT)** -> equal(Z:naT,one_one_nat).
(d0,A,r0,rw0) 1247[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT))* equal(Z:naT,one_one_nat) -> equal(divide_divide_nat2(Y:naT,Z:naT),Y:naT)**.
(d0,A,r0,rw0) 1156[0:Inp] || pp(ord_less_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(X3:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 1158[0:Inp] || pp(ord_less_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Y:naT)).
(d0,A,r0,rw0) 1135[0:Inp] || equal(plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT)),zero_zero_int)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1136[0:Inp] || equal(plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT)),zero_zero_int)** -> equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1133[0:Inp] ||  -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))))* equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 1134[0:Inp] ||  -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))))* equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1160[0:Inp] || equal(divide_divide_nat2(Y:naT,Z:naT),zero_zero_nat) -> pp(ord_less_nat2(Y:naT,Z:naT))* equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 1168[0:Inp] ||  -> equal(U:nuM,onE) equal(bit11(skf684(U:nuM)),U:nuM)** equal(bit01(skf683(U:nuM)),U:nuM).
(d0,A,r0,rw0) 1025[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_eq_nat2(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Y:naT,X3:naT)))*.
(d0,A,r0,rw0) 1026[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),times_times_nat2(X3:naT,Y:naT)))*.
(d0,A,r0,rw0) 1011[0:Inp] || equal(times_times_int2(W:inT,X1:inT),X1:inT)** -> equal(W:inT,one_one_int) equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1013[0:Inp] || equal(times_times_int2(W:inT,X1:inT),W:inT)** -> equal(W:inT,zero_zero_int) equal(X1:inT,one_one_int).
(d0,A,r0,rw0) 1034[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),Y:naT)** -> equal(Z:naT,one_one_nat) equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 1027[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> equal(divide_divide_nat2(times_times_nat2(Z:naT,Y:naT),Y:naT),Z:naT)**.
(d0,A,r0,rw0) 1028[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> equal(divide_divide_nat2(times_times_nat2(Y:naT,Z:naT),Y:naT),Z:naT)**.
(d0,A,r0,rw0) 955[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(Y:naT,Z:naT),X3:naT))* -> pp(ord_less_nat2(Y:naT,X3:naT)).
(d0,A,r0,rw0) 956[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 957[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1876[0:MRR:1318.0,22.0] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(Y:naT,plus_plus_nat2(X3:naT,Z:naT)))*.
(d0,A,r0,rw0) 1877[0:MRR:1322.0,22.0] || pp(ord_less_eq_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(Y:naT,plus_plus_nat2(Z:naT,X3:naT)))*.
(d0,A,r0,rw0) 1854[0:Rew:336.0,770.0] ||  -> equal(times_times_num2(U:nuM,plus_plus_num2(X2:nuM,onE)),plus_plus_num2(times_times_num2(U:nuM,X2:nuM),U:nuM))*.
(d0,A,r0,rw0) 718[0:Inp] || pp(ord_less_eq_num2(skf613(U:nuM,X31:fun_num_bool),U:nuM))* -> SkP9(U:nuM,X31:fun_num_bool).
(d0,A,r0,rw0) 720[0:Inp] || pp(ord_less_eq_int2(skf617(W:inT,X30:fun_int_bool),W:inT))* -> SkP11(W:inT,X30:fun_int_bool).
(d0,A,r0,rw0) 773[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,divide_divide_nat2(Y:naT,Z:naT)))* -> SkP24(X25:fun_nat_bool,Z:naT).
(d0,A,r0,rw0) 719[0:Inp] || pp(ord_less_eq_nat2(skf615(Y:naT,X25:fun_nat_bool),Y:naT))* -> SkP10(Y:naT,X25:fun_nat_bool).
(d0,A,r0,rw0) 669[0:Inp] || equal(Y:naT,plus_plus_nat2(Z:naT,X3:naT))* -> pp(ord_less_eq_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 735[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(times_times_int2(X1:inT,W:inT),W:inT),X1:inT)**.
(d0,A,r0,rw0) 737[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(times_times_int2(W:inT,X1:inT),W:inT),X1:inT)**.
(d0,A,r0,rw0) 734[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(times_times_nat2(Z:naT,Y:naT),Y:naT),Z:naT)**.
(d0,A,r0,rw0) 736[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(times_times_nat2(Y:naT,Z:naT),Y:naT),Z:naT)**.
(d0,A,r0,rw0) 609[0:Inp] ||  -> pp(aa_num_bool(X31:fun_num_bool,skf613(U:nuM,X31:fun_num_bool)))* SkP9(U:nuM,X31:fun_num_bool).
(d0,A,r0,rw0) 611[0:Inp] ||  -> pp(aa_int_bool(X30:fun_int_bool,skf617(W:inT,X30:fun_int_bool)))* SkP11(W:inT,X30:fun_int_bool).
(d0,A,r0,rw0) 610[0:Inp] ||  -> pp(aa_nat_bool(X25:fun_nat_bool,skf615(Y:naT,X25:fun_nat_bool)))* SkP10(Y:naT,X25:fun_nat_bool).
(d0,A,r0,rw0) 437[0:Inp] ||  -> pp(ord_less_eq_num2(U:nuM,X2:nuM))* SkP0(X9:nuM,X2:nuM,U:nuM)*.
(d0,A,r0,rw0) 438[0:Inp] ||  -> pp(ord_less_eq_num2(U:nuM,X2:nuM))* SkP0(X2:nuM,U:nuM,X9:nuM)*.
(d0,A,r0,rw0) 441[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,X1:inT))* SkP2(X4:inT,X1:inT,W:inT)*.
(d0,A,r0,rw0) 442[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,X1:inT))* SkP2(X1:inT,W:inT,X4:inT)*.
(d0,A,r0,rw0) 439[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,Z:naT))* SkP1(X3:naT,Z:naT,Y:naT)*.
(d0,A,r0,rw0) 440[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,Z:naT))* SkP1(Z:naT,Y:naT,X3:naT)*.
(d0,A,r0,rw0) 1852[0:Rew:352.0,1452.0] || pp(ord_less_int2(plus_plus_int2(W:inT,plus_plus_int2(one_one_int,W:inT)),zero_zero_int))* member_int(W:inT,ring_1_Ints_int) -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1853[0:Rew:352.0,1453.2] || pp(ord_less_int2(W:inT,zero_zero_int)) member_int(W:inT,ring_1_Ints_int) -> pp(ord_less_int2(plus_plus_int2(W:inT,plus_plus_int2(one_one_int,W:inT)),zero_zero_int))*.
(d0,A,r0,rw0) 1381[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,times_times_int2(X1:inT,W:inT)))* -> pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1383[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1362[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(X1:inT,zero_zero_int)) -> pp(ord_less_eq_int2(zero_zero_int,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1385[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(X1:inT,zero_zero_int)) -> pp(ord_less_int2(zero_zero_int,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1313[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1325[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1334[0:Inp] || pp(ord_less_int2(one_one_int,W:inT)) pp(ord_less_int2(one_one_int,X1:inT)) -> pp(ord_less_int2(one_one_int,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1361[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(zero_zero_int,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1384[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(zero_zero_int,times_times_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1301[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1305[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 1311[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(X1:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1327[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(X1:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1299[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_int2(X1:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1303[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(X1:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1364[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1368[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)) -> pp(ord_less_eq_int2(times_times_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1387[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1391[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)) -> pp(ord_less_int2(times_times_int2(X1:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 1333[0:Inp] || pp(ord_less_nat2(one_one_nat,Y:naT)) pp(ord_less_nat2(one_one_nat,Z:naT)) -> pp(ord_less_nat2(one_one_nat,times_times_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1388[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_nat2(zero_zero_nat,Z:naT)) -> pp(ord_less_nat2(zero_zero_nat,times_times_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1326[0:Inp] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) pp(ord_less_eq_nat2(Z:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Z:naT,Y:naT),zero_zero_nat))*.
(d0,A,r0,rw0) 1868[0:MRR:1603.2,22.0] || pp(ord_less_eq_nat2(Y:naT,one_one_nat)) pp(ord_less_eq_nat2(Z:naT,one_one_nat)) -> pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),one_one_nat))*.
(d0,A,r0,rw0) 1297[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat)) pp(aa_nat_bool(X25:fun_nat_bool,one_one_nat)) -> pp(aa_nat_bool(X25:fun_nat_bool,skf685(X25:fun_nat_bool)))*.
(d0,A,r0,rw0) 1253[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1278[0:Inp] || pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_eq_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1286[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1274[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_eq_int2(W:inT,zero_zero_int)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1275[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)) pp(ord_less_eq_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1282[0:Inp] || pp(ord_less_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1283[0:Inp] || pp(ord_less_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1281[0:Inp] || pp(ord_less_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1284[0:Inp] || pp(ord_less_int2(zero_zero_int,times_times_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1285[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_int2(X1:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1288[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_int2(W:inT,zero_zero_int)) pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 1279[0:Inp] || pp(ord_less_eq_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_eq_int2(zero_zero_int,W:inT)) pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1287[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,X1:inT),zero_zero_int))* -> pp(ord_less_int2(zero_zero_int,W:inT)) pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 1290[0:Inp] || pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(Y:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Y:naT)) pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 1143[0:Inp] || pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),uminus_uminus_int1(numeral_numeral_int1(X2:nuM))))* -> pp(ord_less_eq_num2(X2:nuM,U:nuM)).
(d0,A,r0,rw0) 1145[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),uminus_uminus_int1(numeral_numeral_int1(X2:nuM))))* -> pp(ord_less_num2(X2:nuM,U:nuM)).
(d0,A,r0,rw0) 1144[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) -> pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(X2:nuM)),uminus_uminus_int1(numeral_numeral_int1(U:nuM))))*.
(d0,A,r0,rw0) 1146[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_int2(uminus_uminus_int1(numeral_numeral_int1(X2:nuM)),uminus_uminus_int1(numeral_numeral_int1(U:nuM))))*.
(d0,A,r0,rw0) 1137[0:Inp] || member_int(W:inT,ring_1_Ints_int) member_int(X1:inT,ring_1_Ints_int) -> member_int(times_times_int2(X1:inT,W:inT),ring_1_Ints_int)*.
(d0,A,r0,rw0) 1138[0:Inp] || member_int(W:inT,ring_1_Ints_int) member_int(X1:inT,ring_1_Ints_int) -> member_int(plus_plus_int2(X1:inT,W:inT),ring_1_Ints_int)*.
(d0,A,r0,rw0) 1148[0:Inp] || equal(Y:naT,one_one_nat) equal(Z:naT,one_one_nat) -> equal(times_times_nat2(Y:naT,Z:naT),one_one_nat)**.
(d0,A,r0,rw0) 1147[0:Inp] || equal(times_times_int2(W:inT,W:inT),one_one_int)** -> equal(W:inT,one_one_int) equal(W:inT,uminus_uminus_int1(one_one_int)).
(d0,A,r0,rw0) 1029[0:Inp] || SkP24(X25:fun_nat_bool,Y:naT)* equal(Y:naT,zero_zero_nat) -> pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat))*.
(d0,A,r0,rw0) 1010[0:Inp] || equal(times_times_int2(W:inT,X1:inT),zero_zero_int)** -> equal(W:inT,zero_zero_int) equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 1009[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),zero_zero_nat)** -> equal(Y:naT,zero_zero_nat) equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 858[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)) pp(ord_less_nat2(Y:naT,skf506(X25:fun_nat_bool)))* -> .
(d0,A,r0,rw0) 851[0:Inp] || pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf426(X24:fun_int_fun_int_bool)),skf427(X24:fun_int_fun_int_bool)))* -> SkP5(X24:fun_int_fun_int_bool).
(d0,A,r0,rw0) 861[0:Inp] || pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf522(X24:fun_int_fun_int_bool)),skf523(X24:fun_int_fun_int_bool)))* -> SkP8(X24:fun_int_fun_int_bool).
(d0,A,r0,rw0) 850[0:Inp] SkP5(X24:fun_int_fun_int_bool) ||  -> pp(aa_int_bool(aa_int_fun_int_bool(X24:fun_int_fun_int_bool,skf424(X24:fun_int_fun_int_bool)),skf425(X24:fun_int_fun_int_bool)))*.
(d0,A,r0,rw0) 849[0:Inp] || pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf422(X23:fun_nat_fun_nat_bool)),skf423(X23:fun_nat_fun_nat_bool)))* -> SkP4(X23:fun_nat_fun_nat_bool).
(d0,A,r0,rw0) 860[0:Inp] || pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf517(X23:fun_nat_fun_nat_bool)),skf518(X23:fun_nat_fun_nat_bool)))* -> SkP7(X23:fun_nat_fun_nat_bool).
(d0,A,r0,rw0) 848[0:Inp] SkP4(X23:fun_nat_fun_nat_bool) ||  -> pp(aa_nat_bool(aa_nat_fun_nat_bool(X23:fun_nat_fun_nat_bool,skf420(X23:fun_nat_fun_nat_bool)),skf421(X23:fun_nat_fun_nat_bool)))*.
(d0,A,r0,rw0) 847[0:Inp] || pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf418(X22:fun_num_fun_num_bool)),skf419(X22:fun_num_fun_num_bool)))* -> SkP3(X22:fun_num_fun_num_bool).
(d0,A,r0,rw0) 859[0:Inp] || pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf512(X22:fun_num_fun_num_bool)),skf513(X22:fun_num_fun_num_bool)))* -> SkP6(X22:fun_num_fun_num_bool).
(d0,A,r0,rw0) 846[0:Inp] SkP3(X22:fun_num_fun_num_bool) ||  -> pp(aa_num_bool(aa_num_fun_num_bool(X22:fun_num_fun_num_bool,skf416(X22:fun_num_fun_num_bool)),skf417(X22:fun_num_fun_num_bool)))*.
(d0,A,r0,rw0) 884[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_num2(X2:nuM,skf666(U:nuM)))* -> .
(d0,A,r0,rw0) 875[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X2:nuM,skf596(U:nuM))) -> .
(d0,A,r0,rw0) 881[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_num2(skf639(X2:nuM),U:nuM))* -> .
(d0,A,r0,rw0) 878[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(skf605(X2:nuM),U:nuM)) -> .
(d0,A,r0,rw0) 938[0:Inp] || pp(ord_less_num2(bit01(U:nuM),bit01(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 940[0:Inp] || pp(ord_less_num2(bit11(U:nuM),bit11(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 910[0:Inp] || pp(ord_less_eq_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)))* -> pp(ord_less_eq_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 912[0:Inp] || pp(ord_less_eq_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)))* -> pp(ord_less_eq_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 914[0:Inp] || pp(ord_less_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 916[0:Inp] || pp(ord_less_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 946[0:Inp] || pp(ord_less_num2(bit11(U:nuM),bit01(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 948[0:Inp] || pp(ord_less_eq_num2(bit11(U:nuM),bit01(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 950[0:Inp] || pp(ord_less_num2(bit01(U:nuM),bit11(X2:nuM))) -> pp(ord_less_eq_num2(U:nuM,X2:nuM))*.
(d0,A,r0,rw0) 939[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_num2(bit01(U:nuM),bit01(X2:nuM)))*.
(d0,A,r0,rw0) 941[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_num2(bit11(U:nuM),bit11(X2:nuM)))*.
(d0,A,r0,rw0) 911[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) -> pp(ord_less_eq_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)))*.
(d0,A,r0,rw0) 913[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM)) -> pp(ord_less_eq_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)))*.
(d0,A,r0,rw0) 915[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)))*.
(d0,A,r0,rw0) 917[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)))*.
(d0,A,r0,rw0) 947[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_num2(bit11(U:nuM),bit01(X2:nuM)))*.
(d0,A,r0,rw0) 949[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_eq_num2(bit11(U:nuM),bit01(X2:nuM)))*.
(d0,A,r0,rw0) 951[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* -> pp(ord_less_num2(bit01(U:nuM),bit11(X2:nuM))).
(d0,A,r0,rw0) 922[0:Inp] || equal(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),uminus_uminus_int1(numeral_numeral_int1(X2:nuM)))* -> equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 923[0:Inp] || equal(U:nuM,X2:nuM) -> equal(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),uminus_uminus_int1(numeral_numeral_int1(X2:nuM)))*.
(d0,A,r0,rw0) 1839[0:Rew:389.0,643.0,336.0,643.0,336.0,643.0] ||  -> equal(plus_plus_num2(onE,plus_plus_num2(U:nuM,X2:nuM)),plus_plus_num2(U:nuM,plus_plus_num2(X2:nuM,onE)))*.
(d0,A,r0,rw0) 937[0:Inp] ||  -> equal(times_times_num2(bit01(U:nuM),bit01(X2:nuM)),bit01(bit01(times_times_num2(U:nuM,X2:nuM))))**.
(d0,A,r0,rw0) 945[0:Inp] ||  -> equal(times_times_num2(bit01(U:nuM),bit11(X2:nuM)),bit01(times_times_num2(U:nuM,bit11(X2:nuM))))**.
(d0,A,r0,rw0) 944[0:Inp] ||  -> equal(times_times_num2(bit11(U:nuM),bit01(X2:nuM)),bit01(times_times_num2(bit11(U:nuM),X2:nuM)))**.
(d0,A,r0,rw0) 886[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(X1:inT,skf668(W:inT)))* -> .
(d0,A,r0,rw0) 877[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X1:inT,skf598(W:inT)))* -> .
(d0,A,r0,rw0) 883[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) pp(ord_less_int2(skf641(X1:inT),W:inT))* -> .
(d0,A,r0,rw0) 880[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(skf607(X1:inT),W:inT))* -> .
(d0,A,r0,rw0) 909[0:Inp] || pp(ord_less_int2(W:inT,plus_plus_int2(X1:inT,one_one_int)))* -> pp(ord_less_eq_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 918[0:Inp] || pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),uminus_uminus_int1(X1:inT)))* -> pp(ord_less_eq_int2(X1:inT,W:inT)).
(d0,A,r0,rw0) 920[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(W:inT),uminus_uminus_int1(X1:inT)))* -> pp(ord_less_int2(X1:inT,W:inT)).
(d0,A,r0,rw0) 905[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,one_one_int),X1:inT)) -> pp(ord_less_int2(W:inT,X1:inT))*.
(d0,A,r0,rw0) 820[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,X1:inT),X1:inT))* -> pp(ord_less_eq_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 824[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_eq_int2(X1:inT,zero_zero_int)).
(d0,A,r0,rw0) 830[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),W:inT))* -> pp(ord_less_int2(X1:inT,zero_zero_int)).
(d0,A,r0,rw0) 834[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),X1:inT))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 924[0:Inp] || pp(ord_less_eq_int2(W:inT,uminus_uminus_int1(X1:inT)))* -> pp(ord_less_eq_int2(X1:inT,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 927[0:Inp] || pp(ord_less_int2(W:inT,uminus_uminus_int1(X1:inT)))* -> pp(ord_less_int2(X1:inT,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 813[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,plus_plus_int2(W:inT,X1:inT)))*.
(d0,A,r0,rw0) 817[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(X1:inT,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 839[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(X1:inT,plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 843[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(X1:inT,plus_plus_int2(W:inT,X1:inT)))*.
(d0,A,r0,rw0) 908[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_int2(W:inT,plus_plus_int2(X1:inT,one_one_int)))*.
(d0,A,r0,rw0) 812[0:Inp] || pp(ord_less_eq_int2(W:inT,plus_plus_int2(X1:inT,W:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 816[0:Inp] || pp(ord_less_eq_int2(W:inT,plus_plus_int2(W:inT,X1:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 838[0:Inp] || pp(ord_less_int2(W:inT,plus_plus_int2(W:inT,X1:inT)))* -> pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 842[0:Inp] || pp(ord_less_int2(W:inT,plus_plus_int2(X1:inT,W:inT)))* -> pp(ord_less_int2(zero_zero_int,X1:inT)).
(d0,A,r0,rw0) 925[0:Inp] || pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),X1:inT))* -> pp(ord_less_eq_int2(uminus_uminus_int1(X1:inT),W:inT))*.
(d0,A,r0,rw0) 928[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(W:inT),X1:inT))* -> pp(ord_less_int2(uminus_uminus_int1(X1:inT),W:inT))*.
(d0,A,r0,rw0) 919[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) -> pp(ord_less_eq_int2(uminus_uminus_int1(X1:inT),uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 921[0:Inp] || pp(ord_less_int2(W:inT,X1:inT)) -> pp(ord_less_int2(uminus_uminus_int1(X1:inT),uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 821[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 825[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 831[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(X1:inT,W:inT),X1:inT))*.
(d0,A,r0,rw0) 835[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(W:inT,X1:inT),X1:inT))*.
(d0,A,r0,rw0) 904[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* -> pp(ord_less_eq_int2(plus_plus_int2(W:inT,one_one_int),X1:inT)).
(d0,A,r0,rw0) 901[0:Inp] || pp(ord_less_int2(plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT)),zero_zero_int))* -> .
(d0,A,r0,rw0) 885[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(Z:naT,skf667(Y:naT)))* -> .
(d0,A,r0,rw0) 876[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(Z:naT,skf597(Y:naT))) -> .
(d0,A,r0,rw0) 882[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_nat2(skf640(Z:naT),Y:naT))* -> .
(d0,A,r0,rw0) 879[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(skf606(Z:naT),Y:naT)) -> .
(d0,A,r0,rw0) 907[0:Inp] || pp(ord_less_nat2(Y:naT,plus_plus_nat2(Z:naT,one_one_nat))) -> pp(ord_less_eq_nat2(Y:naT,Z:naT))*.
(d0,A,r0,rw0) 952[0:Inp] || pp(ord_less_nat2(zero_zero_nat,divide_divide_nat2(Y:naT,Z:naT)))* -> pp(ord_less_eq_nat2(Z:naT,Y:naT)).
(d0,A,r0,rw0) 903[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,one_one_nat),Z:naT))* -> pp(ord_less_nat2(Y:naT,Z:naT)).
(d0,A,r0,rw0) 818[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,Z:naT),Z:naT))* -> pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)).
(d0,A,r0,rw0) 822[0:Inp] || pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,Z:naT),Y:naT))* -> pp(ord_less_eq_nat2(Z:naT,zero_zero_nat)).
(d0,A,r0,rw0) 837[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(Z:naT,plus_plus_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 841[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(Z:naT,plus_plus_nat2(Y:naT,Z:naT)))*.
(d0,A,r0,rw0) 906[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(Z:naT,one_one_nat))).
(d0,A,r0,rw0) 836[0:Inp] || pp(ord_less_nat2(Y:naT,plus_plus_nat2(Y:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 840[0:Inp] || pp(ord_less_nat2(Y:naT,plus_plus_nat2(Z:naT,Y:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 819[0:Inp] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,Z:naT),Z:naT))*.
(d0,A,r0,rw0) 823[0:Inp] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Z:naT,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 1866[0:MRR:1335.1,22.0] || pp(ord_less_eq_nat2(Y:naT,one_one_nat)) -> pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),Z:naT))*.
(d0,A,r0,rw0) 902[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(plus_plus_nat2(Y:naT,one_one_nat),Z:naT))*.
(d0,A,r0,rw0) 674[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf504(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))*.
(d0,A,r0,rw0) 776[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf680(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))*.
(d0,A,r0,rw0) 778[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,skf682(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))*.
(d0,A,r0,rw0) 673[0:Inp] || pp(ord_less_nat2(Y:naT,skf504(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 775[0:Inp] || pp(ord_less_nat2(Y:naT,skf680(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 777[0:Inp] || pp(ord_less_nat2(Y:naT,skf682(X25:fun_nat_bool)))* -> pp(aa_nat_bool(X25:fun_nat_bool,Y:naT)).
(d0,A,r0,rw0) 678[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,Y:naT))* -> pp(aa_nat_bool(X25:fun_nat_bool,skf506(X25:fun_nat_bool)))*.
(d0,A,r0,rw0) 670[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X2:nuM,U:nuM))* -> .
(d0,A,r0,rw0) 666[0:Inp] || pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_num2(X2:nuM,U:nuM)) -> .
(d0,A,r0,rw0) 730[0:Inp] || pp(ord_less_num2(U:nuM,skf663(X2:nuM)))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 712[0:Inp] || pp(ord_less_num2(U:nuM,skf599(X2:nuM))) -> pp(ord_less_eq_num2(U:nuM,X2:nuM))*.
(d0,A,r0,rw0) 723[0:Inp] || pp(ord_less_num2(skf642(U:nuM),X2:nuM))* -> pp(ord_less_num2(U:nuM,X2:nuM)).
(d0,A,r0,rw0) 715[0:Inp] || pp(ord_less_num2(skf602(U:nuM),X2:nuM)) -> pp(ord_less_eq_num2(U:nuM,X2:nuM))*.
(d0,A,r0,rw0) 738[0:Inp] ||  -> equal(times_times_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)),numeral_numeral_nat1(times_times_num2(U:nuM,X2:nuM)))**.
(d0,A,r0,rw0) 739[0:Inp] ||  -> equal(times_times_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)),numeral_numeral_int1(times_times_num2(U:nuM,X2:nuM)))**.
(d0,A,r0,rw0) 740[0:Inp] ||  -> equal(plus_plus_nat2(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM)),numeral_numeral_nat1(plus_plus_num2(U:nuM,X2:nuM)))**.
(d0,A,r0,rw0) 741[0:Inp] ||  -> equal(plus_plus_int2(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM)),numeral_numeral_int1(plus_plus_num2(U:nuM,X2:nuM)))**.
(d0,A,r0,rw0) 672[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_int2(X1:inT,W:inT))* -> .
(d0,A,r0,rw0) 668[0:Inp] || pp(ord_less_eq_int2(W:inT,X1:inT)) pp(ord_less_int2(X1:inT,W:inT))* -> .
(d0,A,r0,rw0) 732[0:Inp] || pp(ord_less_int2(W:inT,skf665(X1:inT)))* -> pp(ord_less_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 714[0:Inp] || pp(ord_less_int2(W:inT,skf601(X1:inT)))* -> pp(ord_less_eq_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 725[0:Inp] || pp(ord_less_int2(skf644(W:inT),X1:inT))* -> pp(ord_less_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 717[0:Inp] || pp(ord_less_int2(skf604(W:inT),X1:inT))* -> pp(ord_less_eq_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 762[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),zero_zero_int)** -> equal(X1:inT,uminus_uminus_int1(W:inT)).
(d0,A,r0,rw0) 766[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),zero_zero_int)** -> equal(W:inT,uminus_uminus_int1(X1:inT)).
(d0,A,r0,rw0) 763[0:Inp] || equal(W:inT,uminus_uminus_int1(X1:inT)) -> equal(plus_plus_int2(X1:inT,W:inT),zero_zero_int)**.
(d0,A,r0,rw0) 765[0:Inp] || equal(W:inT,uminus_uminus_int1(X1:inT)) -> equal(plus_plus_int2(W:inT,X1:inT),zero_zero_int)**.
(d0,A,r0,rw0) 733[0:Inp] ||  -> pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(times_times_int2(W:inT,W:inT),times_times_int2(X1:inT,X1:inT))))*.
(d0,A,r0,rw0) 742[0:Inp] ||  -> equal(plus_plus_int2(uminus_uminus_int1(W:inT),uminus_uminus_int1(X1:inT)),uminus_uminus_int1(plus_plus_int2(W:inT,X1:inT)))**.
(d0,A,r0,rw0) 671[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(Z:naT,Y:naT))* -> .
(d0,A,r0,rw0) 667[0:Inp] || pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_nat2(Z:naT,Y:naT)) -> .
(d0,A,r0,rw0) 731[0:Inp] || pp(ord_less_nat2(Y:naT,skf664(Z:naT)))* -> pp(ord_less_nat2(Y:naT,Z:naT)).
(d0,A,r0,rw0) 713[0:Inp] || pp(ord_less_nat2(Y:naT,skf600(Z:naT))) -> pp(ord_less_eq_nat2(Y:naT,Z:naT))*.
(d0,A,r0,rw0) 724[0:Inp] || pp(ord_less_nat2(skf643(Y:naT),Z:naT))* -> pp(ord_less_nat2(Y:naT,Z:naT)).
(d0,A,r0,rw0) 716[0:Inp] || pp(ord_less_nat2(skf603(Y:naT),Z:naT)) -> pp(ord_less_eq_nat2(Y:naT,Z:naT))*.
(d0,A,r0,rw0) 772[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* -> equal(divide_divide_nat2(Y:naT,Z:naT),zero_zero_nat).
(d0,A,r0,rw0) 549[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM))* equal(U:nuM,X2:nuM) -> .
(d0,A,r0,rw0) 558[0:Inp] || pp(ord_less_num2(U:nuM,X2:nuM)) -> pp(ord_less_eq_num2(U:nuM,X2:nuM))*.
(d0,A,r0,rw0) 628[0:Inp] || equal(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM))* -> equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 630[0:Inp] || equal(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM))* -> equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 648[0:Inp] || equal(bit01(U:nuM),bit01(X2:nuM))* -> equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 650[0:Inp] || equal(bit11(U:nuM),bit11(X2:nuM))* -> equal(U:nuM,X2:nuM).
(d0,A,r0,rw0) 629[0:Inp] || equal(U:nuM,X2:nuM) -> equal(numeral_numeral_nat1(U:nuM),numeral_numeral_nat1(X2:nuM))*.
(d0,A,r0,rw0) 631[0:Inp] || equal(U:nuM,X2:nuM) -> equal(numeral_numeral_int1(U:nuM),numeral_numeral_int1(X2:nuM))*.
(d0,A,r0,rw0) 649[0:Inp] || equal(U:nuM,X2:nuM) -> equal(bit01(U:nuM),bit01(X2:nuM))*.
(d0,A,r0,rw0) 651[0:Inp] || equal(U:nuM,X2:nuM) -> equal(bit11(U:nuM),bit11(X2:nuM))*.
(d0,A,r0,rw0) 551[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* equal(W:inT,X1:inT) -> .
(d0,A,r0,rw0) 562[0:Inp] || pp(ord_less_int2(W:inT,X1:inT))* -> pp(ord_less_eq_int2(W:inT,X1:inT)).
(d0,A,r0,rw0) 632[0:Inp] || equal(uminus_uminus_int1(W:inT),uminus_uminus_int1(X1:inT))* -> equal(W:inT,X1:inT).
(d0,A,r0,rw0) 523[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),X1:inT)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 527[0:Inp] || equal(plus_plus_int2(W:inT,X1:inT),W:inT)** -> equal(X1:inT,zero_zero_int).
(d0,A,r0,rw0) 637[0:Inp] || equal(W:inT,uminus_uminus_int1(X1:inT))* -> equal(X1:inT,uminus_uminus_int1(W:inT))*.
(d0,A,r0,rw0) 633[0:Inp] || equal(W:inT,X1:inT) -> equal(uminus_uminus_int1(W:inT),uminus_uminus_int1(X1:inT))*.
(d0,A,r0,rw0) 524[0:Inp] || equal(W:inT,zero_zero_int) -> equal(plus_plus_int2(W:inT,X1:inT),X1:inT)**.
(d0,A,r0,rw0) 528[0:Inp] || equal(W:inT,zero_zero_int) -> equal(plus_plus_int2(X1:inT,W:inT),X1:inT)**.
(d0,A,r0,rw0) 617[0:Inp] || equal(W:inT,one_one_int) -> equal(times_times_int2(W:inT,X1:inT),X1:inT)**.
(d0,A,r0,rw0) 621[0:Inp] || equal(W:inT,one_one_int) -> equal(times_times_int2(X1:inT,W:inT),X1:inT)**.
(d0,A,r0,rw0) 1840[0:Rew:742.0,759.0] ||  -> equal(uminus_uminus_int1(plus_plus_int2(W:inT,X1:inT)),uminus_uminus_int1(plus_plus_int2(X1:inT,W:inT)))*.
(d0,A,r0,rw0) 636[0:Inp] ||  -> equal(times_times_int2(W:inT,uminus_uminus_int1(X1:inT)),uminus_uminus_int1(times_times_int2(W:inT,X1:inT)))**.
(d0,A,r0,rw0) 634[0:Inp] ||  -> equal(times_times_int2(uminus_uminus_int1(W:inT),X1:inT),uminus_uminus_int1(times_times_int2(W:inT,X1:inT)))**.
(d0,A,r0,rw0) 550[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT))* equal(Y:naT,Z:naT) -> .
(d0,A,r0,rw0) 560[0:Inp] || pp(ord_less_nat2(Y:naT,Z:naT)) -> pp(ord_less_eq_nat2(Y:naT,Z:naT))*.
(d0,A,r0,rw0) 521[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),Z:naT)** -> equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 525[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),Y:naT)** -> equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 522[0:Inp] || equal(Y:naT,zero_zero_nat) -> equal(plus_plus_nat2(Y:naT,Z:naT),Z:naT)**.
(d0,A,r0,rw0) 526[0:Inp] || equal(Y:naT,zero_zero_nat) -> equal(plus_plus_nat2(Z:naT,Y:naT),Z:naT)**.
(d0,A,r0,rw0) 432[0:Inp] || equal(U:nuM,X2:nuM) -> pp(ord_less_eq_num2(X2:nuM,U:nuM))*.
(d0,A,r0,rw0) 431[0:Inp] ||  -> pp(ord_less_eq_num2(U:nuM,X2:nuM))* pp(ord_less_eq_num2(X2:nuM,U:nuM))*.
(d0,A,r0,rw0) 425[0:Inp] ||  -> pp(ord_less_num2(U:nuM,X2:nuM)) pp(ord_less_eq_num2(X2:nuM,U:nuM))*.
(d0,A,r0,rw0) 406[0:Inp] ||  -> equal(aa_num_num(plus_plus_num(U:nuM),X2:nuM),plus_plus_num2(U:nuM,X2:nuM))**.
(d0,A,r0,rw0) 409[0:Inp] ||  -> equal(aa_num_num(times_times_num(U:nuM),X2:nuM),times_times_num2(U:nuM,X2:nuM))**.
(d0,A,r0,rw0) 412[0:Inp] ||  -> equal(aa_num_bool(ord_less_num1(U:nuM),X2:nuM),ord_less_num2(U:nuM,X2:nuM))**.
(d0,A,r0,rw0) 421[0:Inp] ||  -> equal(aa_num_bool(ord_less_eq_num1(U:nuM),X2:nuM),ord_less_eq_num2(U:nuM,X2:nuM))**.
(d0,A,r0,rw0) 436[0:Inp] || equal(W:inT,X1:inT) -> pp(ord_less_eq_int2(X1:inT,W:inT))*.
(d0,A,r0,rw0) 435[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X1:inT,W:inT))*.
(d0,A,r0,rw0) 427[0:Inp] ||  -> pp(ord_less_int2(W:inT,X1:inT))* pp(ord_less_eq_int2(X1:inT,W:inT)).
(d0,A,r0,rw0) 499[0:Inp] ||  -> equal(plus_plus_int2(W:inT,plus_plus_int2(uminus_uminus_int1(W:inT),X1:inT)),X1:inT)**.
(d0,A,r0,rw0) 404[0:Inp] ||  -> equal(aa_int_int(plus_plus_int1(W:inT),X1:inT),plus_plus_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 407[0:Inp] ||  -> equal(aa_int_int(times_times_int1(W:inT),X1:inT),times_times_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 410[0:Inp] ||  -> equal(aa_int_bool(ord_less_int1(W:inT),X1:inT),ord_less_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 413[0:Inp] ||  -> equal(aa_int_int(divide_divide_int(W:inT),X1:inT),divide_divide_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 415[0:Inp] ||  -> equal(aa_int_bool(nO_MATCH_int_int1(W:inT),X1:inT),nO_MATCH_int_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 419[0:Inp] ||  -> equal(aa_int_bool(ord_less_eq_int1(W:inT),X1:inT),ord_less_eq_int2(W:inT,X1:inT))**.
(d0,A,r0,rw0) 434[0:Inp] || equal(Y:naT,Z:naT) -> pp(ord_less_eq_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 433[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,Z:naT))* pp(ord_less_eq_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 426[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,Z:naT)) pp(ord_less_eq_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 1825[0:Rew:372.0,511.0] ||  -> pp(ord_less_eq_nat2(times_times_nat2(Y:naT,divide_divide_nat2(Z:naT,Y:naT)),Z:naT))*.
(d0,A,r0,rw0) 403[0:Inp] ||  -> equal(aa_nat_bool(dvd_dvd_nat1(Y:naT),Z:naT),dvd_dvd_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 405[0:Inp] ||  -> equal(aa_nat_nat(plus_plus_nat1(Y:naT),Z:naT),plus_plus_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 408[0:Inp] ||  -> equal(aa_nat_nat(times_times_nat1(Y:naT),Z:naT),times_times_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 411[0:Inp] ||  -> equal(aa_nat_bool(ord_less_nat1(Y:naT),Z:naT),ord_less_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 414[0:Inp] ||  -> equal(aa_nat_nat(divide_divide_nat(Y:naT),Z:naT),divide_divide_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 418[0:Inp] ||  -> equal(aa_nat_bool(nO_MATCH_nat_nat1(Y:naT),Z:naT),nO_MATCH_nat_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 420[0:Inp] ||  -> equal(aa_nat_bool(ord_less_eq_nat1(Y:naT),Z:naT),ord_less_eq_nat2(Y:naT,Z:naT))**.
(d0,A,r0,rw0) 514[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,times_times_nat2(Y:naT,times_times_nat2(Y:naT,Y:naT))))*.
(d0,A,r0,rw0) 400[0:Inp] ||  -> equal(aa_nat_bool(monoid_nat(X:fun_nat_fun_nat_nat),Y:naT),monoid_nat2(X:fun_nat_fun_nat_nat,Y:naT))**.
(d0,A,r0,rw0) 402[0:Inp] ||  -> equal(aa_nat_bool(comm_monoid_nat(X:fun_nat_fun_nat_nat),Y:naT),comm_monoid_nat2(X:fun_nat_fun_nat_nat,Y:naT))**.
(d0,A,r0,rw0) 416[0:Inp] ||  -> equal(aa_nat_bool(nO_MATCH_int_nat(W:inT),Y:naT),nO_MATCH_int_nat2(W:inT,Y:naT))**.
(d0,A,r0,rw0) 417[0:Inp] ||  -> equal(aa_int_bool(nO_MATCH_nat_int(Y:naT),W:inT),nO_MATCH_nat_int2(Y:naT,W:inT))**.
(d0,A,r0,rw0) 422[0:Inp] ||  -> equal(aa_int_int(bit_se1474455250it_int(Y:naT),W:inT),bit_se664156431t_int2(Y:naT,W:inT))**.
(d0,A,r0,rw0) 399[0:Inp] ||  -> equal(aa_int_bool(monoid_int(V:fun_int_fun_int_int),W:inT),monoid_int2(V:fun_int_fun_int_int,W:inT))**.
(d0,A,r0,rw0) 401[0:Inp] ||  -> equal(aa_int_bool(comm_monoid_int(V:fun_int_fun_int_int),W:inT),comm_monoid_int2(V:fun_int_fun_int_int,W:inT))**.
(d0,A,r0,rw0) 363[0:Inp] ||  -> pp(ord_less_int2(W:inT,skf626(X30:fun_int_bool,X34:fun_int_bool,W:inT)))*.
(d0,A,r0,rw0) 365[0:Inp] ||  -> pp(ord_less_int2(W:inT,skf632(X30:fun_int_bool,X34:fun_int_bool,W:inT)))*.
(d0,A,r0,rw0) 366[0:Inp] ||  -> pp(ord_less_int2(skf650(X30:fun_int_bool,X34:fun_int_bool,W:inT),W:inT))*.
(d0,A,r0,rw0) 367[0:Inp] ||  -> pp(ord_less_int2(skf656(X30:fun_int_bool,X34:fun_int_bool,W:inT),W:inT))*.
(d0,A,r0,rw0) 362[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,skf624(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))*.
(d0,A,r0,rw0) 364[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,skf630(X25:fun_nat_bool,X33:fun_nat_bool,Y:naT)))*.
(d0,A,r0,rw0) 360[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,skf611(X30:fun_int_bool,X1:inT,W:inT)))*.
(d0,A,r0,rw0) 361[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,skf610(X30:fun_int_bool,X1:inT,W:inT)))*.
(d0,A,r0,rw0) 358[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,skf609(X25:fun_nat_bool,Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 359[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,skf608(X25:fun_nat_bool,Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 352[0:Inp] ||  -> equal(plus_plus_int2(W:inT,X1:inT),plus_plus_int2(X1:inT,W:inT))*.
(d0,A,r0,rw0) 373[0:Inp] ||  -> equal(times_times_int2(W:inT,X1:inT),times_times_int2(X1:inT,W:inT))*.
(d0,A,r0,rw0) 351[0:Inp] ||  -> equal(plus_plus_nat2(Y:naT,Z:naT),plus_plus_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 372[0:Inp] ||  -> equal(times_times_nat2(Y:naT,Z:naT),times_times_nat2(Z:naT,Y:naT))*.
(d0,A,r0,rw0) 1818[0:Rew:352.0,1019.1] || member_int(W:inT,ring_1_Ints_int) equal(plus_plus_int2(W:inT,plus_plus_int2(one_one_int,W:inT)),zero_zero_int)** -> .
(d0,A,r0,rw0) 942[0:Inp] || pp(ord_less_nat2(zero_zero_nat,times_times_nat2(Y:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Y:naT)).
(d0,A,r0,rw0) 943[0:Inp] || pp(ord_less_nat2(zero_zero_nat,times_times_nat2(Y:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 953[0:Inp] || pp(ord_less_nat2(zero_zero_nat,divide_divide_nat2(Y:naT,Z:naT)))* -> pp(ord_less_nat2(zero_zero_nat,Z:naT)).
(d0,A,r0,rw0) 931[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(Y:naT,Z:naT)))*.
(d0,A,r0,rw0) 932[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT)) -> pp(ord_less_nat2(zero_zero_nat,plus_plus_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1850[0:MRR:1363.0,22.0] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(times_times_nat2(Y:naT,Z:naT),zero_zero_nat))*.
(d0,A,r0,rw0) 1851[0:MRR:1367.0,22.0] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat)) -> pp(ord_less_eq_nat2(times_times_nat2(Z:naT,Y:naT),zero_zero_nat))*.
(d0,A,r0,rw0) 962[0:Inp] || pp(ord_less_int2(bit_se664156431t_int2(Y:naT,W:inT),zero_zero_int))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 963[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(bit_se664156431t_int2(Y:naT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 808[0:Inp] || pp(ord_less_eq_int2(plus_plus_int2(W:inT,W:inT),zero_zero_int))* -> pp(ord_less_eq_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 844[0:Inp] || pp(ord_less_int2(plus_plus_int2(W:inT,W:inT),zero_zero_int))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 806[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(W:inT,W:inT)))* -> pp(ord_less_eq_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 826[0:Inp] || pp(ord_less_int2(zero_zero_int,plus_plus_int2(W:inT,W:inT)))* -> pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 807[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(zero_zero_int,plus_plus_int2(W:inT,W:inT)))*.
(d0,A,r0,rw0) 827[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(W:inT,W:inT)))*.
(d0,A,r0,rw0) 809[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> pp(ord_less_eq_int2(plus_plus_int2(W:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 845[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(plus_plus_int2(W:inT,W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 771[0:Inp] || pp(aa_num_bool(X31:fun_num_bool,onE)) -> pp(aa_num_bool(X31:fun_num_bool,skf669(X31:fun_num_bool)))*.
(d0,A,r0,rw0) 745[0:Inp] || pp(ord_less_eq_int2(W:inT,uminus_uminus_int1(W:inT)))* -> pp(ord_less_eq_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 757[0:Inp] || pp(ord_less_int2(W:inT,uminus_uminus_int1(W:inT)))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 746[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> pp(ord_less_eq_int2(W:inT,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 758[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(W:inT,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 743[0:Inp] || pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),W:inT))* -> pp(ord_less_eq_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 755[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(W:inT),W:inT))* -> pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 744[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),W:inT))*.
(d0,A,r0,rw0) 756[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(uminus_uminus_int1(W:inT),W:inT))*.
(d0,A,r0,rw0) 769[0:Inp] || equal(W:inT,uminus_uminus_int1(one_one_int)) -> equal(times_times_int2(W:inT,W:inT),one_one_int)**.
(d0,A,r0,rw0) 614[0:Inp] || equal(W:inT,zero_zero_int) -> equal(times_times_int2(W:inT,X1:inT),zero_zero_int)**.
(d0,A,r0,rw0) 615[0:Inp] || equal(W:inT,zero_zero_int) -> equal(times_times_int2(X1:inT,W:inT),zero_zero_int)**.
(d0,A,r0,rw0) 537[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),zero_zero_nat)** -> equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 538[0:Inp] || equal(plus_plus_nat2(Y:naT,Z:naT),zero_zero_nat)** -> equal(Z:naT,zero_zero_nat).
(d0,A,r0,rw0) 644[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),one_one_nat)** -> equal(Y:naT,one_one_nat).
(d0,A,r0,rw0) 645[0:Inp] || equal(times_times_nat2(Y:naT,Z:naT),one_one_nat)** -> equal(Z:naT,one_one_nat).
(d0,A,r0,rw0) 612[0:Inp] || equal(Y:naT,zero_zero_nat) -> equal(times_times_nat2(Y:naT,Z:naT),zero_zero_nat)**.
(d0,A,r0,rw0) 613[0:Inp] || equal(Y:naT,zero_zero_nat) -> equal(times_times_nat2(Z:naT,Y:naT),zero_zero_nat)**.
(d0,A,r0,rw0) 657[0:Inp] || equal(Y:naT,zero_zero_nat) -> equal(divide_divide_nat2(Z:naT,Y:naT),zero_zero_nat)**.
(d0,A,r0,rw0) 519[0:Inp] || equal(plus_plus_int2(W:inT,W:inT),zero_zero_int)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 513[0:Inp] || pp(aa_nat_bool(X25:fun_nat_bool,zero_zero_nat))* -> SkP24(X25:fun_nat_bool,Y:naT)*.
(d0,A,r0,rw0) 488[0:Inp] ||  -> equal(Y:naT,zero_zero_nat) equal(divide_divide_nat2(Y:naT,Y:naT),one_one_nat)**.
(d0,A,r0,rw0) 495[0:Inp] || equal(uminus_uminus_int1(W:inT),W:inT)** -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 489[0:Inp] ||  -> equal(W:inT,zero_zero_int) equal(divide_divide_int2(W:inT,W:inT),one_one_int)**.
(d0,A,r0,rw0) 1821[0:Rew:352.0,490.0] ||  -> equal(plus_plus_int2(one_one_int,plus_plus_int2(W:inT,W:inT)),neg_nu323594467c_int1(W:inT))**.
(d0,A,r0,rw0) 396[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(Y:naT,Z:naT),Y:naT))* -> .
(d0,A,r0,rw0) 397[0:Inp] || pp(ord_less_nat2(plus_plus_nat2(Y:naT,Z:naT),Z:naT))* -> .
(d0,A,r0,rw0) 339[0:Inp] ||  -> SkP24(X25:fun_nat_bool,Y:naT)* equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 343[0:Inp] ||  -> pp(ord_less_eq_nat2(skf676(X25:fun_nat_bool,Y:naT),Y:naT))*.
(d0,A,r0,rw0) 1842[0:MRR:811.0,22.0] ||  -> pp(ord_less_eq_nat2(Y:naT,plus_plus_nat2(Z:naT,Y:naT)))*.
(d0,A,r0,rw0) 1843[0:MRR:815.0,22.0] ||  -> pp(ord_less_eq_nat2(Y:naT,plus_plus_nat2(Y:naT,Z:naT)))*.
(d0,A,r0,rw0) 340[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,times_times_nat2(Y:naT,Y:naT)))*.
(d0,A,r0,rw0) 1152[0:Inp] || pp(ord_less_int2(divide_divide_int2(W:inT,numeral_numeral_int1(bit01(onE))),zero_zero_int))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 1153[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(divide_divide_int2(W:inT,numeral_numeral_int1(bit01(onE))),zero_zero_int))*.
(d0,A,r0,rw0) 749[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,uminus_uminus_int1(W:inT)))* -> pp(ord_less_eq_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 753[0:Inp] || pp(ord_less_int2(zero_zero_int,uminus_uminus_int1(W:inT)))* -> pp(ord_less_int2(W:inT,zero_zero_int)).
(d0,A,r0,rw0) 747[0:Inp] || pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),zero_zero_int))* -> pp(ord_less_eq_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 751[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(W:inT),zero_zero_int))* -> pp(ord_less_int2(zero_zero_int,W:inT)).
(d0,A,r0,rw0) 750[0:Inp] || pp(ord_less_eq_int2(W:inT,zero_zero_int)) -> pp(ord_less_eq_int2(zero_zero_int,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 754[0:Inp] || pp(ord_less_int2(W:inT,zero_zero_int)) -> pp(ord_less_int2(zero_zero_int,uminus_uminus_int1(W:inT)))*.
(d0,A,r0,rw0) 748[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,W:inT)) -> pp(ord_less_eq_int2(uminus_uminus_int1(W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 752[0:Inp] || pp(ord_less_int2(zero_zero_int,W:inT)) -> pp(ord_less_int2(uminus_uminus_int1(W:inT),zero_zero_int))*.
(d0,A,r0,rw0) 547[0:Inp] || pp(ord_less_nat2(zero_zero_nat,Y:naT))* equal(Y:naT,zero_zero_nat) -> .
(d0,A,r0,rw0) 1811[0:Rew:389.0,393.0,336.0,393.0,336.0,393.0] ||  -> equal(plus_plus_num2(onE,bit11(U:nuM)),bit01(plus_plus_num2(U:nuM,onE)))**.
(d0,A,r0,rw0) 501[0:Inp] || pp(ord_less_int2(numeral_numeral_int1(U:nuM),uminus_uminus_int1(numeral_numeral_int1(X2:nuM))))* -> .
(d0,A,r0,rw0) 502[0:Inp] || pp(ord_less_eq_int2(numeral_numeral_int1(U:nuM),uminus_uminus_int1(numeral_numeral_int1(X2:nuM))))* -> .
(d0,A,r0,rw0) 424[0:Inp] || equal(Y:naT,zero_zero_nat) -> pp(ord_less_eq_nat2(Y:naT,zero_zero_nat))*.
(d0,A,r0,rw0) 518[0:Inp] || equal(Y:naT,one_one_nat) -> pp(dvd_dvd_nat2(Y:naT,one_one_nat))*.
(d0,A,r0,rw0) 510[0:Inp] || equal(Y:naT,zero_zero_nat) -> pp(ord_less_nat2(Y:naT,one_one_nat))*.
(d0,A,r0,rw0) 423[0:Inp] || pp(ord_less_eq_nat2(Y:naT,zero_zero_nat))* -> equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 517[0:Inp] || pp(dvd_dvd_nat2(Y:naT,one_one_nat))* -> equal(Y:naT,one_one_nat).
(d0,A,r0,rw0) 509[0:Inp] || pp(ord_less_nat2(Y:naT,one_one_nat))* -> equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 505[0:Inp] || member_int(uminus_uminus_int1(W:inT),ring_1_Ints_int)* -> member_int(W:inT,ring_1_Ints_int).
(d0,A,r0,rw0) 491[0:Inp] || equal(uminus_uminus_int1(W:inT),zero_zero_int)** -> equal(zero_zero_int,W:inT).
(d0,A,r0,rw0) 504[0:Inp] || member_int(W:inT,ring_1_Ints_int) -> member_int(uminus_uminus_int1(W:inT),ring_1_Ints_int)*.
(d0,A,r0,rw0) 492[0:Inp] || equal(zero_zero_int,W:inT) -> equal(uminus_uminus_int1(W:inT),zero_zero_int)**.
(d0,A,r0,rw0) 508[0:Inp] || equal(U:nuM,onE) -> pp(ord_less_eq_num2(U:nuM,onE))*.
(d0,A,r0,rw0) 507[0:Inp] || pp(ord_less_eq_num2(U:nuM,onE))* -> equal(U:nuM,onE).
(d0,A,r0,rw0) 345[0:Inp] || equal(zero_zero_a,X5:a)* -> equal(X5:a,zero_zero_a).
(d0,A,r0,rw0) 379[0:Inp] || equal(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),numeral_numeral_int1(X2:nuM))* -> .
(d0,A,r0,rw0) 378[0:Inp] ||  -> pp(ord_less_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),numeral_numeral_int1(X2:nuM)))*.
(d0,A,r0,rw0) 381[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),numeral_numeral_int1(X2:nuM)))*.
(d0,A,r0,rw0) 347[0:Inp] || equal(zero_zero_nat,Y:naT)* -> equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 368[0:Inp] || equal(one_one_nat,Y:naT)* -> equal(Y:naT,one_one_nat).
(d0,A,r0,rw0) 355[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,Y:naT))* equal(Y:naT,zero_zero_nat).
(d0,A,r0,rw0) 349[0:Inp] || equal(zero_zero_int,W:inT)* -> equal(W:inT,zero_zero_int).
(d0,A,r0,rw0) 370[0:Inp] || equal(one_one_int,W:inT)* -> equal(W:inT,one_one_int).
(d0,A,r0,rw0) 374[0:Inp] || pp(ord_less_int2(times_times_int2(W:inT,W:inT),zero_zero_int))* -> .
(d0,A,r0,rw0) 377[0:Inp] ||  -> equal(divide_divide_int2(W:inT,uminus_uminus_int1(one_one_int)),uminus_uminus_int1(W:inT))**.
(d0,A,r0,rw0) 389[0:Inp] ||  -> equal(plus_plus_num2(onE,U:nuM),plus_plus_num2(U:nuM,onE))*.
(d0,A,r0,rw0) 1807[0:Rew:336.0,159.0] ||  -> equal(aa_num_num(inC,U:nuM),plus_plus_num2(U:nuM,onE))**.
(d0,A,r0,rw0) 1810[0:Rew:389.0,1809.0] ||  -> equal(plus_plus_num2(onE,bit01(U:nuM)),bit11(U:nuM))**.
(d0,A,r0,rw0) 392[0:Inp] ||  -> equal(times_times_num2(bit01(onE),U:nuM),bit01(U:nuM))**.
(d0,A,r0,rw0) 218[0:Inp] ||  -> pp(ord_less_eq_int2(skf426(X24:fun_int_fun_int_bool),skf427(X24:fun_int_fun_int_bool)))*.
(d0,A,r0,rw0) 257[0:Inp] ||  -> pp(ord_less_int2(skf522(X24:fun_int_fun_int_bool),skf523(X24:fun_int_fun_int_bool)))*.
(d0,A,r0,rw0) 217[0:Inp] ||  -> pp(ord_less_eq_nat2(skf422(X23:fun_nat_fun_nat_bool),skf423(X23:fun_nat_fun_nat_bool)))*.
(d0,A,r0,rw0) 256[0:Inp] ||  -> pp(ord_less_nat2(skf517(X23:fun_nat_fun_nat_bool),skf518(X23:fun_nat_fun_nat_bool)))*.
(d0,A,r0,rw0) 216[0:Inp] ||  -> pp(ord_less_eq_num2(skf418(X22:fun_num_fun_num_bool),skf419(X22:fun_num_fun_num_bool)))*.
(d0,A,r0,rw0) 255[0:Inp] ||  -> pp(ord_less_num2(skf512(X22:fun_num_fun_num_bool),skf513(X22:fun_num_fun_num_bool)))*.
(d0,A,r0,rw0) 188[0:Inp] ||  -> pp(ord_less_int2(skf360(X20:fun_int_int),skf361(X20:fun_int_int)))*.
(d0,A,r0,rw0) 197[0:Inp] ||  -> pp(ord_less_eq_int2(skf378(X20:fun_int_int),skf379(X20:fun_int_int)))*.
(d0,A,r0,rw0) 206[0:Inp] ||  -> pp(ord_less_eq_int2(skf396(X20:fun_int_int),skf397(X20:fun_int_int)))*.
(d0,A,r0,rw0) 215[0:Inp] ||  -> pp(ord_less_int2(skf414(X20:fun_int_int),skf415(X20:fun_int_int)))*.
(d0,A,r0,rw0) 227[0:Inp] ||  -> pp(ord_less_eq_int2(skf444(X20:fun_int_int),skf445(X20:fun_int_int)))*.
(d0,A,r0,rw0) 236[0:Inp] ||  -> pp(ord_less_eq_int2(skf462(X20:fun_int_int),skf463(X20:fun_int_int)))*.
(d0,A,r0,rw0) 245[0:Inp] ||  -> pp(ord_less_eq_int2(skf480(X20:fun_int_int),skf481(X20:fun_int_int)))*.
(d0,A,r0,rw0) 254[0:Inp] ||  -> pp(ord_less_eq_int2(skf498(X20:fun_int_int),skf499(X20:fun_int_int)))*.
(d0,A,r0,rw0) 266[0:Inp] ||  -> pp(ord_less_int2(skf540(X20:fun_int_int),skf541(X20:fun_int_int)))*.
(d0,A,r0,rw0) 275[0:Inp] ||  -> pp(ord_less_int2(skf558(X20:fun_int_int),skf559(X20:fun_int_int)))*.
(d0,A,r0,rw0) 284[0:Inp] ||  -> pp(ord_less_int2(skf576(X20:fun_int_int),skf577(X20:fun_int_int)))*.
(d0,A,r0,rw0) 293[0:Inp] ||  -> pp(ord_less_int2(skf594(X20:fun_int_int),skf595(X20:fun_int_int)))*.
(d0,A,r0,rw0) 187[0:Inp] ||  -> pp(ord_less_nat2(skf358(X19:fun_nat_int),skf359(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 194[0:Inp] ||  -> pp(ord_less_eq_nat2(skf372(X19:fun_nat_int),skf373(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 203[0:Inp] ||  -> pp(ord_less_eq_nat2(skf390(X19:fun_nat_int),skf391(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 214[0:Inp] ||  -> pp(ord_less_nat2(skf412(X19:fun_nat_int),skf413(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 226[0:Inp] ||  -> pp(ord_less_eq_nat2(skf442(X19:fun_nat_int),skf443(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 233[0:Inp] ||  -> pp(ord_less_eq_nat2(skf456(X19:fun_nat_int),skf457(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 242[0:Inp] ||  -> pp(ord_less_eq_nat2(skf474(X19:fun_nat_int),skf475(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 251[0:Inp] ||  -> pp(ord_less_eq_nat2(skf492(X19:fun_nat_int),skf493(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 263[0:Inp] ||  -> pp(ord_less_nat2(skf534(X19:fun_nat_int),skf535(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 272[0:Inp] ||  -> pp(ord_less_nat2(skf552(X19:fun_nat_int),skf553(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 283[0:Inp] ||  -> pp(ord_less_nat2(skf574(X19:fun_nat_int),skf575(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 290[0:Inp] ||  -> pp(ord_less_nat2(skf588(X19:fun_nat_int),skf589(X19:fun_nat_int)))*.
(d0,A,r0,rw0) 186[0:Inp] ||  -> pp(ord_less_num2(skf356(X18:fun_num_int),skf357(X18:fun_num_int)))*.
(d0,A,r0,rw0) 191[0:Inp] ||  -> pp(ord_less_eq_num2(skf366(X18:fun_num_int),skf367(X18:fun_num_int)))*.
(d0,A,r0,rw0) 200[0:Inp] ||  -> pp(ord_less_eq_num2(skf384(X18:fun_num_int),skf385(X18:fun_num_int)))*.
(d0,A,r0,rw0) 213[0:Inp] ||  -> pp(ord_less_num2(skf410(X18:fun_num_int),skf411(X18:fun_num_int)))*.
(d0,A,r0,rw0) 225[0:Inp] ||  -> pp(ord_less_eq_num2(skf440(X18:fun_num_int),skf441(X18:fun_num_int)))*.
(d0,A,r0,rw0) 230[0:Inp] ||  -> pp(ord_less_eq_num2(skf450(X18:fun_num_int),skf451(X18:fun_num_int)))*.
(d0,A,r0,rw0) 239[0:Inp] ||  -> pp(ord_less_eq_num2(skf468(X18:fun_num_int),skf469(X18:fun_num_int)))*.
(d0,A,r0,rw0) 248[0:Inp] ||  -> pp(ord_less_eq_num2(skf486(X18:fun_num_int),skf487(X18:fun_num_int)))*.
(d0,A,r0,rw0) 260[0:Inp] ||  -> pp(ord_less_num2(skf528(X18:fun_num_int),skf529(X18:fun_num_int)))*.
(d0,A,r0,rw0) 269[0:Inp] ||  -> pp(ord_less_num2(skf546(X18:fun_num_int),skf547(X18:fun_num_int)))*.
(d0,A,r0,rw0) 282[0:Inp] ||  -> pp(ord_less_num2(skf572(X18:fun_num_int),skf573(X18:fun_num_int)))*.
(d0,A,r0,rw0) 287[0:Inp] ||  -> pp(ord_less_num2(skf582(X18:fun_num_int),skf583(X18:fun_num_int)))*.
(d0,A,r0,rw0) 185[0:Inp] ||  -> pp(ord_less_int2(skf354(X17:fun_int_nat),skf355(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 196[0:Inp] ||  -> pp(ord_less_eq_int2(skf376(X17:fun_int_nat),skf377(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 205[0:Inp] ||  -> pp(ord_less_eq_int2(skf394(X17:fun_int_nat),skf395(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 212[0:Inp] ||  -> pp(ord_less_int2(skf408(X17:fun_int_nat),skf409(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 224[0:Inp] ||  -> pp(ord_less_eq_int2(skf438(X17:fun_int_nat),skf439(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 235[0:Inp] ||  -> pp(ord_less_eq_int2(skf460(X17:fun_int_nat),skf461(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 244[0:Inp] ||  -> pp(ord_less_eq_int2(skf478(X17:fun_int_nat),skf479(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 253[0:Inp] ||  -> pp(ord_less_eq_int2(skf496(X17:fun_int_nat),skf497(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 265[0:Inp] ||  -> pp(ord_less_int2(skf538(X17:fun_int_nat),skf539(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 274[0:Inp] ||  -> pp(ord_less_int2(skf556(X17:fun_int_nat),skf557(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 281[0:Inp] ||  -> pp(ord_less_int2(skf570(X17:fun_int_nat),skf571(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 292[0:Inp] ||  -> pp(ord_less_int2(skf592(X17:fun_int_nat),skf593(X17:fun_int_nat)))*.
(d0,A,r0,rw0) 184[0:Inp] ||  -> pp(ord_less_nat2(skf352(X15:fun_nat_nat),skf353(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 193[0:Inp] ||  -> pp(ord_less_eq_nat2(skf370(X15:fun_nat_nat),skf371(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 202[0:Inp] ||  -> pp(ord_less_eq_nat2(skf388(X15:fun_nat_nat),skf389(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 211[0:Inp] ||  -> pp(ord_less_nat2(skf406(X15:fun_nat_nat),skf407(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 223[0:Inp] ||  -> pp(ord_less_eq_nat2(skf436(X15:fun_nat_nat),skf437(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 232[0:Inp] ||  -> pp(ord_less_eq_nat2(skf454(X15:fun_nat_nat),skf455(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 241[0:Inp] ||  -> pp(ord_less_eq_nat2(skf472(X15:fun_nat_nat),skf473(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 250[0:Inp] ||  -> pp(ord_less_eq_nat2(skf490(X15:fun_nat_nat),skf491(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 262[0:Inp] ||  -> pp(ord_less_nat2(skf532(X15:fun_nat_nat),skf533(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 271[0:Inp] ||  -> pp(ord_less_nat2(skf550(X15:fun_nat_nat),skf551(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 280[0:Inp] ||  -> pp(ord_less_nat2(skf568(X15:fun_nat_nat),skf569(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 289[0:Inp] ||  -> pp(ord_less_nat2(skf586(X15:fun_nat_nat),skf587(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 341[0:Inp] ||  -> pp(ord_less_nat2(skf672(X15:fun_nat_nat),skf673(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 342[0:Inp] ||  -> pp(ord_less_nat2(skf674(X15:fun_nat_nat),skf675(X15:fun_nat_nat)))*.
(d0,A,r0,rw0) 183[0:Inp] ||  -> pp(ord_less_num2(skf350(X14:fun_num_nat),skf351(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 190[0:Inp] ||  -> pp(ord_less_eq_num2(skf364(X14:fun_num_nat),skf365(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 199[0:Inp] ||  -> pp(ord_less_eq_num2(skf382(X14:fun_num_nat),skf383(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 210[0:Inp] ||  -> pp(ord_less_num2(skf404(X14:fun_num_nat),skf405(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 222[0:Inp] ||  -> pp(ord_less_eq_num2(skf434(X14:fun_num_nat),skf435(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 229[0:Inp] ||  -> pp(ord_less_eq_num2(skf448(X14:fun_num_nat),skf449(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 238[0:Inp] ||  -> pp(ord_less_eq_num2(skf466(X14:fun_num_nat),skf467(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 247[0:Inp] ||  -> pp(ord_less_eq_num2(skf484(X14:fun_num_nat),skf485(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 259[0:Inp] ||  -> pp(ord_less_num2(skf526(X14:fun_num_nat),skf527(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 268[0:Inp] ||  -> pp(ord_less_num2(skf544(X14:fun_num_nat),skf545(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 279[0:Inp] ||  -> pp(ord_less_num2(skf566(X14:fun_num_nat),skf567(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 286[0:Inp] ||  -> pp(ord_less_num2(skf580(X14:fun_num_nat),skf581(X14:fun_num_nat)))*.
(d0,A,r0,rw0) 182[0:Inp] ||  -> pp(ord_less_int2(skf348(X13:fun_int_num),skf349(X13:fun_int_num)))*.
(d0,A,r0,rw0) 195[0:Inp] ||  -> pp(ord_less_eq_int2(skf374(X13:fun_int_num),skf375(X13:fun_int_num)))*.
(d0,A,r0,rw0) 204[0:Inp] ||  -> pp(ord_less_eq_int2(skf392(X13:fun_int_num),skf393(X13:fun_int_num)))*.
(d0,A,r0,rw0) 209[0:Inp] ||  -> pp(ord_less_int2(skf402(X13:fun_int_num),skf403(X13:fun_int_num)))*.
(d0,A,r0,rw0) 221[0:Inp] ||  -> pp(ord_less_eq_int2(skf432(X13:fun_int_num),skf433(X13:fun_int_num)))*.
(d0,A,r0,rw0) 234[0:Inp] ||  -> pp(ord_less_eq_int2(skf458(X13:fun_int_num),skf459(X13:fun_int_num)))*.
(d0,A,r0,rw0) 243[0:Inp] ||  -> pp(ord_less_eq_int2(skf476(X13:fun_int_num),skf477(X13:fun_int_num)))*.
(d0,A,r0,rw0) 252[0:Inp] ||  -> pp(ord_less_eq_int2(skf494(X13:fun_int_num),skf495(X13:fun_int_num)))*.
(d0,A,r0,rw0) 264[0:Inp] ||  -> pp(ord_less_int2(skf536(X13:fun_int_num),skf537(X13:fun_int_num)))*.
(d0,A,r0,rw0) 273[0:Inp] ||  -> pp(ord_less_int2(skf554(X13:fun_int_num),skf555(X13:fun_int_num)))*.
(d0,A,r0,rw0) 278[0:Inp] ||  -> pp(ord_less_int2(skf564(X13:fun_int_num),skf565(X13:fun_int_num)))*.
(d0,A,r0,rw0) 291[0:Inp] ||  -> pp(ord_less_int2(skf590(X13:fun_int_num),skf591(X13:fun_int_num)))*.
(d0,A,r0,rw0) 181[0:Inp] ||  -> pp(ord_less_nat2(skf346(X12:fun_nat_num),skf347(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 192[0:Inp] ||  -> pp(ord_less_eq_nat2(skf368(X12:fun_nat_num),skf369(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 201[0:Inp] ||  -> pp(ord_less_eq_nat2(skf386(X12:fun_nat_num),skf387(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 208[0:Inp] ||  -> pp(ord_less_nat2(skf400(X12:fun_nat_num),skf401(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 220[0:Inp] ||  -> pp(ord_less_eq_nat2(skf430(X12:fun_nat_num),skf431(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 231[0:Inp] ||  -> pp(ord_less_eq_nat2(skf452(X12:fun_nat_num),skf453(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 240[0:Inp] ||  -> pp(ord_less_eq_nat2(skf470(X12:fun_nat_num),skf471(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 249[0:Inp] ||  -> pp(ord_less_eq_nat2(skf488(X12:fun_nat_num),skf489(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 261[0:Inp] ||  -> pp(ord_less_nat2(skf530(X12:fun_nat_num),skf531(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 270[0:Inp] ||  -> pp(ord_less_nat2(skf548(X12:fun_nat_num),skf549(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 277[0:Inp] ||  -> pp(ord_less_nat2(skf562(X12:fun_nat_num),skf563(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 288[0:Inp] ||  -> pp(ord_less_nat2(skf584(X12:fun_nat_num),skf585(X12:fun_nat_num)))*.
(d0,A,r0,rw0) 180[0:Inp] ||  -> pp(ord_less_num2(skf344(X8:fun_num_num),skf345(X8:fun_num_num)))*.
(d0,A,r0,rw0) 189[0:Inp] ||  -> pp(ord_less_eq_num2(skf362(X8:fun_num_num),skf363(X8:fun_num_num)))*.
(d0,A,r0,rw0) 198[0:Inp] ||  -> pp(ord_less_eq_num2(skf380(X8:fun_num_num),skf381(X8:fun_num_num)))*.
(d0,A,r0,rw0) 207[0:Inp] ||  -> pp(ord_less_num2(skf398(X8:fun_num_num),skf399(X8:fun_num_num)))*.
(d0,A,r0,rw0) 219[0:Inp] ||  -> pp(ord_less_eq_num2(skf428(X8:fun_num_num),skf429(X8:fun_num_num)))*.
(d0,A,r0,rw0) 228[0:Inp] ||  -> pp(ord_less_eq_num2(skf446(X8:fun_num_num),skf447(X8:fun_num_num)))*.
(d0,A,r0,rw0) 237[0:Inp] ||  -> pp(ord_less_eq_num2(skf464(X8:fun_num_num),skf465(X8:fun_num_num)))*.
(d0,A,r0,rw0) 246[0:Inp] ||  -> pp(ord_less_eq_num2(skf482(X8:fun_num_num),skf483(X8:fun_num_num)))*.
(d0,A,r0,rw0) 258[0:Inp] ||  -> pp(ord_less_num2(skf524(X8:fun_num_num),skf525(X8:fun_num_num)))*.
(d0,A,r0,rw0) 267[0:Inp] ||  -> pp(ord_less_num2(skf542(X8:fun_num_num),skf543(X8:fun_num_num)))*.
(d0,A,r0,rw0) 276[0:Inp] ||  -> pp(ord_less_num2(skf560(X8:fun_num_num),skf561(X8:fun_num_num)))*.
(d0,A,r0,rw0) 285[0:Inp] ||  -> pp(ord_less_num2(skf578(X8:fun_num_num),skf579(X8:fun_num_num)))*.
(d0,A,r0,rw0) 338[0:Inp] || equal(bit01(U:nuM),bit11(X2:nuM))* -> .
(d0,A,r0,rw0) 179[0:Inp] || equal(skf343(Y:naT,Z:naT),zero_zero_nat)** -> .
(d0,A,r0,rw0) 344[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,skf678(Y:naT,Z:naT)))*.
(d0,A,r0,rw0) 301[0:Inp] || pp(ord_less_nat2(Y:naT,skf658(Y:naT)))* -> .
(d0,A,r0,rw0) 304[0:Inp] || pp(ord_less_nat2(Y:naT,skf661(Y:naT)))* -> .
(d0,A,r0,rw0) 295[0:Inp] || pp(ord_less_nat2(skf634(Y:naT),Y:naT))* -> .
(d0,A,r0,rw0) 298[0:Inp] || pp(ord_less_nat2(skf637(Y:naT),Y:naT))* -> .
(d0,A,r0,rw0) 307[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,plus_plus_nat2(Y:naT,one_one_nat)))*.
(d0,A,r0,rw0) 162[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(dvd_dvd_nat,Y:naT),dvd_dvd_nat1(Y:naT))**.
(d0,A,r0,rw0) 164[0:Inp] ||  -> equal(aa_nat_fun_nat_nat(plus_plus_nat,Y:naT),plus_plus_nat1(Y:naT))**.
(d0,A,r0,rw0) 166[0:Inp] ||  -> equal(aa_nat_fun_nat_nat(times_times_nat,Y:naT),times_times_nat1(Y:naT))**.
(d0,A,r0,rw0) 168[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_nat,Y:naT),ord_less_nat1(Y:naT))**.
(d0,A,r0,rw0) 174[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(nO_MATCH_nat_nat,Y:naT),nO_MATCH_nat_nat1(Y:naT))**.
(d0,A,r0,rw0) 176[0:Inp] ||  -> equal(aa_nat_fun_nat_bool(ord_less_eq_nat,Y:naT),ord_less_eq_nat1(Y:naT))**.
(d0,A,r0,rw0) 302[0:Inp] || pp(ord_less_int2(W:inT,skf659(W:inT)))* -> .
(d0,A,r0,rw0) 305[0:Inp] || pp(ord_less_int2(W:inT,skf662(W:inT)))* -> .
(d0,A,r0,rw0) 296[0:Inp] || pp(ord_less_int2(skf635(W:inT),W:inT))* -> .
(d0,A,r0,rw0) 299[0:Inp] || pp(ord_less_int2(skf638(W:inT),W:inT))* -> .
(d0,A,r0,rw0) 308[0:Inp] ||  -> pp(ord_less_int2(W:inT,plus_plus_int2(W:inT,one_one_int)))*.
(d0,A,r0,rw0) 306[0:Inp] ||  -> pp(ord_less_eq_int2(zero_zero_int,times_times_int2(W:inT,W:inT)))*.
(d0,A,r0,rw0) 311[0:Inp] ||  -> equal(plus_plus_int2(W:inT,uminus_uminus_int1(W:inT)),zero_zero_int)**.
(d0,A,r0,rw0) 163[0:Inp] ||  -> equal(aa_int_fun_int_int(plus_plus_int,W:inT),plus_plus_int1(W:inT))**.
(d0,A,r0,rw0) 165[0:Inp] ||  -> equal(aa_int_fun_int_int(times_times_int,W:inT),times_times_int1(W:inT))**.
(d0,A,r0,rw0) 167[0:Inp] ||  -> equal(aa_int_fun_int_bool(ord_less_int,W:inT),ord_less_int1(W:inT))**.
(d0,A,r0,rw0) 172[0:Inp] ||  -> equal(aa_int_int(uminus_uminus_int,W:inT),uminus_uminus_int1(W:inT))**.
(d0,A,r0,rw0) 173[0:Inp] ||  -> equal(aa_int_fun_int_bool(nO_MATCH_int_int,W:inT),nO_MATCH_int_int1(W:inT))**.
(d0,A,r0,rw0) 175[0:Inp] ||  -> equal(aa_int_fun_int_bool(ord_less_eq_int,W:inT),ord_less_eq_int1(W:inT))**.
(d0,A,r0,rw0) 1824[0:Rew:1821.0,1822.0] ||  -> equal(aa_int_int(neg_nu1877376189nc_int,W:inT),neg_nu323594467c_int1(W:inT))**.
(d0,A,r0,rw0) 300[0:Inp] || pp(ord_less_num2(U:nuM,skf657(U:nuM)))* -> .
(d0,A,r0,rw0) 303[0:Inp] || pp(ord_less_num2(U:nuM,skf660(U:nuM)))* -> .
(d0,A,r0,rw0) 294[0:Inp] || pp(ord_less_num2(skf633(U:nuM),U:nuM))* -> .
(d0,A,r0,rw0) 297[0:Inp] || pp(ord_less_num2(skf636(U:nuM),U:nuM))* -> .
(d0,A,r0,rw0) 336[0:Inp] ||  -> equal(inc1(U:nuM),plus_plus_num2(U:nuM,onE))**.
(d0,A,r0,rw0) 160[0:Inp] ||  -> equal(aa_num_num(bit0,U:nuM),bit01(U:nuM))**.
(d0,A,r0,rw0) 161[0:Inp] ||  -> equal(aa_num_num(bit1,U:nuM),bit11(U:nuM))**.
(d0,A,r0,rw0) 169[0:Inp] ||  -> equal(aa_num_fun_num_bool(ord_less_num,U:nuM),ord_less_num1(U:nuM))**.
(d0,A,r0,rw0) 170[0:Inp] ||  -> equal(aa_num_int(numeral_numeral_int,U:nuM),numeral_numeral_int1(U:nuM))**.
(d0,A,r0,rw0) 171[0:Inp] ||  -> equal(aa_num_nat(numeral_numeral_nat,U:nuM),numeral_numeral_nat1(U:nuM))**.
(d0,A,r0,rw0) 177[0:Inp] ||  -> equal(aa_num_fun_num_bool(ord_less_eq_num,U:nuM),ord_less_eq_num1(U:nuM))**.
(d0,A,r0,rw0) 64[0:Inp] || pp(ord_less_nat2(Y:naT,Y:naT))* -> .
(d0,A,r0,rw0) 71[0:Inp] ||  -> pp(ord_less_nat2(Y:naT,skf501(Y:naT)))*.
(d0,A,r0,rw0) 52[0:Inp] ||  -> equal(plus_plus_nat2(Y:naT,zero_zero_nat),Y:naT)**.
(d0,A,r0,rw0) 100[0:Inp] ||  -> equal(times_times_nat2(Y:naT,one_one_nat),Y:naT)**.
(d0,A,r0,rw0) 116[0:Inp] ||  -> equal(divide_divide_nat2(Y:naT,one_one_nat),Y:naT)**.
(d0,A,r0,rw0) 54[0:Inp] ||  -> equal(plus_plus_nat2(zero_zero_nat,Y:naT),Y:naT)**.
(d0,A,r0,rw0) 98[0:Inp] ||  -> equal(times_times_nat2(one_one_nat,Y:naT),Y:naT)**.
(d0,A,r0,rw0) 65[0:Inp] || pp(ord_less_int2(W:inT,W:inT))* -> .
(d0,A,r0,rw0) 72[0:Inp] ||  -> pp(ord_less_int2(W:inT,skf502(W:inT)))*.
(d0,A,r0,rw0) 70[0:Inp] ||  -> pp(ord_less_int2(skf500(W:inT),W:inT))*.
(d0,A,r0,rw0) 120[0:Inp] ||  -> equal(uminus_uminus_int1(uminus_uminus_int1(W:inT)),W:inT)**.
(d0,A,r0,rw0) 53[0:Inp] ||  -> equal(plus_plus_int2(W:inT,zero_zero_int),W:inT)**.
(d0,A,r0,rw0) 101[0:Inp] ||  -> equal(times_times_int2(W:inT,one_one_int),W:inT)**.
(d0,A,r0,rw0) 117[0:Inp] ||  -> equal(divide_divide_int2(W:inT,one_one_int),W:inT)**.
(d0,A,r0,rw0) 55[0:Inp] ||  -> equal(plus_plus_int2(zero_zero_int,W:inT),W:inT)**.
(d0,A,r0,rw0) 99[0:Inp] ||  -> equal(times_times_int2(one_one_int,W:inT),W:inT)**.
(d0,A,r0,rw0) 63[0:Inp] || pp(ord_less_num2(U:nuM,U:nuM))* -> .
(d0,A,r0,rw0) 136[0:Inp] ||  -> equal(times_times_num2(U:nuM,onE),U:nuM)**.
(d0,A,r0,rw0) 137[0:Inp] ||  -> equal(times_times_num2(onE,U:nuM),U:nuM)**.
(d0,A,r0,rw0) 18[0:Inp] ||  -> pp(ord_less_eq_nat2(Y:naT,Y:naT))*.
(d0,A,r0,rw0) 19[0:Inp] ||  -> pp(ord_less_eq_int2(W:inT,W:inT))*.
(d0,A,r0,rw0) 17[0:Inp] ||  -> pp(ord_less_eq_num2(U:nuM,U:nuM))*.
(d0,A,r0,rw0) 1862[0:Rew:612.1,1035.1,612.1,1035.1] || equal(Y:naT,zero_zero_nat)* -> pp(dvd_dvd_nat2(zero_zero_nat,zero_zero_nat))*.
(d0,A,r0,rw0) 503[0:Inp] || pp(ord_less_int2(uminus_uminus_int1(one_one_int),uminus_uminus_int1(numeral_numeral_int1(U:nuM))))* -> .
(d0,A,r0,rw0) 382[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,uminus_uminus_int1(numeral_numeral_int1(U:nuM))))* -> .
(d0,A,r0,rw0) 383[0:Inp] || pp(ord_less_int2(zero_zero_int,uminus_uminus_int1(numeral_numeral_int1(U:nuM))))* -> .
(d0,A,r0,rw0) 384[0:Inp] || pp(ord_less_eq_int2(one_one_int,uminus_uminus_int1(numeral_numeral_int1(U:nuM))))* -> .
(d0,A,r0,rw0) 388[0:Inp] || pp(ord_less_int2(one_one_int,uminus_uminus_int1(numeral_numeral_int1(U:nuM))))* -> .
(d0,A,r0,rw0) 385[0:Inp] || pp(ord_less_eq_int2(numeral_numeral_int1(U:nuM),uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 387[0:Inp] || pp(ord_less_int2(numeral_numeral_int1(U:nuM),uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 386[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),uminus_uminus_int1(one_one_int)))*.
(d0,A,r0,rw0) 328[0:Inp] || pp(ord_less_eq_nat2(numeral_numeral_nat1(U:nuM),zero_zero_nat))* -> .
(d0,A,r0,rw0) 329[0:Inp] || pp(ord_less_eq_int2(numeral_numeral_int1(U:nuM),zero_zero_int))* -> .
(d0,A,r0,rw0) 331[0:Inp] || pp(ord_less_int2(numeral_numeral_int1(U:nuM),zero_zero_int))* -> .
(d0,A,r0,rw0) 332[0:Inp] || pp(ord_less_nat2(numeral_numeral_nat1(U:nuM),one_one_nat))* -> .
(d0,A,r0,rw0) 333[0:Inp] || pp(ord_less_int2(numeral_numeral_int1(U:nuM),one_one_int))* -> .
(d0,A,r0,rw0) 317[0:Inp] || equal(numeral_numeral_int1(U:nuM),uminus_uminus_int1(one_one_int))* -> .
(d0,A,r0,rw0) 316[0:Inp] || equal(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),one_one_int)** -> .
(d0,A,r0,rw0) 318[0:Inp] || equal(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),zero_zero_int)** -> .
(d0,A,r0,rw0) 321[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(one_one_int),numeral_numeral_int1(U:nuM)))*.
(d0,A,r0,rw0) 324[0:Inp] ||  -> pp(ord_less_int2(uminus_uminus_int1(one_one_int),numeral_numeral_int1(U:nuM)))*.
(d0,A,r0,rw0) 319[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),zero_zero_int))*.
(d0,A,r0,rw0) 320[0:Inp] ||  -> pp(ord_less_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),zero_zero_int))*.
(d0,A,r0,rw0) 322[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),one_one_int))*.
(d0,A,r0,rw0) 323[0:Inp] ||  -> pp(ord_less_int2(uminus_uminus_int1(numeral_numeral_int1(U:nuM)),one_one_int))*.
(d0,A,r0,rw0) 147[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,skf677(X25:fun_nat_bool)))*.
(d0,A,r0,rw0) 68[0:Inp] || pp(ord_less_nat2(Y:naT,zero_zero_nat))* -> .
(d0,A,r0,rw0) 94[0:Inp] ||  -> equal(times_times_nat2(Y:naT,zero_zero_nat),zero_zero_nat)**.
(d0,A,r0,rw0) 114[0:Inp] ||  -> equal(divide_divide_nat2(Y:naT,zero_zero_nat),zero_zero_nat)**.
(d0,A,r0,rw0) 96[0:Inp] ||  -> equal(times_times_nat2(zero_zero_nat,Y:naT),zero_zero_nat)**.
(d0,A,r0,rw0) 112[0:Inp] ||  -> equal(divide_divide_nat2(zero_zero_nat,Y:naT),zero_zero_nat)**.
(d0,A,r0,rw0) 95[0:Inp] ||  -> equal(times_times_int2(W:inT,zero_zero_int),zero_zero_int)**.
(d0,A,r0,rw0) 115[0:Inp] ||  -> equal(divide_divide_int2(W:inT,zero_zero_int),zero_zero_int)**.
(d0,A,r0,rw0) 97[0:Inp] ||  -> equal(times_times_int2(zero_zero_int,W:inT),zero_zero_int)**.
(d0,A,r0,rw0) 113[0:Inp] ||  -> equal(divide_divide_int2(zero_zero_int,W:inT),zero_zero_int)**.
(d0,A,r0,rw0) 138[0:Inp] || pp(ord_less_num2(U:nuM,onE))* -> .
(d0,A,r0,rw0) 124[0:Inp] || equal(numeral_numeral_nat1(U:nuM),zero_zero_nat)** -> .
(d0,A,r0,rw0) 125[0:Inp] || equal(numeral_numeral_int1(U:nuM),zero_zero_int)** -> .
(d0,A,r0,rw0) 153[0:Inp] || equal(bit11(U:nuM),onE)** -> .
(d0,A,r0,rw0) 154[0:Inp] || equal(bit01(U:nuM),onE)** -> .
(d0,A,r0,rw0) 130[0:Inp] ||  -> pp(ord_less_eq_int2(zero_zero_int,numeral_numeral_int1(U:nuM)))*.
(d0,A,r0,rw0) 131[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,numeral_numeral_nat1(U:nuM)))*.
(d0,A,r0,rw0) 132[0:Inp] ||  -> pp(ord_less_int2(zero_zero_int,numeral_numeral_int1(U:nuM)))*.
(d0,A,r0,rw0) 133[0:Inp] ||  -> pp(ord_less_eq_nat2(one_one_nat,numeral_numeral_nat1(U:nuM)))*.
(d0,A,r0,rw0) 134[0:Inp] ||  -> pp(ord_less_eq_int2(one_one_int,numeral_numeral_int1(U:nuM)))*.
(d0,A,r0,rw0) 141[0:Inp] ||  -> pp(ord_less_num2(onE,bit01(U:nuM)))*.
(d0,A,r0,rw0) 142[0:Inp] ||  -> pp(ord_less_num2(onE,bit11(U:nuM)))*.
(d0,A,r0,rw0) 22[0:Inp] ||  -> pp(ord_less_eq_nat2(zero_zero_nat,Y:naT))*.
(d0,A,r0,rw0) 50[0:Inp] ||  -> member_int(numeral_numeral_int1(U:nuM),ring_1_Ints_int)*.
(d0,A,r0,rw0) 652[0:Inp] ||  -> equal(divide_divide_int2(uminus_uminus_int1(one_one_int),numeral_numeral_int1(bit01(onE))),uminus_uminus_int1(one_one_int))**.
(d0,A,r0,rw0) 398[0:Inp] ||  -> equal(plus_plus_nat2(one_one_nat,one_one_nat),numeral_numeral_nat1(bit01(onE)))**.
(d0,A,r0,rw0) 325[0:Inp] || pp(ord_less_eq_int2(one_one_int,uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 327[0:Inp] || pp(ord_less_int2(one_one_int,uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 334[0:Inp] || pp(ord_less_eq_int2(zero_zero_int,uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 335[0:Inp] || pp(ord_less_int2(zero_zero_int,uminus_uminus_int1(one_one_int)))* -> .
(d0,A,r0,rw0) 310[0:Inp] ||  -> pp(ord_less_int2(zero_zero_int,plus_plus_int2(one_one_int,one_one_int)))*.
(d0,A,r0,rw0) 1823[0:Rew:1821.0,1820.0] ||  -> equal(neg_nu323594467c_int1(uminus_uminus_int1(one_one_int)),uminus_uminus_int1(one_one_int))**.
(d0,A,r0,rw0) 1808[0:Rew:336.0,155.0] ||  -> equal(plus_plus_num2(onE,onE),bit01(onE))**.
(d0,A,r0,rw0) 108[0:Inp] || pp(ord_less_eq_nat2(one_one_nat,zero_zero_nat))* -> .
(d0,A,r0,rw0) 109[0:Inp] || pp(ord_less_eq_int2(one_one_int,zero_zero_int))* -> .
(d0,A,r0,rw0) 111[0:Inp] || pp(ord_less_int2(one_one_int,zero_zero_int))* -> .
(d0,A,r0,rw0) 123[0:Inp] || equal(uminus_uminus_int1(one_one_int),one_one_int)** -> .
(d0,A,r0,rw0) 127[0:Inp] || equal(uminus_uminus_int1(one_one_int),zero_zero_int)** -> .
(d0,A,r0,rw0) 126[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(one_one_int),one_one_int))*.
(d0,A,r0,rw0) 128[0:Inp] ||  -> pp(ord_less_int2(uminus_uminus_int1(one_one_int),one_one_int))*.
(d0,A,r0,rw0) 135[0:Inp] ||  -> pp(ord_less_eq_int2(uminus_uminus_int1(one_one_int),zero_zero_int))*.
(d0,A,r0,rw0) 38[0:Inp] || equal(zero_zero_nat,one_one_nat)** -> .
(d0,A,r0,rw0) 39[0:Inp] || equal(zero_zero_int,one_one_int)** -> .
(d0,A,r0,rw0) 13[0:Inp] ||  -> pp(monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r0,rw0) 14[0:Inp] ||  -> pp(monoid_int2(plus_plus_int,zero_zero_int))*.
(d0,A,r0,rw0) 15[0:Inp] ||  -> pp(comm_monoid_nat2(plus_plus_nat,zero_zero_nat))*.
(d0,A,r0,rw0) 16[0:Inp] ||  -> pp(comm_monoid_int2(plus_plus_int,zero_zero_int))*.
(d0,A,r0,rw0) 32[0:Inp] ||  -> pp(comm_monoid_nat2(times_times_nat,one_one_nat))*.
(d0,A,r0,rw0) 33[0:Inp] ||  -> pp(comm_monoid_int2(times_times_int,one_one_int))*.
(d0,A,r0,rw0) 34[0:Inp] ||  -> pp(monoid_nat2(times_times_nat,one_one_nat))*.
(d0,A,r0,rw0) 35[0:Inp] ||  -> pp(monoid_int2(times_times_int,one_one_int))*.
(d0,A,r0,rw0) 43[0:Inp] ||  -> pp(ord_less_eq_int2(zero_zero_int,one_one_int))*.
(d0,A,r0,rw0) 46[0:Inp] ||  -> pp(ord_less_nat2(zero_zero_nat,one_one_nat))*.
(d0,A,r0,rw0) 47[0:Inp] ||  -> pp(ord_less_int2(zero_zero_int,one_one_int))*.
(d0,A,r0,rw0) 49[0:Inp] ||  -> equal(uminus_uminus_int1(zero_zero_int),zero_zero_int)**.
(d0,A,r0,rw0) 51[0:Inp] ||  -> equal(numeral_numeral_nat1(onE),one_one_nat)**.
(d0,A,r0,rw0) 12[0:Inp] || pp(fFalsE)* -> .
(d0,A,r0,rw0) 10[0:Inp] ||  -> member_int(zero_zero_int,ring_1_Ints_int)*.
(d0,A,r0,rw0) 11[0:Inp] ||  -> member_int(one_one_int,ring_1_Ints_int)*.
(d0,A,r0,rw0) 9[0:Inp] ||  -> pp(fTruE)*.
(d0,A,r0,rw0) 1[0:Inp] ||  -> abel_semigroup_nat(times_times_nat)*.
(d0,A,r0,rw0) 2[0:Inp] ||  -> abel_semigroup_int(times_times_int)*.
(d0,A,r0,rw0) 3[0:Inp] ||  -> semigroup_nat(times_times_nat)*.
(d0,A,r0,rw0) 4[0:Inp] ||  -> semigroup_int(times_times_int)*.
(d0,A,r0,rw0) 5[0:Inp] ||  -> abel_semigroup_nat(plus_plus_nat)*.
(d0,A,r0,rw0) 6[0:Inp] ||  -> abel_semigroup_int(plus_plus_int)*.
(d0,A,r0,rw0) 7[0:Inp] ||  -> semigroup_nat(plus_plus_nat)*.
(d0,A,r0,rw0) 8[0:Inp] ||  -> semigroup_int(plus_plus_int)*.