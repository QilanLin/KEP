theory Test_Sledgehammer
imports Main
begin

(* 测试Sledgehammer基本功能 *)
lemma test1: "x + 0 = x"
  by sledgehammer

(* 测试是否可以导出 *)
lemma test2: "\<forall>x. P(x) \<longrightarrow> P(x)"
  by sledgehammer

end

