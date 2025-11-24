theory Test_Proving_Goals
imports Main
begin

text \<open>Testing different proving scenarios - 测试不同的证明场景\<close>

(* 应该能证明的简单目标 *)
lemma easy_goal: "a \<and> b \<longrightarrow> b \<and> a"
  by auto

(* 需要多步推理 *)
lemma multi_step: "\<lbrakk>a \<longrightarrow> b; b \<longrightarrow> c\<rbrakk> \<Longrightarrow> a \<longrightarrow> c"
  by auto

(* 可能更难证明的目标 *)
lemma harder_goal: "(\<forall>x. P x \<or> Q x) \<longrightarrow> (\<forall>x. P x) \<or> (\<exists>x. Q x)"
  by auto

end

