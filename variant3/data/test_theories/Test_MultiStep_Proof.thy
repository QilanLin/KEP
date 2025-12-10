theory Test_MultiStep_Proof
imports Main
begin

text \<open>Testing multi-step proofs that might fail\<close>

(* 需要多步推理 *)
lemma multi_step_1:
  assumes "a = b" and "b = c" and "c = d"
  shows "a = d"
  using assms by simp

(* 复杂的case分析 *)
lemma case_analysis:
  "P x \<or> Q x \<Longrightarrow> (\<forall>y. P y \<longrightarrow> R y) \<Longrightarrow> (\<forall>z. Q z \<longrightarrow> R z) \<Longrightarrow> R x"
  by auto

(* 需要lemma辅助 *)
lemma helper: "x + 0 = (x::nat)" by simp

lemma needs_helper: "x + 0 + y = x + (y::nat)"
  by (simp add: helper)

end

