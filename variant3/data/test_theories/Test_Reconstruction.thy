theory Test_Reconstruction
imports Main
begin

(* 
   专门测试 Proof Reconstruction 的 theory
   包含简单的 lemmas，让 Sledgehammer 找到 proof，
   然后测试 proof 是否能成功重构
*)

(* 简单的逻辑定理 - Sledgehammer 应该很容易找到 proof *)
lemma conjunction_comm: "A \<and> B \<longrightarrow> B \<and> A"
  by auto

lemma disjunction_comm: "A \<or> B \<longrightarrow> B \<or> A"
  by auto

lemma implication_trans: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  by auto

lemma double_neg: "\<not>\<not>A \<longrightarrow> A"
  by auto

lemma de_morgan_1: "\<not>(A \<and> B) \<longleftrightarrow> \<not>A \<or> \<not>B"
  by auto

lemma de_morgan_2: "\<not>(A \<or> B) \<longleftrightarrow> \<not>A \<and> \<not>B"
  by auto

(* 集合定理 *)
lemma set_union_comm: "A \<union> B = B \<union> A"
  by auto

lemma set_inter_comm: "A \<inter> B = B \<inter> A"
  by auto

(* 算术定理 *)
lemma add_comm: "(a::nat) + b = b + a"
  by auto

lemma add_assoc: "((a::nat) + b) + c = a + (b + c)"
  by auto

lemma mult_comm: "(a::nat) * b = b * a"
  by auto

(* 列表定理 *)
lemma list_append_nil: "xs @ [] = xs"
  by auto

lemma list_rev_rev: "rev (rev xs) = xs"
  by auto

(* 需要 Sledgehammer 帮助的定理 *)
lemma needs_sledgehammer_1:
  assumes "A \<longrightarrow> B" and "B \<longrightarrow> C" and "C \<longrightarrow> D"
  shows "A \<longrightarrow> D"
  using assms by auto

lemma needs_sledgehammer_2:
  assumes "x \<in> A" and "A \<subseteq> B"
  shows "x \<in> B"
  using assms by auto

lemma needs_sledgehammer_3:
  fixes n :: nat
  shows "n + 0 = n"
  by auto

end

