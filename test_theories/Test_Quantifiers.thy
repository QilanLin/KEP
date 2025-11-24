theory Test_Quantifiers
imports Main
begin

text \<open>Quantifier properties\<close>

lemma forall_conj: "(\<forall>x. P x \<and> Q x) \<longleftrightarrow> (\<forall>x. P x) \<and> (\<forall>x. Q x)"
  by auto

lemma exists_disj: "(\<exists>x. P x \<or> Q x) \<longleftrightarrow> (\<exists>x. P x) \<or> (\<exists>x. Q x)"
  by auto

lemma forall_implies_exists: "(\<forall>x. P x) \<Longrightarrow> (\<exists>x. P x) \<Longrightarrow> True"
  by auto

lemma demorgan_forall: "\<not>(\<forall>x. P x) \<longleftrightarrow> (\<exists>x. \<not>P x)"
  by auto

lemma demorgan_exists: "\<not>(\<exists>x. P x) \<longleftrightarrow> (\<forall>x. \<not>P x)"
  by auto

end

