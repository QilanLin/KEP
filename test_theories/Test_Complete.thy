theory Test_Complete
imports Main
begin

text \<open>Completeness properties\<close>

lemma complete_lub: "(\<exists>x. x \<in> S) \<Longrightarrow> (\<exists>b. \<forall>x\<in>S. x \<le> (b::nat)) \<Longrightarrow> 
  \<exists>l. (\<forall>x\<in>S. x \<le> l) \<and> (\<forall>b. (\<forall>x\<in>S. x \<le> b) \<longrightarrow> l \<le> b)"
  by (rule_tac x="Max S" in exI, auto simp: Max_ge_iff)

end

