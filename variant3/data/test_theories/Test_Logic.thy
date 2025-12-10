theory Test_Logic
imports Main
begin

text \<open>Propositional logic properties\<close>

lemma logic_and_comm: "P \<and> Q \<longleftrightarrow> Q \<and> P"
  by auto

lemma logic_or_comm: "P \<or> Q \<longleftrightarrow> Q \<or> P"
  by auto

lemma logic_implies_trans: "\<lbrakk>P \<longrightarrow> Q; Q \<longrightarrow> R\<rbrakk> \<Longrightarrow> P \<longrightarrow> R"
  by auto

lemma logic_not_not: "\<not>\<not>P \<longleftrightarrow> P"
  by auto

text \<open>More complex logical properties\<close>

lemma logic_distrib_and_or: "P \<and> (Q \<or> R) \<longleftrightarrow> (P \<and> Q) \<or> (P \<and> R)"
  by auto

lemma logic_distrib_or_and: "P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)"
  by auto

end

