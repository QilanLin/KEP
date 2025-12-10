theory Test_Sets
imports Main
begin

text \<open>Set operations for testing\<close>

lemma set_union_comm: "A \<union> B = B \<union> A"
  by auto

lemma set_inter_comm: "A \<inter> B = B \<inter> A"
  by auto

lemma set_union_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by auto

lemma set_inter_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by auto

text \<open>De Morgan's laws\<close>

lemma demorgan_union: "-(A \<union> B) = -A \<inter> -B"
  by auto

lemma demorgan_inter: "-(A \<inter> B) = -A \<union> -B"
  by auto

end

