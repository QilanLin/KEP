theory Test_Sorting
imports Main
begin

text \<open>Sorting and ordering properties\<close>

lemma sorted_append: "\<lbrakk>sorted xs; sorted ys; \<forall>x\<in>set xs. \<forall>y\<in>set ys. x \<le> y\<rbrakk> 
  \<Longrightarrow> sorted (xs @ ys)"
  by (simp add: sorted_append)

lemma sorted_filter: "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (induct xs, auto)

lemma sorted_map_mono: "\<lbrakk>sorted xs; mono f\<rbrakk> \<Longrightarrow> sorted (map f xs)"
  by (induct xs, auto simp: mono_def sorted_Cons)

end

