theory Test_Relations
imports Main
begin

text \<open>Relation properties\<close>

definition reflexive :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "reflexive R \<longleftrightarrow> (\<forall>x. (x, x) \<in> R)"

definition symmetric :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "symmetric R \<longleftrightarrow> (\<forall>x y. (x, y) \<in> R \<longrightarrow> (y, x) \<in> R)"

definition transitive :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "transitive R \<longleftrightarrow> (\<forall>x y z. (x, y) \<in> R \<and> (y, z) \<in> R \<longrightarrow> (x, z) \<in> R)"

lemma sym_union: "symmetric R \<Longrightarrow> symmetric S \<Longrightarrow> symmetric (R \<union> S)"
  unfolding symmetric_def by auto

end

