theory Test_HOL
imports Main
begin

text \<open>Higher-order logic properties\<close>

lemma hol_extensionality: "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
  by auto

lemma hol_exists_unique: "(\<exists>!x. P x) \<longleftrightarrow> (\<exists>x. P x \<and> (\<forall>y. P y \<longrightarrow> y = x))"
  by auto

lemma hol_choice: "(\<forall>x. \<exists>y. P x y) \<Longrightarrow> \<exists>f. \<forall>x. P x (f x)"
  by (rule choice, auto)

end

