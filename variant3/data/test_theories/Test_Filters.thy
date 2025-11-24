theory Test_Filters
imports Main
begin

text \<open>Filter and partition properties\<close>

lemma filter_all: "(\<forall>x\<in>set xs. P x) \<Longrightarrow> filter P xs = xs"
  by (induct xs, auto)

lemma filter_none: "(\<forall>x\<in>set xs. \<not>P x) \<Longrightarrow> filter P xs = []"
  by (induct xs, auto)

lemma filter_comp: "filter P (filter Q xs) = filter (\<lambda>x. P x \<and> Q x) xs"
  by (induct xs, auto)

lemma partition_filter: "partition P xs = (filter P xs, filter (\<lambda>x. \<not>P x) xs)"
  by (induct xs, auto)

end

