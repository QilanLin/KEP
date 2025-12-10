theory Test_Pairs
imports Main
begin

text \<open>Pair/Product type properties\<close>

lemma pair_fst_snd: "(fst p, snd p) = p"
  by simp

lemma pair_surjective: "\<exists>a b. p = (a, b)"
  by simp

lemma pair_inject: "(a, b) = (c, d) \<longleftrightarrow> a = c \<and> b = d"
  by simp

text \<open>Product operations\<close>

lemma pair_map: "map_prod f g (a, b) = (f a, g b)"
  by simp

end

