theory Test_Options
imports Main
begin

text \<open>Option type properties\<close>

lemma option_map_none: "map_option f None = None"
  by simp

lemma option_map_some: "map_option f (Some x) = Some (f x)"
  by simp

lemma option_bind_none: "Option.bind None f = None"
  by simp

lemma option_bind_some: "Option.bind (Some x) f = f x"
  by simp

text \<open>Option comparison\<close>

lemma option_none_not_some: "None \<noteq> Some x"
  by simp

end

