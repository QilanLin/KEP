theory Test_Functions
imports Main
begin

text \<open>Function composition properties\<close>

lemma function_comp_assoc: "f \<circ> (g \<circ> h) = (f \<circ> g) \<circ> h"
  by (rule ext, simp)

lemma function_id_left: "id \<circ> f = f"
  by (rule ext, simp)

lemma function_id_right: "f \<circ> id = f"
  by (rule ext, simp)

text \<open>Function application properties\<close>

lemma function_map_comp: "map (f \<circ> g) xs = map f (map g xs)"
  by simp

lemma function_filter_map: "(\<forall>x. P (f x) = Q x) \<Longrightarrow> filter P (map f xs) = map f (filter Q xs)"
  by (induction xs) auto

end

