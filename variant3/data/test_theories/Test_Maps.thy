theory Test_Maps
imports Main
begin

text \<open>Map (finite function) properties\<close>

lemma map_empty: "Map.empty x = None"
  by simp

lemma map_update: "(m(k \<mapsto> v)) k = Some v"
  by simp

lemma map_update_other: "k \<noteq> k' \<Longrightarrow> (m(k \<mapsto> v)) k' = m k'"
  by simp

lemma map_dom_empty: "dom Map.empty = {}"
  by simp

lemma map_dom_update: "dom (m(k \<mapsto> v)) = insert k (dom m)"
  by auto

end

