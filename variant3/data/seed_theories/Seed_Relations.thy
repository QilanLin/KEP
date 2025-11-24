theory Seed_Relations
  imports Main
begin

(* Relations and order lemmas *)

lemma refl_on_empty: "refl_on {} {}"
  by (simp add: refl_on_def)

lemma sym_empty: "sym {}"
  by (simp add: sym_def)

lemma trans_empty: "trans {}"
  by (simp add: trans_def)

lemma converse_converse: "r^-1^-1 = r"
  by auto

lemma converse_Un: "(r ∪ s)^-1 = r^-1 ∪ s^-1"
  by auto

lemma Image_empty: "r `` {} = {}"
  by auto

lemma Image_Un: "r `` (A ∪ B) = r `` A ∪ r `` B"
  by auto

lemma antisym_subset: "⟦antisym r; s ⊆ r⟧ ⟹ antisym s"
  by (auto simp: antisym_def)

lemma linear_order_on_empty: "linear_order_on {} {}"
  by (simp add: linear_order_on_def partial_order_on_def preorder_on_def refl_on_def trans_def antisym_def total_on_def)

end

