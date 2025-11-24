theory Seed_Set_Operations
  imports Main
begin

(* Set operation lemmas - good for mutations *)

lemma union_comm: "A ∪ B = B ∪ A"
  by auto

lemma union_assoc: "(A ∪ B) ∪ C = A ∪ (B ∪ C)"
  by auto

lemma inter_comm: "A ∩ B = B ∩ A"
  by auto

lemma inter_assoc: "(A ∩ B) ∩ C = A ∩ (B ∩ C)"
  by auto

lemma union_empty: "A ∪ {} = A"
  by simp

lemma inter_empty: "A ∩ {} = {}"
  by simp

lemma inter_absorb: "A ∩ (A ∪ B) = A"
  by auto

lemma union_absorb: "A ∪ (A ∩ B) = A"
  by auto

lemma de_morgan_1: "-(A ∪ B) = -A ∩ -B"
  by auto

lemma de_morgan_1_dup: "-(A ∪ B) = -A ∩ -B"
  by auto

lemma de_morgan_2: "-(A ∩ B) = -A ∪ -B"
  by auto

lemma subset_union: "A ⊆ B ⟹ A ∪ C ⊆ B ∪ C"
  by auto

lemma subset_inter: "A ⊆ B ⟹ A ∩ C ⊆ B ∩ C"
  by auto

end

