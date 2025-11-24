theory Seed_Logic_Formulas
  imports Main
begin

(* Logic formulas - good for mutations *)

lemma conj_comm: "(P ∧ Q) = (Q ∧ P)"
  by simp

lemma disj_comm: "(P ∨ Q) = (Q ∨ P)"
  by simp

lemma conj_assoc: "((P ∧ Q) ∧ R) = (P ∧ (Q ∧ R))"
  by simp

lemma disj_assoc: "((P ∨ Q) ∨ R) = (P ∨ (Q ∨ R))"
  by simp

lemma double_neg: "(¬ ¬ P) = P"
  by simp

lemma de_morgan_conj: "(¬ (P ∧ Q)) = (¬ P ∨ ¬ Q)"
  by simp

lemma de_morgan_disj: "(¬ (P ∨ Q)) = (¬ P ∧ ¬ Q)"
  by simp

lemma impl_to_disj: "(P ⟶ Q) = (¬ P ∨ Q)"
  by simp

lemma contrapositive: "(P ⟶ Q) = (¬ Q ⟶ ¬ P)"
  by simp

lemma distrib_conj_disj: "(P ∧ (Q ∨ R)) = ((P ∧ Q) ∨ (P ∧ R))"
  by simp

lemma distrib_disj_conj: "(P ∨ (Q ∧ R)) = ((P ∨ Q) ∧ (P ∨ R))"
  by simp

lemma distrib_disj_conj_dup: "(P ∨ (Q ∧ R)) = ((P ∨ Q) ∧ (P ∨ R))"
  by simp

end

