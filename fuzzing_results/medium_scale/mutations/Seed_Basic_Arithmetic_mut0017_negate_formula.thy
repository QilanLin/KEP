theory Seed_Basic_Arithmetic
  imports Main
begin

(* Basic arithmetic lemmas - good for mutations *)

lemma add_comm: "¬ (x + y = y + (x::nat))"
  by simp

lemma add_assoc: "(x + y) + z = x + (y + (z::nat))"
  by simp

lemma add_zero: "x + 0 = (x::nat)"
  by simp

lemma mult_comm: "x * y = y * (x::nat)"
  by simp

lemma mult_one: "x * 1 = (x::nat)"
  by simp

lemma mult_zero: "x * 0 = (0::nat)"
  by simp

lemma add_mult_distrib: "(x + y) * z = x * z + y * (z::nat)"
  by (simp add: algebra_simps)

lemma sub_add: "x ≥ y ⟹ (x - y) + y = (x::nat)"
  by simp

lemma double_eq: "x + x = 2 * (x::nat)"
  by simp

lemma square_pos: "x > 0 ⟹ x * x > (0::nat)"
  by simp

end

