theory Seed_Numbers
  imports Main
begin

(* Number theory basics *)

lemma even_double: "even (2 * n)"
  by simp

lemma odd_Suc: "odd (Suc n) = even n"
  by simp

lemma even_Suc: "even (Suc n) = odd n"
  by simp

lemma dvd_refl: "True ⟹ n dvd (n::nat)"
  by simp

lemma dvd_trans: "⟦k dvd m; m dvd n⟧ ⟹ k dvd (n::nat)"
  by (rule dvd_trans)

lemma dvd_add: "⟦k dvd m; k dvd n⟧ ⟹ k dvd (m + n::nat)"
  by (simp add: dvd_add)

lemma dvd_mult: "k dvd m ⟹ k dvd (m * n::nat)"
  by simp

lemma dvd_mult2: "k dvd n ⟹ k dvd (m * n::nat)"
  by simp

lemma gcd_comm: "gcd m n = gcd n (m::nat)"
  by (simp add: gcd.commute)

lemma gcd_zero: "gcd n 0 = (n::nat)"
  by simp

lemma lcm_comm: "lcm m n = lcm n (m::nat)"
  by (simp add: lcm.commute)

end

