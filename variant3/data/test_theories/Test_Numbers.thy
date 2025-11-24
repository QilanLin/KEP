theory Test_Numbers
imports Main
begin

text \<open>Natural number properties\<close>

lemma nat_add_mono: "x \<le> y \<Longrightarrow> x + z \<le> y + (z::nat)"
  by simp

lemma nat_mult_mono: "\<lbrakk>x \<le> y; 0 < z\<rbrakk> \<Longrightarrow> x * z \<le> y * (z::nat)"
  by simp

lemma nat_pred_succ: "0 < n \<Longrightarrow> Suc (n - 1) = n"
  by simp

text \<open>Integer properties\<close>

lemma int_abs_pos: "abs (x::int) \<ge> 0"
  by simp

lemma int_abs_mult: "abs (x * y) = abs x * abs (y::int)"
  by (simp add: abs_mult)

end

