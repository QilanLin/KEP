theory Test_Arithmetic
imports Main
begin

text \<open>Arithmetic properties\<close>

lemma arith_distrib: "x * (y + z) = x * y + x * (z::nat)"
  by (simp add: distrib_left)

lemma arith_factor: "x * y + x * z = x * (y + z::nat)"
  by (simp add: distrib_left)

lemma arith_div_mult: "0 < n \<Longrightarrow> (x * n) div n = (x::nat)"
  by simp

lemma arith_mod_mult: "(x * n) mod n = (0::nat)"
  by simp

lemma arith_power: "(x::nat) ^ (m + n) = x ^ m * x ^ n"
  by (simp add: power_add)

end

