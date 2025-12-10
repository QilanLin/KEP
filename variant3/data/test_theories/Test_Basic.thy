theory Test_Basic
imports Main
begin

text \<open>Basic arithmetic properties\<close>

lemma add_zero: "x + 0 = (x::nat)"
  by simp

lemma add_comm: "x + y = y + (x::nat)"
  by simp

lemma mult_one: "x * 1 = (x::nat)"
  by simp

lemma mult_zero: "x * 0 = (0::nat)"
  by simp

text \<open>Test with sledgehammer\<close>

lemma test_sledgehammer_1: "x + (y + z) = (x + y) + (z::nat)"
  by (simp add: add.assoc)

lemma test_sledgehammer_2: "x + y = y + x \<Longrightarrow> x + y + z = z + y + (x::nat)"
  by (simp add: add.commute add.left_commute)

end

