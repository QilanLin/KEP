theory Test_Monoids
imports Main
begin

text \<open>Monoid properties\<close>

class my_monoid = 
  fixes m_unit :: "'a" ("1\<^sub>m")
  fixes m_op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*\<^sub>m" 70)
  assumes m_assoc: "(x *\<^sub>m y) *\<^sub>m z = x *\<^sub>m (y *\<^sub>m z)"
  assumes m_left_unit: "1\<^sub>m *\<^sub>m x = x"
  assumes m_right_unit: "x *\<^sub>m 1\<^sub>m = x"

lemma (in my_monoid) monoid_unit_unique:
  assumes "\<forall>x. e *\<^sub>m x = x" and "\<forall>x. x *\<^sub>m e = x"
  shows "e = 1\<^sub>m"
  using assms m_right_unit by metis

end

