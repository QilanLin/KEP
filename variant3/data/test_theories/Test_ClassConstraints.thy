theory Test_ClassConstraints
imports Main
begin

text \<open>Testing type class constraints\<close>

(* 可能的type class问题 *)
lemma class_test_1: "(x::'a::comm_monoid_add) + y = y + x"
  by (simp add: add.commute)

(* 错误的type class constraint *)
lemma class_test_2: "x * y = y * (x::'a::monoid_add)"
  by simp

end

