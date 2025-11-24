theory Test_Metis_Smt
imports Main
begin

text \<open>Testing metis and smt proof methods\<close>

(* metis proof *)
lemma metis_test_1: "A \<and> B \<longrightarrow> B \<and> A"
  by metis

(* metis可能失败的场景 *)
lemma metis_fail: "(\<forall>x. P x) \<and> (\<forall>x. Q x) \<longrightarrow> (\<forall>x. P x \<and> Q x)"
  by metis

(* smt proof *)
lemma smt_test_1: "(a::int) * b = b * a"
  by simp

end

