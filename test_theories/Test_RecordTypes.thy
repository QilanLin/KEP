theory Test_RecordTypes
imports Main
begin

text \<open>Testing record type operations\<close>

record point =
  x :: nat
  y :: nat

(* Record操作 *)
lemma record_test_1: "x (point.make 3 4) = 3"
  by simp

(* Record update *)
lemma record_test_2: "x (point.make 1 2) = 1"
  by simp

end

