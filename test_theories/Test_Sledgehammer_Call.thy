theory Test_Sledgehammer_Call
imports Main
begin

text \<open>Test Sledgehammer integration - 测试Sledgehammer调用\<close>

(* 简单的lemma，应该能用sledgehammer找到proof *)
lemma sledgehammer_test_1: "x + 0 = (x::nat)"
  sledgehammer

(* 更复杂的lemma *)
lemma sledgehammer_test_2: "x + y + z = (x + z) + (y::nat)"
  sledgehammer [timeout = 10]

end

