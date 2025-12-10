theory Test_TPTPEncoding
imports Main
begin

text \<open>Testing TPTP encoding edge cases\<close>

(* 特殊字符在名称中 *)
definition "my_special_pred x = (x > 0)"

lemma special_char_test: "my_special_pred (5::nat)"
  by (simp add: my_special_pred_def)

(* 高阶函数 *)
lemma higher_order: "map (map f) xss = map (\<lambda>xs. map f xs) xss"
  by simp

(* Lambda表达式 *)
lemma lambda_test: "(\<lambda>x. x + 1) y = y + (1::nat)"
  by simp

end

