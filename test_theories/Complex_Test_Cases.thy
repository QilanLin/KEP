theory Complex_Test_Cases
imports Main "HOL-Library.Multiset"
begin

text \<open>更复杂的测试用例 - 可能触发Sledgehammer Integration bugs\<close>

(* 高阶逻辑 - HOL推理 *)
lemma higher_order_1: "(\<forall>x. P x \<or> Q x) \<longleftrightarrow> (\<forall>x. P x) \<or> (\<exists>x. Q x)"
  by auto

(* 深度嵌套的量词 - 可能难以编码到TPTP *)
lemma nested_quantifiers:
  "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>f. \<forall>x. P x (f x))"
  by (rule choice, simp)

(* Induction - 需要特殊处理 *)
lemma list_induction_test: "length (rev xs) = length xs"
  by simp

(* 更复杂的induction *)
lemma list_rev_append: "rev (xs @ ys) = rev ys @ rev xs"
  by simp

(* Type class constraints *)
lemma type_class_test: 
  fixes x y :: "'a::comm_monoid_add"
  shows "x + y = y + x"
  by (simp add: add.commute)

(* Lambda表达式 - 可能在TPTP编码中有问题 *)
lemma lambda_test_1: "(\<lambda>x. x + (1::nat)) 5 = 6"
  by simp

lemma lambda_composition: "(\<lambda>x. f (g x)) = f \<circ> g"
  by (rule ext, simp)

(* 高阶函数 *)
lemma map_compose: "map (f \<circ> g) xs = map f (map g xs)"
  by simp

lemma fold_append: "fold f (xs @ ys) a = fold f ys (fold f xs a)"
  by simp

(* Set理论 *)
lemma set_union_comm: "A \<union> B = B \<union> A"
  by auto

lemma set_intersection_dist: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by auto

(* 涉及多个type variables *)
lemma map_fusion: 
  "map f (map g xs) = map (\<lambda>x. f (g x)) xs"
  by simp

(* 需要arithmetic reasoning *)
lemma arith_complex_1:
  fixes n m :: nat
  assumes "n > 0" "m > 0"
  shows "n * m > 0"
  using assms by simp

(* 条件推理 *)
lemma conditional_reasoning:
  "(if P then Q else R) \<and> (P \<or> \<not>P) \<longleftrightarrow> (P \<and> Q) \<or> (\<not>P \<and> R)"
  by auto

end

