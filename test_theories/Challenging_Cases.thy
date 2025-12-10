theory Challenging_Cases
imports Main "HOL-Library.Multiset" "HOL-Library.FSet"
begin

text \<open>挑战性测试用例 - 可能触发Sledgehammer问题\<close>

(* 1. 高阶逻辑和量词交换 - TPTP编码可能有问题 *)
lemma quantifier_swap:
  assumes "\<forall>x. \<exists>y. P x y"
  shows "\<exists>f. \<forall>x. P x (f x)"
  using assms by (rule choice)

(* 2. 复杂的List induction *)
lemma list_rev_induct:
  assumes "P []"
    and "\<And>xs x. P xs \<Longrightarrow> P (xs @ [x])"
  shows "P xs"
  using assms by (induct xs rule: rev_induct, auto)

(* 3. 涉及多个type classes *)
lemma multi_typeclass:
  fixes x y :: "'a::comm_monoid_add"
  shows "x + y + 0 = y + x"
  by (simp add: add.commute)

(* 4. 嵌套的data structures *)
lemma nested_map:
  "map (map f) xss = map (\<lambda>xs. map f xs) xss"
  by simp

(* 5. Set和List的交互 *)
lemma set_list_interaction:
  "set (filter P xs) = {x \<in> set xs. P x}"
  by auto

(* 6. 更复杂的arithmetic *)
lemma complex_arith:
  fixes m n k :: nat
  assumes "m > 0" "n > 0"
  shows "m * n + k = k + n * m"
  by (simp add: mult.commute)

(* 7. 条件表达式 *)
lemma conditional_complex:
  "filter (\<lambda>x. if x > 0 then True else False) xs = 
   filter (\<lambda>x. x > (0::int)) xs"
  by auto

(* 8. Fold操作 *)
lemma fold_append_simple:
  "fold f (xs @ ys) z = fold f ys (fold f xs z)"
  by simp

(* 9. 涉及FSet的性质 *)
lemma fset_ops:
  "finsert x (finsert y s) = finsert y (finsert x s)"
  by auto

(* 10. Multiset操作 *)
lemma multiset_union:
  "(M :: 'a multiset) + N = N + M"
  by (simp add: add.commute)

(* 11. 存在性证明 *)
lemma exists_witness:
  "\<exists>x::nat. x > 0"
  by auto

(* 12. 复杂的逻辑组合 *)
lemma logic_combination:
  "(\<forall>x. P x \<longrightarrow> Q x) \<and> (\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)"
  by auto

(* 13. Case分析 *)
lemma case_analysis_list:
  "length (case xs of [] \<Rightarrow> [y] | _ \<Rightarrow> xs) > 0"
  by (cases xs, auto)

(* 14. 高阶函数组合 *)
lemma higher_order_compose:
  "map f (map g (map h xs)) = map (f \<circ> g \<circ> h) xs"
  by simp

(* 15. 涉及Option类型 *)
lemma option_map:
  "map_option f None = None"
  by simp

end

