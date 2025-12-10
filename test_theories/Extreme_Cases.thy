theory Extreme_Cases
imports Main "HOL-Library.Multiset" "HOL-Library.FSet"
begin

text \<open>极端复杂的测试用例 - 更可能触发Integration bugs\<close>

(* 1. 深度嵌套的数据结构 *)
datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"

fun tree_height :: "'a tree \<Rightarrow> nat" where
  "tree_height (Leaf _) = 0" |
  "tree_height (Node l r) = 1 + max (tree_height l) (tree_height r)"

lemma tree_height_nonneg: "tree_height t \<ge> 0"
  by (induction t) auto

(* 2. 复杂的相互递归 *)
fun even :: "nat \<Rightarrow> bool" and odd :: "nat \<Rightarrow> bool" where
  "even 0 = True" |
  "even (Suc n) = odd n" |
  "odd 0 = False" |
  "odd (Suc n) = even n"

lemma even_or_odd: "even n \<or> odd n"
  by (induction n) auto

(* 3. 高度参数化的类型 *)
lemma parametric_lemma:
  fixes f :: "'a \<Rightarrow> 'b"
  fixes g :: "'b \<Rightarrow> 'c"
  shows "map (g \<circ> f) xs = map g (map f xs)"
  by simp

(* 4. 复杂的存在性量词 *)
lemma complex_exists:
  assumes "\<forall>x. \<exists>y. P x y"
  shows "\<exists>f. \<forall>x. P x (f x)"
  using assms by (rule choice)

(* 5. 深度嵌套的case表达式 *)
lemma nested_cases:
  "length (case xs of 
            [] \<Rightarrow> (case ys of [] \<Rightarrow> [1::nat] | _ \<Rightarrow> ys)
          | _ \<Rightarrow> xs @ ys) > 0"
  by (cases xs; cases ys) auto

(* 6. 涉及wellفounded recursion *)
function fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0" |
  "fib (Suc 0) = 1" |
  "fib (Suc (Suc n)) = fib (Suc n) + fib n"
  by pat_completeness auto
termination by (relation "measure id") auto

lemma fib_positive: "n > 0 \<Longrightarrow> fib n > 0"
  by (induction n rule: fib.induct) auto

(* 7. 复杂的Set操作 *)
lemma complex_set_ops:
  "(\<Union>x\<in>A. \<Union>y\<in>B. {x, y}) = {x. (\<exists>a\<in>A. \<exists>b\<in>B. x = a \<or> x = b)}"
  by auto

(* 8. 涉及Multiset的复杂推理 *)
lemma multiset_complex:
  fixes M N :: "'a multiset"
  shows "M + N = N + M"
  by (simp add: add.commute)

(* 9. 高阶逻辑与Transitive closure *)
lemma trans_closure_comp:
  assumes "trans r"
  shows "r O r \<subseteq> r"
  using assms by (auto simp: trans_def)

(* 10. 复杂的Induction with multiple variables *)
lemma complex_induction:
  shows "length (replicate n x @ replicate m x) = n + m"
  by simp

(* 11. 涉及quotient types *)
lemma list_set_eq:
  "set xs = set ys \<Longrightarrow> set (xs @ zs) = set (ys @ zs)"
  by auto

(* 12. 复杂的类型类约束组合 *)
lemma complex_typeclass:
  fixes x y :: "'a::{comm_monoid_add, linorder}"
  assumes "x \<le> y"
  shows "x + 0 \<le> y + 0"
  using assms by simp

(* 13. 涉及Option和Maybe的复杂模式 *)
lemma option_complex:
  "map_option f (case x of None \<Rightarrow> None | Some v \<Rightarrow> Some (g v)) =
   (case x of None \<Rightarrow> None | Some v \<Rightarrow> Some (f (g v)))"
  by (cases x) auto

(* 14. 深度嵌套的量词和逻辑 *)
lemma deep_logic:
  "(\<forall>x. (\<exists>y. P x y) \<longrightarrow> (\<forall>z. Q x z)) \<longleftrightarrow>
   (\<forall>x z. (\<exists>y. P x y) \<longrightarrow> Q x z)"
  by auto

(* 15. 涉及filter和partition的复杂操作 *)
lemma filter_partition:
  "filter P xs @ filter (\<lambda>x. \<not> P x) xs = 
   (let (ys, zs) = partition P xs in ys @ zs)"
  by (induction xs) auto

end

