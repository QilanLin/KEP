theory Simple_Valid_Tests
imports Main
begin

text \<open>简单有效的测试用例 - 用于Mirabelle Sledgehammer测试\<close>

(* 基本命题逻辑 *)
lemma simple_impl: "P \<longrightarrow> P"
  by auto

lemma simple_and: "P \<and> Q \<longrightarrow> Q \<and> P"
  by auto

lemma simple_or: "P \<or> Q \<longrightarrow> Q \<or> P"
  by auto

lemma modus_ponens: "\<lbrakk>P; P \<longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
  by auto

(* List基本性质 *)
lemma list_nil: "xs @ [] = xs"
  by simp

lemma list_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by simp

lemma list_length: "length (xs @ ys) = length xs + length ys"
  by simp

lemma list_rev_rev: "rev (rev xs) = xs"
  by simp

(* Arithmetic *)  
lemma add_comm: "(x::nat) + y = y + x"
  by simp

lemma add_assoc: "(x::nat) + (y + z) = (x + y) + z"
  by simp

lemma mult_comm: "(x::nat) * y = y * x"
  by simp

(* 稍微复杂一点的 *)
lemma list_filter_append: "filter P (xs @ ys) = filter P xs @ filter P ys"
  by simp

lemma list_map_append: "map f (xs @ ys) = map f xs @ map f ys"
  by simp

lemma list_length_map: "length (map f xs) = length xs"
  by simp

end

