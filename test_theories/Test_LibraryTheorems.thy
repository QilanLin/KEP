theory Test_LibraryTheorems
imports Main
begin

text \<open>Testing references to library theorems\<close>

(* 引用可能不存在的库定理 *)
lemma lib_ref_1: "xs @ [] = xs"
  by (rule append_Nil2)

(* 引用名称可能错误 *)
lemma lib_ref_2: "length [] = 0"
  by (rule length_nil)

(* 引用正确但在错误的context *)
lemma lib_ref_3: "x + 0 = (x::nat)"
  by (rule add_0)

end

