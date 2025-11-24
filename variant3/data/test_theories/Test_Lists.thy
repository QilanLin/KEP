theory Test_Lists
imports Main
begin

text \<open>List properties for testing\<close>

lemma list_append_nil: "xs @ [] = xs"
  by simp

lemma list_append_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by simp

lemma list_length_append: "length (xs @ ys) = length xs + length ys"
  by simp

lemma list_rev_rev: "rev (rev xs) = xs"
  by simp

text \<open>More complex list lemmas\<close>

lemma list_map_append: "map f (xs @ ys) = map f xs @ map f ys"
  by simp

lemma list_filter_append: "filter P (xs @ ys) = filter P xs @ filter P ys"
  by simp

end

