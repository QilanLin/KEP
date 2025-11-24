theory Test_Strings
imports Main
begin

text \<open>String properties (using lists of characters)\<close>

lemma string_append_nil: "s @ [] = s"
  by simp

lemma string_length: "length (s @ t) = length s + length t"
  by simp

lemma string_rev: "rev (rev s) = s"
  by simp

end

