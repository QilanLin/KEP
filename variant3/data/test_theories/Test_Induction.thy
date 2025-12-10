theory Test_Induction
imports Main
begin

text \<open>Simple induction examples\<close>

lemma sum_first_n: "(\<Sum>i<n. i) = n * (n - 1) div 2"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by simp
qed

lemma list_length_map: "length (map f xs) = length xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

end

