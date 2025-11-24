theory Test_Recursion
imports Main
begin

text \<open>Recursive function properties\<close>

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1" |
  "factorial (Suc n) = Suc n * factorial n"

lemma factorial_pos: "factorial n > 0"
  by (induct n, auto)

fun fibonacci :: "nat \<Rightarrow> nat" where
  "fibonacci 0 = 0" |
  "fibonacci (Suc 0) = 1" |
  "fibonacci (Suc (Suc n)) = fibonacci (Suc n) + fibonacci n"

lemma fib_mono: "fibonacci n \<le> fibonacci (Suc n)"
  by (induct n rule: fibonacci.induct, auto)

end

