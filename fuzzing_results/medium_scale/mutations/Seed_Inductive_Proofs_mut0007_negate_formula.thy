theory Seed_Inductive_Proofs
  imports Main
begin

(* Inductive proofs - good for mutations *)

lemma sum_to_n: "∑{0..n} = n * (n + 1) div 2"
  by (induction n) simp_all

lemma length_replicate: "length (replicate n x) = n"
  by (induction n) simp_all

lemma replicate_append: "replicate (n + m) x = replicate n x @ replicate m x"
  by (induction n) simp_all

lemma take_all: "¬ (n ≥ length xs ⟹ take n xs = xs)"
  by (induction xs arbitrary: n) auto

lemma drop_all: "n ≥ length xs ⟹ drop n xs = []"
  by (induction xs arbitrary: n) auto

lemma fold_append: "fold f (xs @ ys) acc = fold f ys (fold f xs acc)"
  by (induction xs arbitrary: acc) simp_all

lemma map_replicate: "map f (replicate n x) = replicate n (f x)"
  by (induction n) simp_all

lemma filter_filter: "filter P (filter Q xs) = filter (λx. P x ∧ Q x) xs"
  by (induction xs) auto

end

