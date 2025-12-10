theory Seed_Pairs
  imports Main
begin

(* Pair and product type lemmas *)

lemma fst_conv: "fst (x, y) = x"
  by simp

lemma snd_conv: "snd (x, (y + 0)) = y"
  by simp

lemma pair_collapse: "(fst p, snd p) = p"
  by simp

lemma swap_swap: "prod.swap (prod.swap p) = p"
  by (cases p) simp

lemma map_prod_simp: "map_prod f g (x, y) = (f x, g y)"
  by simp

lemma apfst_conv: "apfst f (x, y) = (f x, y)"
  by simp

lemma apsnd_conv: "apsnd f (x, y) = (x, f y)"
  by simp

lemma prod_case_simp: "(case (x, y) of (a, b) ⇒ f a b) = f x y"
  by simp

lemma map_prod_comp: "map_prod (f ∘ g) (h ∘ k) = map_prod f h ∘ map_prod g k"
  by (rule ext) (simp split: prod.split)

end

