theory Seed_Functions
  imports Main
begin

(* Function composition and higher-order functions *)

lemma comp_assoc: "True ⟹ (f ∘ g) ∘ h = f ∘ (g ∘ (h::'a ⇒ 'b))"
  by (rule ext) simp

lemma comp_id: "f ∘ id = f"
  by (rule ext) simp

lemma id_comp: "id ∘ f = f"
  by (rule ext) simp

lemma map_comp: "map (f ∘ g) xs = (map f ∘ map g) xs"
  by simp

lemma filter_comp: "filter (P ∘ f) xs = filter P (map f xs)"
  by (induction xs) auto

lemma fold_map: "fold f (map g xs) acc = fold (f ∘ g) xs acc"
  by (induction xs arbitrary: acc) simp_all

lemma const_comp: "(λx. c) ∘ f = (λx. c)"
  by (rule ext) simp

lemma fun_upd_apply: "(f(x := y)) x = y"
  by simp

lemma fun_upd_other: "x ≠ y ⟹ (f(x := z)) y = f y"
  by simp

end

