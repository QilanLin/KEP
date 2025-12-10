theory Seed_Options
  imports Main
begin

(* Option type lemmas *)

lemma option_case_None: "(case None of None ⇒ x | Some y ⇒ f y) = x"
  by simp

lemma option_case_Some: "(case Some v of None ⇒ x | Some y ⇒ f y) = f v"
  by simp

lemma map_option_None: "map_option f None = None"
  by simp

lemma map_option_Some: "map_option f (Some x) = Some (f x)"
  sledgehammer; by simp

lemma bind_None: "Option.bind None f = None"
  by simp

lemma bind_Some: "Option.bind (Some x) f = f x"
  by simp

lemma option_map_comp: "map_option (f ∘ g) = map_option f ∘ map_option g"
  by (rule ext) (simp split: option.split)

lemma the_Some: "the (Some x) = x"
  by simp

lemma is_Some_None: "¬ is_Some None"
  by simp

lemma is_Some_Some: "is_Some (Some x)"
  by simp

end

