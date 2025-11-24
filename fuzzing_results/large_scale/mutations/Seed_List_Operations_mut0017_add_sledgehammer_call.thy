theory Seed_List_Operations
  imports Main
begin

(* List operation lemmas - good for mutations *)

lemma append_nil: "xs @ [] = xs"
  by simp

lemma append_assoc: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by simp

lemma length_append: "length (xs @ ys) = length xs + length ys"
  by simp

lemma rev_rev: "rev (rev xs) = xs"
  sledgehammer; by simp

lemma rev_append: "rev (xs @ ys) = rev ys @ rev xs"
  by simp

lemma map_append: "map f (xs @ ys) = map f xs @ map f ys"
  by simp

lemma map_compose: "map (f ∘ g) xs = map f (map g xs)"
  by simp

lemma filter_append: "filter P (xs @ ys) = filter P xs @ filter P ys"
  by simp

lemma length_map: "length (map f xs) = length xs"
  by simp

lemma take_append: "take n (xs @ ys) = (if n ≤ length xs then take n xs else xs @ take (n - length xs) ys)"
  by simp

end

