theory Test_Datatypes
imports Main
begin

text \<open>Custom datatype properties\<close>

datatype tree = Leaf | Node tree nat tree

fun tree_size :: "tree \<Rightarrow> nat" where
  "tree_size Leaf = 0" |
  "tree_size (Node l x r) = 1 + tree_size l + tree_size r"

fun tree_height :: "tree \<Rightarrow> nat" where
  "tree_height Leaf = 0" |
  "tree_height (Node l x r) = 1 + max (tree_height l) (tree_height r)"

lemma tree_height_le_size: "tree_height t \<le> tree_size t"
  by (induct t, auto)

end

