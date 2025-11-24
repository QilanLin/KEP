theory Test_ProverSelection
imports Main
begin

text \<open>Testing different prover selections\<close>

(* 可能需要特定prover的lemma *)
lemma needs_eprover: "(\<forall>x. P x \<or> Q x) = ((\<forall>x. P x) \<or> (\<exists>x. Q x))"
  by auto

(* 可能需要SMT solver *)
lemma needs_smt: "(a::int) + b = b + a"
  by auto

(* 需要arithmetic reasoning *)
lemma needs_arithmetic: "(x::nat) + y + z = x + (y + z)"
  by simp

end

