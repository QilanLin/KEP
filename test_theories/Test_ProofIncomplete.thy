theory Test_ProofIncomplete
imports Main
begin

text \<open>Incomplete proof examples - 故意不完整的proof\<open>

lemma incomplete_proof: "x + y = y + (x::nat)"
proof -
  show ?thesis
  (* 缺少实际的proof步骤 *)
qed

end

