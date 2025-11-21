theory Test_Sledgehammer
imports Main
begin

(* 设置Sledgehammer导出目录 *)
declare [[sledgehammer_atp_problem_dest_dir = "/Users/linqilan/Downloads/KEP AWS/sledgehammer_export"]]
declare [[sledgehammer_atp_proof_dest_dir = "/Users/linqilan/Downloads/KEP AWS/sledgehammer_export"]]

(* 测试Sledgehammer基本功能 - 使用ATP prover（导出TPTP）*)
lemma test1: "(x::nat) + 0 = x"
  by sledgehammer

(* 测试使用SMT prover（可能导出SMT-LIB）*)
lemma test2: "(\<forall>x::nat. P x \<longrightarrow> P x)"
  by sledgehammer

(* 测试SMT-specific的问题 - 使用Z3 *)
lemma test3: "(x::nat) + y = y + x"
  by sledgehammer

end

