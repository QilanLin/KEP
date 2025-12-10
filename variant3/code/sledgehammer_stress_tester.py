#!/usr/bin/env python3
"""
Sledgehammer Stress Tester - 专门针对 Sledgehammer 的压力测试

与 aggressive_reconstruction_tester.py 不同，这个测试器：
1. 创建有效的 lemmas，让 Sledgehammer 实际运行并找到 proof
2. 使用 Mirabelle 运行 Sledgehammer 并获取 proof 输出
3. 检测 reconstruction 过程中的问题

目标：找到 Sledgehammer 的 proof reconstruction bug，即：
- Prover 声称找到了 proof
- 但 Isabelle 无法重构该 proof

策略：
1. 复杂逻辑公式 - 可能导致 metis 重构失败
2. 高阶函数 - 可能导致编码/解码错误
3. 类型类约束 - 可能导致类型推导问题
4. 多 prover 差异 - 不同 prover 的 proof 格式可能有问题
5. 极端 fact 依赖 - 大量 facts 可能导致 reconstruction 超时

Usage:
    tester = SledgehammerStressTester()
    results = tester.run_stress_test()
"""

import subprocess
import tempfile
import time
import re
import logging
import json
from pathlib import Path
from typing import Optional, List, Dict, Tuple
from dataclasses import dataclass, asdict

logger = logging.getLogger(__name__)


@dataclass
class StressTestResult:
    """压力测试结果"""
    test_name: str
    category: str
    theory_content: str
    mirabelle_ran: bool
    sledgehammer_found_proof: bool
    proof_method: str
    reconstruction_success: bool
    reconstruction_error: str
    execution_time: float
    full_output: str


class SledgehammerStressTester:
    """
    Sledgehammer 压力测试器
    
    专门设计来触发 proof reconstruction 问题
    """
    
    def __init__(self, isabelle_path: str = "isabelle", timeout: int = 90):
        self.isabelle_path = isabelle_path
        self.timeout = timeout
        self.results: List[StressTestResult] = []
        
        logger.info("⚡ SledgehammerStressTester 初始化")
    
    def run_stress_test(self, output_dir: str = "stress_test_results") -> Dict:
        """
        运行完整的压力测试
        """
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        logger.info("=" * 70)
        logger.info("⚡ 开始 Sledgehammer 压力测试")
        logger.info("=" * 70)
        
        start_time = time.time()
        
        # 运行所有测试类别
        test_categories = [
            ("复杂逻辑公式", self._generate_complex_logic_tests()),
            ("高阶函数", self._generate_higher_order_tests()),
            ("类型类约束", self._generate_typeclass_tests()),
            ("多 prover 测试", self._generate_multi_prover_tests()),
            ("极端 fact 依赖", self._generate_fact_heavy_tests()),
            ("边界条件", self._generate_edge_case_tests()),
            ("递归与归纳", self._generate_induction_tests()),
        ]
        
        for category, tests in test_categories:
            logger.info(f"\n{'='*70}")
            logger.info(f"📁 类别: {category}")
            logger.info(f"{'='*70}")
            
            for test_name, theory_content in tests:
                self._run_stress_test(category, test_name, theory_content)
        
        total_time = time.time() - start_time
        
        # 生成报告
        report = self._generate_report(total_time)
        
        # 保存结果
        report_file = output_path / "stress_test_report.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        # 保存发现的 bug
        bugs = [r for r in self.results if r.sledgehammer_found_proof and not r.reconstruction_success]
        if bugs:
            bugs_file = output_path / "reconstruction_bugs.json"
            with open(bugs_file, 'w') as f:
                json.dump([asdict(b) for b in bugs], f, indent=2, default=str)
            logger.info(f"🐛 发现 {len(bugs)} 个 reconstruction bugs，已保存到 {bugs_file}")
        
        logger.info(f"\n✅ 报告已保存: {report_file}")
        
        return report
    
    def _generate_complex_logic_tests(self) -> List[Tuple[str, str]]:
        """生成复杂逻辑公式测试"""
        return [
            ("complex_nested_quantifiers", '''
theory Complex_Nested_Quantifiers imports Main begin
(* 嵌套量词 - 可能导致 metis 困难 *)
lemma nested_quant: 
  "\\<forall>x::nat. \\<exists>y. \\<forall>z. x + y > z \\<longrightarrow> x > 0 \\<or> y > 0"
  sorry
end
'''),
            ("complex_mixed_connectives", '''
theory Complex_Mixed_Connectives imports Main begin
(* 混合连接词 *)
lemma mixed: 
  "(A \\<and> B \\<longrightarrow> C) \\<longleftrightarrow> (\\<not>A \\<or> \\<not>B \\<or> C)"
  sorry
end
'''),
            ("complex_iff_chain", '''
theory Complex_Iff_Chain imports Main begin
(* 双向蕴含链 *)
lemma iff_chain:
  "(A \\<longleftrightarrow> B) \\<and> (B \\<longleftrightarrow> C) \\<and> (C \\<longleftrightarrow> D) \\<longrightarrow> (A \\<longleftrightarrow> D)"
  sorry
end
'''),
            ("complex_skolem", '''
theory Complex_Skolem imports Main begin
(* Skolem 函数相关 *)
lemma skolem_like:
  "(\\<forall>x::nat. \\<exists>y. P x y) \\<longrightarrow> (\\<exists>f. \\<forall>x. P x (f x))"
  sorry
end
'''),
        ]
    
    def _generate_higher_order_tests(self) -> List[Tuple[str, str]]:
        """生成高阶函数测试"""
        return [
            ("ho_lambda_nested", '''
theory HO_Lambda_Nested imports Main begin
(* 嵌套 lambda *)
lemma nested_lambda:
  "(\\<lambda>f. \\<lambda>x. f (f x)) Suc 0 = 2"
  sorry
end
'''),
            ("ho_function_composition", '''
theory HO_Function_Composition imports Main begin
(* 函数组合 *)
lemma func_comp:
  "(f \\<circ> g) x = f (g x)"
  sorry
end
'''),
            ("ho_higher_order_pred", '''
theory HO_Higher_Order_Pred imports Main begin
(* 高阶谓词 *)
lemma ho_pred:
  "(\\<forall>P. P x \\<longrightarrow> P y) \\<longrightarrow> x = y"
  sorry
end
'''),
            ("ho_map_filter", '''
theory HO_Map_Filter imports Main begin
(* map 和 filter 组合 *)
lemma map_filter:
  "map f (filter P xs) = filter (P \\<circ> inv f) (map f xs)"
  sorry
end
'''),
        ]
    
    def _generate_typeclass_tests(self) -> List[Tuple[str, str]]:
        """生成类型类约束测试"""
        return [
            ("tc_ord_constraint", '''
theory TC_Ord_Constraint imports Main begin
(* Ord 类型类 *)
lemma ord_trans:
  fixes a b c :: "'a::ord"
  assumes "a < b" "b < c"
  shows "a < c"
  using assms sorry
end
'''),
            ("tc_monoid", '''
theory TC_Monoid imports Main begin
(* Monoid 操作 *)
lemma monoid_assoc:
  fixes a b c :: "'a::monoid_add"
  shows "(a + b) + c = a + (b + c)"
  sorry
end
'''),
            ("tc_ring", '''
theory TC_Ring imports Main begin
(* Ring 分配律 *)
lemma ring_distrib:
  fixes a b c :: "'a::ring"
  shows "a * (b + c) = a * b + a * c"
  sorry
end
'''),
            ("tc_lattice", '''
theory TC_Lattice imports Main begin
(* Lattice 操作 *)
lemma lattice_absorb:
  fixes a b :: "'a::lattice"
  shows "a \\<squnion> (a \\<sqinter> b) = a"
  sorry
end
'''),
        ]
    
    def _generate_multi_prover_tests(self) -> List[Tuple[str, str]]:
        """生成多 prover 测试"""
        return [
            ("mp_e_prover_focus", '''
theory MP_E_Prover_Focus imports Main begin
(* E prover 擅长的 FOL *)
lemma e_friendly:
  "\\<forall>x y z::nat. (x < y \\<and> y < z) \\<longrightarrow> x < z"
  sorry
end
'''),
            ("mp_z3_focus", '''
theory MP_Z3_Focus imports Main begin
(* Z3 擅长的算术 *)
lemma z3_friendly:
  fixes x y :: int
  assumes "x > 0" "y > 0"
  shows "x + y > 0 \\<and> x * y > 0"
  using assms sorry
end
'''),
            ("mp_cvc5_focus", '''
theory MP_CVC5_Focus imports Main begin
(* cvc5 擅长的量词 *)
lemma cvc5_friendly:
  "\\<forall>xs::nat list. length xs \\<ge> 0"
  sorry
end
'''),
            ("mp_spass_focus", '''
theory MP_SPASS_Focus imports Main begin
(* SPASS 擅长的纯逻辑 *)
lemma spass_friendly:
  "((A \\<longrightarrow> B) \\<longrightarrow> A) \\<longrightarrow> A"
  sorry
end
'''),
        ]
    
    def _generate_fact_heavy_tests(self) -> List[Tuple[str, str]]:
        """生成依赖大量 facts 的测试"""
        return [
            ("fact_many_assms", '''
theory Fact_Many_Assms imports Main begin
(* 大量假设 *)
lemma many_assms:
  assumes "a1 > 0" "a2 > 0" "a3 > 0" "a4 > 0" "a5 > 0"
          "a6 > 0" "a7 > 0" "a8 > 0" "a9 > 0" "a10 > 0"
  shows "(a1::nat) + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 > 0"
  using assms sorry
end
'''),
            ("fact_chain_reasoning", '''
theory Fact_Chain_Reasoning imports Main begin
(* 链式推理 *)
lemma chain:
  assumes "A \\<longrightarrow> B" "B \\<longrightarrow> C" "C \\<longrightarrow> D" "D \\<longrightarrow> E" "E \\<longrightarrow> F"
  shows "A \\<longrightarrow> F"
  using assms sorry
end
'''),
            ("fact_set_theory", '''
theory Fact_Set_Theory imports Main begin
(* 集合论证明 *)
lemma set_reasoning:
  assumes "A \\<subseteq> B" "B \\<subseteq> C" "x \\<in> A"
  shows "x \\<in> C"
  using assms sorry
end
'''),
        ]
    
    def _generate_edge_case_tests(self) -> List[Tuple[str, str]]:
        """生成边界情况测试"""
        return [
            ("edge_empty_structures", '''
theory Edge_Empty_Structures imports Main begin
(* 空结构 *)
lemma empty_list_props:
  "length [] = 0 \\<and> rev [] = [] \\<and> [] @ xs = xs"
  sorry
end
'''),
            ("edge_singleton", '''
theory Edge_Singleton imports Main begin
(* 单元素 *)
lemma singleton_props:
  "length [x] = 1 \\<and> hd [x] = x \\<and> tl [x] = []"
  sorry
end
'''),
            ("edge_nat_boundary", '''
theory Edge_Nat_Boundary imports Main begin
(* 自然数边界 *)
lemma nat_zero:
  "(0::nat) + x = x \\<and> 0 * x = 0 \\<and> x - 0 = x"
  sorry
end
'''),
            ("edge_bool_identity", '''
theory Edge_Bool_Identity imports Main begin
(* 布尔恒等 *)
lemma bool_id:
  "True \\<and> P \\<longleftrightarrow> P" "False \\<or> P \\<longleftrightarrow> P" "\\<not>\\<not>P \\<longleftrightarrow> P"
  sorry
end
'''),
        ]
    
    def _generate_induction_tests(self) -> List[Tuple[str, str]]:
        """生成递归和归纳测试"""
        return [
            ("ind_nat_induction", '''
theory Ind_Nat_Induction imports Main begin
(* 自然数归纳 *)
lemma nat_ind_example:
  fixes n :: nat
  shows "n + 0 = n"
  sorry
end
'''),
            ("ind_list_induction", '''
theory Ind_List_Induction imports Main begin
(* 列表归纳 *)
lemma list_ind_example:
  "length (xs @ ys) = length xs + length ys"
  sorry
end
'''),
            ("ind_strong_induction", '''
theory Ind_Strong_Induction imports Main begin
(* 强归纳 *)
lemma strong_ind:
  fixes n :: nat
  assumes "\\<forall>m. (\\<forall>k < m. P k) \\<longrightarrow> P m"
  shows "P n"
  using assms sorry
end
'''),
        ]
    
    def _run_stress_test(self, category: str, test_name: str, theory_content: str):
        """
        运行单个压力测试
        
        使用 Mirabelle 来真正运行 Sledgehammer
        """
        logger.info(f"  📝 测试: {test_name}")
        
        start_time = time.time()
        
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            
            # 提取 theory 名称
            match = re.search(r'theory\s+(\w+)', theory_content)
            theory_name = match.group(1) if match else "Test"
            
            # 创建 theory 文件
            theory_file = temp_path / f"{theory_name}.thy"
            theory_file.write_text(theory_content)
            
            # 创建 ROOT 文件
            root_content = f'''session Stress_Test = "HOL" +
  options [timeout = {self.timeout}, quick_and_dirty = true]
  theories
    {theory_name}
'''
            root_file = temp_path / "ROOT"
            root_file.write_text(root_content)
            
            # 创建 Mirabelle 输出目录
            mirabelle_output = temp_path / "mirabelle_output"
            mirabelle_output.mkdir()
            
            try:
                # 运行 Mirabelle with Sledgehammer
                result = subprocess.run(
                    [self.isabelle_path, 'mirabelle',
                     '-A', 'sledgehammer',
                     '-T', str(min(30, self.timeout)),
                     '-O', str(mirabelle_output),
                     '-d', str(temp_path),
                     'Stress_Test'],
                    capture_output=True,
                    text=True,
                    timeout=self.timeout + 60
                )
                
                execution_time = time.time() - start_time
                output = result.stdout + "\n" + result.stderr
                
                # 读取 Mirabelle 日志
                mirabelle_log = mirabelle_output / "mirabelle.log"
                mirabelle_content = ""
                if mirabelle_log.exists():
                    mirabelle_content = mirabelle_log.read_text()
                
                # 分析结果
                mirabelle_ran = "Mirabelle" in output or mirabelle_log.exists()
                found_proof, proof_method = self._extract_proof_info(output + mirabelle_content)
                recon_success, recon_error = self._check_reconstruction(output + mirabelle_content)
                
                if found_proof:
                    if recon_success:
                        logger.info(f"    ✅ Sledgehammer 找到并重构了 proof: {proof_method}")
                    else:
                        logger.warning(f"    🐛 Sledgehammer 找到 proof 但重构失败!")
                        logger.warning(f"        错误: {recon_error[:100]}")
                else:
                    logger.info(f"    ⚪ Sledgehammer 未找到 proof ({execution_time:.1f}s)")
                
                test_result = StressTestResult(
                    test_name=test_name,
                    category=category,
                    theory_content=theory_content,
                    mirabelle_ran=mirabelle_ran,
                    sledgehammer_found_proof=found_proof,
                    proof_method=proof_method,
                    reconstruction_success=recon_success,
                    reconstruction_error=recon_error,
                    execution_time=execution_time,
                    full_output=(output + mirabelle_content)[:5000]
                )
                
            except subprocess.TimeoutExpired:
                execution_time = time.time() - start_time
                logger.warning(f"    ⏱️ 超时 ({self.timeout}s)")
                
                test_result = StressTestResult(
                    test_name=test_name,
                    category=category,
                    theory_content=theory_content,
                    mirabelle_ran=False,
                    sledgehammer_found_proof=False,
                    proof_method="",
                    reconstruction_success=False,
                    reconstruction_error="TIMEOUT",
                    execution_time=execution_time,
                    full_output=""
                )
                
            except Exception as e:
                execution_time = time.time() - start_time
                logger.error(f"    ❌ 异常: {e}")
                
                test_result = StressTestResult(
                    test_name=test_name,
                    category=category,
                    theory_content=theory_content,
                    mirabelle_ran=False,
                    sledgehammer_found_proof=False,
                    proof_method="",
                    reconstruction_success=False,
                    reconstruction_error=str(e),
                    execution_time=execution_time,
                    full_output=""
                )
            
            self.results.append(test_result)
    
    def _extract_proof_info(self, output: str) -> Tuple[bool, str]:
        """从输出中提取 proof 信息"""
        # 检查 Sledgehammer 是否找到了 proof
        proof_patterns = [
            r"Try this:\s*by\s+(\w+)",
            r"Proof found.*?by\s+(\w+)",
            r"sledgehammer\s+found\s+.*?by\s+(\w+)",
            r"\((\w+),\s*[\d.]+s?\)\s*Try this:",
        ]
        
        for pattern in proof_patterns:
            match = re.search(pattern, output, re.IGNORECASE)
            if match:
                method = match.group(1) if match.lastindex else "unknown"
                return True, method
        
        # 检查是否有任何成功的 prover 响应
        if "sledgehammer" in output.lower() and ("proof" in output.lower() or "try this" in output.lower()):
            return True, "unknown"
        
        return False, ""
    
    def _check_reconstruction(self, output: str) -> Tuple[bool, str]:
        """检查 reconstruction 是否成功"""
        output_lower = output.lower()
        
        # 检查 reconstruction 失败模式
        failure_patterns = [
            "failed to reconstruct",
            "reconstruction failed",
            "metis failed",
            "smt method failed",
            "proof method failed",
            "replay failed",
        ]
        
        for pattern in failure_patterns:
            if pattern in output_lower:
                # 提取错误详情
                for line in output.split('\n'):
                    if pattern in line.lower():
                        return False, line.strip()
                return False, pattern
        
        # 如果没有失败模式，假设成功
        return True, ""
    
    def _generate_report(self, total_time: float) -> Dict:
        """生成测试报告"""
        total_tests = len(self.results)
        proofs_found = sum(1 for r in self.results if r.sledgehammer_found_proof)
        recon_success = sum(1 for r in self.results if r.sledgehammer_found_proof and r.reconstruction_success)
        recon_failures = sum(1 for r in self.results if r.sledgehammer_found_proof and not r.reconstruction_success)
        timeouts = sum(1 for r in self.results if r.reconstruction_error == "TIMEOUT")
        
        # 按类别分组
        by_category = {}
        for r in self.results:
            if r.category not in by_category:
                by_category[r.category] = {"total": 0, "proofs": 0, "recon_success": 0, "recon_fail": 0}
            by_category[r.category]["total"] += 1
            if r.sledgehammer_found_proof:
                by_category[r.category]["proofs"] += 1
                if r.reconstruction_success:
                    by_category[r.category]["recon_success"] += 1
                else:
                    by_category[r.category]["recon_fail"] += 1
        
        report = {
            "summary": {
                "total_tests": total_tests,
                "proofs_found": proofs_found,
                "reconstruction_success": recon_success,
                "reconstruction_failures": recon_failures,
                "timeouts": timeouts,
                "total_time": total_time
            },
            "by_category": by_category,
            "all_results": [asdict(r) for r in self.results]
        }
        
        # 打印摘要
        print("\n")
        print("╔════════════════════════════════════════════════════════════════╗")
        print("║       Sledgehammer Stress Test Results                        ║")
        print("╠════════════════════════════════════════════════════════════════╣")
        print(f"║  Total tests:              {total_tests:4d}                            ║")
        print(f"║  Sledgehammer found proof: {proofs_found:4d}                            ║")
        print(f"║  Reconstruction success:   {recon_success:4d}                            ║")
        print(f"║  🐛 Reconstruction fail:    {recon_failures:4d}                            ║")
        print(f"║  Timeouts:                 {timeouts:4d}                            ║")
        print(f"║  Total time:               {total_time/60:.1f} min                         ║")
        print("╠════════════════════════════════════════════════════════════════╣")
        print("║  Results by Category:                                         ║")
        
        for cat, stats in by_category.items():
            recon_info = f"{stats['recon_fail']} fail" if stats['recon_fail'] > 0 else "OK"
            print(f"║    {cat[:25]:25s} {stats['proofs']:2d}/{stats['total']:2d} proofs, {recon_info:8s} ║")
        
        print("╚════════════════════════════════════════════════════════════════╝")
        
        if recon_failures > 0:
            print("\n🐛 Reconstruction Failures:")
            for r in self.results:
                if r.sledgehammer_found_proof and not r.reconstruction_success:
                    print(f"  - [{r.category}] {r.test_name}: {r.reconstruction_error[:50]}")
        
        return report


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Sledgehammer Stress Tester"
    )
    parser.add_argument(
        "--output", "-o",
        default="stress_test_results",
        help="Output directory"
    )
    parser.add_argument(
        "--timeout", "-t",
        type=int,
        default=90,
        help="Timeout per test (seconds)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Verbose output"
    )
    
    args = parser.parse_args()
    
    # 配置日志
    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    # 运行测试
    tester = SledgehammerStressTester(timeout=args.timeout)
    report = tester.run_stress_test(output_dir=args.output)
    
    # 返回码
    import sys
    recon_failures = report["summary"]["reconstruction_failures"]
    sys.exit(0 if recon_failures == 0 else 1)


if __name__ == "__main__":
    main()

