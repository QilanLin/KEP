#!/usr/bin/env python3
"""
Aggressive Proof Reconstruction Tester - 激进的 Proof Reconstruction Bug 检测

目标：使用更激进的策略触发 Sledgehammer 的 proof reconstruction 边界情况。

激进策略：
1. 类型破坏 (Type Breaking)
   - 修改类型注释使其不一致
   - 混合不同类型的表达式
   - 使用边界类型值

2. 编码攻击 (Encoding Attacks)
   - 注入 TPTP 特殊字符
   - 破坏 SMT-LIB 格式
   - 测试 Unicode 边界情况

3. 极端值测试 (Extreme Values)
   - 超大数值
   - 深度嵌套表达式
   - 超长标识符

4. 配置模糊 (Configuration Fuzzing)
   - 非标准 prover 配置
   - 极端超时值
   - 不兼容的编码策略

5. Proof 破坏 (Proof Corruption)
   - 修改 proof 中的 fact 引用
   - 破坏 metis 参数
   - 注入无效的 proof step

Usage:
    tester = AggressiveReconstructionTester()
    results = tester.run_aggressive_campaign()
"""

import subprocess
import tempfile
import time
import re
import random
import string
import logging
import json
from pathlib import Path
from typing import Optional, List, Dict, Tuple
from dataclasses import dataclass, asdict
from enum import Enum

logger = logging.getLogger(__name__)


class AggressiveStrategy(Enum):
    """激进策略类型"""
    TYPE_BREAKING = "type_breaking"
    ENCODING_ATTACK = "encoding_attack"
    EXTREME_VALUES = "extreme_values"
    CONFIG_FUZZING = "config_fuzzing"
    PROOF_CORRUPTION = "proof_corruption"
    UNICODE_INJECTION = "unicode_injection"
    BOUNDARY_TESTING = "boundary_testing"


@dataclass
class AggressiveTestResult:
    """激进测试结果"""
    strategy: AggressiveStrategy
    test_name: str
    theory_content: str
    success: bool
    bug_found: bool
    error_type: str
    error_message: str
    execution_time: float
    sledgehammer_output: str


class AggressiveReconstructionTester:
    """
    激进的 Proof Reconstruction 测试器
    
    使用各种边界情况和破坏性测试来触发 reconstruction bugs。
    """
    
    def __init__(self, isabelle_path: str = "isabelle", timeout: int = 60):
        self.isabelle_path = isabelle_path
        self.timeout = timeout
        self.results: List[AggressiveTestResult] = []
        
        logger.info("🔥 AggressiveReconstructionTester 初始化")
    
    def run_aggressive_campaign(self, output_dir: str = "aggressive_results") -> Dict:
        """
        运行完整的激进测试 campaign
        """
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        logger.info("=" * 70)
        logger.info("🔥 开始激进 Proof Reconstruction 测试 Campaign")
        logger.info("=" * 70)
        
        start_time = time.time()
        
        # 运行所有策略
        strategies = [
            (self._test_type_breaking, AggressiveStrategy.TYPE_BREAKING),
            (self._test_encoding_attacks, AggressiveStrategy.ENCODING_ATTACK),
            (self._test_extreme_values, AggressiveStrategy.EXTREME_VALUES),
            (self._test_unicode_injection, AggressiveStrategy.UNICODE_INJECTION),
            (self._test_boundary_cases, AggressiveStrategy.BOUNDARY_TESTING),
            (self._test_proof_corruption, AggressiveStrategy.PROOF_CORRUPTION),
            (self._test_config_fuzzing, AggressiveStrategy.CONFIG_FUZZING),
        ]
        
        for test_func, strategy in strategies:
            logger.info(f"\n{'='*70}")
            logger.info(f"🎯 策略: {strategy.value}")
            logger.info(f"{'='*70}")
            
            try:
                test_func()
            except Exception as e:
                logger.error(f"❌ 策略执行失败: {e}")
        
        total_time = time.time() - start_time
        
        # 生成报告
        report = self._generate_report(total_time)
        
        # 保存结果
        report_file = output_path / "aggressive_test_report.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2, default=str)
        
        logger.info(f"\n✅ 报告已保存: {report_file}")
        
        return report
    
    def _test_type_breaking(self):
        """
        类型破坏测试 - 创建类型不一致的表达式
        """
        test_cases = [
            # 1. nat 和 int 混合
            ("type_mix_nat_int", '''
theory Type_Mix_Nat_Int imports Main begin
lemma type_confusion: "(x::nat) + (y::int) = z"
  sorry
end
'''),
            # 2. bool 当作 nat 使用
            ("type_bool_as_nat", '''
theory Type_Bool_As_Nat imports Main begin
lemma bool_arithmetic: "(True::nat) + 1 = 2"
  sorry
end
'''),
            # 3. 函数类型不匹配
            ("type_func_mismatch", '''
theory Type_Func_Mismatch imports Main begin
lemma func_type_error: "(\\<lambda>x::nat. x + 1) True = 2"
  sorry
end
'''),
            # 4. 多态类型滥用
            ("type_poly_abuse", '''
theory Type_Poly_Abuse imports Main begin
lemma poly_abuse: "(undefined::'a) + (1::nat) = 1"
  sorry
end
'''),
            # 5. 类型类约束违反
            ("type_class_violation", '''
theory Type_Class_Violation imports Main begin
lemma class_violation: "sort_key (\\<lambda>x. x) [True, False] = [False, True]"
  sorry
end
'''),
            # 6. 空类型
            ("type_void", '''
theory Type_Void imports Main begin
typedef void = "{x::nat. False}"
  by auto
lemma void_lemma: "\\<exists>x::void. True"
  sorry
end
'''),
            # 7. 递归类型问题
            ("type_recursive", '''
theory Type_Recursive imports Main begin
datatype 'a tree = Leaf 'a | Node "'a tree" "'a tree"
lemma tree_confusion: "Leaf (1::nat) = Node (Leaf True) (Leaf False)"
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.TYPE_BREAKING, name, content)
    
    def _test_encoding_attacks(self):
        """
        编码攻击测试 - 注入可能破坏 TPTP/SMT-LIB 编码的内容
        """
        test_cases = [
            # 1. TPTP 特殊字符
            ("encoding_tptp_special", '''
theory Encoding_TPTP_Special imports Main begin
definition "special_name$with%chars" :: "nat" where
  "special_name$with%chars = 0"
lemma tptp_test: "special_name$with%chars = 0"
  sorry
end
'''),
            # 2. SMT-LIB 保留字
            ("encoding_smtlib_reserved", '''
theory Encoding_SMTLIB_Reserved imports Main begin
definition "assert" :: "nat \\<Rightarrow> nat" where
  "assert x = x"
definition "check-sat" :: "nat" where
  "check-sat = 0"
lemma smtlib_test: "assert check-sat = 0"
  sorry
end
'''),
            # 3. 反斜杠和引号
            ("encoding_escape_chars", '''
theory Encoding_Escape_Chars imports Main begin
definition backslash :: "char" where
  "backslash = CHR 0x5C"
lemma escape_test: "backslash = CHR 92"
  sorry
end
'''),
            # 4. 空字符串和空列表边界
            ("encoding_empty", '''
theory Encoding_Empty imports Main begin
lemma empty_string: "''''''  = ([]::string)"
  sorry
lemma empty_list: "([]::nat list) @ [] = []"
  sorry
end
'''),
            # 5. 嵌套引号
            ("encoding_nested_quotes", '''
theory Encoding_Nested_Quotes imports Main begin
definition "quoted''name" :: "nat" where
  "quoted''name = 0"
lemma quote_test: "quoted''name = 0"
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.ENCODING_ATTACK, name, content)
    
    def _test_extreme_values(self):
        """
        极端值测试 - 使用可能导致溢出或性能问题的值
        """
        test_cases = [
            # 1. 超大数值
            ("extreme_huge_number", '''
theory Extreme_Huge_Number imports Main begin
lemma huge_nat: "(999999999999999999999999999999::nat) > 0"
  sorry
lemma huge_arith: "(10^100::nat) + 1 > 10^100"
  sorry
end
'''),
            # 2. 深度嵌套
            ("extreme_deep_nesting", '''
theory Extreme_Deep_Nesting imports Main begin
lemma deep_and: "A \\<and> (B \\<and> (C \\<and> (D \\<and> (E \\<and> (F \\<and> (G \\<and> (H \\<and> (I \\<and> (J \\<and> (K \\<and> (L \\<and> (M \\<and> (N \\<and> (O \\<and> P))))))))))))))"
  sorry
lemma deep_impl: "A \\<longrightarrow> (B \\<longrightarrow> (C \\<longrightarrow> (D \\<longrightarrow> (E \\<longrightarrow> (F \\<longrightarrow> (G \\<longrightarrow> (H \\<longrightarrow> (I \\<longrightarrow> (J \\<longrightarrow> True)))))))))"
  sorry
end
'''),
            # 3. 超长标识符
            ("extreme_long_name", f'''
theory Extreme_Long_Name imports Main begin
definition {"a" * 500} :: "nat" where
  "{"a" * 500} = 0"
lemma long_name_test: "{"a" * 500} = 0"
  sorry
end
'''),
            # 4. 大量变量
            ("extreme_many_vars", '''
theory Extreme_Many_Vars imports Main begin
lemma many_vars: "\\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20::nat.
  x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 + x20 >= 0"
  sorry
end
'''),
            # 5. 复杂嵌套函数
            ("extreme_nested_func", '''
theory Extreme_Nested_Func imports Main begin
lemma nested_func: "(\\<lambda>f. f (f (f (f (f (f (f (f (f (f 0)))))))))) Suc = 10"
  sorry
end
'''),
            # 6. 零和负边界
            ("extreme_zero_boundary", '''
theory Extreme_Zero_Boundary imports Main begin
lemma zero_div: "(0::nat) div 0 = 0"
  sorry
lemma zero_mod: "(0::nat) mod 0 = 0"
  sorry
lemma sub_underflow: "(0::nat) - 1 = 0"
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.EXTREME_VALUES, name, content)
    
    def _test_unicode_injection(self):
        """
        Unicode 注入测试 - 使用各种 Unicode 字符
        """
        test_cases = [
            # 1. 数学符号
            ("unicode_math_symbols", '''
theory Unicode_Math_Symbols imports Main begin
lemma forall_unicode: "\\<forall>x::nat. x \\<ge> 0"
  sorry
lemma exists_unicode: "\\<exists>x::nat. x = 0"
  sorry
lemma impl_unicode: "A \\<longrightarrow> A"
  sorry
end
'''),
            # 2. 希腊字母（常见但可能有问题）
            ("unicode_greek", '''
theory Unicode_Greek imports Main begin
definition "\\<alpha>" :: "nat" where "\\<alpha> = 0"
definition "\\<beta>" :: "nat" where "\\<beta> = 1"
definition "\\<gamma>" :: "nat" where "\\<gamma> = 2"
lemma greek_test: "\\<alpha> + \\<beta> + \\<gamma> = 3"
  sorry
end
'''),
            # 3. 下标和上标
            ("unicode_subscript", '''
theory Unicode_Subscript imports Main begin
definition "x\\<^sub>1" :: "nat" where "x\\<^sub>1 = 1"
definition "x\\<^sub>2" :: "nat" where "x\\<^sub>2 = 2"
lemma subscript_test: "x\\<^sub>1 + x\\<^sub>2 = 3"
  sorry
end
'''),
            # 4. 特殊 Unicode 运算符
            ("unicode_operators", '''
theory Unicode_Operators imports Main begin
lemma union_op: "A \\<union> B = B \\<union> A"
  sorry
lemma inter_op: "A \\<inter> B = B \\<inter> A"
  sorry
lemma subset_op: "A \\<subseteq> A \\<union> B"
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.UNICODE_INJECTION, name, content)
    
    def _test_boundary_cases(self):
        """
        边界情况测试 - 测试各种边界条件
        """
        test_cases = [
            # 1. 空集合操作
            ("boundary_empty_set", '''
theory Boundary_Empty_Set imports Main begin
lemma empty_union: "{} \\<union> A = A"
  sorry
lemma empty_inter: "{} \\<inter> A = {}"
  sorry
lemma empty_subset: "{} \\<subseteq> A"
  sorry
lemma empty_card: "card {} = 0"
  sorry
end
'''),
            # 2. 单元素情况
            ("boundary_singleton", '''
theory Boundary_Singleton imports Main begin
lemma singleton_card: "card {x} = 1"
  sorry
lemma singleton_member: "x \\<in> {x}"
  sorry
lemma singleton_insert: "insert x {} = {x}"
  sorry
end
'''),
            # 3. 递归基础情况
            ("boundary_recursion_base", '''
theory Boundary_Recursion_Base imports Main begin
lemma fac_0: "fact 0 = 1"
  sorry
lemma fib_0: "fib 0 = 0"
  sorry
lemma fib_1: "fib 1 = 1"
  sorry
end
'''),
            # 4. 列表边界
            ("boundary_list", '''
theory Boundary_List imports Main begin
lemma hd_singleton: "hd [x] = x"
  sorry
lemma tl_singleton: "tl [x] = []"
  sorry
lemma last_singleton: "last [x] = x"
  sorry
lemma butlast_singleton: "butlast [x] = []"
  sorry
lemma nth_zero: "[x, y, z] ! 0 = x"
  sorry
end
'''),
            # 5. 布尔边界
            ("boundary_bool", '''
theory Boundary_Bool imports Main begin
lemma true_and: "True \\<and> P = P"
  sorry
lemma false_and: "False \\<and> P = False"
  sorry
lemma true_or: "True \\<or> P = True"
  sorry
lemma false_or: "False \\<or> P = P"
  sorry
lemma not_not: "\\<not> \\<not> P = P"
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.BOUNDARY_TESTING, name, content)
    
    def _test_proof_corruption(self):
        """
        Proof 破坏测试 - 尝试使用无效或错误的 proof methods
        """
        test_cases = [
            # 1. 错误的 metis 参数
            ("proof_wrong_metis", '''
theory Proof_Wrong_Metis imports Main begin
lemma simple: "A \\<and> B \\<longrightarrow> B"
  by (metis nonexistent_fact_12345)
end
'''),
            # 2. 错误的 simp 规则
            ("proof_wrong_simp", '''
theory Proof_Wrong_Simp imports Main begin
lemma simple: "A \\<or> B \\<longrightarrow> B \\<or> A"
  by (simp add: totally_fake_rule)
end
'''),
            # 3. 循环 simp 规则
            ("proof_circular_simp", '''
theory Proof_Circular_Simp imports Main begin
lemma circular: "x = x + 0"
  by (simp add: add_0_right)
end
'''),
            # 4. 不完整的 induct
            ("proof_incomplete_induct", '''
theory Proof_Incomplete_Induct imports Main begin
fun mysum :: "nat list \\<Rightarrow> nat" where
  "mysum [] = 0" |
  "mysum (x#xs) = x + mysum xs"
lemma sum_append: "mysum (xs @ ys) = mysum xs + mysum ys"
  by (induct xs) auto
end
'''),
            # 5. blast 无法解决
            ("proof_blast_fail", '''
theory Proof_Blast_Fail imports Main begin
lemma need_arith: "(x::nat) + y = y + x"
  by blast
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.PROOF_CORRUPTION, name, content)
    
    def _test_config_fuzzing(self):
        """
        配置模糊测试 - 使用非标准 Sledgehammer 配置
        """
        # 创建带有各种 Sledgehammer 配置的 theories
        test_cases = [
            # 1. 超短超时
            ("config_short_timeout", '''
theory Config_Short_Timeout imports Main begin
lemma needs_time: "\\<forall>x::nat. \\<exists>y::nat. x + y = y + x"
  sledgehammer [timeout = 1]
  sorry
end
'''),
            # 2. 限制 prover
            ("config_single_prover", '''
theory Config_Single_Prover imports Main begin
lemma single_prover: "A \\<and> B \\<longrightarrow> B \\<and> A"
  sledgehammer [provers = e]
  sorry
end
'''),
            # 3. 不同的类型编码
            ("config_type_enc", '''
theory Config_Type_Enc imports Main begin
lemma type_enc_test: "(x::nat) + y = y + x"
  sledgehammer [type_enc = mono_native]
  sorry
end
'''),
            # 4. 禁用 smt_proofs
            ("config_no_smt", '''
theory Config_No_Smt imports Main begin
lemma no_smt_test: "A \\<or> \\<not>A"
  sledgehammer [smt_proofs = false]
  sorry
end
'''),
            # 5. 极端 fact 限制
            ("config_max_facts", '''
theory Config_Max_Facts imports Main begin
lemma max_facts_test: "card {1::nat, 2, 3} = 3"
  sledgehammer [max_facts = 1]
  sorry
end
'''),
        ]
        
        for name, content in test_cases:
            self._run_test(AggressiveStrategy.CONFIG_FUZZING, name, content)
    
    def _run_test(self, strategy: AggressiveStrategy, test_name: str, theory_content: str):
        """
        运行单个测试
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
            root_content = f'''session Aggressive_Test = "HOL" +
  options [timeout = {self.timeout}, quick_and_dirty = true]
  theories
    {theory_name}
'''
            root_file = temp_path / "ROOT"
            root_file.write_text(root_content)
            
            try:
                # 运行 isabelle build
                result = subprocess.run(
                    [self.isabelle_path, 'build', '-d', str(temp_path),
                     '-v', 'Aggressive_Test'],
                    capture_output=True,
                    text=True,
                    timeout=self.timeout + 30
                )
                
                execution_time = time.time() - start_time
                output = result.stdout + "\n" + result.stderr
                
                # 分析结果
                success = result.returncode == 0
                bug_found, error_type, error_msg = self._analyze_output(output, success)
                
                if bug_found:
                    logger.warning(f"    🐛 发现问题: {error_type}")
                elif success:
                    logger.info(f"    ✅ 测试通过 ({execution_time:.2f}s)")
                else:
                    logger.info(f"    ❌ 预期失败: {error_type[:50]}...")
                
                test_result = AggressiveTestResult(
                    strategy=strategy,
                    test_name=test_name,
                    theory_content=theory_content,
                    success=success,
                    bug_found=bug_found,
                    error_type=error_type,
                    error_message=error_msg,
                    execution_time=execution_time,
                    sledgehammer_output=output[:2000]
                )
                
            except subprocess.TimeoutExpired:
                execution_time = time.time() - start_time
                logger.warning(f"    ⏱️ 超时 ({self.timeout}s)")
                
                test_result = AggressiveTestResult(
                    strategy=strategy,
                    test_name=test_name,
                    theory_content=theory_content,
                    success=False,
                    bug_found=True,  # 超时可能是 bug
                    error_type="TIMEOUT",
                    error_message=f"Test timed out after {self.timeout}s",
                    execution_time=execution_time,
                    sledgehammer_output=""
                )
                
            except Exception as e:
                execution_time = time.time() - start_time
                logger.error(f"    ❌ 异常: {e}")
                
                test_result = AggressiveTestResult(
                    strategy=strategy,
                    test_name=test_name,
                    theory_content=theory_content,
                    success=False,
                    bug_found=True,
                    error_type="EXCEPTION",
                    error_message=str(e),
                    execution_time=execution_time,
                    sledgehammer_output=""
                )
            
            self.results.append(test_result)
    
    def _analyze_output(self, output: str, success: bool) -> Tuple[bool, str, str]:
        """
        分析 Isabelle 输出，检测潜在的 bug
        """
        output_lower = output.lower()
        
        # 潜在的 bug 模式
        bug_patterns = [
            ("CRASH", ["exception", "internal error", "stack overflow", "segmentation fault"]),
            ("RECONSTRUCTION_FAILURE", ["failed to reconstruct", "reconstruction failed"]),
            ("TYPE_ERROR", ["type error", "type mismatch", "incompatible types"]),
            ("ENCODING_ERROR", ["encoding failed", "tptp error", "smt-lib error"]),
            ("PROVER_CRASH", ["prover crashed", "external prover error"]),
            ("MEMORY_ERROR", ["out of memory", "heap exhausted"]),
            ("TIMEOUT_BUG", ["timeout during proof", "preplay timeout"]),
        ]
        
        for error_type, patterns in bug_patterns:
            for pattern in patterns:
                if pattern in output_lower:
                    # 提取错误消息
                    error_lines = [l for l in output.split('\n') if pattern in l.lower()]
                    error_msg = error_lines[0] if error_lines else "Unknown error"
                    return True, error_type, error_msg
        
        # 如果测试失败但没有已知的 bug 模式
        if not success:
            # 提取失败原因
            fail_match = re.search(r'\*\*\*\s*(.+)', output)
            if fail_match:
                return False, "EXPECTED_FAILURE", fail_match.group(1)
            return False, "UNKNOWN_FAILURE", "Test failed without clear error"
        
        return False, "SUCCESS", ""
    
    def _generate_report(self, total_time: float) -> Dict:
        """
        生成测试报告
        """
        # 统计
        total_tests = len(self.results)
        bugs_found = sum(1 for r in self.results if r.bug_found)
        successes = sum(1 for r in self.results if r.success)
        timeouts = sum(1 for r in self.results if r.error_type == "TIMEOUT")
        
        # 按策略分组
        by_strategy = {}
        for r in self.results:
            strategy = r.strategy.value
            if strategy not in by_strategy:
                by_strategy[strategy] = {"total": 0, "bugs": 0, "success": 0}
            by_strategy[strategy]["total"] += 1
            if r.bug_found:
                by_strategy[strategy]["bugs"] += 1
            if r.success:
                by_strategy[strategy]["success"] += 1
        
        # 收集 bug 详情
        bug_details = [
            {
                "test_name": r.test_name,
                "strategy": r.strategy.value,
                "error_type": r.error_type,
                "error_message": r.error_message[:200]
            }
            for r in self.results if r.bug_found
        ]
        
        report = {
            "summary": {
                "total_tests": total_tests,
                "bugs_found": bugs_found,
                "successes": successes,
                "failures": total_tests - successes,
                "timeouts": timeouts,
                "total_time": total_time,
                "bug_rate": bugs_found / total_tests if total_tests > 0 else 0
            },
            "by_strategy": by_strategy,
            "bug_details": bug_details,
            "all_results": [asdict(r) for r in self.results]
        }
        
        # 打印摘要
        print("\n")
        print("╔════════════════════════════════════════════════════════════════╗")
        print("║       Aggressive Reconstruction Test Results                  ║")
        print("╠════════════════════════════════════════════════════════════════╣")
        print(f"║  Total tests:        {total_tests:4d}                                  ║")
        print(f"║  Tests passed:       {successes:4d}                                  ║")
        print(f"║  Tests failed:       {total_tests - successes:4d}                                  ║")
        print(f"║  🐛 Bugs found:       {bugs_found:4d}                                  ║")
        print(f"║  ⏱️  Timeouts:         {timeouts:4d}                                  ║")
        print(f"║  Total time:         {total_time/60:.1f} min                              ║")
        print("╠════════════════════════════════════════════════════════════════╣")
        print("║  Results by Strategy:                                         ║")
        
        for strategy, stats in by_strategy.items():
            print(f"║    {strategy:25s} {stats['bugs']:2d} bugs / {stats['total']:2d} tests   ║")
        
        print("╚════════════════════════════════════════════════════════════════╝")
        
        if bug_details:
            print("\n🐛 发现的问题:")
            for bug in bug_details[:10]:
                print(f"  - [{bug['strategy']}] {bug['test_name']}: {bug['error_type']}")
        
        return report


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Aggressive Proof Reconstruction Tester"
    )
    parser.add_argument(
        "--output", "-o",
        default="aggressive_results",
        help="Output directory"
    )
    parser.add_argument(
        "--timeout", "-t",
        type=int,
        default=60,
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
    tester = AggressiveReconstructionTester(timeout=args.timeout)
    report = tester.run_aggressive_campaign(output_dir=args.output)
    
    # 返回码
    import sys
    sys.exit(0 if report["summary"]["bugs_found"] == 0 else 1)


if __name__ == "__main__":
    main()

