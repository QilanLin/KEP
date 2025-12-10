#!/usr/bin/env python3
"""
Metamorphic Testing (方案E)

目标: 利用数学性质检测Bug
方法: 比较等价/相关公式的Sledgehammer结果

Metamorphic Relations:
1. 双重否定不变性
2. 交换律
3. 结合律
4. De Morgan定律
5. 子公式性质
6. 分配律

如果等价的公式产生不一致的结果 → 可能发现Bug
"""

import subprocess
import tempfile
import re
import json
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from enum import Enum
import logging
import time

# 导入隐藏异常检测器
from hidden_exception_detector import HiddenExceptionDetector

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('metamorphic_tester')


class SledgehammerOutcome(Enum):
    """Sledgehammer结果类型"""
    SUCCESS = "success"      # 找到证明
    TIMEOUT = "timeout"      # 超时
    NONE = "none"           # 未找到证明
    UNKNOWN = "unknown"      # 未知/错误
    ERROR = "error"         # 明确的错误


@dataclass
class MetamorphicTestCase:
    """Metamorphic测试用例"""
    relation_name: str
    description: str
    formula1: str
    formula2: str
    expected_relation: str  # "equivalent", "implies", "independent"


@dataclass
class SledgehammerResult:
    """Sledgehammer测试结果"""
    formula: str
    outcome: SledgehammerOutcome
    proof_found: bool
    time_taken: float
    output: str
    error: str
    hidden_exception: str = ""  # 隐藏异常信息


@dataclass
class MetamorphicTestResult:
    """Metamorphic测试结果"""
    test_case: MetamorphicTestCase
    result1: SledgehammerResult
    result2: SledgehammerResult
    consistency_check: bool  # True if results are consistent
    violation_details: str


class MetamorphicTester:
    """Metamorphic Testing工具"""
    
    def __init__(self, output_dir: str = "results/metamorphic_testing"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.results: List[MetamorphicTestResult] = []
        
        # 初始化隐藏异常检测器
        self.hidden_detector = HiddenExceptionDetector()
        self.hidden_exceptions_found = 0
        
    def run_sledgehammer_on_formula(self, formula: str, 
                                    timeout: int = 30) -> SledgehammerResult:
        """在单个公式上运行Sledgehammer"""
        
        # 【重要】测试前清空隐藏异常日志
        self.hidden_detector.clear_logs()
        
        # 创建theory文件
        theory_content = f'''theory Metamorphic_Test
imports Main
begin

lemma test_formula: "{formula}"
  sledgehammer [timeout = {timeout}]

end
'''
        
        # 创建临时文件
        with tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False) as f:
            f.write(theory_content)
            temp_path = f.name
        
        hidden_exception = ""
        
        try:
            start_time = time.time()
            
            # 运行isabelle process
            result = subprocess.run(
                ['isabelle', 'process', '-T', temp_path],
                capture_output=True,
                text=True,
                timeout=timeout + 10  # 给Isabelle额外的时间
            )
            
            time_taken = time.time() - start_time
            
            # 【重要】检查隐藏异常
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                self.hidden_exceptions_found += hidden_result["exception_count"]
                hidden_exception = hidden_result["raw_content"][:500]
                logger.warning(f"🔴 发现隐藏异常: {hidden_result['exception_count']} 个")
            
            # 解析输出
            outcome = self._parse_outcome(result.stdout, result.stderr)
            proof_found = outcome == SledgehammerOutcome.SUCCESS
            
            return SledgehammerResult(
                formula=formula,
                outcome=outcome,
                proof_found=proof_found,
                time_taken=time_taken,
                output=result.stdout,
                error=result.stderr,
                hidden_exception=hidden_exception
            )
            
        except subprocess.TimeoutExpired:
            # 即使超时也检查隐藏异常
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                self.hidden_exceptions_found += hidden_result["exception_count"]
                hidden_exception = hidden_result["raw_content"][:500]
            
            return SledgehammerResult(
                formula=formula,
                outcome=SledgehammerOutcome.TIMEOUT,
                proof_found=False,
                time_taken=timeout + 10,
                output="",
                error="Process timeout",
                hidden_exception=hidden_exception
            )
        except Exception as e:
            return SledgehammerResult(
                formula=formula,
                outcome=SledgehammerOutcome.ERROR,
                proof_found=False,
                time_taken=0,
                output="",
                error=str(e),
                hidden_exception=""
            )
        finally:
            # 清理临时文件
            import os
            if os.path.exists(temp_path):
                os.unlink(temp_path)
    
    def _parse_outcome(self, stdout: str, stderr: str) -> SledgehammerOutcome:
        """解析Sledgehammer输出"""
        combined = stdout + stderr
        
        # 检查是否找到证明
        if re.search(r'Proof found|Try this|metis|smt|blast', combined, re.IGNORECASE):
            return SledgehammerOutcome.SUCCESS
        
        # 检查超时
        if re.search(r'Timeout|timed out', combined, re.IGNORECASE):
            return SledgehammerOutcome.TIMEOUT
        
        # 检查明确的错误
        if re.search(r'Error|Failed|Exception', combined, re.IGNORECASE):
            return SledgehammerOutcome.ERROR
        
        # 检查"未找到"
        if re.search(r'none|no proof', combined, re.IGNORECASE):
            return SledgehammerOutcome.NONE
        
        return SledgehammerOutcome.UNKNOWN
    
    def get_test_cases(self) -> List[MetamorphicTestCase]:
        """生成所有Metamorphic测试用例"""
        test_cases = []
        
        # ============================================
        # 1. 双重否定不变性
        # ============================================
        
        formulas_for_double_negation = [
            "True",
            "x = (x::nat)",
            "x + y = y + (x::nat)",
            "(a::nat) + (b + c) = (a + b) + c",
        ]
        
        for formula in formulas_for_double_negation:
            test_cases.append(MetamorphicTestCase(
                relation_name="double_negation",
                description="双重否定不变性",
                formula1=formula,
                formula2=f"~~({formula})",
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 2. 交换律
        # ============================================
        
        commutative_pairs = [
            ("x + y = y + (x::nat)", "y + x = x + (y::nat)"),
            ("x * y = y * (x::nat)", "y * x = x * (y::nat)"),
            ("(P \\<and> Q)", "(Q \\<and> P)"),
            ("(P \\<or> Q)", "(Q \\<or> P)"),
        ]
        
        for f1, f2 in commutative_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="commutativity",
                description="交换律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 3. 结合律
        # ============================================
        
        associative_pairs = [
            ("(x + y) + z = x + (y + (z::nat))", "x + (y + z) = (x + y) + (z::nat)"),
            ("(P \\<and> Q) \\<and> R", "P \\<and> (Q \\<and> R)"),
            ("(P \\<or> Q) \\<or> R", "P \\<or> (Q \\<or> R)"),
        ]
        
        for f1, f2 in associative_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="associativity",
                description="结合律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 4. De Morgan定律
        # ============================================
        
        de_morgan_pairs = [
            ("~(P \\<and> Q)", "(~P \\<or> ~Q)"),
            ("~(P \\<or> Q)", "(~P \\<and> ~Q)"),
        ]
        
        for f1, f2 in de_morgan_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="de_morgan",
                description="De Morgan定律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 5. 分配律
        # ============================================
        
        distributive_pairs = [
            ("x * (y + z) = x * y + x * (z::nat)", "(x * y) + (x * z) = x * (y + (z::nat))"),
            ("P \\<and> (Q \\<or> R)", "(P \\<and> Q) \\<or> (P \\<and> R)"),
        ]
        
        for f1, f2 in distributive_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="distributivity",
                description="分配律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 6. 子公式性质
        # ============================================
        
        # 如果 P ∧ Q 可证明，那么 P 应该也可证明
        subformula_pairs = [
            ("True \\<and> True", "True"),
            ("x + 0 = (x::nat) \\<and> 0 + x = (x::nat)", "x + 0 = (x::nat)"),
        ]
        
        for f1, f2 in subformula_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="subformula",
                description="子公式性质 (P∧Q → P应该更容易)",
                formula1=f1,
                formula2=f2,
                expected_relation="implies"
            ))
        
        # ============================================
        # 7. 恒等律 (Identity Laws) - 新增
        # ============================================
        
        identity_pairs = [
            ("P \\<and> True", "P"),
            ("P \\<or> False", "P"),
            ("x + 0 = (x::nat)", "0 + x = (x::nat)"),
            ("x * 1 = (x::nat)", "1 * x = (x::nat)"),
        ]
        
        for f1, f2 in identity_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="identity",
                description="恒等律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 8. 幂等律 (Idempotent Laws) - 新增
        # ============================================
        
        idempotent_pairs = [
            ("P \\<and> P", "P"),
            ("P \\<or> P", "P"),
        ]
        
        for f1, f2 in idempotent_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="idempotent",
                description="幂等律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 9. 吸收律 (Absorption Laws) - 新增
        # ============================================
        
        absorption_pairs = [
            ("P \\<and> (P \\<or> Q)", "P"),
            ("P \\<or> (P \\<and> Q)", "P"),
        ]
        
        for f1, f2 in absorption_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="absorption",
                description="吸收律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 10. 矛盾律和排中律 - 新增
        # ============================================
        
        logic_laws = [
            ("P \\<and> ~P", "False"),
            ("P \\<or> ~P", "True"),
            ("P \\<longrightarrow> P", "True"),
            ("False \\<longrightarrow> Q", "True"),
        ]
        
        for f1, f2 in logic_laws:
            test_cases.append(MetamorphicTestCase(
                relation_name="logic_law",
                description="逻辑基本定律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 11. 条件等价 (Implication equivalence) - 新增
        # ============================================
        
        implication_pairs = [
            ("P \\<longrightarrow> Q", "~P \\<or> Q"),
            ("~(P \\<longrightarrow> Q)", "P \\<and> ~Q"),
        ]
        
        for f1, f2 in implication_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="implication_equiv",
                description="条件等价",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 12. 双条件等价 (Biconditional) - 新增
        # ============================================
        
        biconditional_pairs = [
            ("P \\<longleftrightarrow> Q", "(P \\<longrightarrow> Q) \\<and> (Q \\<longrightarrow> P)"),
            ("P \\<longleftrightarrow> P", "True"),
        ]
        
        for f1, f2 in biconditional_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="biconditional",
                description="双条件等价",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 13. 零元素 (Annihilator) - 新增
        # ============================================
        
        annihilator_pairs = [
            ("P \\<and> False", "False"),
            ("P \\<or> True", "True"),
            ("x * 0 = (0::nat)", "0 * x = (0::nat)"),
        ]
        
        for f1, f2 in annihilator_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="annihilator",
                description="零元素律",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 14. 对合律 (Involution) - 新增
        # ============================================
        
        involution_pairs = [
            ("~~P", "P"),
            ("~~True", "True"),
            ("~~False", "False"),
        ]
        
        for f1, f2 in involution_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="involution",
                description="对合律 (双重否定)",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 15. 量词等价 (Quantifier equivalence) - 新增
        # ============================================
        
        quantifier_pairs = [
            ("\\<forall>x. P x \\<and> Q x", "\\<forall>x. P x \\<and> \\<forall>x. Q x"),
            ("\\<exists>x. P x \\<or> Q x", "\\<exists>x. P x \\<or> \\<exists>x. Q x"),
        ]
        
        for f1, f2 in quantifier_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="quantifier",
                description="量词等价",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        # ============================================
        # 16. 算术等价 - 新增
        # ============================================
        
        arithmetic_pairs = [
            ("x + x = 2 * (x::nat)", "2 * x = x + (x::nat)"),
            ("x - x = (0::nat)", "0 = x - (x::nat)"),
            ("x * (y + 1) = x * y + (x::nat)", "x * y + x = x * (y + (1::nat))"),
        ]
        
        for f1, f2 in arithmetic_pairs:
            test_cases.append(MetamorphicTestCase(
                relation_name="arithmetic",
                description="算术等价",
                formula1=f1,
                formula2=f2,
                expected_relation="equivalent"
            ))
        
        return test_cases
    
    def check_consistency(self, result1: SledgehammerResult,
                         result2: SledgehammerResult,
                         expected_relation: str) -> Tuple[bool, str]:
        """检查两个结果的一致性"""
        
        if expected_relation == "equivalent":
            # 等价公式应该有相同的证明结果
            if result1.proof_found == result2.proof_found:
                return True, "Results consistent (both proved or both failed)"
            else:
                violation = (
                    f"Inconsistency detected!\n"
                    f"  Formula 1: {result1.proof_found} in {result1.time_taken:.2f}s\n"
                    f"  Formula 2: {result2.proof_found} in {result2.time_taken:.2f}s\n"
                    f"  Expected: Both should have same result"
                )
                return False, violation
        
        elif expected_relation == "implies":
            # P∧Q → P, 如果P∧Q可证明，P也应该可证明
            if result1.proof_found and not result2.proof_found:
                violation = (
                    f"Subformula property violation!\n"
                    f"  Complex formula: proved in {result1.time_taken:.2f}s\n"
                    f"  Simpler formula: NOT proved\n"
                    f"  Expected: Simpler should also be provable"
                )
                return False, violation
            else:
                return True, "Subformula property holds"
        
        else:
            return True, "No specific expectation"
    
    def run_metamorphic_test(self, test_case: MetamorphicTestCase) -> MetamorphicTestResult:
        """运行单个metamorphic测试"""
        logger.info(f"Testing: {test_case.relation_name}")
        logger.info(f"  Description: {test_case.description}")
        logger.info(f"  Formula 1: {test_case.formula1}")
        logger.info(f"  Formula 2: {test_case.formula2}")
        
        # 测试两个公式
        result1 = self.run_sledgehammer_on_formula(test_case.formula1)
        result2 = self.run_sledgehammer_on_formula(test_case.formula2)
        
        # 检查一致性
        consistent, details = self.check_consistency(
            result1, result2, test_case.expected_relation
        )
        
        # 记录结果
        if not consistent:
            logger.warning(f"  ⚠️  VIOLATION DETECTED!")
            logger.warning(f"  {details}")
        else:
            logger.info(f"  ✅ Consistent ({details})")
        
        return MetamorphicTestResult(
            test_case=test_case,
            result1=result1,
            result2=result2,
            consistency_check=consistent,
            violation_details=details if not consistent else ""
        )
    
    def run_all_tests(self) -> List[MetamorphicTestResult]:
        """运行所有metamorphic测试"""
        logger.info("=" * 60)
        logger.info("🚀 Starting Metamorphic Testing Campaign")
        logger.info("=" * 60)
        
        test_cases = self.get_test_cases()
        logger.info(f"Total test cases: {len(test_cases)}")
        logger.info("")
        
        results = []
        for i, test_case in enumerate(test_cases, 1):
            logger.info(f"[{i}/{len(test_cases)}] {test_case.relation_name}")
            result = self.run_metamorphic_test(test_case)
            results.append(result)
            self.results.append(result)
            logger.info("")
        
        return results
    
    def generate_report(self) -> str:
        """生成测试报告"""
        lines = [
            "=" * 70,
            "📊 Metamorphic Testing 报告",
            "=" * 70,
            "",
            f"测试时间: {time.strftime('%Y-%m-%d %H:%M:%S')}",
            f"总测试数: {len(self.results)}",
            "",
        ]
        
        # 统计
        violations = [r for r in self.results if not r.consistency_check]
        consistent = [r for r in self.results if r.consistency_check]
        
        lines.extend([
            "【统计摘要】",
            f"  一致: {len(consistent)}",
            f"  不一致（可能的Bug）: {len(violations)}",
            "",
        ])
        
        # 按relation类型分组统计
        relations = {}
        for result in self.results:
            rel = result.test_case.relation_name
            if rel not in relations:
                relations[rel] = {'consistent': 0, 'violations': 0}
            if result.consistency_check:
                relations[rel]['consistent'] += 1
            else:
                relations[rel]['violations'] += 1
        
        lines.extend([
            "【按Relation类型统计】",
            "━" * 70,
        ])
        
        for rel_name, stats in sorted(relations.items()):
            total = stats['consistent'] + stats['violations']
            lines.append(
                f"  {rel_name}: {stats['consistent']}/{total} consistent, "
                f"{stats['violations']} violations"
            )
        
        lines.extend([
            "",
            "【详细结果】",
            "━" * 70,
        ])
        
        # 详细结果
        for i, result in enumerate(self.results, 1):
            status = "✅" if result.consistency_check else "⚠️ VIOLATION"
            lines.append(f"\n[{i}] {status} {result.test_case.relation_name}")
            lines.append(f"    {result.test_case.description}")
            lines.append(f"    Formula 1: {result.test_case.formula1}")
            lines.append(f"      → {result.result1.outcome.value}, "
                        f"proof: {result.result1.proof_found}, "
                        f"time: {result.result1.time_taken:.2f}s")
            lines.append(f"    Formula 2: {result.test_case.formula2}")
            lines.append(f"      → {result.result2.outcome.value}, "
                        f"proof: {result.result2.proof_found}, "
                        f"time: {result.result2.time_taken:.2f}s")
            if not result.consistency_check:
                lines.append(f"    ⚠️  {result.violation_details}")
        
        # 关键发现
        lines.extend([
            "",
            "=" * 70,
            "【关键发现】",
            "=" * 70,
        ])
        
        if violations:
            lines.append(f"\n🎯 发现 {len(violations)} 个不一致的情况:")
            lines.append("")
            for v in violations:
                lines.append(f"  - {v.test_case.relation_name}: {v.test_case.description}")
                lines.append(f"    公式1: {v.test_case.formula1}")
                lines.append(f"    公式2: {v.test_case.formula2}")
                lines.append(f"    不一致: {v.violation_details[:200]}")
                lines.append("")
            lines.extend([
                "这些不一致可能是:",
                "  1. Sledgehammer的真正Bug",
                "  2. 外部证明器的Bug",
                "  3. 超时导致的不确定性",
                "  4. 启发式搜索的非确定性",
            ])
        else:
            lines.append("\n✅ 所有测试用例都通过了一致性检查")
            lines.append("")
            lines.append("这意味着:")
            lines.append("  1. Sledgehammer对等价公式的处理是一致的")
            lines.append("  2. 数学性质被正确保持")
            lines.append("  3. 没有发现语义层面的Bug")
        
        lines.extend([
            "",
            "【Metamorphic Testing的价值】",
            "━" * 70,
            "",
            "✅ 不需要oracle（无需知道正确答案）",
            "✅ 利用数学性质检测Bug",
            "✅ 发现传统测试难以发现的语义Bug",
            "✅ 方法论创新（很少应用于theorem provers）",
            "",
            "【论文贡献】",
            "━" * 70,
            "",
            f"我们实施了Metamorphic Testing，设计了{len(self.results)}个",
            "基于数学性质的测试用例，包括:",
            "  - 双重否定不变性",
            "  - 交换律",
            "  - 结合律",
            "  - De Morgan定律",
            "  - 分配律",
            "  - 子公式性质",
            "",
        ])
        
        if violations:
            lines.append(f"发现了{len(violations)}个不一致的情况，需要进一步分析。")
        else:
            lines.append("所有测试通过，证明Sledgehammer正确保持了数学性质。")
        
        lines.extend([
            "",
            "=" * 70,
            "报告结束",
            "=" * 70,
        ])
        
        return "\n".join(lines)
    
    def save_results(self):
        """保存测试结果"""
        # 保存JSON数据
        json_path = self.output_dir / "metamorphic_results.json"
        results_data = []
        
        for r in self.results:
            results_data.append({
                'relation': r.test_case.relation_name,
                'description': r.test_case.description,
                'formula1': r.test_case.formula1,
                'formula2': r.test_case.formula2,
                'expected': r.test_case.expected_relation,
                'result1': {
                    'outcome': r.result1.outcome.value,
                    'proof_found': r.result1.proof_found,
                    'time': r.result1.time_taken,
                },
                'result2': {
                    'outcome': r.result2.outcome.value,
                    'proof_found': r.result2.proof_found,
                    'time': r.result2.time_taken,
                },
                'consistent': r.consistency_check,
                'violation': r.violation_details if not r.consistency_check else ""
            })
        
        with open(json_path, 'w') as f:
            json.dump(results_data, f, indent=2)
        logger.info(f"Results saved to: {json_path}")
        
        # 保存文本报告
        report = self.generate_report()
        report_path = self.output_dir / "metamorphic_report.txt"
        report_path.write_text(report)
        logger.info(f"Report saved to: {report_path}")
        
        return report


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Metamorphic Tester')
    parser.add_argument('--output-dir', default='results/metamorphic_testing',
                       help='输出目录')
    parser.add_argument('--timeout', type=int, default=30,
                       help='每个测试的超时时间（秒）')
    args = parser.parse_args()
    
    # 创建tester
    tester = MetamorphicTester(output_dir=args.output_dir)
    
    # 运行所有测试
    tester.run_all_tests()
    
    # 生成报告
    report = tester.save_results()
    
    # 打印报告
    print("\n" + report)


if __name__ == '__main__':
    main()

