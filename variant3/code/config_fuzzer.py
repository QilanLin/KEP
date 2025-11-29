#!/usr/bin/env python3
"""
配置级 Fuzzer (方案B)

目标: 测试 Sledgehammer 的配置健壮性
方法: 使用各种无效/边界配置调用 Sledgehammer

测试内容:
1. 无效的证明器名称
2. 边界超时值
3. 无效的选项组合
4. 缺失的配置
"""

import subprocess
import tempfile
import os
import json
import time
import logging
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Any, Optional
from datetime import datetime

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('config_fuzzer')


@dataclass
class ConfigTestCase:
    """配置测试用例"""
    name: str
    description: str
    sledgehammer_options: str
    expected_behavior: str  # "error", "timeout", "success", "unknown"
    

@dataclass
class ConfigTestResult:
    """配置测试结果"""
    test_case: ConfigTestCase
    success: bool
    output: str
    error: str
    duration: float
    triggered_exception: bool
    exception_log: str


class ConfigFuzzer:
    """配置级 Fuzzer"""
    
    def __init__(self, output_dir: str = "results/config_fuzzing"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.results: List[ConfigTestResult] = []
        self.exception_log_path = Path("/tmp/sledgehammer_hidden_errors.log")
        
        # 创建测试用的简单theory文件
        self.test_theory = self._create_test_theory()
        
    def _create_test_theory(self) -> Path:
        """创建用于测试的简单theory文件"""
        theory_content = '''theory Config_Test
imports Main
begin

(* 简单的测试引理 - 应该很容易证明 *)
lemma test_lemma: "True"
  by simp

(* 稍微复杂一点的引理 *)
lemma add_comm_test: "(a::nat) + b = b + a"
  by simp

(* 需要 Sledgehammer 的引理 *)
lemma needs_sledgehammer: "\\<forall>x::nat. x + 0 = x"
  sledgehammer

end
'''
        theory_path = self.output_dir / "Config_Test.thy"
        theory_path.write_text(theory_content)
        return theory_path
    
    def get_test_cases(self) -> List[ConfigTestCase]:
        """生成所有配置测试用例"""
        test_cases = []
        
        # ============================================
        # 1. 证明器配置测试
        # ============================================
        
        # 1.1 不存在的证明器
        test_cases.append(ConfigTestCase(
            name="nonexistent_prover",
            description="使用不存在的证明器名称",
            sledgehammer_options="provers = nonexistent_prover_xyz",
            expected_behavior="error"
        ))
        
        # 1.2 空证明器列表
        test_cases.append(ConfigTestCase(
            name="empty_provers",
            description="空的证明器列表",
            sledgehammer_options="provers = \"\"",
            expected_behavior="error"
        ))
        
        # 1.3 多个不存在的证明器
        test_cases.append(ConfigTestCase(
            name="multiple_nonexistent_provers",
            description="多个不存在的证明器",
            sledgehammer_options="provers = fake1 fake2 fake3",
            expected_behavior="error"
        ))
        
        # 1.4 混合有效和无效的证明器
        test_cases.append(ConfigTestCase(
            name="mixed_provers",
            description="混合有效和无效的证明器",
            sledgehammer_options="provers = e nonexistent_prover",
            expected_behavior="unknown"
        ))
        
        # 1.5 特殊字符的证明器名称
        test_cases.append(ConfigTestCase(
            name="special_char_prover",
            description="包含特殊字符的证明器名称",
            sledgehammer_options="provers = \"prover@#$%\"",
            expected_behavior="error"
        ))
        
        # ============================================
        # 2. 超时配置测试
        # ============================================
        
        # 2.1 零超时
        test_cases.append(ConfigTestCase(
            name="zero_timeout",
            description="超时设置为0",
            sledgehammer_options="timeout = 0",
            expected_behavior="timeout"
        ))
        
        # 2.2 极短超时
        test_cases.append(ConfigTestCase(
            name="very_short_timeout",
            description="极短的超时 (0.001秒)",
            sledgehammer_options="timeout = 0.001",
            expected_behavior="timeout"
        ))
        
        # 2.3 负数超时
        test_cases.append(ConfigTestCase(
            name="negative_timeout",
            description="负数超时",
            sledgehammer_options="timeout = -1",
            expected_behavior="error"
        ))
        
        # 2.4 极大超时
        test_cases.append(ConfigTestCase(
            name="huge_timeout",
            description="极大的超时值",
            sledgehammer_options="timeout = 999999",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 3. max_facts 配置测试
        # ============================================
        
        # 3.1 零 facts
        test_cases.append(ConfigTestCase(
            name="zero_facts",
            description="max_facts = 0",
            sledgehammer_options="max_facts = 0",
            expected_behavior="unknown"
        ))
        
        # 3.2 负数 facts
        test_cases.append(ConfigTestCase(
            name="negative_facts",
            description="max_facts = -1",
            sledgehammer_options="max_facts = -1",
            expected_behavior="error"
        ))
        
        # 3.3 极大 facts
        test_cases.append(ConfigTestCase(
            name="huge_facts",
            description="max_facts = 1000000",
            sledgehammer_options="max_facts = 1000000",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 4. 组合配置测试
        # ============================================
        
        # 4.1 多个无效选项组合
        test_cases.append(ConfigTestCase(
            name="multiple_invalid_options",
            description="多个无效选项组合",
            sledgehammer_options="timeout = 0, max_facts = -1",
            expected_behavior="error"
        ))
        
        # 4.2 矛盾的选项
        test_cases.append(ConfigTestCase(
            name="contradictory_options",
            description="矛盾的选项设置",
            sledgehammer_options="provers = e, dont_preplay, preplay_timeout = 10",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 5. 无效选项名称测试
        # ============================================
        
        # 5.1 不存在的选项名称
        test_cases.append(ConfigTestCase(
            name="nonexistent_option",
            description="不存在的选项名称",
            sledgehammer_options="nonexistent_option = 123",
            expected_behavior="error"
        ))
        
        # 5.2 拼写错误的选项
        test_cases.append(ConfigTestCase(
            name="typo_option",
            description="选项名称拼写错误",
            sledgehammer_options="timout = 30",  # typo: timout
            expected_behavior="error"
        ))
        
        # ============================================
        # 6. 边界值测试
        # ============================================
        
        # 6.1 最小有效配置
        test_cases.append(ConfigTestCase(
            name="minimal_config",
            description="最小有效配置",
            sledgehammer_options="provers = e, timeout = 1",
            expected_behavior="unknown"
        ))
        
        # 6.2 只有超时
        test_cases.append(ConfigTestCase(
            name="timeout_only",
            description="只设置超时",
            sledgehammer_options="timeout = 5",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 7. Pairwise配置组合测试 (新增)
        # ============================================
        
        # 7.1 短超时 + 少facts
        test_cases.append(ConfigTestCase(
            name="short_timeout_few_facts",
            description="短超时配合少facts",
            sledgehammer_options="timeout = 1, max_facts = 5",
            expected_behavior="unknown"
        ))
        
        # 7.2 长超时 + 多facts
        test_cases.append(ConfigTestCase(
            name="long_timeout_many_facts",
            description="长超时配合多facts",
            sledgehammer_options="timeout = 60, max_facts = 500",
            expected_behavior="unknown"
        ))
        
        # 7.3 单个prover + 短超时
        test_cases.append(ConfigTestCase(
            name="single_prover_short_timeout",
            description="单个prover配合短超时",
            sledgehammer_options="provers = e, timeout = 2",
            expected_behavior="unknown"
        ))
        
        # 7.4 多prover + 零超时
        test_cases.append(ConfigTestCase(
            name="multi_prover_zero_timeout",
            description="多prover配合零超时",
            sledgehammer_options="provers = e cvc5, timeout = 0",
            expected_behavior="timeout"
        ))
        
        # 7.5 禁用preplay + 长超时
        test_cases.append(ConfigTestCase(
            name="no_preplay_long_timeout",
            description="禁用preplay配合长超时",
            sledgehammer_options="dont_preplay, timeout = 30",
            expected_behavior="unknown"
        ))
        
        # 7.6 SMT provers + 边界facts
        test_cases.append(ConfigTestCase(
            name="smt_provers_boundary_facts",
            description="SMT provers配合边界facts",
            sledgehammer_options="provers = cvc5 z3, max_facts = 1",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 8. 三参数组合测试 (新增)
        # ============================================
        
        # 8.1 prover + timeout + facts 组合1
        test_cases.append(ConfigTestCase(
            name="triple_combo_1",
            description="e + 短超时 + 少facts",
            sledgehammer_options="provers = e, timeout = 3, max_facts = 10",
            expected_behavior="unknown"
        ))
        
        # 8.2 prover + timeout + facts 组合2
        test_cases.append(ConfigTestCase(
            name="triple_combo_2",
            description="cvc5 + 中超时 + 中facts",
            sledgehammer_options="provers = cvc5, timeout = 10, max_facts = 50",
            expected_behavior="unknown"
        ))
        
        # 8.3 多prover + 超时 + facts
        test_cases.append(ConfigTestCase(
            name="triple_combo_3",
            description="多prover + 长超时 + 多facts",
            sledgehammer_options="provers = e cvc5 z3, timeout = 20, max_facts = 100",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 9. 极端组合测试 (新增)
        # ============================================
        
        # 9.1 所有边界值组合
        test_cases.append(ConfigTestCase(
            name="all_boundary_values",
            description="所有参数使用边界值",
            sledgehammer_options="timeout = 1, max_facts = 1, slices = 1",
            expected_behavior="unknown"
        ))
        
        # 9.2 最小slices + 单prover
        test_cases.append(ConfigTestCase(
            name="min_slices_single_prover",
            description="最小slices配合单prover",
            sledgehammer_options="provers = e, slices = 1",
            expected_behavior="unknown"
        ))
        
        # 9.3 最大slices + 短超时
        test_cases.append(ConfigTestCase(
            name="max_slices_short_timeout",
            description="最大slices配合短超时",
            sledgehammer_options="slices = 100, timeout = 2",
            expected_behavior="unknown"
        ))
        
        # 9.4 verbose模式组合
        test_cases.append(ConfigTestCase(
            name="verbose_with_options",
            description="verbose模式配合其他选项",
            sledgehammer_options="verbose, timeout = 10, max_facts = 20",
            expected_behavior="unknown"
        ))
        
        # 9.5 debug模式组合
        test_cases.append(ConfigTestCase(
            name="debug_with_options",
            description="debug模式配合其他选项",
            sledgehammer_options="debug, provers = e, timeout = 5",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 10. Boolean选项组合测试 (新增)
        # ============================================
        
        # 10.1 try0禁用
        test_cases.append(ConfigTestCase(
            name="no_try0",
            description="禁用try0",
            sledgehammer_options="dont_try0, timeout = 10",
            expected_behavior="unknown"
        ))
        
        # 10.2 learn禁用
        test_cases.append(ConfigTestCase(
            name="no_learn",
            description="禁用learn",
            sledgehammer_options="dont_learn, timeout = 10",
            expected_behavior="unknown"
        ))
        
        # 10.3 多个boolean选项组合
        test_cases.append(ConfigTestCase(
            name="multiple_boolean_options",
            description="多个boolean选项组合",
            sledgehammer_options="dont_preplay, dont_try0, verbose",
            expected_behavior="unknown"
        ))
        
        # ============================================
        # 11. 证明方法组合测试 (新增)
        # ============================================
        
        # 11.1 指定证明方法
        test_cases.append(ConfigTestCase(
            name="specific_proof_method",
            description="指定simp证明方法",
            sledgehammer_options="provers = e, timeout = 10",
            expected_behavior="unknown"
        ))
        
        # 11.2 ATP only模式
        test_cases.append(ConfigTestCase(
            name="atp_only_mode",
            description="仅使用ATP证明器",
            sledgehammer_options="provers = e spass vampire, timeout = 15",
            expected_behavior="unknown"
        ))
        
        # 11.3 SMT only模式
        test_cases.append(ConfigTestCase(
            name="smt_only_mode",
            description="仅使用SMT证明器",
            sledgehammer_options="provers = cvc5 z3 verit, timeout = 15",
            expected_behavior="unknown"
        ))
        
        return test_cases
    
    def run_sledgehammer_with_config(self, theory_content: str, options: str, 
                                      timeout: int = 60) -> Dict[str, Any]:
        """使用指定配置运行 Sledgehammer"""
        
        # 创建临时theory文件
        with tempfile.NamedTemporaryFile(mode='w', suffix='.thy', delete=False) as f:
            # 修改theory内容，添加配置
            modified_content = theory_content.replace(
                "sledgehammer",
                f"sledgehammer [{options}]"
            )
            f.write(modified_content)
            temp_path = f.name
        
        try:
            # 运行 isabelle build
            start_time = time.time()
            
            result = subprocess.run(
                ['isabelle', 'process', '-T', temp_path],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            duration = time.time() - start_time
            
            return {
                'success': result.returncode == 0,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'returncode': result.returncode,
                'duration': duration,
                'timeout': False
            }
            
        except subprocess.TimeoutExpired:
            return {
                'success': False,
                'stdout': '',
                'stderr': 'Process timed out',
                'returncode': -1,
                'duration': timeout,
                'timeout': True
            }
        except Exception as e:
            return {
                'success': False,
                'stdout': '',
                'stderr': str(e),
                'returncode': -1,
                'duration': 0,
                'timeout': False
            }
        finally:
            # 清理临时文件
            if os.path.exists(temp_path):
                os.unlink(temp_path)
    
    def check_exception_log(self) -> str:
        """检查异常日志文件"""
        if self.exception_log_path.exists():
            content = self.exception_log_path.read_text()
            return content
        return ""
    
    def clear_exception_log(self):
        """清空异常日志"""
        if self.exception_log_path.exists():
            self.exception_log_path.unlink()
    
    def run_test_case(self, test_case: ConfigTestCase) -> ConfigTestResult:
        """运行单个测试用例"""
        logger.info(f"Running test: {test_case.name}")
        logger.info(f"  Description: {test_case.description}")
        logger.info(f"  Options: {test_case.sledgehammer_options}")
        
        # 清空之前的异常日志
        initial_log = self.check_exception_log()
        
        # 读取测试theory内容
        theory_content = self.test_theory.read_text()
        
        # 运行测试
        start_time = time.time()
        result = self.run_sledgehammer_with_config(
            theory_content, 
            test_case.sledgehammer_options,
            timeout=30  # 每个测试最多30秒
        )
        duration = time.time() - start_time
        
        # 检查异常日志
        final_log = self.check_exception_log()
        new_exceptions = final_log[len(initial_log):] if len(final_log) > len(initial_log) else ""
        triggered_exception = len(new_exceptions) > 0
        
        # 创建结果
        test_result = ConfigTestResult(
            test_case=test_case,
            success=result['success'],
            output=result['stdout'],
            error=result['stderr'],
            duration=duration,
            triggered_exception=triggered_exception,
            exception_log=new_exceptions
        )
        
        # 记录结果
        if triggered_exception:
            logger.warning(f"  ⚠️  EXCEPTION TRIGGERED!")
            logger.warning(f"  Exception log: {new_exceptions[:200]}...")
        elif result['success']:
            logger.info(f"  ✅ Completed successfully ({duration:.2f}s)")
        else:
            logger.info(f"  ❌ Failed ({duration:.2f}s)")
            if result['stderr']:
                logger.info(f"  Error: {result['stderr'][:200]}...")
        
        return test_result
    
    def run_all_tests(self) -> List[ConfigTestResult]:
        """运行所有测试用例"""
        logger.info("=" * 60)
        logger.info("🚀 Starting Config Fuzzing Campaign")
        logger.info("=" * 60)
        
        test_cases = self.get_test_cases()
        logger.info(f"Total test cases: {len(test_cases)}")
        
        # 清空异常日志
        self.clear_exception_log()
        
        results = []
        for i, test_case in enumerate(test_cases, 1):
            logger.info(f"\n[{i}/{len(test_cases)}] {test_case.name}")
            result = self.run_test_case(test_case)
            results.append(result)
            self.results.append(result)
        
        return results
    
    def generate_report(self) -> str:
        """生成测试报告"""
        report_lines = [
            "=" * 70,
            "📊 配置级 Fuzzing 测试报告",
            "=" * 70,
            "",
            f"测试时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
            f"总测试数: {len(self.results)}",
            "",
        ]
        
        # 统计
        success_count = sum(1 for r in self.results if r.success)
        error_count = sum(1 for r in self.results if not r.success)
        exception_count = sum(1 for r in self.results if r.triggered_exception)
        
        report_lines.extend([
            "【统计摘要】",
            f"  成功: {success_count}",
            f"  失败: {error_count}",
            f"  触发异常: {exception_count}",
            "",
            "【详细结果】",
            "-" * 70,
        ])
        
        # 详细结果
        for result in self.results:
            status = "✅" if result.success else "❌"
            exception_flag = " ⚠️EXCEPTION" if result.triggered_exception else ""
            report_lines.append(
                f"{status} {result.test_case.name}{exception_flag}"
            )
            report_lines.append(f"   描述: {result.test_case.description}")
            report_lines.append(f"   选项: {result.test_case.sledgehammer_options}")
            report_lines.append(f"   耗时: {result.duration:.2f}s")
            if result.triggered_exception:
                report_lines.append(f"   异常: {result.exception_log[:100]}...")
            if result.error and not result.success:
                report_lines.append(f"   错误: {result.error[:100]}...")
            report_lines.append("")
        
        # 关键发现
        report_lines.extend([
            "=" * 70,
            "【关键发现】",
            "=" * 70,
        ])
        
        exceptions = [r for r in self.results if r.triggered_exception]
        if exceptions:
            report_lines.append(f"\n🎯 发现 {len(exceptions)} 个触发异常的配置:")
            for r in exceptions:
                report_lines.append(f"  - {r.test_case.name}: {r.test_case.sledgehammer_options}")
                report_lines.append(f"    异常内容: {r.exception_log[:200]}")
        else:
            report_lines.append("\n📝 没有配置触发异常")
            report_lines.append("   这可能意味着:")
            report_lines.append("   1. Sledgehammer 对配置错误有良好的错误处理")
            report_lines.append("   2. 或者需要更激进的配置测试")
        
        report_lines.extend([
            "",
            "=" * 70,
            "报告结束",
            "=" * 70,
        ])
        
        return "\n".join(report_lines)
    
    def save_results(self):
        """保存测试结果"""
        # 保存 JSON 结果
        json_path = self.output_dir / "config_fuzzing_results.json"
        results_data = []
        for r in self.results:
            results_data.append({
                'name': r.test_case.name,
                'description': r.test_case.description,
                'options': r.test_case.sledgehammer_options,
                'expected': r.test_case.expected_behavior,
                'success': r.success,
                'duration': r.duration,
                'triggered_exception': r.triggered_exception,
                'exception_log': r.exception_log,
                'error': r.error[:500] if r.error else ""
            })
        
        with open(json_path, 'w') as f:
            json.dump(results_data, f, indent=2)
        logger.info(f"Results saved to: {json_path}")
        
        # 保存文本报告
        report = self.generate_report()
        report_path = self.output_dir / "config_fuzzing_report.txt"
        report_path.write_text(report)
        logger.info(f"Report saved to: {report_path}")
        
        return report


def main():
    """主函数"""
    import argparse
    from datetime import datetime
    
    parser = argparse.ArgumentParser(description='配置级 Fuzzer')
    parser.add_argument('--output-dir', default='results/config_fuzzing',
                        help='输出目录')
    parser.add_argument('--timeout', type=int, default=30,
                        help='每个测试的超时时间（秒）')
    parser.add_argument('--limit', type=int, default=None,
                        help='限制运行的测试数量（默认全部）')
    parser.add_argument('--category', type=str, default=None,
                        choices=['prover', 'timeout', 'fact', 'option', 'method', 'combined'],
                        help='只运行指定类别的测试')
    parser.add_argument('--timestamp', action='store_true',
                        help='在输出目录名中添加时间戳')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='详细输出')
    args = parser.parse_args()
    
    # 处理时间戳
    output_dir = args.output_dir
    if args.timestamp:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = f"{args.output_dir}_{timestamp}"
    
    # 设置日志级别
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    # 创建 fuzzer
    fuzzer = ConfigFuzzer(output_dir=output_dir)
    
    # 获取测试用例
    test_cases = fuzzer.get_test_cases()
    
    # 按类别过滤
    if args.category:
        category_map = {
            'prover': ['nonexistent_prover', 'empty_provers', 'multiple_nonexistent', 'mixed_provers', 'special_char'],
            'timeout': ['negative_timeout', 'zero_timeout', 'huge_timeout', 'float_timeout'],
            'fact': ['negative_facts', 'huge_facts', 'invalid_fact_filter'],
            'option': ['contradictory_options', 'unknown_option', 'malformed_option'],
            'method': ['unknown_methods', 'empty_methods'],
            'combined': ['pairwise', 'triple', 'extreme', 'boolean', 'proof_method']
        }
        keywords = category_map.get(args.category, [])
        test_cases = [tc for tc in test_cases if any(kw in tc.name.lower() for kw in keywords)]
        logger.info(f"过滤后测试数量: {len(test_cases)}")
    
    # 限制数量
    if args.limit:
        test_cases = test_cases[:args.limit]
        logger.info(f"限制测试数量: {len(test_cases)}")
    
    # 运行测试
    logger.info(f"开始运行 {len(test_cases)} 个配置测试...")
    for i, tc in enumerate(test_cases, 1):
        logger.info(f"[{i}/{len(test_cases)}] {tc.name}")
        result = fuzzer.run_test_case(tc)
        fuzzer.results.append(result)
    
    # 生成报告
    report = fuzzer.save_results()
    
    # 打印报告
    print("\n" + report)


if __name__ == '__main__':
    main()

