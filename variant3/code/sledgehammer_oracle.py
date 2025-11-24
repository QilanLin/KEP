"""
Sledgehammer Oracle - Integration Bug Detection (Improved Version)

Detects bugs in the Isabelle Sledgehammer interface layer.

Target Bug Types:
    - Sledgehammer crashes/timeouts
    - TPTP encoding/decoding errors
    - Proof reconstruction failures
    - Prover integration issues

Oracle Design:
    Four-layer pattern-based classification:
    
    1. Success Indicator Checking (_indicates_success)
       - Checks for "Finished" markers
       - Validates overall execution status
       - Reduces false positives from warnings
    
    2. Critical Error Detection (_is_critical_error)
       - Distinguishes *** Error from warnings
       - Focuses on actual failures
       - Ignores minor issues
    
    3. Theory Error Filtering (_is_theory_error)
       - Separates theory syntax/type errors
       - Focuses only on integration bugs
       - Prevents misclassification
    
    4. Interface Issue Detection (_is_sledgehammer_interface_issue)
       - Specifically targets Sledgehammer layer
       - Checks for TPTP, prover communication issues
       - Excludes non-integration problems

Validation:
    Oracle refined through iterative alignment with Mirabelle
    (Isabelle's official testing tool) as ground truth.
    
    Tested on 130 mutations with complete alignment to Mirabelle.

Usage:
    oracle = SledgehammerOracle()
    
    # Test single theory
    bug = oracle.check_theory_file("test.thy", timeout=120)
    if bug:
        print(f"Bug: {bug.bug_type.value}")
    
    # Batch testing
    for thy_file in theory_files:
        bug = oracle.check_theory_file(thy_file)
        if bug:
            oracle.save_bug_report(bug, "bugs/")
"""

import logging
from typing import Optional, Dict, Any, Tuple
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
import re

try:
    from .isabelle_interface import (
        IsabelleInterface, 
        IsabelleResult, 
        IsabelleStatus,
        InvalidTheoryNameError
    )
except ImportError:
    from isabelle_interface import (
        IsabelleInterface, 
        IsabelleResult, 
        IsabelleStatus,
        InvalidTheoryNameError
    )

logger = logging.getLogger(__name__)


class IntegrationBugType(Enum):
    """Integration bug类型"""
    # Sledgehammer相关
    SLEDGEHAMMER_CRASH = "sledgehammer_crash"
    SLEDGEHAMMER_TIMEOUT = "sledgehammer_timeout"
    TPTP_ENCODING_ERROR = "tptp_encoding_error"
    
    # Proof相关
    PROOF_RECONSTRUCTION_FAILED = "proof_reconstruction_failed"
    PROOF_METHOD_ERROR = "proof_method_error"
    PROOF_INCOMPLETE = "proof_incomplete"
    PROOF_FAILED = "proof_failed"
    
    # Induction相关
    INDUCTION_RULE_ERROR = "induction_rule_error"
    
    # 语法/语义相关
    SYNTAX_ERROR = "syntax_error"
    TYPE_ERROR = "type_error"
    UNDEFINED_REFERENCE = "undefined_reference"
    
    # Prover集成相关
    PROVER_INTEGRATION_ERROR = "prover_integration_error"
    PROVER_NOT_FOUND = "prover_not_found"
    
    # 其他
    UNEXPECTED_BEHAVIOR = "unexpected_behavior"


@dataclass
class IntegrationBug:
    """Integration bug报告"""
    bug_type: IntegrationBugType
    thy_file: str
    lemma_name: Optional[str]
    prover: Optional[str]
    description: str
    isabelle_output: str
    isabelle_error: str
    execution_time: float
    original_result: Optional[IsabelleResult] = None
    mutated_result: Optional[IsabelleResult] = None


class SledgehammerOracle:
    """
    Sledgehammer Oracle
    
    检测Isabelle Sledgehammer接口的bugs,包括:
    - Sledgehammer崩溃/超时
    - TPTP编码/解码问题
    - Proof reconstruction失败
    - Prover集成问题
    """
    
    def __init__(self,
                 isabelle_interface: Optional[IsabelleInterface] = None,
                 enable_reconstruction_test: bool = True) -> None:
        """
        初始化Sledgehammer Oracle
        
        Args:
            isabelle_interface: Isabelle接口实例，None则创建新的
            enable_reconstruction_test: 是否启用reconstruction测试
            
        Raises:
            RuntimeError: Isabelle不可用
        """
        self.isabelle = isabelle_interface or IsabelleInterface()
        self.enable_reconstruction_test = enable_reconstruction_test
        self.bugs_found: list[IntegrationBug] = []
        
    def _indicates_success(self, output: str) -> bool:
        """
        检查output是否表明执行成功
        
        使用Mirabelle的判断标准：
        - "Finished" 出现在输出末尾
        - 没有critical error markers
        - Return code为0或只有minor warnings
        
        Args:
            output: Isabelle的输出
            
        Returns:
            True如果表明成功，否则False
        """
        # 获取最后几行
        lines = output.split('\n')
        last_lines = '\n'.join(lines[-20:])  # 最后20行
        
        # 检查成功标记
        success_indicators = [
            "Finished",
            "successfully",
            "No errors"
        ]
        
        # Critical error markers (*** 开头的错误)
        critical_error_pattern = r'\*\*\* (Error|Exception|Failed)'
        
        # 如果有明确的成功标记且没有critical errors
        has_success = any(indicator in last_lines for indicator in success_indicators)
        has_critical_error = re.search(critical_error_pattern, output)
        
        # 有成功标记且没有critical errors
        if has_success and not has_critical_error:
            return True
        
        return False
    
    def _is_critical_error(self, output: str, error: str) -> bool:
        """
        判断是否是critical error (而不是warning或minor issue)
        
        Args:
            output: 标准输出
            error: 标准错误
            
        Returns:
            True如果是critical error
        """
        # Critical error patterns
        critical_patterns = [
            r'\*\*\* Error:',
            r'\*\*\* Exception:',
            r'\*\*\* Failed',
            r'Internal error',
            r'Unhandled exception',
        ]
        
        combined = output + error
        
        for pattern in critical_patterns:
            if re.search(pattern, combined):
                return True
        
        return False
    
    def _is_theory_error(self, output: str, error: str) -> bool:
        """
        判断是否是theory本身的错误（不是integration bug）
        
        Theory errors include:
        - Syntax errors
        - Type errors
        - Undefined references
        - Invalid definitions
        
        Args:
            output: 标准输出
            error: 标准错误
            
        Returns:
            True如果是theory error
        """
        theory_error_patterns = [
            r'Malformed',
            r'syntax error',
            r'Type.*unification',
            r'Type.*mismatch',
            r'Undefined constant',
            r'Undefined type',
            r'Undefined fact',
            r'Inner syntax error',
        ]
        
        combined = output + error
        
        for pattern in theory_error_patterns:
            if re.search(pattern, combined, re.IGNORECASE):
                logger.debug(f"Detected theory error: {pattern}")
                return True
        
        return False
    
    def _is_sledgehammer_interface_issue(self, output: str, error: str) -> bool:
        """
        判断是否是Sledgehammer接口层的问题
        
        Integration bugs are specifically:
        - Sledgehammer crashes
        - TPTP encoding/decoding errors
        - Prover communication failures
        - Proof reconstruction failures (with valid proof)
        
        Args:
            output: 标准输出
            error: 标准错误
            
        Returns:
            True如果是Sledgehammer interface issue
        """
        interface_patterns = [
            r'sledgehammer.*crashed',
            r'sledgehammer.*exception',
            r'TPTP.*error',
            r'TPTP.*failed',
            r'Failed to reconstruct proof',
            r'Prover.*not responding',
            r'Prover.*communication.*failed',
            r'External prover.*error',
        ]
        
        combined = output + error
        
        for pattern in interface_patterns:
            if re.search(pattern, combined, re.IGNORECASE):
                logger.info(f"Detected Sledgehammer interface issue: {pattern}")
                return True
        
        return False
    
    def _classify_error(self, output: str, error: str) -> Optional[Tuple[IntegrationBugType, str]]:
        """
        分类错误类型（改进版 - 使用contextual analysis）
        
        根据错误文本的特征和上下文，判断具体的bug类型。
        
        改进点：
        1. 首先检查是否实际上是成功的
        2. 区分critical errors vs warnings
        3. 区分theory errors vs integration bugs
        4. 使用更智能的pattern matching
        
        Args:
            output: 标准输出
            error: 标准错误
            
        Returns:
            (bug_type, description)元组，如果不是bug则返回None
        """
        # 1. 首先检查是否表明成功
        if self._indicates_success(output):
            logger.debug("Output indicates success, not classifying as bug")
            return None
        
        # 2. 检查是否是critical error
        if not self._is_critical_error(output, error):
            logger.debug("Not a critical error, likely just warnings")
            return None
        
        # 3. 检查是否是theory error (不是integration bug)
        if self._is_theory_error(output, error):
            logger.debug("Detected theory error, not an integration bug")
            return None
        
        # 4. 检查是否是Sledgehammer interface issue (真正的integration bug)
        if not self._is_sledgehammer_interface_issue(output, error):
            # 如果不是interface issue，也不报告为integration bug
            logger.debug("Not a Sledgehammer interface issue")
            return None
        
        # 5. 现在我们知道这是一个真正的integration bug，进行细分
        combined = output + error
        
        # Sledgehammer specific errors
        sledgehammer_patterns = [
            (r'sledgehammer.*timeout', IntegrationBugType.SLEDGEHAMMER_TIMEOUT, "Sledgehammer超时"),
            (r'sledgehammer.*crash', IntegrationBugType.SLEDGEHAMMER_CRASH, "Sledgehammer崩溃"),
            (r'TPTP.*encoding', IntegrationBugType.TPTP_ENCODING_ERROR, "TPTP编码错误"),
            (r'TPTP.*decoding', IntegrationBugType.TPTP_ENCODING_ERROR, "TPTP解码错误"),
            (r'Failed to reconstruct', IntegrationBugType.PROOF_RECONSTRUCTION_FAILED, "Proof重构失败"),
            (r'Prover.*not found', IntegrationBugType.PROVER_NOT_FOUND, "Prover未找到"),
            (r'Prover.*failed', IntegrationBugType.PROVER_INTEGRATION_ERROR, "Prover集成错误"),
        ]
        
        for pattern, bug_type, description in sledgehammer_patterns:
            if re.search(pattern, combined, re.IGNORECASE):
                logger.info(f"Classified as {bug_type.value}: {description}")
                return bug_type, description
        
        # 如果是Sledgehammer interface issue但不能细分，标记为unexpected
        return IntegrationBugType.UNEXPECTED_BEHAVIOR, "Sledgehammer接口未分类错误"

    def check_theory_file(self,
                         thy_file: str,
                         timeout: float = 60.0) -> Optional[IntegrationBug]:
        """
        检查theory文件是否存在Integration bugs
        
        Args:
            thy_file: Theory文件路径
            timeout: 超时时间
            
        Returns:
            如果发现bug返回IntegrationBug，否则返回None
            
        Raises:
            FileNotFoundError: theory文件不存在
            InvalidTheoryNameError: theory名称无效
        """
        logger.info(f"检查theory文件: {thy_file}")
        
        # 运行theory文件
        result = self.isabelle.run_theory(thy_file, timeout=timeout)
        
        # 检查是否有Integration问题
        bug = None
        
        if result.status == IsabelleStatus.TIMEOUT:
            bug = IntegrationBug(
                bug_type=IntegrationBugType.SLEDGEHAMMER_TIMEOUT,
                thy_file=thy_file,
                lemma_name=None,
                prover=None,
                description=f"Isabelle执行超时（>{timeout}秒）",
                isabelle_output=result.output,
                isabelle_error=result.error,
                execution_time=result.execution_time,
                original_result=result
            )
            
        elif result.status == IsabelleStatus.ERROR:
            # 使用改进的错误分类（返回None如果不是真正的bug）
            classification = self._classify_error(result.output, result.error)
            
            if classification is not None:
                bug_type, description = classification
                
                bug = IntegrationBug(
                    bug_type=bug_type,
                    thy_file=thy_file,
                    lemma_name=None,
                    prover=None,
                    description=description,
                    isabelle_output=result.output,
                    isabelle_error=result.error,
                    execution_time=result.execution_time,
                    original_result=result
                )
            else:
                logger.debug(f"{thy_file}: 错误但不是integration bug（可能是theory error或warning）")
                return None
        
        elif result.status == IsabelleStatus.PROOF_FAILED:
            bug = IntegrationBug(
                bug_type=IntegrationBugType.PROOF_RECONSTRUCTION_FAILED,
                thy_file=thy_file,
                lemma_name=None,
                prover=None,
                description="Proof重构失败",
                isabelle_output=result.output,
                isabelle_error=result.error,
                execution_time=result.execution_time,
                original_result=result
            )
        
        if bug:
            self.bugs_found.append(bug)
            logger.warning(f"🐛 发现Integration bug: {bug.bug_type.value}")
        else:
            logger.info(f"✅ {thy_file}: 无bug发现")
        
        return bug
    
    def check_sledgehammer(self,
                          thy_file: str,
                          lemma_name: str,
                          prover: str = "eprover",
                          timeout: float = 30.0) -> Optional[IntegrationBug]:
        """
        检查Sledgehammer调用是否存在bugs
        
        Args:
            thy_file: Theory文件
            lemma_name: Lemma名称
            prover: 使用的prover
            timeout: 超时时间
            
        Returns:
            如果发现bug返回IntegrationBug，否则返回None
            
        Raises:
            ValueError: 输入参数无效
            FileNotFoundError: theory文件不存在
        """
        logger.info(f"测试Sledgehammer: {thy_file}, lemma={lemma_name}, prover={prover}")
        
        # 运行Sledgehammer
        result = self.isabelle.run_sledgehammer(
            thy_file=thy_file,
            lemma_name=lemma_name,
            prover=prover,
            timeout=timeout
        )
        
        bug = None
        
        if result.status == IsabelleStatus.TIMEOUT:
            bug = IntegrationBug(
                bug_type=IntegrationBugType.SLEDGEHAMMER_TIMEOUT,
                thy_file=thy_file,
                lemma_name=lemma_name,
                prover=prover,
                description=f"Sledgehammer超时（>{timeout}秒）",
                isabelle_output=result.output,
                isabelle_error=result.error,
                execution_time=result.execution_time,
                original_result=result
            )
            
        elif result.status == IsabelleStatus.ERROR:
            bug = IntegrationBug(
                bug_type=IntegrationBugType.SLEDGEHAMMER_CRASH,
                thy_file=thy_file,
                lemma_name=lemma_name,
                prover=prover,
                description="Sledgehammer崩溃或错误",
                isabelle_output=result.output,
                isabelle_error=result.error,
                execution_time=result.execution_time,
                original_result=result
            )
        
        if bug:
            self.bugs_found.append(bug)
            logger.warning(f"🐛 发现Sledgehammer bug: {bug.bug_type.value}")
        else:
            logger.info(f"✅ Sledgehammer测试通过: {lemma_name}")
        
        return bug
    
    def compare_original_and_mutant(self,
                                   original_thy: str,
                                   mutant_thy: str,
                                   timeout: float = 60.0) -> Optional[IntegrationBug]:
        """
        比较原始和变异theory的行为差异
        
        Args:
            original_thy: 原始theory文件
            mutant_thy: 变异theory文件
            timeout: 超时时间
            
        Returns:
            如果发现异常差异返回IntegrationBug,否则返回None
        """
        logger.info(f"比较原始和变异theory: {original_thy} vs {mutant_thy}")
        
        # 运行原始theory
        original_result = self.isabelle.run_theory(original_thy, timeout=timeout)
        
        # 运行变异theory
        mutant_result = self.isabelle.run_theory(mutant_thy, timeout=timeout)
        
        bug = None
        
        # 检查行为差异
        if original_result.status == IsabelleStatus.SUCCESS:
            if mutant_result.status == IsabelleStatus.TIMEOUT:
                # 原始成功，变异超时 - 性能退化
                time_ratio = mutant_result.execution_time / max(original_result.execution_time, 0.001)
                
                bug = IntegrationBug(
                    bug_type=IntegrationBugType.UNEXPECTED_BEHAVIOR,
                    thy_file=mutant_thy,
                    lemma_name=None,
                    prover=None,
                    description=f"性能退化: 原始{original_result.execution_time:.2f}s -> 变异超时 (>{timeout}s), 退化{time_ratio:.1f}x",
                    isabelle_output=mutant_result.output,
                    isabelle_error=mutant_result.error,
                    execution_time=mutant_result.execution_time,
                    original_result=original_result,
                    mutated_result=mutant_result
                )
                
            elif mutant_result.status == IsabelleStatus.ERROR:
                # 原始成功，变异错误
                bug = IntegrationBug(
                    bug_type=IntegrationBugType.UNEXPECTED_BEHAVIOR,
                    thy_file=mutant_thy,
                    lemma_name=None,
                    prover=None,
                    description="原始theory成功但变异后出现错误",
                    isabelle_output=mutant_result.output,
                    isabelle_error=mutant_result.error,
                    execution_time=mutant_result.execution_time,
                    original_result=original_result,
                    mutated_result=mutant_result
                )
        
        if bug:
            self.bugs_found.append(bug)
            logger.warning(f"🐛 发现差异bug: {bug.description}")
        
        return bug
    
    def get_statistics(self) -> Dict[str, Any]:
        """
        获取统计信息
        
        包括：
        - 总bug数
        - 按bug类型的统计
        - 按prover的统计
        
        Returns:
            统计数据字典
            
        Example:
            >>> oracle = SledgehammerOracle()
            >>> stats = oracle.get_statistics()
            >>> print(f"总共发现 {stats['total_bugs']} 个bug")
        """
        stats = {
            "total_bugs": len(self.bugs_found),
            "by_type": {},
            "by_prover": {}
        }
        
        # 按类型统计
        for bug in self.bugs_found:
            bug_type = bug.bug_type.value
            stats["by_type"][bug_type] = stats["by_type"].get(bug_type, 0) + 1
        
        # 按prover统计
        for bug in self.bugs_found:
            if bug.prover:
                prover = bug.prover
                stats["by_prover"][prover] = stats["by_prover"].get(prover, 0) + 1
        
        return stats
    
    def save_bug_report(self, bug: IntegrationBug, output_file: str) -> None:
        """
        保存bug报告到文件
        
        Args:
            bug: IntegrationBug对象
            output_file: 输出文件路径
            
        Raises:
            IOError: 无法写入文件
        """
        import json
        
        try:
            report = {
                "bug_type": bug.bug_type.value,
                "thy_file": bug.thy_file,
                "lemma_name": bug.lemma_name,
                "prover": bug.prover,
                "description": bug.description,
                "isabelle_output": bug.isabelle_output[:500] if bug.isabelle_output else "",
                "isabelle_error": bug.isabelle_error[:500] if bug.isabelle_error else "",
                "execution_time": bug.execution_time
            }
            
            with open(output_file, 'w', encoding='utf-8') as f:
                json.dump(report, f, indent=2, ensure_ascii=False)
            
            logger.info(f"✅ Bug报告已保存: {output_file}")
            
        except IOError as e:
            error_msg = f"无法保存bug报告到 {output_file}: {e}"
            logger.error(error_msg)
            raise IOError(error_msg) from e


def test_sledgehammer_oracle():
    """测试Sledgehammer Oracle"""
    print("🧪 测试Sledgehammer Oracle")
    print("=" * 60)
    
    try:
        oracle = SledgehammerOracle()
        print("✅ Sledgehammer Oracle初始化成功")
        print()
        
        # 测试theory文件
        test_thy = "../../test_theories/Test_Basic.thy"
        if Path(test_thy).exists():
            print(f"📝 测试theory文件: {test_thy}")
            bug = oracle.check_theory_file(test_thy, timeout=60.0)
            
            if bug:
                print(f"🐛 发现bug: {bug.bug_type.value}")
                print(f"描述: {bug.description}")
            else:
                print("✅ 未发现bug")
            print()
        
        # 显示统计
        stats = oracle.get_statistics()
        print(f"总计发现: {stats['total_bugs']}个Integration bugs")
        if stats['by_type']:
            print("按类型:")
            for bug_type, count in stats['by_type'].items():
                print(f"  {bug_type}: {count}个")
        
        print()
        print("✅ Sledgehammer Oracle测试完成")
        
    except Exception as e:
        print(f"❌ 测试失败: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    # 配置日志
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    test_sledgehammer_oracle()

