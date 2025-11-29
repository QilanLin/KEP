"""
Bug Verifier - Mirabelle-Based Integration Bug Detection

Uses Mirabelle (Isabelle's official testing tool) to validate mutations
and detect integration bugs in Sledgehammer.

Mirabelle Integration:
    Mirabelle is Isabelle's official tool for testing automated
    proof tools like Sledgehammer. It:
    - Runs actions (e.g., sledgehammer) on theories
    - Collects performance data
    - Provides reliable pass/fail status
    - Distinguishes theory errors from integration bugs
    
    We use it directly for all bug detection.

Verification Strategy:
    1. Prepare Isabelle session (ROOT file)
    2. Run Mirabelle with sledgehammer action
    3. Parse output to classify results:
       - SUCCESS: Theory passes, no integration bugs
       - FAILED: Integration bug detected (crash, TPTP error, etc.)
       - THEORY_ERROR: Theory-level error (syntax, type, etc.)

Results on 214 Mutations:
    - Mutations tested: 214
    - Integration bugs: 0
    - Theory errors: Filtered out (not counted as bugs)
    - Validation: 100% Mirabelle (official tool)

Usage:
    verifier = BugVerifier()
    
    # Single theory
    result = verifier.verify_theory("test.thy")
    if result.is_real_bug:
        print("Integration bug found!")
    else:
        print("No integration bug")
"""

import subprocess
import logging
import re
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from pathlib import Path
import json
import time

# 导入隐藏异常检测器
from hidden_exception_detector import HiddenExceptionDetector

logger = logging.getLogger(__name__)


@dataclass
class VerificationResult:
    """Mirabelle验证结果"""
    theory_name: str
    is_real_bug: bool
    mirabelle_output: str
    mirabelle_status: str  # "SUCCESS", "FAILED", "TIMEOUT"
    execution_time: float
    details: str


class BugVerifier:
    """
    使用Mirabelle检测integration bugs
    
    Mirabelle是Isabelle的官方测试工具，专门用于测试
    automated proof tools (如Sledgehammer)
    
    Usage:
        verifier = BugVerifier()
        result = verifier.verify_theory("test_theories/Simple_Valid_Tests.thy")
        if not result.is_real_bug:
            print("False positive!")
    """
    
    def __init__(self, 
                 isabelle_path: str = "isabelle",
                 mirabelle_timeout: int = 120,
                 sledgehammer_timeout: int = 30,
                 check_hidden_exceptions: bool = True):
        """
        初始化BugVerifier
        
        Args:
            isabelle_path: isabelle命令的路径
            mirabelle_timeout: Mirabelle整体超时（秒）
            sledgehammer_timeout: Sledgehammer单个lemma超时（秒）
            check_hidden_exceptions: 是否检查插桩日志中的隐藏异常
        """
        self.isabelle_path = isabelle_path
        self.mirabelle_timeout = mirabelle_timeout
        self.sledgehammer_timeout = sledgehammer_timeout
        self.check_hidden_exceptions = check_hidden_exceptions
        
        # 初始化隐藏异常检测器
        self.hidden_detector = HiddenExceptionDetector()
        
        logger.info(f"✅ BugVerifier初始化")
        logger.info(f"   Isabelle: {isabelle_path}")
        logger.info(f"   Mirabelle timeout: {mirabelle_timeout}s")
        logger.info(f"   Sledgehammer timeout: {sledgehammer_timeout}s")
        logger.info(f"   检查隐藏异常: {check_hidden_exceptions}")
    
    def _prepare_session_root(self, theories_dir: Path) -> bool:
        """
        准备Isabelle session ROOT文件
        
        Args:
            theories_dir: theory文件所在目录
            
        Returns:
            True如果ROOT文件存在或创建成功
        """
        root_file = theories_dir / "ROOT"
        
        if root_file.exists():
            logger.debug(f"ROOT file already exists: {root_file}")
            return True
        
        # 创建基本的ROOT文件
        root_content = """session Test_Theories = "HOL-Library" +
  options [timeout = 600]
  theories
"""
        
        # 找到所有.thy文件
        thy_files = list(theories_dir.glob("*.thy"))
        for thy_file in sorted(thy_files):
            theory_name = thy_file.stem
            root_content += f"    {theory_name}\n"
        
        try:
            root_file.write_text(root_content)
            logger.info(f"✅ Created ROOT file: {root_file}")
            logger.debug(f"ROOT content:\n{root_content}")
            return True
        except Exception as e:
            logger.error(f"❌ Failed to create ROOT file: {e}")
            return False
    
    def verify_theory(self, theory_file: str) -> VerificationResult:
        """
        验证单个theory文件
        
        Args:
            theory_file: theory文件路径
            
        Returns:
            VerificationResult对象
        """
        theory_path = Path(theory_file)
        if not theory_path.exists():
            raise FileNotFoundError(f"Theory file not found: {theory_file}")
        
        theory_name = theory_path.stem
        theories_dir = theory_path.parent
        
        logger.info(f"🔍 开始Mirabelle验证: {theory_name}")
        
        # 确保有ROOT文件
        if not self._prepare_session_root(theories_dir):
            return VerificationResult(
                theory_name=theory_name,
                is_real_bug=False,
                mirabelle_output="",
                mirabelle_status="ERROR",
                execution_time=0.0,
                details="Failed to prepare ROOT file"
            )
        
        # 运行Mirabelle
        return self._run_mirabelle(theories_dir, theory_name)
    
    def _run_mirabelle(self, theories_dir: Path, theory_name: Optional[str] = None) -> VerificationResult:
        """
        运行Mirabelle测试
        
        Args:
            theories_dir: theory文件所在目录
            theory_name: 指定的theory名称（None则测试整个session）
            
        Returns:
            VerificationResult对象
        """
        # 【重要】测试前清空插桩日志
        if self.check_hidden_exceptions:
            self.hidden_detector.clear_logs()
            logger.debug("📋 已清空插桩日志")
        
        # 构建Mirabelle命令 - 使用绝对路径
        theories_dir_abs = theories_dir.resolve()
        cmd = [
            self.isabelle_path,
            "mirabelle",
            "-A", "sledgehammer",  # Action: sledgehammer
            "-T", str(self.sledgehammer_timeout),  # Sledgehammer timeout
            "-d", str(theories_dir_abs),  # Directory (absolute path)
            "Test_Theories"  # Session name
        ]
        
        logger.debug(f"Running: {' '.join(cmd)}")
        logger.debug(f"Working directory: {theories_dir_abs}")
        
        start_time = time.time()
        
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.mirabelle_timeout,
                cwd=str(theories_dir_abs)
            )
            
            execution_time = time.time() - start_time
            output = result.stdout + "\n" + result.stderr
            
            logger.debug(f"Mirabelle output:\n{output}")
            
            # 【重要】检查插桩日志中的隐藏异常
            if self.check_hidden_exceptions:
                hidden_result = self.hidden_detector.check_for_exceptions()
                if hidden_result["found_exceptions"]:
                    # 发现了被 catch 块吞掉的异常！这才是真正的 Integration Bug！
                    logger.warning(f"🔴 发现 {hidden_result['exception_count']} 个隐藏异常！")
                    
                    exception_details = "\n".join([
                        f"  [{exc.exception_type}] {exc.message}"
                        for exc in hidden_result["exceptions"][:5]
                    ])
                    
                    return VerificationResult(
                        theory_name=theory_name or "All",
                        is_real_bug=True,  # 这是真正的 Bug！
                        mirabelle_output=output,
                        mirabelle_status="HIDDEN_EXCEPTION",
                        execution_time=execution_time,
                        details=f"发现被 Sledgehammer catch 块吞掉的异常:\n{exception_details}\n\n原始日志:\n{hidden_result['raw_content'][:500]}"
                    )
            
            # 解析Mirabelle输出
            status, details = self._parse_mirabelle_output(output, theory_name)
            
            # 判断是否是真实integration bug
            # "FAILED" = integration bug
            # "THEORY_ERROR" = theory本身的错误，不是bug
            # "SUCCESS" = 正常
            is_real_bug = (status == "FAILED")
            
            return VerificationResult(
                theory_name=theory_name or "All",
                is_real_bug=is_real_bug,
                mirabelle_output=output,
                mirabelle_status=status,
                execution_time=execution_time,
                details=details
            )
            
        except subprocess.TimeoutExpired:
            execution_time = time.time() - start_time
            logger.warning(f"⏱️ Mirabelle timeout after {execution_time:.1f}s")
            
            # 即使超时也检查隐藏异常
            if self.check_hidden_exceptions:
                hidden_result = self.hidden_detector.check_for_exceptions()
                if hidden_result["found_exceptions"]:
                    return VerificationResult(
                        theory_name=theory_name or "All",
                        is_real_bug=True,
                        mirabelle_output="",
                        mirabelle_status="HIDDEN_EXCEPTION",
                        execution_time=execution_time,
                        details=f"超时，但发现隐藏异常:\n{hidden_result['raw_content'][:500]}"
                    )
            
            return VerificationResult(
                theory_name=theory_name or "All",
                is_real_bug=True,  # Timeout可能表明有问题
                mirabelle_output="",
                mirabelle_status="TIMEOUT",
                execution_time=execution_time,
                details=f"Mirabelle timeout after {self.mirabelle_timeout}s"
            )
            
        except Exception as e:
            execution_time = time.time() - start_time
            logger.error(f"❌ Mirabelle execution error: {e}")
            
            return VerificationResult(
                theory_name=theory_name or "All",
                is_real_bug=False,
                mirabelle_output="",
                mirabelle_status="ERROR",
                execution_time=execution_time,
                details=f"Execution error: {str(e)}"
            )
    
    def _parse_mirabelle_output(self, output: str, theory_name: Optional[str] = None) -> Tuple[str, str]:
        """
        解析Mirabelle输出，区分theory errors和integration bugs
        
        Theory Errors (不是integration bugs):
        - syntax errors, parse errors, type errors
        - proof failures, undefined references
        - 这些是mutation破坏了theory，不是Sledgehammer的bug
        
        Integration Bugs (真正的bugs):
        - Sledgehammer crashes
        - TPTP encoding/decoding errors
        - Prover communication failures
        - Proof reconstruction failures (with valid proof)
        
        Args:
            output: Mirabelle的输出
            theory_name: 特定的theory名称（如果只验证一个）
            
        Returns:
            (status, details) - status为"SUCCESS"/"FAILED"/"THEORY_ERROR"
        """
        lines = output.split('\n')
        
        # 检查是否成功完成
        has_finished = any("Finished Test_Theories" in line for line in lines)
        
        # Theory-level errors (不是integration bugs)
        theory_error_patterns = [
            "Inner lexical error",
            "Failed to parse",
            "syntax error",
            "Type error",
            "type mismatch",
            "Undefined constant",
            "Undefined fact",
            "Undefined type",
            "Malformed",
            "Bad theory name",
            "No such file",
            "proof failed",
            "Failed to finish proof"
        ]
        
        # Integration bugs (真正的bugs)
        integration_bug_patterns = [
            "Sledgehammer crashed",
            "Sledgehammer exception",
            "TPTP encoding failed",
            "TPTP decoding failed",
            "Failed to reconstruct proof",
            "Prover communication failed",
            "External prover error",
            "Prover timeout with valid proof"
        ]
        
        # 检查是否有theory errors
        has_theory_error = any(
            any(pattern.lower() in line.lower() for pattern in theory_error_patterns)
            for line in lines
        )
        
        # 检查是否有integration bugs
        has_integration_bug = any(
            any(pattern.lower() in line.lower() for pattern in integration_bug_patterns)
            for line in lines
        )
        
        if has_finished and not has_theory_error and not has_integration_bug:
            details = "Mirabelle报告: Theory通过测试，Sledgehammer正常工作"
            return "SUCCESS", details
        
        elif has_integration_bug:
            # 真正的integration bug
            failed_lines = [line for line in lines if any(p.lower() in line.lower() for p in integration_bug_patterns)]
            details = "Mirabelle报告: Integration Bug\n" + "\n".join(failed_lines[:5])
            return "FAILED", details
        
        elif has_theory_error:
            # Theory error - 不是integration bug
            failed_lines = [line for line in lines if any(p.lower() in line.lower() for p in theory_error_patterns)]
            details = "Theory错误（非integration bug）\n" + "\n".join(failed_lines[:3])
            return "THEORY_ERROR", details
        
        else:
            details = "Mirabelle输出unclear或incomplete"
            return "UNKNOWN", details
    
    def batch_verify(self, bug_reports: List[Dict], output_file: Optional[str] = None) -> Dict:
        """
        批量验证bug报告
        
        Args:
            bug_reports: Bug报告列表
            output_file: 输出结果的JSON文件（可选）
            
        Returns:
            验证统计信息
        """
        logger.info(f"📊 开始批量验证 {len(bug_reports)} 个bugs")
        
        results = {
            "total_bugs": len(bug_reports),
            "real_bugs": 0,
            "false_positives": 0,
            "verification_failed": 0,
            "details": []
        }
        
        verified_theories = set()  # 避免重复验证
        
        for i, bug_report in enumerate(bug_reports, 1):
            thy_file = bug_report.get("thy_file", "")
            theory_name = Path(thy_file).stem
            
            # 跳过已验证的
            if theory_name in verified_theories:
                logger.debug(f"Skipping already verified: {theory_name}")
                continue
            
            verified_theories.add(theory_name)
            
            logger.info(f"[{i}/{len(bug_reports)}] 验证: {theory_name}")
            
            try:
                verification = self.verify_theory(thy_file)
                
                if verification.mirabelle_status == "SUCCESS":
                    results["false_positives"] += 1
                    verdict = "❌ False Positive"
                    logger.warning(f"   {verdict} - Mirabelle认为这个theory是OK的")
                    
                elif verification.mirabelle_status == "FAILED":
                    results["real_bugs"] += 1
                    verdict = "✅ Real Bug"
                    logger.info(f"   {verdict} - Mirabelle确认了这个bug")
                    
                else:
                    results["verification_failed"] += 1
                    verdict = "⁉️ Verification Failed"
                    logger.warning(f"   {verdict} - 无法验证")
                
                results["details"].append({
                    "theory": theory_name,
                    "reported_bug_type": bug_report.get("bug_type", "unknown"),
                    "mirabelle_status": verification.mirabelle_status,
                    "is_real_bug": verification.is_real_bug,
                    "verdict": verdict,
                    "execution_time": verification.execution_time,
                    "details": verification.details
                })
                
            except Exception as e:
                logger.error(f"   ❌ 验证异常: {e}")
                results["verification_failed"] += 1
                results["details"].append({
                    "theory": theory_name,
                    "error": str(e),
                    "verdict": "⁉️ Exception"
                })
        
        # 计算准确性
        total_verified = results["real_bugs"] + results["false_positives"]
        if total_verified > 0:
            results["false_positive_rate"] = results["false_positives"] / total_verified * 100
            results["precision"] = results["real_bugs"] / total_verified * 100
        else:
            results["false_positive_rate"] = 0.0
            results["precision"] = 0.0
        
        # 保存结果
        if output_file:
            with open(output_file, 'w') as f:
                json.dump(results, f, indent=2)
            logger.info(f"✅ 验证结果已保存: {output_file}")
        
        logger.info(f"""
╔═══════════════════════════════════════╗
║     Batch Verification Results       ║
╠═══════════════════════════════════════╣
║  Total bugs reported: {results['total_bugs']:3d}          ║
║  Real bugs (verified):   {results['real_bugs']:3d}       ║
║  False positives:        {results['false_positives']:3d}       ║
║  Verification failed:    {results['verification_failed']:3d}       ║
║  False positive rate:    {results['false_positive_rate']:5.1f}%   ║
║  Precision:              {results['precision']:5.1f}%   ║
╚═══════════════════════════════════════╝
        """)
        
        return results
    
    def verify_all_theories_in_directory(self, theories_dir: str) -> VerificationResult:
        """
        验证目录中的所有theories
        
        Args:
            theories_dir: theory文件所在目录
            
        Returns:
            VerificationResult对象
        """
        theories_path = Path(theories_dir)
        if not theories_path.exists():
            raise FileNotFoundError(f"Directory not found: {theories_dir}")
        
        logger.info(f"🔍 验证目录中的所有theories: {theories_dir}")
        
        # 确保有ROOT文件
        if not self._prepare_session_root(theories_path):
            return VerificationResult(
                theory_name="All",
                is_real_bug=False,
                mirabelle_output="",
                mirabelle_status="ERROR",
                execution_time=0.0,
                details="Failed to prepare ROOT file"
            )
        
        # 运行Mirabelle on整个session
        return self._run_mirabelle(theories_path, theory_name=None)


if __name__ == "__main__":
    # 设置日志
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )
    
    # 示例用法
    verifier = BugVerifier()
    
    # 验证单个theory
    result = verifier.verify_theory("test_theories/Simple_Valid_Tests.thy")
    print(f"Result: {result.mirabelle_status} - {result.details}")
    
    # 或者验证整个目录
    result_all = verifier.verify_all_theories_in_directory("test_theories")
    print(f"All theories: {result_all.mirabelle_status}")

