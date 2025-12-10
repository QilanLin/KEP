#!/usr/bin/env python3
"""
Proof Reconstruction Tester - 专门测试 Proof Reconstruction Bug

这是项目中最重要的 bug 检测模块之一。

核心思路：
    当 Sledgehammer 调用外部 prover (E, Z3, cvc5) 找到证明后，
    需要将该证明"翻译回"Isabelle 可以验证的格式（如 metis, smt 等）。
    
    这个过程叫做 Proof Reconstruction。如果重构失败，说明：
    1. 外部 prover 的输出有问题
    2. 翻译/编码有 bug
    3. Isabelle 的重构机制有 bug
    
    这才是真正的 Integration Bug！

Bug 类型分类：
    - SYNTAX_ERROR: proof 格式语法错误
    - TYPE_ERROR: 类型不匹配（prover 返回的 proof 类型无法在 Isabelle 中验证）
    - PROOF_RECONSTRUCTION_FAILURE: 无法重构（核心 bug）
    - RECONSTRUCTION_TIMEOUT: 重构超时
    - UNKNOWN_ERROR: 其他错误

测试流程：
    1. 运行 Sledgehammer（在 mutated theory 上）
    2. 如果 Sledgehammer 返回 "Try this: by metis ..." 等
    3. 提取这个 proof
    4. 创建一个新的 theory，将 proof 插入
    5. 运行 Isabelle 验证这个 proof
    6. 如果验证失败 → 发现 Reconstruction Bug！

为什么这很重要：
    - 这是 Sledgehammer 最复杂的部分
    - 涉及 TPTP/SMT-LIB 到 Isabelle 的翻译
    - 传统 fuzzing 工具无法检测这类 bug
    - 这是我们论文的核心创新点

Usage:
    tester = ProofReconstructionTester()
    
    # 测试单个 theory
    result = tester.test_theory("test.thy")
    if result.bug_found:
        print(f"发现 Reconstruction Bug: {result.bug_type}")
    
    # 批量测试
    results = tester.batch_test(theory_files)

Author: KEP AWS Project
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
from enum import Enum

# 导入隐藏异常检测器
try:
    from hidden_exception_detector import HiddenExceptionDetector
except ImportError:
    HiddenExceptionDetector = None

logger = logging.getLogger(__name__)


class ReconstructionBugType(Enum):
    """Reconstruction Bug 类型"""
    SYNTAX_ERROR = "syntax_error"
    TYPE_ERROR = "type_error"
    PROOF_RECONSTRUCTION_FAILURE = "proof_reconstruction_failure"
    RECONSTRUCTION_TIMEOUT = "reconstruction_timeout"
    METIS_FAILURE = "metis_failure"
    SMT_REPLAY_FAILURE = "smt_replay_failure"
    UNKNOWN_ERROR = "unknown_error"


class ReconstructionStatus(Enum):
    """Reconstruction 测试状态"""
    NO_PROOF_FOUND = "no_proof_found"  # Sledgehammer 未找到证明
    RECONSTRUCTION_SUCCESS = "success"  # 重构成功
    RECONSTRUCTION_FAILED = "failed"    # 重构失败 → Bug!
    SLEDGEHAMMER_ERROR = "sledgehammer_error"  # Sledgehammer 本身出错
    TIMEOUT = "timeout"


@dataclass
class ProofInfo:
    """提取的 Proof 信息"""
    proof_text: str           # 完整 proof 文本，如 "by metis"
    proof_method: str         # proof 方法，如 "metis", "smt", "blast"
    lemma_name: str           # lemma 名称
    lemma_statement: str      # lemma 原始语句
    prover_used: Optional[str] = None  # 使用的 prover，如 "e", "z3"
    facts_used: Optional[List[str]] = None  # 使用的 facts


@dataclass
class ReconstructionTestResult:
    """Reconstruction 测试结果"""
    theory_file: str
    status: ReconstructionStatus
    bug_found: bool
    bug_type: Optional[ReconstructionBugType] = None
    
    # Sledgehammer 阶段
    sledgehammer_output: str = ""
    sledgehammer_time: float = 0.0
    proofs_found: int = 0
    
    # Reconstruction 阶段
    proof_info: Optional[ProofInfo] = None
    reconstruction_output: str = ""
    reconstruction_time: float = 0.0
    reconstruction_error: str = ""
    
    # 隐藏异常
    hidden_exception_found: bool = False
    hidden_exception_details: str = ""


class ProofReconstructionTester:
    """
    Proof Reconstruction 测试器
    
    专门测试 Sledgehammer 的 proof reconstruction 阶段。
    这是检测 integration bug 的核心模块。
    """
    
    def __init__(self,
                 isabelle_path: str = "isabelle",
                 sledgehammer_timeout: int = 60,
                 reconstruction_timeout: int = 30,
                 check_hidden_exceptions: bool = True):
        """
        初始化测试器
        
        Args:
            isabelle_path: Isabelle 可执行文件路径
            sledgehammer_timeout: Sledgehammer 超时时间（秒）
            reconstruction_timeout: Reconstruction 超时时间（秒）
            check_hidden_exceptions: 是否检查隐藏异常
        """
        self.isabelle_path = isabelle_path
        self.sledgehammer_timeout = sledgehammer_timeout
        self.reconstruction_timeout = reconstruction_timeout
        self.check_hidden_exceptions = check_hidden_exceptions
        
        # 初始化隐藏异常检测器
        if HiddenExceptionDetector and check_hidden_exceptions:
            self.hidden_detector = HiddenExceptionDetector()
        else:
            self.hidden_detector = None
        
        logger.info(f"✅ ProofReconstructionTester 初始化")
        logger.info(f"   Sledgehammer timeout: {sledgehammer_timeout}s")
        logger.info(f"   Reconstruction timeout: {reconstruction_timeout}s")
    
    def test_theory(self, theory_file: str) -> ReconstructionTestResult:
        """
        测试单个 theory 的 proof reconstruction
        
        核心流程：
        1. 运行 Sledgehammer，获取 proof
        2. 提取 proof 信息
        3. 创建测试 theory，验证 proof
        4. 分类结果
        
        Args:
            theory_file: Theory 文件路径
            
        Returns:
            ReconstructionTestResult
        """
        theory_path = Path(theory_file)
        if not theory_path.exists():
            return ReconstructionTestResult(
                theory_file=str(theory_path),
                status=ReconstructionStatus.SLEDGEHAMMER_ERROR,
                bug_found=False,
                sledgehammer_output=f"Theory file not found: {theory_file}"
            )
        
        theory_name = theory_path.stem
        logger.info(f"🔍 测试 Proof Reconstruction: {theory_name}")
        
        # 清空隐藏异常日志
        if self.hidden_detector:
            self.hidden_detector.clear_logs()
        
        # Step 1: 运行 Sledgehammer，获取 proof
        sledgehammer_result = self._run_sledgehammer(theory_path)
        
        if sledgehammer_result["status"] == "error":
            return ReconstructionTestResult(
                theory_file=str(theory_path),
                status=ReconstructionStatus.SLEDGEHAMMER_ERROR,
                bug_found=False,
                sledgehammer_output=sledgehammer_result["output"],
                sledgehammer_time=sledgehammer_result["time"]
            )
        
        if sledgehammer_result["status"] == "timeout":
            return ReconstructionTestResult(
                theory_file=str(theory_path),
                status=ReconstructionStatus.TIMEOUT,
                bug_found=False,
                sledgehammer_output=sledgehammer_result["output"],
                sledgehammer_time=sledgehammer_result["time"]
            )
        
        # Step 2: 提取 proof 信息
        proofs = self._extract_proofs(sledgehammer_result["output"])
        
        if not proofs:
            # 检查隐藏异常
            hidden_result = self._check_hidden_exceptions()
            
            return ReconstructionTestResult(
                theory_file=str(theory_path),
                status=ReconstructionStatus.NO_PROOF_FOUND,
                bug_found=hidden_result["found"],
                bug_type=ReconstructionBugType.UNKNOWN_ERROR if hidden_result["found"] else None,
                sledgehammer_output=sledgehammer_result["output"],
                sledgehammer_time=sledgehammer_result["time"],
                proofs_found=0,
                hidden_exception_found=hidden_result["found"],
                hidden_exception_details=hidden_result["details"]
            )
        
        logger.info(f"   📝 找到 {len(proofs)} 个 proof")
        
        # Step 3: 逐个测试 proof reconstruction
        for proof_info in proofs:
            logger.info(f"   🔄 测试重构: {proof_info.proof_method} for {proof_info.lemma_name}")
            
            recon_result = self._test_reconstruction(
                theory_path,
                proof_info
            )
            
            if recon_result["status"] == "failed":
                # 发现 Reconstruction Bug!
                bug_type = self._classify_reconstruction_failure(
                    recon_result["error"]
                )
                
                logger.warning(f"   🐛 发现 Reconstruction Bug: {bug_type.value}")
                
                return ReconstructionTestResult(
                    theory_file=str(theory_path),
                    status=ReconstructionStatus.RECONSTRUCTION_FAILED,
                    bug_found=True,
                    bug_type=bug_type,
                    sledgehammer_output=sledgehammer_result["output"],
                    sledgehammer_time=sledgehammer_result["time"],
                    proofs_found=len(proofs),
                    proof_info=proof_info,
                    reconstruction_output=recon_result["output"],
                    reconstruction_time=recon_result["time"],
                    reconstruction_error=recon_result["error"]
                )
        
        # 检查隐藏异常
        hidden_result = self._check_hidden_exceptions()
        
        logger.info(f"   ✅ 所有 proof 重构成功")
        
        return ReconstructionTestResult(
            theory_file=str(theory_path),
            status=ReconstructionStatus.RECONSTRUCTION_SUCCESS,
            bug_found=hidden_result["found"],
            bug_type=ReconstructionBugType.UNKNOWN_ERROR if hidden_result["found"] else None,
            sledgehammer_output=sledgehammer_result["output"],
            sledgehammer_time=sledgehammer_result["time"],
            proofs_found=len(proofs),
            hidden_exception_found=hidden_result["found"],
            hidden_exception_details=hidden_result["details"]
        )
    
    def _run_sledgehammer(self, theory_path: Path) -> Dict:
        """
        使用 Mirabelle 运行 Sledgehammer 并捕获 proof 输出
        
        Mirabelle 是 Isabelle 官方测试工具，能正确运行 Sledgehammer 并获取 proof。
        
        Returns:
            {
                "status": "success" | "error" | "timeout",
                "output": str,
                "time": float
            }
        """
        theory_name = theory_path.stem
        theories_dir = theory_path.parent
        
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            
            # 复制 theory 文件
            theory_copy = temp_path / theory_path.name
            theory_copy.write_text(theory_path.read_text())
            
            # 创建 ROOT 文件（Mirabelle 需要）
            root_content = f'''session Recon_Session = "HOL" +
  options [timeout = {self.sledgehammer_timeout}]
  theories
    {theory_name}
'''
            root_file = temp_path / "ROOT"
            root_file.write_text(root_content)
            
            # 使用 Mirabelle 运行 Sledgehammer
            start_time = time.time()
            
            try:
                # Mirabelle 命令
                result = subprocess.run(
                    [self.isabelle_path, 'mirabelle',
                     '-A', 'sledgehammer',
                     '-T', str(self.sledgehammer_timeout),
                     '-d', str(temp_path),
                     'Recon_Session'],
                    capture_output=True,
                    text=True,
                    timeout=self.sledgehammer_timeout + 60,
                    cwd=str(temp_path)
                )
                
                execution_time = time.time() - start_time
                output = result.stdout + "\n" + result.stderr
                
                # 检查是否有 proof 输出（"Try this:" 表示找到了 proof）
                has_proof = "Try this:" in output or "Proof found" in output
                
                return {
                    "status": "success" if has_proof else ("error" if result.returncode != 0 else "no_proof"),
                    "output": output,
                    "time": execution_time
                }
                
            except subprocess.TimeoutExpired:
                return {
                    "status": "timeout",
                    "output": "Mirabelle/Sledgehammer timeout",
                    "time": self.sledgehammer_timeout
                }
            except Exception as e:
                return {
                    "status": "error",
                    "output": str(e),
                    "time": time.time() - start_time
                }
    
    def _extract_proofs(self, sledgehammer_output: str) -> List[ProofInfo]:
        """
        从 Sledgehammer 输出中提取所有 proof
        
        Sledgehammer 输出格式示例：
        - "Try this: by metis (fact1 fact2)"
        - "Try this: by smt"
        - "Proof found. (e, 0.5s) by metis"
        
        Returns:
            List[ProofInfo]
        """
        proofs = []
        
        # Pattern 1: "Try this: by <method> (<facts>)"
        pattern1 = r"Try this:\s*by\s+(\w+)\s*(?:\(([^)]+)\))?"
        
        # Pattern 2: "by <method>" (standalone)
        pattern2 = r"(?:Proof found|sledgehammer).*?by\s+(\w+)"
        
        # Pattern 3: 完整的 proof 建议，包含 prover 信息
        pattern3 = r"\((\w+),\s*[\d.]+s?\)\s*Try this:\s*by\s+(\w+)\s*(?:\(([^)]+)\))?"
        
        # 尝试 Pattern 3 (最详细)
        for match in re.finditer(pattern3, sledgehammer_output, re.IGNORECASE):
            prover = match.group(1)
            method = match.group(2)
            facts = match.group(3).split() if match.group(3) else []
            
            proofs.append(ProofInfo(
                proof_text=f"by {method}" + (f" ({match.group(3)})" if match.group(3) else ""),
                proof_method=method,
                lemma_name="unknown",  # 需要从上下文提取
                lemma_statement="",
                prover_used=prover,
                facts_used=facts
            ))
        
        # 如果 Pattern 3 没有匹配，尝试 Pattern 1
        if not proofs:
            for match in re.finditer(pattern1, sledgehammer_output, re.IGNORECASE):
                method = match.group(1)
                facts = match.group(2).split() if match.group(2) else []
                
                proofs.append(ProofInfo(
                    proof_text=f"by {method}" + (f" ({match.group(2)})" if match.group(2) else ""),
                    proof_method=method,
                    lemma_name="unknown",
                    lemma_statement="",
                    facts_used=facts
                ))
        
        # 如果还是没有，尝试 Pattern 2
        if not proofs:
            for match in re.finditer(pattern2, sledgehammer_output, re.IGNORECASE):
                method = match.group(1)
                
                proofs.append(ProofInfo(
                    proof_text=f"by {method}",
                    proof_method=method,
                    lemma_name="unknown",
                    lemma_statement=""
                ))
        
        return proofs
    
    def _test_reconstruction(self, 
                            original_theory: Path,
                            proof_info: ProofInfo) -> Dict:
        """
        测试 proof reconstruction
        
        创建一个新的 theory，将 Sledgehammer 返回的 proof 插入，
        然后运行 Isabelle 验证这个 proof 是否能成功重构。
        
        Args:
            original_theory: 原始 theory 文件
            proof_info: 提取的 proof 信息
            
        Returns:
            {
                "status": "success" | "failed" | "timeout",
                "output": str,
                "error": str,
                "time": float
            }
        """
        theory_content = original_theory.read_text()
        
        # 找到需要验证的 lemma 并替换其 proof
        # 这里我们创建一个简单的测试 theory
        test_theory_content = self._create_reconstruction_test_theory(
            theory_content,
            proof_info
        )
        
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            
            # 创建测试 theory
            test_thy = temp_path / "Reconstruction_Verify.thy"
            test_thy.write_text(test_theory_content)
            
            # 创建 ROOT 文件
            root_content = f'''session Recon_Verify = "HOL" +
  options [timeout = {self.reconstruction_timeout}]
  theories
    Reconstruction_Verify
'''
            root_file = temp_path / "ROOT"
            root_file.write_text(root_content)
            
            # 运行验证
            start_time = time.time()
            
            try:
                result = subprocess.run(
                    [self.isabelle_path, 'build', '-d', str(temp_path),
                     '-v', 'Recon_Verify'],
                    capture_output=True,
                    text=True,
                    timeout=self.reconstruction_timeout + 10
                )
                
                execution_time = time.time() - start_time
                output = result.stdout + "\n" + result.stderr
                
                # 检查是否成功
                if result.returncode == 0:
                    return {
                        "status": "success",
                        "output": output,
                        "error": "",
                        "time": execution_time
                    }
                else:
                    # 提取错误信息
                    error_msg = self._extract_error_message(output)
                    return {
                        "status": "failed",
                        "output": output,
                        "error": error_msg,
                        "time": execution_time
                    }
                    
            except subprocess.TimeoutExpired:
                return {
                    "status": "timeout",
                    "output": "Reconstruction timeout",
                    "error": "Timeout during proof reconstruction",
                    "time": self.reconstruction_timeout
                }
            except Exception as e:
                return {
                    "status": "failed",
                    "output": str(e),
                    "error": str(e),
                    "time": time.time() - start_time
                }
    
    def _create_reconstruction_test_theory(self,
                                           original_content: str,
                                           proof_info: ProofInfo) -> str:
        """
        创建用于测试 reconstruction 的 theory
        
        策略：
        1. 如果原始 theory 有 sledgehammer 调用，替换为实际 proof
        2. 否则创建一个简单的测试 theory
        """
        # 尝试替换 sledgehammer 调用为实际 proof
        modified = re.sub(
            r'sledgehammer\b',
            proof_info.proof_text,
            original_content
        )
        
        # 如果没有变化，说明没有 sledgehammer 调用
        if modified == original_content:
            # 尝试替换 "sorry" 或 "oops"
            modified = re.sub(
                r'\b(sorry|oops)\b',
                proof_info.proof_text,
                original_content
            )
        
        return modified
    
    def _extract_error_message(self, output: str) -> str:
        """从 Isabelle 输出中提取错误信息"""
        error_patterns = [
            r"Error[:\s]+([^\n]+)",
            r"Failed[:\s]+([^\n]+)",
            r"Unable to[:\s]+([^\n]+)",
            r"Type error[:\s]+([^\n]+)",
            r"proof failed[:\s]*([^\n]*)",
        ]
        
        for pattern in error_patterns:
            match = re.search(pattern, output, re.IGNORECASE)
            if match:
                return match.group(0)
        
        # 如果没有匹配，返回最后几行
        lines = output.strip().split('\n')
        return '\n'.join(lines[-5:]) if lines else "Unknown error"
    
    def _classify_reconstruction_failure(self, error_msg: str) -> ReconstructionBugType:
        """
        分类 reconstruction 失败类型
        
        Args:
            error_msg: 错误信息
            
        Returns:
            ReconstructionBugType
        """
        error_lower = error_msg.lower()
        
        # Syntax errors
        if any(kw in error_lower for kw in ['syntax', 'parse', 'lexical']):
            return ReconstructionBugType.SYNTAX_ERROR
        
        # Type errors
        if any(kw in error_lower for kw in ['type', 'mismatch', 'incompatible']):
            return ReconstructionBugType.TYPE_ERROR
        
        # Metis failures
        if 'metis' in error_lower:
            return ReconstructionBugType.METIS_FAILURE
        
        # SMT replay failures
        if any(kw in error_lower for kw in ['smt', 'replay', 'z3', 'cvc']):
            return ReconstructionBugType.SMT_REPLAY_FAILURE
        
        # Timeout
        if 'timeout' in error_lower:
            return ReconstructionBugType.RECONSTRUCTION_TIMEOUT
        
        # General reconstruction failure
        if any(kw in error_lower for kw in ['reconstruct', 'proof failed', 'failed']):
            return ReconstructionBugType.PROOF_RECONSTRUCTION_FAILURE
        
        return ReconstructionBugType.UNKNOWN_ERROR
    
    def _check_hidden_exceptions(self) -> Dict:
        """检查隐藏异常"""
        if not self.hidden_detector:
            return {"found": False, "details": ""}
        
        result = self.hidden_detector.check_for_exceptions()
        return {
            "found": result["found_exceptions"],
            "details": result.get("raw_content", "")[:500] if result["found_exceptions"] else ""
        }
    
    def batch_test(self, 
                   theory_files: List[str],
                   output_file: Optional[str] = None) -> Dict:
        """
        批量测试多个 theory 文件
        
        Args:
            theory_files: Theory 文件列表
            output_file: 输出 JSON 文件路径
            
        Returns:
            统计信息
        """
        logger.info(f"📊 开始批量测试 {len(theory_files)} 个 theories")
        
        results = {
            "total": len(theory_files),
            "success": 0,
            "bugs_found": 0,
            "no_proof": 0,
            "errors": 0,
            "bug_details": [],
            "test_results": []
        }
        
        for i, theory_file in enumerate(theory_files, 1):
            logger.info(f"[{i}/{len(theory_files)}] {Path(theory_file).name}")
            
            try:
                result = self.test_theory(theory_file)
                
                if result.bug_found:
                    results["bugs_found"] += 1
                    results["bug_details"].append({
                        "theory": theory_file,
                        "bug_type": result.bug_type.value if result.bug_type else "unknown",
                        "error": result.reconstruction_error
                    })
                elif result.status == ReconstructionStatus.RECONSTRUCTION_SUCCESS:
                    results["success"] += 1
                elif result.status == ReconstructionStatus.NO_PROOF_FOUND:
                    results["no_proof"] += 1
                else:
                    results["errors"] += 1
                
                results["test_results"].append({
                    "theory": theory_file,
                    "status": result.status.value,
                    "bug_found": result.bug_found,
                    "bug_type": result.bug_type.value if result.bug_type else None,
                    "proofs_found": result.proofs_found
                })
                
            except Exception as e:
                logger.error(f"   ❌ 测试异常: {e}")
                results["errors"] += 1
        
        # 保存结果
        if output_file:
            with open(output_file, 'w') as f:
                json.dump(results, f, indent=2)
            logger.info(f"✅ 结果已保存: {output_file}")
        
        # 打印摘要
        logger.info(f"""
╔═══════════════════════════════════════════════════════════╗
║       Proof Reconstruction Test Results                  ║
╠═══════════════════════════════════════════════════════════╣
║  Total theories tested:    {results['total']:4d}                        ║
║  Reconstruction success:   {results['success']:4d}                        ║
║  No proof found:           {results['no_proof']:4d}                        ║
║  🐛 Reconstruction bugs:    {results['bugs_found']:4d}                        ║
║  Errors:                   {results['errors']:4d}                        ║
╚═══════════════════════════════════════════════════════════╝
        """)
        
        return results


def main():
    """命令行入口"""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Proof Reconstruction Bug Tester"
    )
    parser.add_argument(
        "--theory", "-t",
        help="Single theory file to test"
    )
    parser.add_argument(
        "--dir", "-d",
        help="Directory containing theory files"
    )
    parser.add_argument(
        "--output", "-o",
        help="Output JSON file"
    )
    parser.add_argument(
        "--sledgehammer-timeout",
        type=int,
        default=60,
        help="Sledgehammer timeout (seconds)"
    )
    parser.add_argument(
        "--reconstruction-timeout",
        type=int,
        default=30,
        help="Reconstruction timeout (seconds)"
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
    
    # 创建测试器
    tester = ProofReconstructionTester(
        sledgehammer_timeout=args.sledgehammer_timeout,
        reconstruction_timeout=args.reconstruction_timeout
    )
    
    if args.theory:
        # 测试单个 theory
        result = tester.test_theory(args.theory)
        print(f"\nResult: {result.status.value}")
        if result.bug_found:
            print(f"🐛 Bug found: {result.bug_type.value}")
            print(f"   Error: {result.reconstruction_error}")
    
    elif args.dir:
        # 测试目录中的所有 theory
        theory_dir = Path(args.dir)
        theory_files = list(theory_dir.glob("*.thy"))
        
        if not theory_files:
            print(f"No .thy files found in {args.dir}")
            return
        
        results = tester.batch_test(
            [str(f) for f in theory_files],
            output_file=args.output
        )
        
        if results["bugs_found"] > 0:
            print("\n🐛 Bugs found:")
            for bug in results["bug_details"]:
                print(f"  - {bug['theory']}: {bug['bug_type']}")
    
    else:
        parser.print_help()


if __name__ == "__main__":
    main()

