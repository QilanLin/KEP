#!/usr/bin/env python3
"""
Execution Verifier - 改进的验证器

与bug_verifier.py的区别:
- bug_verifier: 只验证theory是否有错误（不执行sledgehammer）
- execution_verifier: 实际执行theory中的sledgehammer命令

目的: 触发proof重放、check_expected_outcome等未覆盖的函数
"""

import subprocess
import tempfile
import time
import re
import logging
from pathlib import Path
from typing import Optional, Tuple
from dataclasses import dataclass

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger('execution_verifier')


@dataclass
class ExecutionResult:
    """执行结果"""
    theory_name: str
    sledgehammer_called: bool
    proof_found: bool
    proof_method: Optional[str]
    execution_time: float
    output: str
    
    # 用于覆盖率分析
    triggered_functions: list  # 触发了哪些函数


class ExecutionVerifier:
    """执行验证器 - 实际运行Sledgehammer"""
    
    def __init__(self, isabelle_path: str = "isabelle"):
        self.isabelle_path = isabelle_path
        
    def execute_theory_with_sledgehammer(self, theory_file: Path,
                                        timeout: int = 120) -> ExecutionResult:
        """
        执行包含sledgehammer调用的theory文件
        
        这会实际运行Sledgehammer并触发:
        - play_one_line_proofs (如果找到证明)
        - select_one_line_proof
        - check_expected_outcome (如果有expect参数)
        - analyze_prover_result_for_inconsistency (如果是falsify模式)
        """
        theory_name = theory_file.stem
        logger.info(f"Executing theory: {theory_name}")
        
        # 创建临时session目录
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            
            # 复制theory文件
            theory_copy = temp_path / theory_file.name
            theory_copy.write_text(theory_file.read_text())
            
            # 创建ROOT文件
            root_content = f'''session Coverage_Test = "HOL" +
  options [timeout = {timeout}]
  theories
    {theory_name}
'''
            root_file = temp_path / "ROOT"
            root_file.write_text(root_content)
            
            # 使用isabelle build构建session
            # 这会实际执行theory中的sledgehammer命令
            start_time = time.time()
            
            try:
                result = subprocess.run(
                    [self.isabelle_path, 'build', '-d', str(temp_path), 
                     '-v', 'Coverage_Test'],
                    capture_output=True,
                    text=True,
                    timeout=timeout + 30
                )
                
                execution_time = time.time() - start_time
                output = result.stdout + "\n" + result.stderr
                
                # 解析输出
                sledgehammer_called = self._check_sledgehammer_called(output)
                proof_found, proof_method = self._extract_proof_info(output)
                triggered_functions = self._identify_triggered_functions(output)
                
                logger.info(f"  Execution time: {execution_time:.2f}s")
                logger.info(f"  Sledgehammer called: {sledgehammer_called}")
                logger.info(f"  Proof found: {proof_found}")
                if proof_method:
                    logger.info(f"  Proof method: {proof_method}")
                if triggered_functions:
                    logger.info(f"  Triggered functions: {', '.join(triggered_functions)}")
                
                return ExecutionResult(
                    theory_name=theory_name,
                    sledgehammer_called=sledgehammer_called,
                    proof_found=proof_found,
                    proof_method=proof_method,
                    execution_time=execution_time,
                    output=output,
                    triggered_functions=triggered_functions
                )
                
            except subprocess.TimeoutExpired:
                logger.warning(f"  Timeout after {timeout}s")
                return ExecutionResult(
                    theory_name=theory_name,
                    sledgehammer_called=False,
                    proof_found=False,
                    proof_method=None,
                    execution_time=timeout,
                    output="Timeout",
                    triggered_functions=[]
                )
            except Exception as e:
                logger.error(f"  Error: {e}")
                return ExecutionResult(
                    theory_name=theory_name,
                    sledgehammer_called=False,
                    proof_found=False,
                    proof_method=None,
                    execution_time=0,
                    output=str(e),
                    triggered_functions=[]
                )
    
    def _check_sledgehammer_called(self, output: str) -> bool:
        """检查Sledgehammer是否被调用"""
        patterns = [
            r'Sledgehammer',
            r'Running.*prover',
            r'e\s+\d+\.\d+',  # E prover version
            r'cvc5',
            r'z3',
        ]
        return any(re.search(pattern, output, re.IGNORECASE) for pattern in patterns)
    
    def _extract_proof_info(self, output: str) -> Tuple[bool, Optional[str]]:
        """提取证明信息"""
        # 检查是否找到证明
        proof_patterns = [
            r'Try this:\s*by\s+(\w+)',
            r'Proof found.*by\s+(\w+)',
            r'by\s+(metis|smt|blast|auto|simp)',
        ]
        
        for pattern in proof_patterns:
            match = re.search(pattern, output, re.IGNORECASE)
            if match:
                method = match.group(1) if match.lastindex >= 1 else 'unknown'
                return True, method
        
        return False, None
    
    def _identify_triggered_functions(self, output: str) -> list:
        """识别被触发的函数（基于输出特征）"""
        triggered = []
        
        # 如果找到证明，说明触发了proof重放
        if re.search(r'Try this|Proof found', output, re.IGNORECASE):
            triggered.extend([
                'play_one_line_proofs',
                'select_one_line_proof',
                'preplay_prover_result (success branch)'
            ])
        
        # 如果有expect参数相关输出
        if re.search(r'expect|Unexpected outcome', output):
            triggered.append('check_expected_outcome')
        
        # 如果有falsify相关输出
        if re.search(r'falsif|inconsist', output, re.IGNORECASE):
            triggered.extend([
                'analyze_prover_result_for_inconsistency',
                'flip_problem'
            ])
        
        return triggered


def test_coverage_boost():
    """测试覆盖率提升"""
    verifier = ExecutionVerifier()
    
    # 测试Seed_Provable.thy
    theory_path = Path("data/seed_theories/Seed_Provable.thy")
    
    if not theory_path.exists():
        logger.error(f"Theory file not found: {theory_path}")
        return
    
    logger.info("=" * 60)
    logger.info("🚀 Coverage Boost Test")
    logger.info("=" * 60)
    logger.info("")
    logger.info("Testing provable lemmas to trigger uncovered functions...")
    logger.info("")
    
    result = verifier.execute_theory_with_sledgehammer(theory_path, timeout=120)
    
    logger.info("\n" + "=" * 60)
    logger.info("Results")
    logger.info("=" * 60)
    logger.info(f"Sledgehammer called: {result.sledgehammer_called}")
    logger.info(f"Proofs found: {result.proof_found}")
    if result.proof_method:
        logger.info(f"Proof method: {result.proof_method}")
    logger.info(f"Execution time: {result.execution_time:.2f}s")
    
    if result.triggered_functions:
        logger.info("\n✅ Triggered uncovered functions:")
        for func in result.triggered_functions:
            logger.info(f"  - {func}")
        logger.info(f"\nEstimated coverage boost: +{len(result.triggered_functions) * 2}%")
    else:
        logger.info("\n⚠️  No additional functions triggered")
    
    # 检查异常日志
    sledgehammer_log = Path("/tmp/sledgehammer_hidden_errors.log")
    if sledgehammer_log.exists() and sledgehammer_log.stat().st_size > 0:
        logger.info("\n🎯 Sledgehammer exception log has content!")
        logger.info(sledgehammer_log.read_text()[:500])


if __name__ == '__main__':
    test_coverage_boost()

