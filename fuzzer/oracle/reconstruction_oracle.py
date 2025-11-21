#!/usr/bin/env python3
"""
重构Oracle
检测证明重构失败（prover找到证明但Isabelle无法重构）
"""

import re
import subprocess
import time
from typing import Dict, Optional, List
from dataclasses import dataclass
from enum import Enum
from pathlib import Path


class ReconstructionStatus(Enum):
    """重构状态"""
    SUCCESS = "success"           # 重构成功
    FAILURE = "failure"           # 重构失败
    TIMEOUT = "timeout"           # 重构超时
    ERROR = "error"               # 重构错误
    NOT_ATTEMPTED = "not_attempted"  # 未尝试重构


class FailureType(Enum):
    """失败类型"""
    SYNTAX_ERROR = "syntax_error"     # 语法错误
    TYPE_ERROR = "type_error"         # 类型错误
    PROOF_RECONSTRUCTION = "proof_reconstruction"  # 证明重构失败
    TIMEOUT = "timeout"               # 超时
    UNKNOWN = "unknown"               # 未知错误


@dataclass
class ProverResult:
    """Prover结果"""
    status: str  # sat, unsat, unknown
    proof: Optional[str] = None
    model: Optional[str] = None
    error: Optional[str] = None


@dataclass
class ReconstructionResult:
    """重构结果"""
    status: ReconstructionStatus
    failure_type: Optional[FailureType] = None
    error_message: Optional[str] = None
    execution_time: float = 0.0
    isabelle_output: Optional[str] = None
    reconstruction_attempted: bool = False


class ReconstructionOracle:
    """重构Oracle"""
    
    def __init__(self, isabelle_path: str = "isabelle", timeout: float = 30.0):
        """
        初始化重构Oracle
        
        Args:
            isabelle_path: Isabelle可执行文件路径
            timeout: 重构超时时间（秒）
        """
        self.isabelle_path = isabelle_path
        self.timeout = timeout
        
        # 错误模式（用于分类失败类型）
        self.error_patterns = {
            FailureType.SYNTAX_ERROR: [
                r'syntax error',
                r'parse error',
                r'lexical error',
                r'unexpected token',
                r'malformed'
            ],
            FailureType.TYPE_ERROR: [
                r'type error',
                r'type mismatch',
                r'cannot unify',
                r'type checking failed'
            ],
            FailureType.PROOF_RECONSTRUCTION: [
                r'reconstruction failed',
                r'proof reconstruction failed',
                r'failed to reconstruct',
                r'cannot replay proof',
                r'sledgehammer.*failed'
            ],
            FailureType.TIMEOUT: [
                r'timeout',
                r'timed out',
                r'exceeded time limit'
            ]
        }
    
    def check(self, prover_result: ProverResult, original_thy_file: str, 
              mutant_file: str) -> ReconstructionResult:
        """
        检查证明重构是否成功
        
        Args:
            prover_result: Prover的执行结果
            original_thy_file: 原始的Isabelle理论文件路径
            mutant_file: 变异后的TPTP文件路径
        
        Returns:
            重构结果
        """
        start_time = time.time()
        
        # 如果prover没有找到证明（UNSAT或UNKNOWN），不需要重构
        if prover_result.status != "sat" and prover_result.proof is None:
            return ReconstructionResult(
                status=ReconstructionStatus.NOT_ATTEMPTED,
                reconstruction_attempted=False,
                execution_time=time.time() - start_time
            )
        
        # 尝试在Isabelle中重构证明
        try:
            result = self._attempt_reconstruction(
                prover_result, original_thy_file, mutant_file
            )
            result.execution_time = time.time() - start_time
            return result
        except Exception as e:
            return ReconstructionResult(
                status=ReconstructionStatus.ERROR,
                failure_type=FailureType.UNKNOWN,
                error_message=str(e),
                execution_time=time.time() - start_time,
                reconstruction_attempted=True
            )
    
    def _attempt_reconstruction(self, prover_result: ProverResult,
                                 original_thy_file: str, mutant_file: str) -> ReconstructionResult:
        """
        尝试在Isabelle中重构证明
        
        Args:
            prover_result: Prover结果
            original_thy_file: 原始理论文件
            mutant_file: 变异文件
        
        Returns:
            重构结果
        """
        # 创建临时的Isabelle理论文件用于重构
        temp_thy_file = self._create_reconstruction_file(
            original_thy_file, prover_result, mutant_file
        )
        
        if not temp_thy_file:
            return ReconstructionResult(
                status=ReconstructionStatus.ERROR,
                failure_type=FailureType.UNKNOWN,
                error_message="Failed to create reconstruction file",
                reconstruction_attempted=True
            )
        
        try:
            # 使用Isabelle CLI尝试重构
            cmd = [
                self.isabelle_path,
                "process",
                "-T",
                str(temp_thy_file.stem),
                "-d",
                str(temp_thy_file.parent)
            ]
            
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=self.timeout
            )
            
            try:
                stdout, stderr = process.communicate(timeout=self.timeout)
                exit_code = process.returncode
                
                # 分析输出
                isabelle_output = stdout + stderr
                
                # 检查是否成功
                if exit_code == 0 and "proof" in isabelle_output.lower():
                    # 检查是否有失败信息
                    if self._check_failure_patterns(isabelle_output):
                        failure_type = self._classify_failure(isabelle_output)
                        return ReconstructionResult(
                            status=ReconstructionStatus.FAILURE,
                            failure_type=failure_type,
                            error_message=self._extract_error_message(isabelle_output),
                            isabelle_output=isabelle_output,
                            reconstruction_attempted=True
                        )
                    else:
                        return ReconstructionResult(
                            status=ReconstructionStatus.SUCCESS,
                            isabelle_output=isabelle_output,
                            reconstruction_attempted=True
                        )
                else:
                    # 重构失败
                    failure_type = self._classify_failure(isabelle_output)
                    return ReconstructionResult(
                        status=ReconstructionStatus.FAILURE,
                        failure_type=failure_type,
                        error_message=self._extract_error_message(isabelle_output),
                        isabelle_output=isabelle_output,
                        reconstruction_attempted=True
                    )
                    
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
                return ReconstructionResult(
                    status=ReconstructionStatus.TIMEOUT,
                    failure_type=FailureType.TIMEOUT,
                    error_message="Reconstruction timeout",
                    reconstruction_attempted=True
                )
        
        finally:
            # 清理临时文件
            if temp_thy_file.exists():
                temp_thy_file.unlink()
    
    def _create_reconstruction_file(self, original_thy_file: str,
                                     prover_result: ProverResult,
                                     mutant_file: str) -> Optional[Path]:
        """
        创建用于重构的临时Isabelle理论文件
        
        Args:
            original_thy_file: 原始理论文件路径
            prover_result: Prover结果
            mutant_file: 变异文件路径
        
        Returns:
            临时文件路径或None
        """
        try:
            # 读取原始理论文件
            with open(original_thy_file, 'r', encoding='utf-8') as f:
                original_content = f.read()
            
            # 创建临时文件
            temp_dir = Path(mutant_file).parent / "reconstruction"
            temp_dir.mkdir(parents=True, exist_ok=True)
            
            temp_thy_file = temp_dir / f"recon_{Path(mutant_file).stem}.thy"
            
            # 修改理论文件以包含prover结果
            # 这里简化处理，实际需要更复杂的集成
            reconstruction_content = f"""
theory Recon_{Path(mutant_file).stem}
imports Main
begin

(* Reconstruction attempt for mutant: {Path(mutant_file).name} *)
(* Prover result: {prover_result.status} *)
(* Proof: {prover_result.proof[:200] if prover_result.proof else "None"} *)

{original_content}

end
"""
            
            with open(temp_thy_file, 'w', encoding='utf-8') as f:
                f.write(reconstruction_content)
            
            return temp_thy_file
        
        except Exception as e:
            # 创建重构文件失败（使用warnings而不是print）
            # Note: 在生产代码中应使用logger，这里使用warnings避免循环依赖
            import warnings
            warnings.warn(f"Error creating reconstruction file: {e}", RuntimeWarning)
            return None
    
    def _check_failure_patterns(self, output: str) -> bool:
        """
        检查输出中是否包含失败模式
        
        Args:
            output: Isabelle输出
        
        Returns:
            是否包含失败模式
        """
        for failure_type, patterns in self.error_patterns.items():
            for pattern in patterns:
                if re.search(pattern, output, re.IGNORECASE):
                    return True
        return False
    
    def _classify_failure(self, output: str) -> FailureType:
        """
        分类失败类型
        
        Args:
            output: Isabelle输出
        
        Returns:
            失败类型
        """
        for failure_type, patterns in self.error_patterns.items():
            for pattern in patterns:
                if re.search(pattern, output, re.IGNORECASE):
                    return failure_type
        
        return FailureType.UNKNOWN
    
    def _extract_error_message(self, output: str) -> str:
        """
        提取错误消息
        
        Args:
            output: Isabelle输出
        
        Returns:
            错误消息
        """
        # 查找错误行
        error_lines = []
        lines = output.split('\n')
        
        for line in lines:
            if any(keyword in line.lower() for keyword in ['error', 'failed', 'failed to', 'cannot']):
                error_lines.append(line.strip())
        
        if error_lines:
            return '\n'.join(error_lines[:5])  # 返回前5行错误
        
        return "Unknown error"
    
    def is_bug(self, result: ReconstructionResult) -> bool:
        """
        检查是否是bug（重构失败）
        
        Args:
            result: 重构结果
        
        Returns:
            是否是bug
        """
        return result.status == ReconstructionStatus.FAILURE

