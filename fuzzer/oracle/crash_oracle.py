#!/usr/bin/env python3
"""
Crash/Hang Oracle
检测prover进程崩溃或超时
"""

import subprocess
import signal
import time
import os
from typing import Dict, Optional, List
from dataclasses import dataclass
from enum import Enum


class OracleResult(Enum):
    """Oracle检测结果"""
    NORMAL = "normal"           # 正常运行
    CRASH = "crash"             # 崩溃
    TIMEOUT = "timeout"         # 超时
    ERROR = "error"             # 错误输出
    UNKNOWN = "unknown"         # 未知状态


@dataclass
class ProverResult:
    """Prover运行结果"""
    status: OracleResult
    stdout: str = ""
    stderr: str = ""
    exit_code: int = -1
    execution_time: float = 0.0
    error_message: str = ""


class CrashOracle:
    """Crash/Hang Oracle实现"""
    
    def __init__(self, timeout: float = 5.0):
        """
        初始化Oracle
        
        Args:
            timeout: 超时时间（秒）
        """
        self.timeout = timeout
    
    def check(self, prover_path: str, input_file: str, args: List[str] = None) -> ProverResult:
        """
        检查prover运行结果
        
        Args:
            prover_path: prover可执行文件路径
            input_file: 输入文件路径
            args: prover额外参数
            
        Returns:
            ProverResult对象
        """
        if args is None:
            args = []
        
        if not os.path.exists(prover_path):
            return ProverResult(
                status=OracleResult.ERROR,
                error_message=f"Prover不存在: {prover_path}"
            )
        
        if not os.path.exists(input_file):
            return ProverResult(
                status=OracleResult.ERROR,
                error_message=f"输入文件不存在: {input_file}"
            )
        
        # 构建命令
        cmd = [prover_path] + args + [input_file]
        
        start_time = time.time()
        
        try:
            # 运行prover
            process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                preexec_fn=os.setsid if hasattr(os, 'setsid') else None
            )
            
            try:
                # 等待进程完成或超时
                stdout, stderr = process.communicate(timeout=self.timeout)
                execution_time = time.time() - start_time
                exit_code = process.returncode
                
                # 判断结果
                if exit_code == 0:
                    status = OracleResult.NORMAL
                elif exit_code < 0:
                    # 被信号终止（可能是崩溃）
                    status = OracleResult.CRASH
                else:
                    # 非零退出码
                    status = OracleResult.ERROR
                
                return ProverResult(
                    status=status,
                    stdout=stdout,
                    stderr=stderr,
                    exit_code=exit_code,
                    execution_time=execution_time
                )
            
            except subprocess.TimeoutExpired:
                # 超时
                execution_time = time.time() - start_time
                
                # 终止进程组
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                except (OSError, ProcessLookupError, AttributeError) as e:
                    # 如果进程组终止失败，尝试直接终止进程
                    # 这可能发生在进程已经结束或进程组不存在的情况下
                    try:
                        process.kill()
                    except ProcessLookupError:
                        # 进程已经不存在，忽略
                        pass
                
                process.wait()
                
                return ProverResult(
                    status=OracleResult.TIMEOUT,
                    execution_time=execution_time,
                    error_message=f"Prover超时（>{self.timeout}秒）"
                )
        
        except Exception as e:
            # 其他异常（可能是崩溃）
            execution_time = time.time() - start_time
            
            return ProverResult(
                status=OracleResult.CRASH,
                execution_time=execution_time,
                error_message=str(e)
            )
    
    def is_bug(self, result: ProverResult) -> bool:
        """
        判断结果是否触发bug
        
        Args:
            result: ProverResult对象
            
        Returns:
            True如果触发bug（crash或timeout）
        """
        return result.status in [OracleResult.CRASH, OracleResult.TIMEOUT]


def main():
    """测试函数"""
    oracle = CrashOracle(timeout=5.0)
    
    # 测试Z3
    z3_path = "z3"
    test_file = "../sledgehammer_export/prob4729480_1.p"
    
    if os.path.exists(test_file):
        print(f"测试Crash Oracle:")
        print(f"Prover: {z3_path}")
        print(f"输入文件: {test_file}")
        print()
        
        result = oracle.check(z3_path, test_file)
        
        print(f"状态: {result.status.value}")
        print(f"执行时间: {result.execution_time:.2f}秒")
        print(f"退出码: {result.exit_code}")
        
        if result.error_message:
            print(f"错误信息: {result.error_message}")
        
        print(f"触发bug: {oracle.is_bug(result)}")
    else:
        print(f"测试文件不存在: {test_file}")


if __name__ == "__main__":
    main()

