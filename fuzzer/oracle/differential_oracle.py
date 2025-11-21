#!/usr/bin/env python3
"""
Differential Oracle
比较多个prover的输出，检测不一致
"""

import re
from typing import List, Dict, Set
from dataclasses import dataclass
from enum import Enum

# Import from crash_oracle (handle both relative and absolute imports)
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from crash_oracle import ProverResult, OracleResult


class ProverStatus(Enum):
    """Prover输出状态"""
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
    ERROR = "error"
    TIMEOUT = "timeout"
    CRASH = "crash"


@dataclass
class DifferentialResult:
    """差异检测结果"""
    is_differential: bool
    prover_results: Dict[str, ProverStatus]
    error_message: str = ""


class DifferentialOracle:
    """Differential Oracle实现"""
    
    def __init__(self):
        """初始化Oracle"""
        self.status_patterns = {
            ProverStatus.SAT: [r'\bsat\b', r'\bSatisfiable\b', r'\bSAT\b'],
            ProverStatus.UNSAT: [r'\bunsat\b', r'\bUnsatisfiable\b', r'\bUNSAT\b'],
            ProverStatus.UNKNOWN: [r'\bunknown\b', r'\bUnknown\b', r'\bUNKNOWN\b'],
        }
    
    def extract_status(self, result: ProverResult) -> ProverStatus:
        """
        从prover输出中提取状态
        
        Args:
            result: ProverResult对象
            
        Returns:
            ProverStatus
        """
        # 先检查异常状态
        if result.status == OracleResult.CRASH:
            return ProverStatus.CRASH
        if result.status == OracleResult.TIMEOUT:
            return ProverStatus.TIMEOUT
        if result.status == OracleResult.ERROR:
            return ProverStatus.ERROR
        
        # 从输出中提取状态
        output = (result.stdout + result.stderr).lower()
        
        for status, patterns in self.status_patterns.items():
            for pattern in patterns:
                if re.search(pattern, output, re.IGNORECASE):
                    return status
        
        return ProverStatus.UNKNOWN
    
    def check(self, results: Dict[str, ProverResult]) -> DifferentialResult:
        """
        检查多个prover结果的差异
        
        Args:
            results: {prover_name: ProverResult}字典
            
        Returns:
            DifferentialResult对象
        """
        if len(results) < 2:
            return DifferentialResult(
                is_differential=False,
                prover_results={},
                error_message="需要至少2个prover结果"
            )
        
        # 提取每个prover的状态
        prover_statuses = {}
        for prover_name, result in results.items():
            prover_statuses[prover_name] = self.extract_status(result)
        
        # 检查差异：只关注SAT vs UNSAT的不一致
        sat_results = set()
        unsat_results = set()
        
        for prover_name, status in prover_statuses.items():
            if status == ProverStatus.SAT:
                sat_results.add(prover_name)
            elif status == ProverStatus.UNSAT:
                unsat_results.add(prover_name)
        
        # 如果同时有SAT和UNSAT结果，则触发差异
        is_differential = len(sat_results) > 0 and len(unsat_results) > 0
        
        return DifferentialResult(
            is_differential=is_differential,
            prover_results=prover_statuses,
            error_message=f"SAT: {sat_results}, UNSAT: {unsat_results}" if is_differential else ""
        )
    
    def is_bug(self, result: DifferentialResult) -> bool:
        """
        判断结果是否触发bug
        
        Args:
            result: DifferentialResult对象
            
        Returns:
            True如果检测到差异
        """
        return result.is_differential


def main():
    """测试函数"""
    oracle = DifferentialOracle()
    
    # 模拟测试结果
    from crash_oracle import OracleResult as OR
    
    results = {
        "z3": ProverResult(
            status=OR.NORMAL,
            stdout="sat",
            exit_code=0
        ),
        "cvc5": ProverResult(
            status=OR.NORMAL,
            stdout="unsat",
            exit_code=0
        )
    }
    
    print("测试Differential Oracle:")
    print(f"Z3输出: {results['z3'].stdout}")
    print(f"cvc5输出: {results['cvc5'].stdout}")
    print()
    
    diff_result = oracle.check(results)
    
    print(f"检测到差异: {diff_result.is_differential}")
    print(f"Prover状态: {diff_result.prover_results}")
    
    if diff_result.is_differential:
        print(f"⚠️  触发bug: {diff_result.error_message}")


if __name__ == "__main__":
    main()

