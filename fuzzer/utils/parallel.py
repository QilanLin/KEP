#!/usr/bin/env python3
"""
并行处理工具
支持多进程并行测试变异体
"""

import os
import multiprocessing
from typing import List, Dict, Callable, Any, Tuple
from pathlib import Path
import time
import shutil

# 修复：确保在Windows上使用spawn而不是fork
if hasattr(multiprocessing, 'set_start_method'):
    try:
        multiprocessing.set_start_method('spawn', force=True)
    except RuntimeError:
        pass  # 如果已经设置过，忽略错误


def _worker_test_mutant(args: Tuple) -> Dict[str, Any]:
    """
    工作进程函数：测试单个变异体
    
    Args:
        args: 元组包含 (mutant_file, prover_paths, timeout, seed_name, mutant_id)
    
    Returns:
        测试结果字典
    """
    import sys
    import os
    # 添加项目路径以便导入模块
    worker_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if worker_dir not in sys.path:
        sys.path.insert(0, worker_dir)
    
    mutant_file, prover_paths, timeout, seed_name, mutant_id = args
    
    try:
        # 延迟导入以避免序列化问题
        from oracle.crash_oracle import CrashOracle
        from oracle.differential_oracle import DifferentialOracle
        
        crash_oracle = CrashOracle(timeout=timeout)
        diff_oracle = DifferentialOracle()
        
        start_time = time.time()
        results = {}
        
        # 测试每个prover
        for prover_name, prover_path in prover_paths.items():
            result = crash_oracle.check(prover_path, str(mutant_file))
            results[prover_name] = result
        
        # 检查差异
        diff_result = diff_oracle.check(results)
        
        execution_time = time.time() - start_time
        
        # 检查是否有bug
        has_crash = any(
            crash_oracle.is_bug(r) and r.status.value == 'crash'
            for r in results.values()
        )
        has_timeout = any(
            crash_oracle.is_bug(r) and r.status.value == 'timeout'
            for r in results.values()
        )
        has_differential = diff_oracle.is_bug(diff_result)
        
        return {
            'seed_name': seed_name,
            'mutant_id': mutant_id,
            'status': 'success',
            'has_crash': has_crash,
            'has_timeout': has_timeout,
            'has_differential': has_differential,
            'results': results,
            'diff_result': diff_result,
            'execution_time': execution_time
        }
    except Exception as e:
        return {
            'seed_name': seed_name,
            'mutant_id': mutant_id,
            'status': 'error',
            'error': str(e),
            'execution_time': 0.0
        }


class ParallelTestRunner:
    """并行测试运行器"""
    
    def __init__(self, num_workers: int = None, timeout: float = 5.0):
        """
        初始化并行测试运行器
        
        Args:
            num_workers: 工作进程数（None表示使用CPU核心数）
            timeout: 每个测试的超时时间
        """
        if num_workers is None:
            num_workers = max(1, multiprocessing.cpu_count() - 1)
        
        self.num_workers = num_workers
        self.timeout = timeout
        self.prover_paths = self._detect_provers()
    
    def _detect_provers(self) -> Dict[str, str]:
        """检测可用的provers"""
        provers = {}
        
        z3_path = shutil.which('z3')
        if z3_path:
            provers['z3'] = z3_path
        
        cvc5_path = shutil.which('cvc5')
        if cvc5_path:
            provers['cvc5'] = cvc5_path
        
        return provers
    
    def run_parallel_tests(
        self,
        test_cases: List[Tuple[Path, str, int]]
    ) -> List[Dict[str, Any]]:
        """
        并行运行测试
        
        Args:
            test_cases: 测试用例列表，每个元素是 (mutant_file, seed_name, mutant_id)
        
        Returns:
            测试结果列表
        """
        if not self.prover_paths:
            raise RuntimeError("未找到任何prover")
        
        # 准备参数
        args_list = [
            (mutant_file, self.prover_paths, self.timeout, seed_name, mutant_id)
            for mutant_file, seed_name, mutant_id in test_cases
        ]
        
        # 使用进程池并行执行
        with multiprocessing.Pool(processes=self.num_workers) as pool:
            results = pool.map(_worker_test_mutant, args_list)
        
        return results

