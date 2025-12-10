#!/usr/bin/env python3
"""
统一的 Isabelle 测试运行器基类

提供统一的 Isabelle 测试接口，包括：
- Isabelle/Mirabelle 进程管理
- 隐藏异常检测
- 结果解析
- 日志管理
- 超时处理

所有测试脚本都可以继承这个基类来减少重复代码。

使用方法：
    from isabelle_test_runner import IsabelleTestRunner, TestResult
    
    class MyTester(IsabelleTestRunner):
        def run_test(self, test_case):
            # 自定义测试逻辑
            result = self.run_mirabelle(theory_path)
            return result
"""

import subprocess
import tempfile
import time
import logging
import json
from abc import ABC, abstractmethod
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Optional, List, Dict, Any
from datetime import datetime

from config import (
    Config, get_config,
    DEFAULT_SLEDGEHAMMER_TIMEOUT,
    DEFAULT_MIRABELLE_TIMEOUT,
    DEFAULT_PROCESS_TIMEOUT,
    ISABELLE_BIN
)
from hidden_exception_detector import HiddenExceptionDetector

logger = logging.getLogger(__name__)


@dataclass
class TestResult:
    """通用测试结果"""
    test_name: str
    success: bool
    duration: float
    output: str
    error: str
    hidden_exception: str = ""
    metadata: Dict[str, Any] = None
    
    def to_dict(self) -> dict:
        """转换为字典"""
        return asdict(self)


class IsabelleTestRunner(ABC):
    """
    Isabelle 测试运行器基类
    
    提供统一的测试接口和工具方法。
    """
    
    def __init__(self, 
                 output_dir: str = "results",
                 isabelle_path: str = None,
                 sledgehammer_timeout: int = None,
                 mirabelle_timeout: int = None):
        """
        初始化测试运行器
        
        Args:
            output_dir: 结果输出目录
            isabelle_path: Isabelle 可执行文件路径
            sledgehammer_timeout: Sledgehammer 超时（秒）
            mirabelle_timeout: Mirabelle 超时（秒）
        """
        self.config = get_config()
        
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.isabelle_path = isabelle_path or ISABELLE_BIN
        self.sledgehammer_timeout = sledgehammer_timeout or DEFAULT_SLEDGEHAMMER_TIMEOUT
        self.mirabelle_timeout = mirabelle_timeout or DEFAULT_MIRABELLE_TIMEOUT
        
        # 初始化隐藏异常检测器
        self.hidden_detector = HiddenExceptionDetector()
        
        # 结果列表
        self.results: List[TestResult] = []
        
        # 统计信息
        self.stats = {
            'total_tests': 0,
            'passed': 0,
            'failed': 0,
            'hidden_exceptions': 0,
            'total_time': 0.0
        }
        
        logger.info(f"✅ {self.__class__.__name__} 初始化")
        logger.info(f"   输出目录: {self.output_dir}")
        logger.info(f"   Isabelle: {self.isabelle_path}")
    
    # ============================================
    # 抽象方法 - 子类必须实现
    # ============================================
    
    @abstractmethod
    def run_test(self, test_case: Any) -> TestResult:
        """
        运行单个测试
        
        Args:
            test_case: 测试用例
            
        Returns:
            TestResult: 测试结果
        """
        pass
    
    # ============================================
    # 通用工具方法
    # ============================================
    
    def run_isabelle_process(self, 
                            theory_path: str,
                            timeout: int = None) -> TestResult:
        """
        运行 Isabelle process 命令
        
        Args:
            theory_path: Theory 文件路径
            timeout: 超时时间
            
        Returns:
            TestResult: 测试结果
        """
        timeout = timeout or DEFAULT_PROCESS_TIMEOUT
        
        # 清空隐藏异常日志
        self.hidden_detector.clear_logs()
        
        start_time = time.time()
        hidden_exception = ""
        
        try:
            result = subprocess.run(
                [self.isabelle_path, 'process', '-T', theory_path],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            duration = time.time() - start_time
            
            # 检查隐藏异常
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                hidden_exception = hidden_result["raw_content"][:500]
                self.stats['hidden_exceptions'] += hidden_result["exception_count"]
                logger.warning(f"🔴 发现隐藏异常: {hidden_result['exception_count']} 个")
            
            return TestResult(
                test_name=Path(theory_path).stem,
                success=result.returncode == 0,
                duration=duration,
                output=result.stdout,
                error=result.stderr,
                hidden_exception=hidden_exception
            )
            
        except subprocess.TimeoutExpired:
            # 即使超时也检查隐藏异常
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                hidden_exception = hidden_result["raw_content"][:500]
            
            return TestResult(
                test_name=Path(theory_path).stem,
                success=False,
                duration=timeout,
                output="",
                error="Process timeout",
                hidden_exception=hidden_exception
            )
            
        except Exception as e:
            return TestResult(
                test_name=Path(theory_path).stem,
                success=False,
                duration=time.time() - start_time,
                output="",
                error=str(e),
                hidden_exception=""
            )
    
    def run_mirabelle(self,
                     theory_dir: str,
                     session_name: str = "Test_Theories",
                     action: str = "sledgehammer",
                     timeout: int = None) -> TestResult:
        """
        运行 Mirabelle 测试
        
        Args:
            theory_dir: Theory 文件目录
            session_name: Session 名称
            action: Mirabelle action
            timeout: 超时时间
            
        Returns:
            TestResult: 测试结果
        """
        timeout = timeout or self.mirabelle_timeout
        
        # 清空隐藏异常日志
        self.hidden_detector.clear_logs()
        
        theory_dir = Path(theory_dir).resolve()
        
        cmd = [
            self.isabelle_path,
            "mirabelle",
            "-A", action,
            "-T", str(self.sledgehammer_timeout),
            "-d", str(theory_dir),
            session_name
        ]
        
        start_time = time.time()
        hidden_exception = ""
        
        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=str(theory_dir)
            )
            
            duration = time.time() - start_time
            
            # 检查隐藏异常
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                hidden_exception = hidden_result["raw_content"][:500]
                self.stats['hidden_exceptions'] += hidden_result["exception_count"]
                logger.warning(f"🔴 发现隐藏异常: {hidden_result['exception_count']} 个")
            
            return TestResult(
                test_name=session_name,
                success=result.returncode == 0,
                duration=duration,
                output=result.stdout + "\n" + result.stderr,
                error="" if result.returncode == 0 else result.stderr,
                hidden_exception=hidden_exception
            )
            
        except subprocess.TimeoutExpired:
            hidden_result = self.hidden_detector.check_for_exceptions()
            if hidden_result["found_exceptions"]:
                hidden_exception = hidden_result["raw_content"][:500]
            
            return TestResult(
                test_name=session_name,
                success=False,
                duration=timeout,
                output="",
                error="Mirabelle timeout",
                hidden_exception=hidden_exception
            )
            
        except Exception as e:
            return TestResult(
                test_name=session_name,
                success=False,
                duration=time.time() - start_time,
                output="",
                error=str(e),
                hidden_exception=""
            )
    
    def create_temp_theory(self, 
                          content: str,
                          name: str = "Test") -> str:
        """
        创建临时 Theory 文件
        
        Args:
            content: Theory 内容
            name: Theory 名称
            
        Returns:
            临时文件路径
        """
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.thy',
            prefix=f"{name}_",
            delete=False
        ) as f:
            f.write(content)
            return f.name
    
    def create_root_file(self, theory_dir: str, theories: List[str]) -> str:
        """
        创建 ROOT 文件
        
        Args:
            theory_dir: Theory 目录
            theories: Theory 名称列表
            
        Returns:
            ROOT 文件路径
        """
        root_content = f'''session Test_Theories = "HOL" +
  options [timeout = {self.mirabelle_timeout}]
  theories
    {' '.join(theories)}
'''
        root_path = Path(theory_dir) / "ROOT"
        root_path.write_text(root_content)
        return str(root_path)
    
    # ============================================
    # 结果管理
    # ============================================
    
    def add_result(self, result: TestResult):
        """添加测试结果"""
        self.results.append(result)
        self.stats['total_tests'] += 1
        if result.success:
            self.stats['passed'] += 1
        else:
            self.stats['failed'] += 1
        self.stats['total_time'] += result.duration
    
    def save_results(self, filename: str = None) -> str:
        """
        保存测试结果
        
        Args:
            filename: 文件名（不含扩展名）
            
        Returns:
            保存的文件路径
        """
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"test_results_{timestamp}"
        
        # 保存 JSON
        json_path = self.output_dir / f"{filename}.json"
        data = {
            'generated_at': datetime.now().isoformat(),
            'stats': self.stats,
            'results': [r.to_dict() for r in self.results]
        }
        
        with open(json_path, 'w') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"✅ 结果已保存: {json_path}")
        return str(json_path)
    
    def generate_summary(self) -> str:
        """生成测试摘要"""
        lines = [
            "=" * 60,
            f"测试摘要: {self.__class__.__name__}",
            "=" * 60,
            f"总测试数: {self.stats['total_tests']}",
            f"通过: {self.stats['passed']}",
            f"失败: {self.stats['failed']}",
            f"隐藏异常: {self.stats['hidden_exceptions']}",
            f"总耗时: {self.stats['total_time']:.2f}s",
            "=" * 60,
        ]
        return "\n".join(lines)
    
    def print_summary(self):
        """打印测试摘要"""
        print(self.generate_summary())


# 便捷函数
def run_isabelle_quick_test(theory_content: str, timeout: int = 30) -> TestResult:
    """
    快速运行 Isabelle 测试
    
    Args:
        theory_content: Theory 内容
        timeout: 超时时间
        
    Returns:
        TestResult: 测试结果
    """
    class QuickRunner(IsabelleTestRunner):
        def run_test(self, test_case):
            return self.run_isabelle_process(test_case, timeout)
    
    runner = QuickRunner(output_dir="/tmp/isabelle_quick_test")
    
    # 创建临时文件
    temp_path = runner.create_temp_theory(theory_content)
    
    try:
        return runner.run_isabelle_process(temp_path, timeout)
    finally:
        import os
        if os.path.exists(temp_path):
            os.unlink(temp_path)


if __name__ == "__main__":
    # 测试代码
    logging.basicConfig(level=logging.INFO)
    
    print("=" * 60)
    print("IsabelleTestRunner 测试")
    print("=" * 60)
    
    # 测试快速运行
    theory = '''theory Quick_Test
imports Main
begin

lemma "True"
  by simp

end
'''
    
    result = run_isabelle_quick_test(theory)
    print(f"测试结果: success={result.success}, duration={result.duration:.2f}s")
    print(f"隐藏异常: {result.hidden_exception or 'None'}")

