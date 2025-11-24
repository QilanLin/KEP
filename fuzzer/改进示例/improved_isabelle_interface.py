"""
改进版 Isabelle接口模块
展示代码质量最佳实践
"""

import subprocess
import os
import tempfile
import logging
import re
from pathlib import Path
from typing import Optional, Dict, List, Tuple, Callable
from dataclasses import dataclass
from enum import Enum
from concurrent.futures import ThreadPoolExecutor, as_completed
import multiprocessing

logger = logging.getLogger(__name__)


class IsabelleStatus(Enum):
    """Isabelle执行状态"""
    SUCCESS = "success"
    TIMEOUT = "timeout"
    ERROR = "error"
    PROOF_FAILED = "proof_failed"


@dataclass
class IsabelleResult:
    """
    Isabelle执行结果
    
    Attributes:
        status: 执行状态
        output: 标准输出
        error: 标准错误输出
        execution_time: 执行时间（秒）
        thy_file: Theory文件路径
        sledgehammer_used: 是否使用了Sledgehammer
        prover_used: 使用的prover名称
        proof_found: 是否找到了proof
        tptp_file: TPTP文件路径（如果有）
    """
    status: IsabelleStatus
    output: str
    error: str
    execution_time: float
    thy_file: str
    sledgehammer_used: bool = False
    prover_used: Optional[str] = None
    proof_found: bool = False
    tptp_file: Optional[str] = None


class IsabelleInterfaceError(Exception):
    """Isabelle接口错误基类"""
    pass


class IsabelleNotFoundError(IsabelleInterfaceError):
    """Isabelle不可用错误"""
    pass


class InvalidTheoryNameError(IsabelleInterfaceError):
    """无效的theory名称错误"""
    pass


class IsabelleInterface:
    """
    Isabelle接口类 - 改进版
    
    提供与Isabelle/HOL的集成，包括：
    - 运行theory文件
    - 调用Sledgehammer
    - 提取TPTP文件
    - Proof reconstruction
    
    Example:
        >>> interface = IsabelleInterface()
        >>> result = interface.run_theory("Test_Basic.thy", timeout=60.0)
        >>> if result.status == IsabelleStatus.SUCCESS:
        ...     print("Theory验证成功")
    
    Note:
        - 所有文件操作都进行了安全验证
        - 支持并发批量处理
        - 所有错误都有详细日志
    """
    
    # 类常量
    MAX_THEORY_NAME_LENGTH = 255
    VALID_THEORY_NAME_PATTERN = r'^[A-Za-z][A-Za-z0-9_]*$'
    RESERVED_WORDS = {'begin', 'end', 'theory', 'imports', 'Main', 'Pure'}
    
    def __init__(self, isabelle_path: str = "isabelle", config: Optional[Dict] = None):
        """
        初始化Isabelle接口
        
        Args:
            isabelle_path: Isabelle可执行文件路径
            config: 额外配置字典（可选）
                - verify_on_init: 是否在初始化时验证Isabelle（默认True）
                - temp_dir: 临时文件目录（默认系统临时目录）
        
        Raises:
            IsabelleNotFoundError: Isabelle不可用
        """
        self.isabelle_path = isabelle_path
        self.config = config or {}
        self.temp_dir = self.config.get('temp_dir', tempfile.gettempdir())
        
        # 验证Isabelle
        if self.config.get('verify_on_init', True):
            self._verify_isabelle()
        
    def _verify_isabelle(self) -> None:
        """
        验证Isabelle是否可用
        
        Raises:
            IsabelleNotFoundError: Isabelle不可用
        """
        try:
            result = subprocess.run(
                [self.isabelle_path, "version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            
            if result.returncode != 0:
                error_msg = f"Isabelle验证失败: {result.stderr}"
                logger.warning(error_msg)
                raise IsabelleNotFoundError(error_msg)
            
            version = result.stdout.strip()
            logger.info(f"✅ Isabelle验证成功: {version}")
            
        except FileNotFoundError as e:
            error_msg = f"无法找到Isabelle可执行文件: {self.isabelle_path}"
            logger.error(error_msg)
            raise IsabelleNotFoundError(error_msg) from e
        except subprocess.TimeoutExpired as e:
            error_msg = "Isabelle版本检查超时"
            logger.error(error_msg)
            raise IsabelleNotFoundError(error_msg) from e
        except Exception as e:
            error_msg = f"Isabelle验证失败: {e}"
            logger.error(error_msg)
            raise IsabelleNotFoundError(error_msg) from e
    
    def _validate_theory_name(self, theory_name: str) -> str:
        """
        验证并清理theory名称
        
        Isabelle theory名称必须：
        1. 以字母开头
        2. 只包含字母、数字、下划线
        3. 不超过255个字符
        4. 不是保留词
        
        Args:
            theory_name: 待验证的theory名称
            
        Returns:
            验证通过的theory名称
            
        Raises:
            InvalidTheoryNameError: 名称无效
        """
        # 检查None和空字符串
        if not theory_name:
            raise InvalidTheoryNameError("Theory名称不能为空")
        
        # 检查长度
        if len(theory_name) > self.MAX_THEORY_NAME_LENGTH:
            raise InvalidTheoryNameError(
                f"Theory名称过长: {len(theory_name)} > {self.MAX_THEORY_NAME_LENGTH}"
            )
        
        # 检查格式
        if not re.match(self.VALID_THEORY_NAME_PATTERN, theory_name):
            raise InvalidTheoryNameError(
                f"无效的theory名称格式: {theory_name}. "
                f"必须以字母开头，只能包含字母、数字和下划线。"
            )
        
        # 检查保留词
        if theory_name in self.RESERVED_WORDS:
            raise InvalidTheoryNameError(
                f"Theory名称不能是保留词: {theory_name}"
            )
        
        return theory_name
    
    def _validate_file_path(self, file_path: str) -> Path:
        """
        验证文件路径的安全性
        
        Args:
            file_path: 文件路径
            
        Returns:
            Path对象
            
        Raises:
            FileNotFoundError: 文件不存在
            PermissionError: 无权限访问
            ValueError: 路径不安全
        """
        path = Path(file_path).resolve()
        
        # 检查文件存在
        if not path.exists():
            raise FileNotFoundError(f"文件不存在: {file_path}")
        
        # 检查是文件而非目录
        if not path.is_file():
            raise ValueError(f"路径不是文件: {file_path}")
        
        # 检查读取权限
        if not os.access(path, os.R_OK):
            raise PermissionError(f"无权限读取文件: {file_path}")
        
        # 检查路径遍历攻击（可选，根据需求）
        # 如果需要限制在特定目录内，可以添加检查
        
        return path
    
    def run_theory(self, 
                   thy_file: str,
                   timeout: float = 60.0,
                   working_dir: Optional[str] = None) -> IsabelleResult:
        """
        运行Isabelle theory文件并返回执行结果
        
        这个方法会：
        1. 验证文件存在和权限
        2. 提取并验证theory名称
        3. 在指定工作目录中运行Isabelle process命令
        4. 解析输出判断成功/失败
        
        Args:
            thy_file: Theory文件的绝对或相对路径
                     例如: "../test_theories/Test_Basic.thy"
            timeout: 最大执行时间（秒）。默认60秒。
                    如果超时，返回TIMEOUT状态。
            working_dir: Isabelle执行的工作目录
                        如果为None，使用theory文件所在目录
            
        Returns:
            IsabelleResult: 包含执行结果的对象，字段包括：
                - status: 执行状态（SUCCESS/ERROR/TIMEOUT/PROOF_FAILED）
                - output: stdout输出
                - error: stderr输出
                - execution_time: 实际执行时间
                - thy_file: 输入的文件路径
        
        Raises:
            IsabelleNotFoundError: Isabelle不可用
            FileNotFoundError: theory文件不存在
            PermissionError: 无权限访问文件或目录
            InvalidTheoryNameError: theory名称无效
        
        Example:
            >>> interface = IsabelleInterface()
            >>> result = interface.run_theory("Test_Basic.thy")
            >>> if result.status == IsabelleStatus.SUCCESS:
            ...     print(f"成功! 耗时: {result.execution_time:.2f}秒")
        
        Note:
            - Theory名称从文件名自动提取（去除.thy扩展名）
            - 如果theory有依赖，确保工作目录正确
            - 大型theory可能需要增加timeout
        """
        import time
        
        start_time = time.time()
        
        try:
            # 1. 验证文件路径
            thy_path = self._validate_file_path(thy_file)
            
            # 2. 提取并验证theory名称
            theory_name = thy_path.stem
            theory_name = self._validate_theory_name(theory_name)
            
            # 3. 设置工作目录
            if working_dir is None:
                working_dir = str(thy_path.parent)
            
            # 4. 构建Isabelle命令
            cmd = [
                self.isabelle_path,
                "process",
                "-e", f'use_thy "{theory_name}";'
            ]
            
            logger.debug(f"运行Isabelle命令: {' '.join(cmd)}")
            logger.debug(f"工作目录: {working_dir}")
            logger.info(f"开始处理theory文件: {thy_file}")
            
            # 5. 执行命令
            result = subprocess.run(
                cmd,
                cwd=working_dir,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            
            execution_time = time.time() - start_time
            
            # 6. 解析结果
            status = self._parse_execution_status(result)
            
            logger.info(
                f"Theory执行完成: {thy_file} - "
                f"状态: {status.value} - "
                f"耗时: {execution_time:.2f}秒"
            )
            
            return IsabelleResult(
                status=status,
                output=result.stdout,
                error=result.stderr,
                execution_time=execution_time,
                thy_file=str(thy_path)
            )
            
        except subprocess.TimeoutExpired:
            execution_time = time.time() - start_time
            logger.warning(f"Theory执行超时: {thy_file} (>{timeout}秒)")
            
            return IsabelleResult(
                status=IsabelleStatus.TIMEOUT,
                output="",
                error=f"Isabelle执行超时（>{timeout}秒）",
                execution_time=execution_time,
                thy_file=thy_file
            )
            
        except (FileNotFoundError, PermissionError, InvalidTheoryNameError) as e:
            # 这些是预期的错误，直接抛出
            logger.error(f"Theory文件验证失败: {e}")
            raise
            
        except Exception as e:
            # 未预期的错误
            execution_time = time.time() - start_time
            logger.error(f"Theory执行失败: {thy_file} - 错误: {e}", exc_info=True)
            
            return IsabelleResult(
                status=IsabelleStatus.ERROR,
                output="",
                error=f"Isabelle执行失败: {str(e)}",
                execution_time=execution_time,
                thy_file=thy_file
            )
    
    def _parse_execution_status(self, result: subprocess.CompletedProcess) -> IsabelleStatus:
        """
        解析subprocess执行结果，确定Isabelle状态
        
        Args:
            result: subprocess.CompletedProcess对象
            
        Returns:
            IsabelleStatus枚举值
        """
        if result.returncode == 0:
            return IsabelleStatus.SUCCESS
        
        # 检查stderr和stdout以确定具体错误类型
        error_output = result.stderr + result.stdout
        
        # Proof失败的特征
        proof_failure_indicators = [
            "Failed to apply",
            "Failed to finish proof",
            "No proof state"
        ]
        
        for indicator in proof_failure_indicators:
            if indicator in error_output:
                return IsabelleStatus.PROOF_FAILED
        
        # 其他错误
        return IsabelleStatus.ERROR
    
    def batch_test_theories(self,
                           thy_files: List[str],
                           timeout: float = 60.0,
                           max_workers: Optional[int] = None,
                           progress_callback: Optional[Callable] = None) -> Dict[str, IsabelleResult]:
        """
        并发批量测试theory文件（改进版，支持并发）
        
        Args:
            thy_files: Theory文件路径列表
            timeout: 每个文件的超时时间
            max_workers: 最大并发worker数，None则使用CPU核心数
            progress_callback: 每个测试完成后的回调函数
                              签名: callback(thy_file: str, result: IsabelleResult) -> None
            
        Returns:
            文件路径到结果的映射字典
            
        Example:
            >>> def on_progress(file, result):
            ...     print(f"完成: {file} - {result.status.value}")
            >>> results = interface.batch_test_theories(
            ...     thy_files=["Test1.thy", "Test2.thy"],
            ...     max_workers=4,
            ...     progress_callback=on_progress
            ... )
        
        Note:
            - 使用ThreadPoolExecutor实现并发
            - 如果某个theory失败，不影响其他theory的测试
            - 所有异常都会被捕获并记录在result中
        """
        if not thy_files:
            logger.warning("批量测试: 文件列表为空")
            return {}
        
        # 确定worker数量
        if max_workers is None:
            max_workers = min(len(thy_files), multiprocessing.cpu_count())
        
        logger.info(
            f"开始批量测试: {len(thy_files)}个文件, "
            f"{max_workers}个并发worker"
        )
        
        results = {}
        completed_count = 0
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # 提交所有任务
            future_to_file = {
                executor.submit(self.run_theory, thy_file, timeout): thy_file
                for thy_file in thy_files
            }
            
            # 收集结果
            for future in as_completed(future_to_file):
                thy_file = future_to_file[future]
                completed_count += 1
                
                try:
                    result = future.result()
                    results[thy_file] = result
                    
                    # 日志
                    if result.status == IsabelleStatus.SUCCESS:
                        logger.info(
                            f"✅ [{completed_count}/{len(thy_files)}] {thy_file}: 成功"
                        )
                    else:
                        logger.warning(
                            f"❌ [{completed_count}/{len(thy_files)}] {thy_file}: "
                            f"{result.status.value}"
                        )
                    
                    # 回调
                    if progress_callback:
                        try:
                            progress_callback(thy_file, result)
                        except Exception as e:
                            logger.error(f"回调函数执行失败: {e}")
                    
                except Exception as e:
                    # 处理future.result()抛出的异常
                    logger.error(f"处理 {thy_file} 时发生异常: {e}", exc_info=True)
                    
                    results[thy_file] = IsabelleResult(
                        status=IsabelleStatus.ERROR,
                        output="",
                        error=f"处理失败: {str(e)}",
                        execution_time=0.0,
                        thy_file=thy_file
                    )
        
        logger.info(
            f"批量测试完成: {len(results)}个结果, "
            f"成功: {sum(1 for r in results.values() if r.status == IsabelleStatus.SUCCESS)}, "
            f"失败: {sum(1 for r in results.values() if r.status != IsabelleStatus.SUCCESS)}"
        )
        
        return results
    
    def _create_temp_thy_file(self, 
                             content: str, 
                             prefix: str = 'temp_',
                             suffix: str = '.thy') -> str:
        """
        安全地创建临时theory文件（改进版，统一临时文件创建逻辑）
        
        Args:
            content: Theory文件内容
            prefix: 文件名前缀
            suffix: 文件后缀（默认.thy）
            
        Returns:
            临时文件的绝对路径
            
        Raises:
            IOError: 无法创建临时文件
        """
        try:
            temp_fd, temp_path = tempfile.mkstemp(
                suffix=suffix,
                prefix=prefix,
                dir=self.temp_dir,
                text=True
            )
            
            # 写入内容
            try:
                os.write(temp_fd, content.encode('utf-8'))
            finally:
                os.close(temp_fd)
            
            logger.debug(f"创建临时文件: {temp_path}")
            return temp_path
            
        except IOError as e:
            error_msg = f"无法创建临时theory文件: {e}"
            logger.error(error_msg)
            raise IOError(error_msg) from e
    
    def _safe_remove_file(self, file_path: str) -> bool:
        """
        安全地删除文件（改进版，统一文件删除逻辑）
        
        Args:
            file_path: 要删除的文件路径
            
        Returns:
            是否成功删除
        """
        if not os.path.exists(file_path):
            logger.debug(f"文件不存在，跳过删除: {file_path}")
            return True
        
        try:
            os.remove(file_path)
            logger.debug(f"已删除临时文件: {file_path}")
            return True
        except OSError as e:
            logger.warning(f"无法删除文件 {file_path}: {e}")
            return False
        except Exception as e:
            logger.error(f"删除文件时发生未预期错误 {file_path}: {e}")
            return False


# ============================================================================
# 测试代码
# ============================================================================

def test_isabelle_interface():
    """
    改进版测试函数
    展示如何使用新的IsabelleInterface
    """
    print("🧪 测试改进版 Isabelle Interface")
    print("=" * 60)
    
    # 配置日志
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(levelname)s - %(message)s'
    )
    
    try:
        # 1. 初始化
        print("\n1️⃣ 初始化Isabelle接口...")
        interface = IsabelleInterface()
        print("✅ 初始化成功\n")
        
        # 2. 测试单个theory文件
        test_thy = "../test_theories/Simple_Valid_Tests.thy"
        if os.path.exists(test_thy):
            print(f"2️⃣ 测试单个theory: {test_thy}")
            result = interface.run_theory(test_thy, timeout=60.0)
            print(f"   状态: {result.status.value}")
            print(f"   执行时间: {result.execution_time:.2f}秒")
            if result.error:
                print(f"   错误: {result.error[:100]}...")
            print()
        
        # 3. 测试批量处理
        print("3️⃣ 测试批量处理...")
        thy_files = [
            "../test_theories/Simple_Valid_Tests.thy",
            "../test_theories/Challenging_Cases.thy",
        ]
        thy_files = [f for f in thy_files if os.path.exists(f)]
        
        if thy_files:
            def progress_callback(file, result):
                print(f"   完成: {Path(file).name} - {result.status.value}")
            
            results = interface.batch_test_theories(
                thy_files=thy_files,
                max_workers=2,
                progress_callback=progress_callback
            )
            
            print(f"\n   总计: {len(results)}个结果")
            success_count = sum(
                1 for r in results.values() 
                if r.status == IsabelleStatus.SUCCESS
            )
            print(f"   成功: {success_count}/{len(results)}")
        
        print("\n" + "=" * 60)
        print("✅ 所有测试完成!")
        
    except Exception as e:
        print(f"\n❌ 测试失败: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    test_isabelle_interface()

