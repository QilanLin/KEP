#!/usr/bin/env python3
"""
统一配置管理模块

集中管理所有测试脚本的配置：
- 日志文件路径
- 超时设置
- Isabelle 路径
- 输出目录等

使用方法：
    from config import Config
    
    # 获取配置
    config = Config()
    print(config.SLEDGEHAMMER_LOG)
    print(config.DEFAULT_TIMEOUT)
    
    # 或直接导入配置常量
    from config import SLEDGEHAMMER_LOG, DEFAULT_TIMEOUT
"""

import os
from pathlib import Path
from dataclasses import dataclass
from typing import Optional
import platform


@dataclass
class Config:
    """统一配置类"""
    
    # ============================================
    # 日志文件路径
    # ============================================
    SLEDGEHAMMER_HIDDEN_ERRORS_LOG: str = "/tmp/sledgehammer_hidden_errors.log"
    MIRABELLE_HIDDEN_ERRORS_LOG: str = "/tmp/mirabelle_hidden_errors.log"
    SLEDGEHAMMER_COVERAGE_LOG: str = "/tmp/sledgehammer_coverage.log"
    
    # ============================================
    # 超时设置（秒）
    # ============================================
    DEFAULT_SLEDGEHAMMER_TIMEOUT: int = 30
    DEFAULT_MIRABELLE_TIMEOUT: int = 120
    DEFAULT_PROCESS_TIMEOUT: int = 60
    DEFAULT_TEST_TIMEOUT: int = 90
    
    # ============================================
    # Isabelle 路径
    # ============================================
    ISABELLE_HOME: str = "/Applications/Isabelle2025.app"
    ISABELLE_BIN: str = "/Applications/Isabelle2025.app/bin/isabelle"
    
    # ============================================
    # 默认输出目录
    # ============================================
    DEFAULT_RESULTS_DIR: str = "results"
    DEFAULT_MUTATIONS_DIR: str = "mutations"
    DEFAULT_BUGS_DIR: str = "bugs"
    
    # ============================================
    # 测试配置
    # ============================================
    DEFAULT_MUTATIONS_PER_SEED: int = 10
    MAX_MUTATIONS_PER_SEED: int = 100
    DEFAULT_BATCH_SIZE: int = 50
    
    def __post_init__(self):
        """初始化后处理"""
        # 自动检测 Isabelle 路径
        self._detect_isabelle_path()
    
    def _detect_isabelle_path(self):
        """自动检测 Isabelle 安装路径"""
        possible_paths = [
            "/Applications/Isabelle2025.app",
            "/Applications/Isabelle2024.app",
            os.path.expanduser("~/Isabelle2025"),
            os.path.expanduser("~/Downloads/Isabelle2025"),
        ]
        
        for path in possible_paths:
            if os.path.exists(path):
                self.ISABELLE_HOME = path
                self.ISABELLE_BIN = os.path.join(path, "bin/isabelle")
                break
    
    @property
    def all_log_files(self) -> list:
        """获取所有日志文件路径"""
        return [
            self.SLEDGEHAMMER_HIDDEN_ERRORS_LOG,
            self.MIRABELLE_HIDDEN_ERRORS_LOG,
            self.SLEDGEHAMMER_COVERAGE_LOG
        ]
    
    @property
    def exception_log_files(self) -> list:
        """获取异常日志文件路径（不包括覆盖率）"""
        return [
            self.SLEDGEHAMMER_HIDDEN_ERRORS_LOG,
            self.MIRABELLE_HIDDEN_ERRORS_LOG
        ]
    
    def get_timestamped_dir(self, base_dir: str) -> str:
        """获取带时间戳的目录名"""
        from datetime import datetime
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        return f"{base_dir}_{timestamp}"
    
    def ensure_dir(self, dir_path: str) -> Path:
        """确保目录存在"""
        path = Path(dir_path)
        path.mkdir(parents=True, exist_ok=True)
        return path


# 全局配置实例
_config = Config()

# 导出常用配置为模块级变量
SLEDGEHAMMER_HIDDEN_ERRORS_LOG = _config.SLEDGEHAMMER_HIDDEN_ERRORS_LOG
MIRABELLE_HIDDEN_ERRORS_LOG = _config.MIRABELLE_HIDDEN_ERRORS_LOG
SLEDGEHAMMER_COVERAGE_LOG = _config.SLEDGEHAMMER_COVERAGE_LOG

DEFAULT_SLEDGEHAMMER_TIMEOUT = _config.DEFAULT_SLEDGEHAMMER_TIMEOUT
DEFAULT_MIRABELLE_TIMEOUT = _config.DEFAULT_MIRABELLE_TIMEOUT
DEFAULT_PROCESS_TIMEOUT = _config.DEFAULT_PROCESS_TIMEOUT
DEFAULT_TEST_TIMEOUT = _config.DEFAULT_TEST_TIMEOUT

ISABELLE_HOME = _config.ISABELLE_HOME
ISABELLE_BIN = _config.ISABELLE_BIN

DEFAULT_RESULTS_DIR = _config.DEFAULT_RESULTS_DIR
DEFAULT_MUTATIONS_PER_SEED = _config.DEFAULT_MUTATIONS_PER_SEED


def get_config() -> Config:
    """获取全局配置实例"""
    return _config


def print_config():
    """打印当前配置"""
    print("=" * 60)
    print("当前配置")
    print("=" * 60)
    print(f"Isabelle 路径: {_config.ISABELLE_HOME}")
    print(f"Isabelle 可执行文件: {_config.ISABELLE_BIN}")
    print(f"Sledgehammer 超时: {_config.DEFAULT_SLEDGEHAMMER_TIMEOUT}s")
    print(f"Mirabelle 超时: {_config.DEFAULT_MIRABELLE_TIMEOUT}s")
    print(f"隐藏异常日志: {_config.SLEDGEHAMMER_HIDDEN_ERRORS_LOG}")
    print(f"覆盖率日志: {_config.SLEDGEHAMMER_COVERAGE_LOG}")
    print("=" * 60)


if __name__ == "__main__":
    print_config()

