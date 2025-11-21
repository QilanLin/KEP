#!/usr/bin/env python3
"""
日志记录工具
提供详细的日志记录功能
"""

import logging
import sys
from pathlib import Path
from datetime import datetime
from typing import Optional


class FuzzerLogger:
    """Fuzzer日志记录器"""
    
    def __init__(self, log_dir: str = "./logs", level: int = logging.INFO):
        """
        初始化日志记录器
        
        Args:
            log_dir: 日志目录
            level: 日志级别
        """
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(parents=True, exist_ok=True)
        
        # 创建日志文件名（带时间戳）
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_file = self.log_dir / f"fuzzer_{timestamp}.log"
        
        # 配置日志
        self.logger = logging.getLogger('Fuzzer')
        self.logger.setLevel(level)
        
        # 清除现有处理器
        self.logger.handlers.clear()
        
        # 文件处理器
        file_handler = logging.FileHandler(log_file, encoding='utf-8')
        file_handler.setLevel(level)
        file_formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )
        file_handler.setFormatter(file_formatter)
        self.logger.addHandler(file_handler)
        
        # 控制台处理器
        console_handler = logging.StreamHandler(sys.stdout)
        console_handler.setLevel(level)
        console_formatter = logging.Formatter(
            '%(levelname)s - %(message)s'
        )
        console_handler.setFormatter(console_formatter)
        self.logger.addHandler(console_handler)
        
        self.log_file = log_file
    
    def info(self, message: str):
        """记录信息"""
        self.logger.info(message)
    
    def warning(self, message: str):
        """记录警告"""
        self.logger.warning(message)
    
    def error(self, message: str):
        """记录错误"""
        self.logger.error(message)
    
    def debug(self, message: str):
        """记录调试信息"""
        self.logger.debug(message)
    
    def test_start(self, seed_name: str, mutant_id: int):
        """记录测试开始"""
        self.info(f"开始测试: {seed_name}_mutant_{mutant_id}")
    
    def test_end(self, seed_name: str, mutant_id: int, status: str):
        """记录测试结束"""
        self.info(f"测试完成: {seed_name}_mutant_{mutant_id} - 状态: {status}")
    
    def bug_found(self, bug_type: str, details: str):
        """记录发现的bug"""
        self.warning(f"发现bug [{bug_type}]: {details}")
    
    def differential_found(self, details: str):
        """记录发现的差异"""
        self.warning(f"发现差异: {details}")


def main():
    """测试函数"""
    print("📝 日志记录工具测试")
    print()
    
    logger = FuzzerLogger(log_dir="./test_logs")
    
    logger.info("Fuzzer开始运行")
    logger.test_start("test_seed", 1)
    logger.test_end("test_seed", 1, "normal")
    logger.bug_found("crash", "Z3崩溃")
    logger.differential_found("Z3: sat, cvc5: unsat")
    logger.info("Fuzzer运行完成")
    
    print(f"\n✅ 日志已保存到: {logger.log_file}")


if __name__ == "__main__":
    main()

