#!/usr/bin/env python3
"""
进度显示工具
提供进度条和实时统计显示
"""

import sys
import time
from typing import Optional


class ProgressBar:
    """进度条类"""
    
    def __init__(self, total: int, prefix: str = 'Progress', suffix: str = 'Complete', length: int = 50):
        """
        初始化进度条
        
        Args:
            total: 总任务数
            prefix: 前缀文本
            suffix: 后缀文本
            length: 进度条长度（字符数）
        """
        self.total = total
        self.prefix = prefix
        self.suffix = suffix
        self.length = length
        self.current = 0
        self.start_time = time.time()
    
    def update(self, n: int = 1):
        """更新进度"""
        self.current += n
        self._display()
    
    def _display(self):
        """显示进度条"""
        if self.total == 0:
            percent = 100.0
        else:
            percent = 100.0 * self.current / self.total
        
        filled = int(self.length * self.current // self.total) if self.total > 0 else self.length
        bar = '█' * filled + '░' * (self.length - filled)
        
        # 计算已用时间和预计剩余时间
        elapsed = time.time() - self.start_time
        if self.current > 0 and self.total > 0:
            eta = elapsed * (self.total - self.current) / self.current
            eta_str = f"ETA: {int(eta)}s"
        else:
            eta_str = "ETA: --"
        
        # 计算速度
        if elapsed > 0:
            speed = self.current / elapsed
            speed_str = f"{speed:.1f}/s"
        else:
            speed_str = "--/s"
        
        sys.stdout.write(f'\r{self.prefix} |{bar}| {self.current}/{self.total} ({percent:.1f}%) {speed_str} {eta_str} {self.suffix}')
        sys.stdout.flush()
        
        if self.current >= self.total:
            print()  # 换行
    
    def finish(self):
        """完成进度条"""
        self.current = self.total
        self._display()


class LiveStats:
    """实时统计显示"""
    
    def __init__(self):
        """初始化实时统计"""
        self.stats = {
            'total_tests': 0,
            'crashes': 0,
            'timeouts': 0,
            'differentials': 0,
            'bugs_found': 0,
            'mutants_generated': 0,
            'seeds_processed': 0,
            'start_time': time.time()
        }
    
    def update(self, **kwargs):
        """更新统计信息"""
        self.stats.update(kwargs)
        self._display()
    
    def _display(self):
        """显示统计信息"""
        elapsed = time.time() - self.stats['start_time']
        speed = self.stats['total_tests'] / elapsed if elapsed > 0 else 0
        
        stats_str = (
            f"Tests: {self.stats['total_tests']} | "
            f"Crashes: {self.stats['crashes']} | "
            f"Timeouts: {self.stats['timeouts']} | "
            f"Differentials: {self.stats['differentials']} | "
            f"Bugs: {self.stats['bugs_found']} | "
            f"Speed: {speed:.1f}/s"
        )
        
        sys.stdout.write(f'\r{stats_str}')
        sys.stdout.flush()
    
    def finish(self):
        """完成统计显示"""
        elapsed = time.time() - self.stats['start_time']
        final_stats = (
            f"\n总测试数: {self.stats['total_tests']} | "
            f"崩溃: {self.stats['crashes']} | "
            f"超时: {self.stats['timeouts']} | "
            f"差异: {self.stats['differentials']} | "
            f"Bug总数: {self.stats['bugs_found']} | "
            f"总时间: {elapsed:.1f}s"
        )
        print(final_stats)

