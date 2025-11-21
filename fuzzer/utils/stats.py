#!/usr/bin/env python3
"""
统计分析工具
收集和分析fuzzing统计数据
"""

import json
import os
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict
from datetime import datetime
from collections import defaultdict


@dataclass
class FuzzingStats:
    """Fuzzing统计信息"""
    total_tests: int = 0
    crashes: int = 0
    timeouts: int = 0
    differentials: int = 0
    bugs_found: int = 0
    total_execution_time: float = 0.0
    avg_execution_time: float = 0.0
    seeds_processed: int = 0
    mutants_generated: int = 0
    start_time: Optional[str] = None
    end_time: Optional[str] = None


class StatsCollector:
    """统计信息收集器"""
    
    def __init__(self, output_dir: str = "./stats"):
        """
        初始化统计收集器
        
        Args:
            output_dir: 统计信息输出目录
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.stats = FuzzingStats()
        self.bug_reports = []
        self.differential_reports = []
        
        self.start_time = datetime.now()
        self.stats.start_time = self.start_time.isoformat()
    
    def record_test(self, execution_time: float = 0.0):
        """记录一次测试"""
        self.stats.total_tests += 1
        self.stats.total_execution_time += execution_time
        self.stats.avg_execution_time = (
            self.stats.total_execution_time / self.stats.total_tests
            if self.stats.total_tests > 0 else 0.0
        )
    
    def record_crash(self, bug_report: Dict):
        """记录崩溃"""
        self.stats.crashes += 1
        self.stats.bugs_found += 1
        self.bug_reports.append(bug_report)
    
    def record_timeout(self, bug_report: Dict):
        """记录超时"""
        self.stats.timeouts += 1
        self.stats.bugs_found += 1
        self.bug_reports.append(bug_report)
    
    def record_differential(self, diff_report: Dict):
        """记录差异"""
        self.stats.differentials += 1
        self.differential_reports.append(diff_report)
    
    def record_seed(self, mutants_generated: int = 0):
        """记录种子处理"""
        self.stats.seeds_processed += 1
        self.stats.mutants_generated += mutants_generated
    
    def save_stats(self, filename: str = "stats.json"):
        """保存统计信息"""
        self.stats.end_time = datetime.now().isoformat()
        
        stats_dict = asdict(self.stats)
        stats_dict['bug_reports_count'] = len(self.bug_reports)
        stats_dict['differential_reports_count'] = len(self.differential_reports)
        
        output_file = self.output_dir / filename
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(stats_dict, f, indent=2)
        
        return output_file
    
    def print_summary(self):
        """打印统计摘要"""
        print("=" * 50)
        print("📊 Fuzzing统计摘要")
        print("=" * 50)
        print(f"总测试数: {self.stats.total_tests}")
        print(f"处理种子数: {self.stats.seeds_processed}")
        print(f"生成变异体数: {self.stats.mutants_generated}")
        print(f"平均执行时间: {self.stats.avg_execution_time:.2f}秒")
        print()
        print(f"崩溃数: {self.stats.crashes}")
        print(f"超时数: {self.stats.timeouts}")
        print(f"差异数: {self.stats.differentials}")
        print(f"发现的bug总数: {self.stats.bugs_found}")
        print()
        
        if self.stats.start_time and self.stats.end_time:
            start = datetime.fromisoformat(self.stats.start_time)
            end = datetime.fromisoformat(self.stats.end_time)
            duration = (end - start).total_seconds()
            print(f"总执行时间: {duration:.2f}秒")
        
        print("=" * 50)


def analyze_results(results_dir: str) -> Dict:
    """
    分析fuzzing结果目录
    
    Args:
        results_dir: 结果目录路径
        
    Returns:
        分析结果字典
    """
    results_path = Path(results_dir)
    
    if not results_path.exists():
        return {"error": f"结果目录不存在: {results_dir}"}
    
    bug_files = list(results_path.glob("bug_*.json"))
    diff_files = list(results_path.glob("differential_*.json"))
    
    bugs = []
    for bug_file in bug_files:
        try:
            with open(bug_file, 'r', encoding='utf-8') as f:
                bugs.append(json.load(f))
        except Exception as e:
            print(f"警告: 无法读取 {bug_file}: {e}")
    
    differentials = []
    for diff_file in diff_files:
        try:
            with open(diff_file, 'r', encoding='utf-8') as f:
                differentials.append(json.load(f))
        except Exception as e:
            print(f"警告: 无法读取 {diff_file}: {e}")
    
    # 统计分析
    bug_types = defaultdict(int)
    for bug in bugs:
        bug_type = bug.get('bug_type', 'unknown')
        bug_types[bug_type] += 1
    
    prover_counts = defaultdict(int)
    for diff in differentials:
        prover_results = diff.get('prover_results', {})
        for prover, status in prover_results.items():
            prover_counts[prover] += 1
    
    return {
        'total_bugs': len(bugs),
        'total_differentials': len(differentials),
        'bug_types': dict(bug_types),
        'prover_counts': dict(prover_counts),
        'bugs': bugs,
        'differentials': differentials
    }


def main():
    """测试函数"""
    print("📊 统计分析工具测试")
    print()
    
    # 测试统计收集器
    collector = StatsCollector()
    
    # 模拟一些数据
    collector.record_seed(mutants_generated=3)
    collector.record_test(execution_time=1.5)
    collector.record_test(execution_time=2.0)
    collector.record_crash({'bug_type': 'crash', 'prover': 'z3'})
    collector.record_differential({'prover_results': {'z3': 'sat', 'cvc5': 'unsat'}})
    
    collector.print_summary()
    
    # 保存统计信息
    output_file = collector.save_stats()
    print(f"\n✅ 统计信息已保存到: {output_file}")


if __name__ == "__main__":
    main()

