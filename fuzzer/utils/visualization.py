#!/usr/bin/env python3
"""
可视化工具
生成统计图表和趋势分析报告
"""

import json
from pathlib import Path
from typing import Dict, List, Optional
from datetime import datetime

try:
    import matplotlib
    matplotlib.use('Agg')  # 非交互式后端
    import matplotlib.pyplot as plt
    import numpy as np
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


class FuzzerVisualizer:
    """Fuzzer可视化工具"""
    
    def __init__(self, output_dir: str):
        """
        初始化可视化工具
        
        Args:
            output_dir: 输出目录
        """
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.fig_size = (10, 6)
    
    def load_stats(self, stats_file: str) -> Dict:
        """
        加载统计文件
        
        Args:
            stats_file: 统计文件路径
        
        Returns:
            统计数据字典
        """
        with open(stats_file, 'r', encoding='utf-8') as f:
            return json.load(f)
    
    def plot_test_overview(self, stats: Dict, save_path: Optional[str] = None):
        """
        绘制测试概览图
        
        Args:
            stats: 统计数据
            save_path: 保存路径（None表示自动生成）
        """
        if not MATPLOTLIB_AVAILABLE:
            print("⚠️  matplotlib未安装，跳过图表生成。请运行: pip install matplotlib")
            return
        
        if save_path is None:
            save_path = self.output_dir / "test_overview.png"
        
        fig, axes = plt.subplots(1, 2, figsize=self.fig_size)
        
        # 左图：测试结果分布
        labels = ['正常', '崩溃', '超时', '差异']
        sizes = [
            stats['total_tests'] - stats['bugs_found'],
            stats['crashes'],
            stats['timeouts'],
            stats['differentials']
        ]
        colors = ['#90EE90', '#FF6B6B', '#FFA500', '#FFD700']
        
        axes[0].pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90)
        axes[0].set_title('测试结果分布')
        
        # 右图：Bug类型统计
        bug_labels = ['崩溃', '超时', '差异']
        bug_counts = [stats['crashes'], stats['timeouts'], stats['differentials']]
        
        bars = axes[1].bar(bug_labels, bug_counts, color=['#FF6B6B', '#FFA500', '#FFD700'])
        axes[1].set_title('发现的Bug类型统计')
        axes[1].set_ylabel('数量')
        axes[1].grid(axis='y', alpha=0.3)
        
        # 在柱状图上显示数值
        for bar in bars:
            height = bar.get_height()
            if height > 0:
                axes[1].text(bar.get_x() + bar.get_width()/2., height,
                           f'{int(height)}',
                           ha='center', va='bottom')
        
        plt.tight_layout()
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        
        print(f"✅ 测试概览图已保存到: {save_path}")
    
    def plot_performance_trend(self, stats: Dict, save_path: Optional[str] = None):
        """
        绘制性能趋势图
        
        Args:
            stats: 统计数据
            save_path: 保存路径
        """
        if not MATPLOTLIB_AVAILABLE:
            print("⚠️  matplotlib未安装，跳过图表生成。请运行: pip install matplotlib")
            return
        
        if save_path is None:
            save_path = self.output_dir / "performance_trend.png"
        
        fig, ax = plt.subplots(figsize=self.fig_size)
        
        # 计算性能指标
        if stats['total_tests'] > 0:
            avg_time = stats['avg_execution_time']
            total_time = stats['total_execution_time']
            
            # 性能指标
            metrics = ['平均执行时间\n(秒/测试)', '总执行时间\n(秒)', '变异体生成率\n(个/种子)']
            values = [
                avg_time,
                total_time / 60.0,  # 转换为分钟
                stats['mutants_generated'] / max(1, stats['seeds_processed'])
            ]
            
            bars = ax.bar(metrics, values, color=['#4ECDC4', '#45B7D1', '#96CEB4'])
            ax.set_title('性能指标')
            ax.set_ylabel('数值')
            ax.grid(axis='y', alpha=0.3)
            
            # 在柱状图上显示数值
            for i, (bar, val) in enumerate(zip(bars, values)):
                height = bar.get_height()
                if i == 2:  # 变异体生成率
                    label = f'{val:.2f}'
                elif i == 1:  # 总时间（分钟）
                    label = f'{val:.1f}min'
                else:
                    label = f'{val:.3f}s'
                ax.text(bar.get_x() + bar.get_width()/2., height,
                       label,
                       ha='center', va='bottom')
        else:
            ax.text(0.5, 0.5, '无数据', ha='center', va='center', transform=ax.transAxes)
            ax.set_title('性能指标（无数据）')
        
        plt.tight_layout()
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        
        print(f"✅ 性能趋势图已保存到: {save_path}")
    
    def plot_test_statistics(self, stats: Dict, save_path: Optional[str] = None):
        """
        绘制测试统计图
        
        Args:
            stats: 统计数据
            save_path: 保存路径
        """
        if not MATPLOTLIB_AVAILABLE:
            print("⚠️  matplotlib未安装，跳过图表生成。请运行: pip install matplotlib")
            return
        
        if save_path is None:
            save_path = self.output_dir / "test_statistics.png"
        
        fig, axes = plt.subplots(2, 1, figsize=(10, 8))
        
        # 上图：主要统计指标
        categories = ['总测试数', '处理种子数', '生成变异体数']
        values = [
            stats['total_tests'],
            stats['seeds_processed'],
            stats['mutants_generated']
        ]
        
        bars1 = axes[0].bar(categories, values, color=['#3498DB', '#9B59B6', '#E74C3C'])
        axes[0].set_title('测试规模统计')
        axes[0].set_ylabel('数量')
        axes[0].grid(axis='y', alpha=0.3)
        
        for bar in bars1:
            height = bar.get_height()
            axes[0].text(bar.get_x() + bar.get_width()/2., height,
                        f'{int(height)}',
                        ha='center', va='bottom')
        
        # 下图：Bug统计
        bug_categories = ['崩溃', '超时', '差异', 'Bug总数']
        bug_values = [
            stats['crashes'],
            stats['timeouts'],
            stats['differentials'],
            stats['bugs_found']
        ]
        
        bars2 = axes[1].bar(bug_categories, bug_values, color=['#FF6B6B', '#FFA500', '#FFD700', '#FF0000'])
        axes[1].set_title('Bug发现统计')
        axes[1].set_ylabel('数量')
        axes[1].grid(axis='y', alpha=0.3)
        
        for bar in bars2:
            height = bar.get_height()
            axes[1].text(bar.get_x() + bar.get_width()/2., height,
                        f'{int(height)}',
                        ha='center', va='bottom')
        
        plt.tight_layout()
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        plt.close()
        
        print(f"✅ 测试统计图已保存到: {save_path}")
    
    def generate_report(self, stats_file: str, output_file: Optional[str] = None):
        """
        生成完整的可视化报告
        
        Args:
            stats_file: 统计文件路径
            output_file: 输出HTML报告路径（None表示自动生成）
        """
        stats = self.load_stats(stats_file)
        
        # 生成所有图表
        self.plot_test_overview(stats)
        self.plot_performance_trend(stats)
        self.plot_test_statistics(stats)
        
        # 生成HTML报告
        if output_file is None:
            output_file = self.output_dir / "visualization_report.html"
        
        html_content = self._generate_html_report(stats)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(html_content)
        
        print(f"✅ 可视化报告已保存到: {output_file}")
    
    def _generate_html_report(self, stats: Dict) -> str:
        """生成HTML报告内容"""
        html = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Fuzzing可视化报告</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        h1 {{ color: #333; }}
        .stats {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 20px; margin: 20px 0; }}
        .stat-card {{ background: #f5f5f5; padding: 15px; border-radius: 5px; }}
        .stat-value {{ font-size: 24px; font-weight: bold; color: #3498DB; }}
        .stat-label {{ color: #666; }}
        img {{ max-width: 100%; height: auto; margin: 20px 0; }}
    </style>
</head>
<body>
    <h1>Fuzzing可视化报告</h1>
    <p>生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
    
    <div class="stats">
        <div class="stat-card">
            <div class="stat-value">{stats['total_tests']}</div>
            <div class="stat-label">总测试数</div>
        </div>
        <div class="stat-card">
            <div class="stat-value">{stats['bugs_found']}</div>
            <div class="stat-label">发现的Bug总数</div>
        </div>
        <div class="stat-card">
            <div class="stat-value">{stats['seeds_processed']}</div>
            <div class="stat-label">处理种子数</div>
        </div>
        <div class="stat-card">
            <div class="stat-value">{stats['mutants_generated']}</div>
            <div class="stat-label">生成变异体数</div>
        </div>
    </div>
    
    <h2>测试概览</h2>
    <img src="test_overview.png" alt="测试概览图">
    
    <h2>性能指标</h2>
    <img src="performance_trend.png" alt="性能趋势图">
    
    <h2>测试统计</h2>
    <img src="test_statistics.png" alt="测试统计图">
</body>
</html>
"""
        return html

