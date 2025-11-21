#!/usr/bin/env python3
"""
结果分析工具
分析fuzzing结果并生成报告
"""

import json
import sys
from pathlib import Path
from utils.stats import analyze_results


def print_analysis(results_dir: str):
    """打印分析结果"""
    print("=" * 60)
    print("📊 Fuzzing结果分析")
    print("=" * 60)
    print()
    
    # 分析结果
    analysis = analyze_results(results_dir)
    
    if 'error' in analysis:
        print(f"❌ 错误: {analysis['error']}")
        return
    
    # 基本统计
    print("📈 基本统计:")
    print(f"  总Bug数: {analysis['total_bugs']}")
    print(f"  总差异数: {analysis['total_differentials']}")
    print()
    
    # Bug类型统计
    if analysis['bug_types']:
        print("🐛 Bug类型分布:")
        for bug_type, count in analysis['bug_types'].items():
            print(f"  {bug_type}: {count}")
        print()
    
    # Prover统计
    if analysis['prover_counts']:
        print("🔧 Prover使用统计:")
        for prover, count in analysis['prover_counts'].items():
            print(f"  {prover}: {count}")
        print()
    
    # Bug详情
    if analysis['bugs']:
        print("🐛 Bug详情（前10个）:")
        for i, bug in enumerate(analysis['bugs'][:10], 1):
            print(f"  [{i}] {bug.get('seed', 'unknown')}_mutant_{bug.get('mutant_id', '?')}")
            print(f"      Prover: {bug.get('prover', 'unknown')}")
            print(f"      Type: {bug.get('bug_type', 'unknown')}")
            if bug.get('error_message'):
                error_msg = bug['error_message'][:80]
                print(f"      Error: {error_msg}...")
            print()
    
    # 差异详情
    if analysis['differentials']:
        print("⚠️  差异详情（前10个）:")
        for i, diff in enumerate(analysis['differentials'][:10], 1):
            print(f"  [{i}] {diff.get('seed', 'unknown')}_mutant_{diff.get('mutant_id', '?')}")
            prover_results = diff.get('prover_results', {})
            for prover, status in prover_results.items():
                print(f"      {prover}: {status}")
            if diff.get('error_message'):
                error_msg = diff['error_message'][:80]
                print(f"      Error: {error_msg}...")
            print()
    
    # 总结
    print("=" * 60)
    print("📊 总结")
    print("=" * 60)
    print(f"总测试结果数: {analysis['total_bugs'] + analysis['total_differentials']}")
    print(f"Bug率: {(analysis['total_bugs'] / max(1, analysis['total_bugs'] + analysis['total_differentials'])) * 100:.2f}%")
    print()


def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("用法: python3 分析结果.py <结果目录>")
        print("示例: python3 分析结果.py ./fuzzer_results")
        sys.exit(1)
    
    results_dir = sys.argv[1]
    print_analysis(results_dir)


if __name__ == "__main__":
    main()

