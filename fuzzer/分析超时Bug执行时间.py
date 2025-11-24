#!/usr/bin/env python3
"""
分析超时Bug的执行时间
对比原始种子文件和变异后文件的执行时间
"""

import json
import glob
import subprocess
import time
from pathlib import Path
from collections import defaultdict

def test_eprover_timeout(input_file: str, timeout: float = 15.0) -> dict:
    """
    测试E Prover的执行时间（带超时）
    
    Returns:
        {
            'execution_time': float,
            'status': 'success' | 'timeout' | 'error',
            'output': str
        }
    """
    try:
        cmd = ['eprover', '--auto', '--tstp-format', input_file]
        start_time = time.time()
        
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )
        
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            execution_time = time.time() - start_time
            exit_code = process.returncode
            
            return {
                'execution_time': execution_time,
                'status': 'success' if exit_code == 0 else 'error',
                'output': stdout[:200] if stdout else stderr[:200],
                'exit_code': exit_code
            }
        except subprocess.TimeoutExpired:
            execution_time = time.time() - start_time
            process.kill()
            process.wait()
            
            return {
                'execution_time': execution_time,
                'status': 'timeout',
                'output': '',
                'exit_code': -1
            }
    except Exception as e:
        return {
            'execution_time': 0.0,
            'status': 'error',
            'output': str(e),
            'exit_code': -1
        }

def analyze_timeout_bugs():
    """分析所有超时Bug的执行时间"""
    
    bug_dir = Path('week8-9_integration_bug_test')
    seed_dir = Path('../sledgehammer_export')
    
    # 读取所有bug报告
    bug_files = sorted(glob.glob(str(bug_dir / 'bug_*.json')))
    
    print("═══════════════════════════════════════════════════════")
    print("🔍 超时Bug执行时间分析")
    print("═══════════════════════════════════════════════════════")
    print()
    print(f"找到 {len(bug_files)} 个超时Bug报告")
    print()
    
    # 收集所有唯一的种子文件
    seeds = set()
    for bug_file in bug_files:
        with open(bug_file, 'r') as f:
            bug = json.load(f)
            seeds.add(bug['seed'])
    
    print(f"涉及 {len(seeds)} 个不同的种子文件")
    print()
    
    # 分析结果
    results = []
    
    # 测试每个bug
    for i, bug_file in enumerate(bug_files, 1):
        with open(bug_file, 'r') as f:
            bug = json.load(f)
        
        seed_name = bug['seed']
        mutant_id = bug['mutant_id']
        prover = bug['prover']
        
        print(f"[{i}/{len(bug_files)}] 分析Bug: {seed_name}_mutant_{mutant_id}")
        
        # 测试原始种子文件
        original_file = seed_dir / f"{seed_name}.p"
        if not original_file.exists():
            # 尝试其他可能的文件名
            possible_names = [
                f"{seed_name}_proof.p",
                f"{seed_name}_1.p",
                f"{seed_name}_1_proof.p"
            ]
            original_file = None
            for name in possible_names:
                test_file = seed_dir / name
                if test_file.exists():
                    original_file = test_file
                    break
        
        if original_file and original_file.exists():
            print(f"  测试原始种子: {original_file.name}")
            original_result = test_eprover_timeout(str(original_file), timeout=15.0)
            original_time = original_result['execution_time']
            print(f"    执行时间: {original_time:.3f}秒 ({original_result['status']})")
        else:
            print(f"  ⚠️  原始种子文件未找到: {seed_name}")
            original_time = None
            original_result = {'status': 'not_found'}
        
        # 查找变异后的文件（可能在临时目录或输出目录）
        mutant_files = [
            bug_dir / f"{seed_name}_mutant_{mutant_id}.p",
            bug_dir / "mutants" / f"{seed_name}_mutant_{mutant_id}.p",
            bug_dir / "temp" / f"{seed_name}_mutant_{mutant_id}.p",
        ]
        
        mutant_file = None
        for f in mutant_files:
            if f.exists():
                mutant_file = f
                break
        
        if mutant_file and mutant_file.exists():
            print(f"  测试变异文件: {mutant_file.name}")
            mutant_result = test_eprover_timeout(str(mutant_file), timeout=15.0)
            mutant_time = mutant_result['execution_time']
            print(f"    执行时间: {mutant_time:.3f}秒 ({mutant_result['status']})")
        else:
            print(f"  ⚠️  变异文件未找到: {seed_name}_mutant_{mutant_id}.p")
            mutant_time = bug.get('execution_time', 10.003)  # 使用bug报告中的时间
            mutant_result = {'status': 'timeout'}
        
        # 对比分析
        if original_time is not None:
            if original_time < 1.0 and mutant_time > 10.0:
                analysis = "✅ 明显的性能退化（正常→超时）"
            elif original_time < 5.0 and mutant_time > 10.0:
                analysis = "⚠️  性能退化（较慢→超时）"
            elif original_time < 10.0 and mutant_time > 10.0:
                analysis = "⚠️  性能退化（接近超时→超时）"
            else:
                analysis = "⚠️  原始文件也较慢"
            
            speedup = mutant_time / original_time if original_time > 0 else float('inf')
            print(f"  对比: {original_time:.3f}秒 → {mutant_time:.3f}秒 (慢 {speedup:.1f}x)")
            print(f"  分析: {analysis}")
        else:
            print(f"  对比: 无法对比（原始文件未找到）")
        
        results.append({
            'seed': seed_name,
            'mutant_id': mutant_id,
            'original_time': original_time,
            'mutant_time': mutant_time,
            'original_status': original_result.get('status'),
            'mutant_status': mutant_result.get('status'),
            'speedup': mutant_time / original_time if original_time and original_time > 0 else None
        })
        
        print()
    
    # 统计分析
    print("═══════════════════════════════════════════════════════")
    print("📊 统计分析")
    print("═══════════════════════════════════════════════════════")
    print()
    
    # 找到原始文件的bug数量
    bugs_with_original = [r for r in results if r['original_time'] is not None]
    print(f"找到原始文件的Bug数量: {len(bugs_with_original)}/{len(results)}")
    
    if bugs_with_original:
        # 原始文件执行时间统计
        original_times = [r['original_time'] for r in bugs_with_original]
        print(f"原始文件执行时间:")
        print(f"  平均: {sum(original_times)/len(original_times):.3f}秒")
        print(f"  最小: {min(original_times):.3f}秒")
        print(f"  最大: {max(original_times):.3f}秒")
        print()
        
        # 变异文件执行时间统计
        mutant_times = [r['mutant_time'] for r in bugs_with_original]
        print(f"变异文件执行时间:")
        print(f"  平均: {sum(mutant_times)/len(mutant_times):.3f}秒")
        print(f"  最小: {min(mutant_times):.3f}秒")
        print(f"  最大: {max(mutant_times):.3f}秒")
        print()
        
        # 性能退化分析
        speedups = [r['speedup'] for r in bugs_with_original if r['speedup'] is not None]
        if speedups:
            print(f"性能退化倍数:")
            print(f"  平均: {sum(speedups)/len(speedups):.1f}x")
            print(f"  最小: {min(speedups):.1f}x")
            print(f"  最大: {max(speedups):.1f}x")
            print()
        
        # 明显的性能退化（<1秒 → >10秒）
        clear_degradations = [r for r in bugs_with_original 
                             if r['original_time'] < 1.0 and r['mutant_time'] > 10.0]
        print(f"明显的性能退化 (<1秒 → >10秒): {len(clear_degradations)}/{len(bugs_with_original)}")
        
        # 原始文件也较慢的（>5秒）
        slow_originals = [r for r in bugs_with_original if r['original_time'] > 5.0]
        print(f"原始文件也较慢 (>5秒): {len(slow_originals)}/{len(bugs_with_original)}")
        print()
    
    # 保存详细结果
    output_file = bug_dir / 'bug_execution_time_analysis.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    print(f"详细结果已保存到: {output_file}")
    print()
    
    # 总结
    print("═══════════════════════════════════════════════════════")
    print("✅ 分析完成")
    print("═══════════════════════════════════════════════════════")
    print()
    
    if bugs_with_original:
        avg_original = sum(original_times) / len(original_times)
        avg_mutant = sum(mutant_times) / len(mutant_times)
        avg_speedup = sum(speedups) / len(speedups) if speedups else None
        
        if avg_original < 1.0 and avg_mutant > 10.0:
            conclusion = "✅ 这些确实是Bug！原始文件很快，变异后超时，说明变异引入了问题。"
        elif avg_original < 5.0 and avg_mutant > 10.0:
            conclusion = "✅ 这些是Bug！原始文件较慢但正常，变异后超时，说明变异导致性能问题。"
        elif avg_speedup and avg_speedup > 10:
            conclusion = f"✅ 这些是Bug！变异导致平均{avg_speedup:.1f}倍的性能退化。"
        else:
            conclusion = "⚠️  需要进一步分析。原始文件也可能较慢。"
        
        print("📊 结论:")
        print(f"  {conclusion}")
    
    return results

if __name__ == "__main__":
    analyze_timeout_bugs()

