#!/usr/bin/env python3
"""
重新分析超时Bug的执行时间
使用10秒超时阈值测试原始文件，对比变异文件
"""

import json
import glob
import subprocess
import time
from pathlib import Path
from collections import defaultdict

def test_eprover_timeout(input_file: str, timeout: float = 10.0) -> dict:
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

def analyze_timeout_bugs_with_10s_timeout():
    """使用10秒超时阈值重新分析所有超时Bug的执行时间"""
    
    bug_dir = Path('week8-9_integration_bug_test')
    seed_dir = Path('../sledgehammer_export')
    timeout_threshold = 10.0  # 使用与fuzzer相同的超时阈值
    
    # 读取所有bug报告
    bug_files = sorted(glob.glob(str(bug_dir / 'bug_*.json')))
    
    print("═══════════════════════════════════════════════════════")
    print("🔍 超时Bug执行时间分析（使用10秒超时阈值）")
    print("═══════════════════════════════════════════════════════")
    print()
    print(f"找到 {len(bug_files)} 个超时Bug报告")
    print(f"使用超时阈值: {timeout_threshold}秒（与fuzzer相同）")
    print()
    
    # 收集所有唯一的种子文件
    seeds = set()
    for bug_file in bug_files:
        with open(bug_file, 'r') as f:
            bug = json.load(f)
            seeds.add(bug['seed'])
    
    print(f"涉及 {len(seeds)} 个不同的种子文件: {', '.join(sorted(seeds))}")
    print()
    
    # 分析结果
    results = []
    
    # 先测试所有唯一的原始种子文件（避免重复测试）
    print("第一步：测试原始种子文件（使用10秒超时阈值）")
    print("─" * 60)
    original_results = {}
    
    for seed_name in sorted(seeds):
        # 查找原始种子文件
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
            print(f"测试原始种子: {original_file.name}")
            result = test_eprover_timeout(str(original_file), timeout=timeout_threshold)
            original_results[seed_name] = result
            if result['status'] == 'timeout':
                print(f"  ⚠️  超时（>{timeout_threshold}秒）")
            elif result['status'] == 'success':
                print(f"  ✅ 成功，执行时间: {result['execution_time']:.3f}秒")
            else:
                print(f"  ❌ 错误: {result['output'][:100]}")
        else:
            print(f"  ⚠️  原始种子文件未找到: {seed_name}")
            original_results[seed_name] = {'status': 'not_found', 'execution_time': None}
        print()
    
    # 第二步：分析每个bug
    print()
    print("第二步：分析每个Bug（变异文件时间来自bug报告）")
    print("─" * 60)
    
    for i, bug_file in enumerate(bug_files, 1):
        with open(bug_file, 'r') as f:
            bug = json.load(f)
        
        seed_name = bug['seed']
        mutant_id = bug['mutant_id']
        prover = bug['prover']
        mutant_time = bug.get('execution_time', 10.003)
        
        original_result = original_results.get(seed_name, {'status': 'unknown', 'execution_time': None})
        original_time = original_result.get('execution_time')
        original_status = original_result.get('status')
        
        print(f"[{i}/{len(bug_files)}] {seed_name}_mutant_{mutant_id}")
        print(f"  原始文件: {original_time:.3f}秒 ({original_status})" if original_time else f"  原始文件: 未找到")
        print(f"  变异文件: {mutant_time:.3f}秒 (timeout)")
        
        # 对比分析
        if original_time is not None:
            if original_status == 'success' and original_time < 1.0:
                if mutant_time > timeout_threshold:
                    analysis = "✅ 明显的性能退化（正常→超时）"
                    classification = "clear_degradation"
                else:
                    analysis = "⚠️  性能退化但未超时"
                    classification = "degradation"
            elif original_status == 'success' and original_time < 5.0:
                if mutant_time > timeout_threshold:
                    analysis = "⚠️  性能退化（较慢→超时）"
                    classification = "degradation"
                else:
                    analysis = "⚠️  轻微性能退化"
                    classification = "minor_degradation"
            elif original_status == 'success' and original_time < timeout_threshold:
                if mutant_time > timeout_threshold:
                    analysis = "⚠️  性能退化（接近超时→超时）"
                    classification = "degradation"
                else:
                    analysis = "⚠️  原始文件也较慢"
                    classification = "both_slow"
            elif original_status == 'timeout':
                # 原始文件也超时
                if abs(original_time - mutant_time) < 0.1:
                    analysis = "⚠️  原始文件也会超时（可能不是变异导致的问题）"
                    classification = "original_also_timeout"
                else:
                    analysis = "⚠️  原始文件也超时，但时间不同"
                    classification = "both_timeout"
            else:
                analysis = "⚠️  需要进一步分析"
                classification = "unknown"
            
            speedup = mutant_time / original_time if original_time > 0 else float('inf')
            if original_time < timeout_threshold:
                print(f"  对比: {original_time:.3f}秒 → {mutant_time:.3f}秒 (慢 {speedup:.1f}x)")
            else:
                print(f"  对比: 原始{original_time:.3f}秒（超时）→ 变异{mutant_time:.3f}秒（超时）")
            print(f"  分析: {analysis}")
        else:
            print(f"  对比: 无法对比（原始文件未找到）")
            analysis = "无法分析"
            classification = "no_original"
        
        results.append({
            'seed': seed_name,
            'mutant_id': mutant_id,
            'original_time': original_time,
            'mutant_time': mutant_time,
            'original_status': original_status,
            'mutant_status': 'timeout',
            'speedup': mutant_time / original_time if original_time and original_time > 0 else None,
            'classification': classification,
            'analysis': analysis
        })
        print()
    
    # 统计分析
    print()
    print("═══════════════════════════════════════════════════════")
    print("📊 统计分析")
    print("═══════════════════════════════════════════════════════")
    print()
    
    # 找到原始文件的bug数量
    bugs_with_original = [r for r in results if r['original_time'] is not None]
    print(f"找到原始文件的Bug数量: {len(bugs_with_original)}/{len(results)}")
    print()
    
    if bugs_with_original:
        # 按分类统计
        classifications = defaultdict(list)
        for r in bugs_with_original:
            classifications[r['classification']].append(r)
        
        print("📊 按分类统计:")
        for cls, bugs in sorted(classifications.items()):
            print(f"  {cls}: {len(bugs)}个 ({len(bugs)*100//len(bugs_with_original)}%)")
        
        # 原始文件执行时间统计
        original_times = [r['original_time'] for r in bugs_with_original]
        print()
        print(f"原始文件执行时间:")
        print(f"  平均: {sum(original_times)/len(original_times):.3f}秒")
        print(f"  最小: {min(original_times):.3f}秒")
        print(f"  最大: {max(original_times):.3f}秒")
        
        # 成功的原始文件
        successful_originals = [r for r in bugs_with_original if r['original_status'] == 'success']
        timeout_originals = [r for r in bugs_with_original if r['original_status'] == 'timeout']
        
        print()
        print(f"原始文件结果:")
        print(f"  成功: {len(successful_originals)}个")
        print(f"  超时: {len(timeout_originals)}个")
        
        if successful_originals:
            successful_times = [r['original_time'] for r in successful_originals]
            print(f"  成功文件平均时间: {sum(successful_times)/len(successful_times):.3f}秒")
            print(f"  成功文件最小时间: {min(successful_times):.3f}秒")
            print(f"  成功文件最大时间: {max(successful_times):.3f}秒")
        
        print()
        print(f"变异文件执行时间:")
        print(f"  平均: {sum([r['mutant_time'] for r in bugs_with_original])/len(bugs_with_original):.3f}秒")
        print(f"  最小: {min([r['mutant_time'] for r in bugs_with_original]):.3f}秒")
        print(f"  最大: {max([r['mutant_time'] for r in bugs_with_original]):.3f}秒")
        
        # 明显的性能退化（<1秒 → >10秒）
        clear_degradations = [r for r in bugs_with_original 
                             if r['classification'] == 'clear_degradation']
        print()
        print(f"明显的性能退化 (<1秒成功 → >10秒超时): {len(clear_degradations)}/{len(bugs_with_original)}")
        
        # 原始文件也超时的
        original_also_timeout = [r for r in bugs_with_original 
                                if r['classification'] == 'original_also_timeout']
        print(f"原始文件也会超时: {len(original_also_timeout)}/{len(bugs_with_original)}")
        
        print()
    
    # 保存详细结果
    output_file = bug_dir / 'bug_execution_time_analysis_10s.json'
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump({
            'analysis_date': time.strftime('%Y-%m-%d %H:%M:%S'),
            'timeout_threshold': timeout_threshold,
            'total_bugs': len(results),
            'original_seeds_test': {k: {
                'status': v['status'],
                'execution_time': v.get('execution_time')
            } for k, v in original_results.items()},
            'bug_analysis': results
        }, f, indent=2, ensure_ascii=False)
    
    print(f"详细结果已保存到: {output_file}")
    print()
    
    # 总结
    print("═══════════════════════════════════════════════════════")
    print("✅ 分析完成")
    print("═══════════════════════════════════════════════════════")
    print()
    
    if bugs_with_original:
        successful_originals = [r for r in bugs_with_original if r['original_status'] == 'success']
        clear_degradations = [r for r in bugs_with_original if r['classification'] == 'clear_degradation']
        original_also_timeout = [r for r in bugs_with_original if r['classification'] == 'original_also_timeout']
        
        if clear_degradations:
            print("✅ 结论:")
            print(f"  发现 {len(clear_degradations)} 个明显的性能退化Bug！")
            print(f"  这些Bug的原始文件在1秒内成功，但变异后超时。")
        elif successful_originals:
            print("⚠️  结论:")
            print(f"  {len(successful_originals)} 个原始文件成功，但变异后超时。")
            print(f"  这可能反映了变异导致的性能问题。")
        elif original_also_timeout:
            print("⚠️  结论:")
            print(f"  所有原始文件也会在10秒超时。")
            print(f"  这些超时Bug可能不是变异导致的，而是原始文件本身就很慢。")
            print(f"  但仍然反映了E Prover处理这些输入时的性能问题。")
        else:
            print("⚠️  结论:")
            print(f"  需要进一步分析。")
    
    return results

if __name__ == "__main__":
    analyze_timeout_bugs_with_10s_timeout()

