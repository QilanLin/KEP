#!/usr/bin/env python3
"""
Isabelle Sledgehammer Fuzzer
主程序入口
"""

import os
import sys
import argparse
import json
from pathlib import Path
from datetime import datetime
from typing import List, Dict

# 添加项目路径
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    from parser.tptp_parser import TPTPParser
    from mutator.token_mutator import TokenMutator
    from mutator.ast_mutator import ASTMutator, ASTMutationType
    from oracle.crash_oracle import CrashOracle
    from oracle.differential_oracle import DifferentialOracle
    from oracle.reconstruction_oracle import ReconstructionOracle, ProverResult as ReconstructionProverResult
    from utils.logger import FuzzerLogger
    from utils.stats import StatsCollector
    from utils.progress import ProgressBar, LiveStats
    from utils.visualization import FuzzerVisualizer
    from utils.cache import ProverPathCache
except ImportError:
    # 如果相对导入失败，尝试直接导入
    import sys
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from parser.tptp_parser import TPTPParser
    from mutator.token_mutator import TokenMutator
    from mutator.ast_mutator import ASTMutator, ASTMutationType
    from oracle.crash_oracle import CrashOracle
    from oracle.differential_oracle import DifferentialOracle
    from oracle.reconstruction_oracle import ReconstructionOracle, ProverResult as ReconstructionProverResult
    from utils.logger import FuzzerLogger
    from utils.stats import StatsCollector
    from utils.progress import ProgressBar, LiveStats
    from utils.visualization import FuzzerVisualizer
    from utils.cache import ProverPathCache


class Fuzzer:
    """Fuzzer主类"""
    
    def __init__(self, config: Dict):
        """
        初始化Fuzzer
        
        Args:
            config: 配置字典
        """
        self.config = config
        self.seed_dir = config.get('seed_dir', '../sledgehammer_export')
        self.output_dir = config.get('output_dir', './fuzzer_results')
        # 修复：将默认超时从5秒增加到30秒，避免复杂种子误报
        self.timeout = config.get('timeout', 30.0)
        self.num_mutants = config.get('num_mutants', 10)
        
        # 新增：种子预过滤配置
        self.enable_seed_filtering = config.get('enable_seed_filtering', True)
        self.seed_filter_timeout = config.get('seed_filter_timeout', 10.0)
        
        # 新增：相对执行时间bug检测配置
        self.use_relative_time_check = config.get('use_relative_time_check', True)
        self.relative_time_threshold = config.get('relative_time_threshold', 2.0)  # 2倍阈值
        
        # 记录种子执行时间（用于相对时间比较）
        self.seed_execution_times = {}
        
        # 变异器选择：Token级别或AST级别
        self.use_ast_mutator = config.get('use_ast_mutator', False)
        
        # 初始化组件
        self.parser = TPTPParser()
        if self.use_ast_mutator:
            self.mutator = ASTMutator(seed=config.get('random_seed'))
            mutator_type = "AST级别"
        else:
            self.mutator = TokenMutator(seed=config.get('random_seed'))
            mutator_type = "Token级别"
        
        self.crash_oracle = CrashOracle(timeout=self.timeout)
        self.diff_oracle = DifferentialOracle()
        
        # 重构Oracle设置
        self.use_reconstruction_oracle = config.get('use_reconstruction_oracle', False)
        self.isabelle_path = config.get('isabelle_path', 'isabelle')
        self.reconstruction_timeout = config.get('reconstruction_timeout', 30.0)
        
        if self.use_reconstruction_oracle:
            self.reconstruction_oracle = ReconstructionOracle(
                isabelle_path=self.isabelle_path,
                timeout=self.reconstruction_timeout
            )
        else:
            self.reconstruction_oracle = None
        
        # 优化：使用缓存
        self.prover_cache = ProverPathCache()
        
        # 并行处理设置
        self.use_parallel = config.get('use_parallel', False)
        self.num_workers = config.get('num_workers', None)
        
        # 进度显示设置
        self.show_progress = config.get('show_progress', True)
        self.progress_bar = None
        self.live_stats = None
        
        # 可视化设置
        self.generate_visualization = config.get('generate_visualization', False)
        
        # 记录变异器类型
        self.mutator_type = mutator_type
        
        # 创建输出目录
        os.makedirs(self.output_dir, exist_ok=True)
        
        # 初始化日志和统计
        log_dir = os.path.join(self.output_dir, 'logs')
        stats_dir = os.path.join(self.output_dir, 'stats')
        self.logger = FuzzerLogger(log_dir=log_dir)
        self.stats_collector = StatsCollector(output_dir=stats_dir)
        
        # 可视化工具
        if self.generate_visualization:
            viz_dir = os.path.join(self.output_dir, 'visualization')
            self.visualizer = FuzzerVisualizer(output_dir=viz_dir)
        else:
            self.visualizer = None
        
        # 保留旧统计信息字典（用于兼容）
        self.stats = {
            'total_tests': 0,
            'crashes': 0,
            'timeouts': 0,
            'differentials': 0,
            'reconstruction_failures': 0,
            'bugs_found': 0
        }
    
    def run(self):
        """运行fuzzer"""
        print("🚀 Isabelle Sledgehammer Fuzzer")
        print("=" * 50)
        print(f"种子目录: {self.seed_dir}")
        print(f"输出目录: {self.output_dir}")
        print(f"超时时间: {self.timeout}秒")
        print(f"每个种子的变异体数: {self.num_mutants}")
        print(f"变异器类型: {self.mutator_type}")
        if self.use_reconstruction_oracle:
            print(f"重构Oracle: 启用 (超时: {self.reconstruction_timeout}秒)")
        else:
            print(f"重构Oracle: 禁用")
        print()
        
        self.logger.info("Fuzzer开始运行")
        self.logger.info(f"配置: seed_dir={self.seed_dir}, output_dir={self.output_dir}, timeout={self.timeout}, num_mutants={self.num_mutants}")
        
        # 获取所有种子文件
        seed_files = list(Path(self.seed_dir).glob("*.p"))
        
        if not seed_files:
            error_msg = f"未找到种子文件: {self.seed_dir}"
            print(f"❌ {error_msg}")
            self.logger.error(error_msg)
            return
        
        print(f"找到 {len(seed_files)} 个种子文件")
        self.logger.info(f"找到 {len(seed_files)} 个种子文件")
        
        # 种子预过滤
        if self.enable_seed_filtering:
            print(f"\n🔍 种子预过滤（超时阈值: {self.seed_filter_timeout}秒）...")
            seed_files = self._filter_slow_seeds(seed_files)
            print(f"✅ 过滤后剩余 {len(seed_files)} 个种子文件")
            self.logger.info(f"种子过滤后剩余 {len(seed_files)} 个")
        
        # 处理每个种子文件（限制数量）
        max_seeds = self.config.get('max_seeds', 10)
        seed_files_to_process = seed_files[:max_seeds]
        
        # 初始化进度条
        if self.show_progress:
            self.progress_bar = ProgressBar(
                total=max_seeds,
                prefix='处理种子',
                suffix='完成'
            )
            self.live_stats = LiveStats()
        
        print()
        
        # 处理每个种子文件
        for i, seed_file in enumerate(seed_files_to_process, 1):
            if not self.show_progress:
                print(f"[{i}/{len(seed_files_to_process)}] 处理种子: {seed_file.name}")
            self.logger.info(f"处理种子 [{i}/{len(seed_files_to_process)}]: {seed_file.name}")
            
            self._process_seed(seed_file)
            
            # 更新进度条
            if self.show_progress:
                self.progress_bar.update(1)
                self.live_stats.update(
                    seeds_processed=i,
                    mutants_generated=self.stats_collector.stats.mutants_generated,
                    total_tests=self.stats['total_tests'],
                    crashes=self.stats['crashes'],
                    timeouts=self.stats['timeouts'],
                    differentials=self.stats['differentials'],
                    bugs_found=self.stats['bugs_found']
                )
            
            if not self.show_progress:
                print()
        
        # 完成进度条
        if self.show_progress:
            self.progress_bar.finish()
            self.live_stats.finish()
            print()
        
        # 保存统计信息
        stats_file = self.stats_collector.save_stats()
        self.logger.info(f"统计信息已保存到: {stats_file}")
        
        # 生成可视化报告
        if self.visualizer:
            try:
                self.visualizer.generate_report(str(stats_file))
            except Exception as e:
                print(f"⚠️  生成可视化报告失败: {e}")
                self.logger.warning(f"生成可视化报告失败: {e}")
        
        # 打印统计信息
        self._print_stats()
        
        self.logger.info("Fuzzer运行完成")
    
    def _filter_slow_seeds(self, seed_files: List[Path]) -> List[Path]:
        """
        过滤掉执行时间过长的种子
        
        Args:
            seed_files: 种子文件列表
            
        Returns:
            过滤后的种子文件列表
        """
        fast_seeds = []
        
        # 获取第一个可用的prover
        prover_path = None
        prover_name = None
        for name in ['z3', 'cvc5', 'eprover']:
            path = self.prover_cache.get_prover_path(name)
            if path:
                prover_path = path
                prover_name = name
                break
        
        if not prover_path:
            print("⚠️  未找到可用的prover，跳过种子过滤")
            return seed_files
        
        print(f"使用 {prover_name} 进行种子过滤测试...")
        
        for seed_file in seed_files:
            try:
                # 测试种子执行时间
                result = self.crash_oracle.check(prover_path, str(seed_file), 
                                                 prover_name=prover_name)
                
                # 记录执行时间
                seed_name = seed_file.stem
                self.seed_execution_times[seed_name] = result.execution_time
                
                # 如果在阈值内完成，则保留
                if result.execution_time < self.seed_filter_timeout:
                    fast_seeds.append(seed_file)
                    print(f"  ✅ {seed_name}: {result.execution_time:.2f}秒")
                else:
                    print(f"  ⏭️  {seed_name}: {result.execution_time:.2f}秒 (过慢，跳过)")
                    self.logger.info(f"种子 {seed_name} 执行时间过长 ({result.execution_time:.2f}秒)，已过滤")
            except Exception as e:
                # 如果测试失败，保留种子
                print(f"  ⚠️  {seed_file.name}: 测试失败，保留")
                fast_seeds.append(seed_file)
        
        return fast_seeds
    
    def _process_seed(self, seed_file: Path):
        """处理单个种子文件"""
        try:
            # 读取种子文件
            with open(seed_file, 'r', encoding='utf-8') as f:
                seed_content = f.read()
            
            # 生成变异体（支持激进策略）
            mutants = self.mutator.generate_mutants(seed_content, count=self.num_mutants)
            
            # 如果启用激进策略，添加激进的bug触发变异体
            if self.config.get('use_aggressive_mutator', False):
                try:
                    from mutator.aggressive_mutator import AggressiveMutator
                    import sys
                    import os
                    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
                    from aggressive_bug_finding_strategy import AggressiveBugFindingStrategy
                    
                    aggressive_mutator = AggressiveMutator(seed=self.config.get('random_seed'))
                    strategy = AggressiveBugFindingStrategy()
                    
                    # 添加激进变异体
                    aggressive_mutants = aggressive_mutator.generate_aggressive_mutants(
                        seed_content, count=self.num_mutants // 2
                    )
                    
                    # 添加crash触发器
                    crash_triggers = strategy.create_crash_triggers(seed_content)
                    
                    # 添加timeout触发器
                    timeout_triggers = strategy.create_timeout_triggers(seed_content)
                    
                    # 如果启用极端策略，添加极端变异体
                    if self.config.get('use_extreme_mutator', False):
                        try:
                            from mutator.extreme_mutator import ExtremeMutator
                            extreme_mutator = ExtremeMutator(seed=self.config.get('random_seed'))
                            extreme_mutants = extreme_mutator.generate_extreme_mutants(
                                seed_content, count=self.num_mutants // 4
                            )
                            aggressive_mutants.extend(extreme_mutants)
                            
                            # 添加极端边界情况
                            edge_cases = extreme_mutator.generate_edge_cases(seed_content)
                            aggressive_mutants.extend(edge_cases[:10])  # 添加前10个边界情况
                        except Exception as e:
                            # 如果极端策略失败，继续使用激进策略
                            import warnings
                            warnings.warn(f"Extreme mutation strategy failed: {e}", RuntimeWarning)
                    
                    # 合并所有变异体
                    all_mutants = list(mutants)
                    all_mutants.extend(aggressive_mutants)
                    all_mutants.extend(crash_triggers)
                    all_mutants.extend(timeout_triggers)
                    
                    # 去重并限制数量
                    seen = set()
                    unique_mutants = []
                    for m in all_mutants:
                        if m not in seen and m != seed_content:
                            seen.add(m)
                            unique_mutants.append(m)
                        if len(unique_mutants) >= self.num_mutants * 3:  # 允许更多激进变异体
                            break
                    
                    mutants = unique_mutants[:self.num_mutants * 3]
                except Exception as e:
                    # 如果激进策略失败，使用原始变异体
                    import warnings
                    warnings.warn(f"Aggressive mutation strategy failed: {e}", RuntimeWarning)
            
            print(f"  生成 {len(mutants)} 个变异体")
            self.logger.info(f"种子 {seed_file.name}: 生成 {len(mutants)} 个变异体")
            self.stats_collector.record_seed(mutants_generated=len(mutants))
            
            # 测试每个变异体
            for j, mutant in enumerate(mutants, 1):
                self._test_mutant(seed_file.stem, j, mutant)
                self.stats['total_tests'] += 1
        
        except Exception as e:
            error_msg = f"处理种子文件失败: {e}"
            print(f"  ❌ {error_msg}")
            self.logger.error(f"种子 {seed_file.name}: {error_msg}")
    
    def _test_mutant(self, seed_name: str, mutant_id: int, mutant_content: str):
        """测试单个变异体"""
        import shutil
        import time
        
        # 记录测试开始
        self.logger.test_start(seed_name, mutant_id)
        start_time = time.time()
        
        # 创建临时文件
        temp_file = Path(self.output_dir) / f"{seed_name}_mutant_{mutant_id}.p"
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(mutant_content)
        
        # 运行provers（检查PATH）
        provers = {}
        
        # SMT Solvers
        z3_path = self.prover_cache.get_prover_path('z3')
        if z3_path:
            provers['z3'] = z3_path
        else:
            warning_msg = "Z3未找到，跳过Z3测试"
            if not self.show_progress:
                print(f"    ⚠️  {warning_msg}")
            self.logger.warning(warning_msg)
        
        cvc5_path = self.prover_cache.get_prover_path('cvc5')
        if cvc5_path:
            provers['cvc5'] = cvc5_path
        else:
            warning_msg = "cvc5未找到，跳过cvc5测试"
            if not self.show_progress:
                print(f"    ⚠️  {warning_msg}")
            self.logger.warning(warning_msg)
        
        # ATP Provers (新增)
        eprover_path = self.prover_cache.get_prover_path('eprover')
        if eprover_path:
            provers['eprover'] = eprover_path
        else:
            warning_msg = "E Prover未找到，跳过E Prover测试"
            if not self.show_progress:
                print(f"    ⚠️  {warning_msg}")
            self.logger.warning(warning_msg)
        
        vampire_path = self.prover_cache.get_prover_path('vampire')
        if vampire_path:
            provers['vampire'] = vampire_path
        else:
            warning_msg = "Vampire未找到，跳过Vampire测试"
            if not self.show_progress:
                print(f"    ⚠️  {warning_msg}")
            self.logger.warning(warning_msg)
        
        spass_path = self.prover_cache.get_prover_path('spass')
        if spass_path:
            provers['spass'] = spass_path
        else:
            warning_msg = "SPASS未找到，跳过SPASS测试"
            if not self.show_progress:
                print(f"    ⚠️  {warning_msg}")
            self.logger.warning(warning_msg)
        
        if not provers:
            error_msg = "未找到任何prover，跳过变异体测试"
            print(f"    ❌ {error_msg}")
            self.logger.error(error_msg)
            if temp_file.exists():
                temp_file.unlink()
            return
        
        results = {}
        prover_results_for_reconstruction = {}
        
        for prover_name, prover_path in provers.items():
            # 传递prover_name以使用正确的命令参数
            result = self.crash_oracle.check(prover_path, str(temp_file), prover_name=prover_name)
            results[prover_name] = result
            
            # 记录统计
            self.stats_collector.record_test(execution_time=result.execution_time)
            
            # 新增：相对执行时间检查
            is_performance_bug = False
            if self.use_relative_time_check and seed_name in self.seed_execution_times:
                original_time = self.seed_execution_times[seed_name]
                mutant_time = result.execution_time
                
                # 如果变异导致执行时间增加超过阈值倍数，认为是性能bug
                if mutant_time > original_time * self.relative_time_threshold:
                    is_performance_bug = True
                    print(f"    ⚠️  性能退化: {prover_name} 执行时间从 {original_time:.2f}秒 增加到 {mutant_time:.2f}秒 ({mutant_time/original_time:.1f}x)")
                    self.logger.warning(f"性能bug: {seed_name}_mutant_{mutant_id} - {prover_name}: {original_time:.2f}秒 → {mutant_time:.2f}秒")
            
            # 检查crash/timeout或性能bug
            if self.crash_oracle.is_bug(result) or is_performance_bug:
                if result.status.value == 'crash':
                    self.stats['crashes'] += 1
                    self.stats_collector.record_crash({
                        'bug_type': 'crash',
                        'prover': prover_name,
                        'seed': seed_name,
                        'mutant_id': mutant_id
                    })
                elif result.status.value == 'timeout':
                    self.stats['timeouts'] += 1
                    self.stats_collector.record_timeout({
                        'bug_type': 'timeout',
                        'prover': prover_name,
                        'seed': seed_name,
                        'mutant_id': mutant_id
                    })
                elif is_performance_bug:
                    self.stats['timeouts'] += 1  # 性能bug归类为timeout
                    self.stats_collector.record_timeout({
                        'bug_type': 'performance_degradation',
                        'prover': prover_name,
                        'seed': seed_name,
                        'mutant_id': mutant_id
                    })
                
                self._report_bug(seed_name, mutant_id, prover_name, result)
            else:
                # 如果prover正常完成，准备用于重构检查
                # 简化处理：假设如果正常完成且有输出，可能有证明
                if result.stdout and ('sat' in result.stdout.lower() or 'unsat' in result.stdout.lower()):
                    prover_results_for_reconstruction[prover_name] = result
        
        # 检查差异
        diff_result = self.diff_oracle.check(results)
        if self.diff_oracle.is_bug(diff_result):
            self.stats['differentials'] += 1
            self.stats_collector.record_differential({
                'seed': seed_name,
                'mutant_id': mutant_id,
                'prover_results': {k: v.value for k, v in diff_result.prover_results.items()}
            })
            self._report_differential(seed_name, mutant_id, diff_result)
        
        # 检查重构失败（如果启用重构Oracle）
        if self.use_reconstruction_oracle and self.reconstruction_oracle and prover_results_for_reconstruction:
            # 对每个找到证明的prover检查重构
            for prover_name, crash_result in prover_results_for_reconstruction.items():
                # 创建重构用的ProverResult
                prover_result = ReconstructionProverResult(
                    status="sat" if "sat" in crash_result.stdout.lower() else "unsat",
                    proof=crash_result.stdout,  # 简化：使用完整输出作为证明
                    model=None,
                    error=crash_result.stderr if crash_result.stderr else None
                )
                
                # 尝试重构（需要原始理论文件，这里简化处理）
                # 注意：实际使用需要维护TPTP文件与原始.thy文件的映射
                original_thy_file = None  # 实际使用时需要提供
                
                if original_thy_file and Path(original_thy_file).exists():
                    recon_result = self.reconstruction_oracle.check(
                        prover_result=prover_result,
                        original_thy_file=original_thy_file,
                        mutant_file=str(temp_file)
                    )
                    
                    if self.reconstruction_oracle.is_bug(recon_result):
                        # 发现重构失败
                        self.stats['reconstruction_failures'] += 1
                        self.stats['bugs_found'] += 1
                        self.stats_collector.record_crash({
                            'bug_type': 'reconstruction_failure',
                            'prover': prover_name,
                            'seed': seed_name,
                            'mutant_id': mutant_id,
                            'failure_type': recon_result.failure_type.value if recon_result.failure_type else 'unknown',
                            'error_message': recon_result.error_message
                        })
                        self._report_reconstruction_failure(seed_name, mutant_id, prover_name, recon_result)
        
        # 计算执行时间
        execution_time = time.time() - start_time
        self.stats_collector.record_test(execution_time)
        
        # 记录测试结束
        status = 'normal'
        if self.stats['bugs_found'] > 0 or self.stats['differentials'] > 0:
            status = 'bug_found'
        self.logger.test_end(seed_name, mutant_id, status)
        
        # 清理临时文件
        if temp_file.exists():
            temp_file.unlink()
    
    def _report_bug(self, seed_name: str, mutant_id: int, prover_name: str, result):
        """报告bug"""
        self.stats['bugs_found'] += 1
        
        # 计算相对执行时间（如果有原始时间记录）
        relative_time = None
        if seed_name in self.seed_execution_times:
            original_time = self.seed_execution_times[seed_name]
            relative_time = result.execution_time / original_time if original_time > 0 else None
        
        bug_report = {
            'timestamp': datetime.now().isoformat(),
            'seed': seed_name,
            'mutant_id': mutant_id,
            'prover': prover_name,
            'bug_type': result.status.value,
            'error_message': result.error_message,
            'execution_time': result.execution_time,
            'original_execution_time': self.seed_execution_times.get(seed_name),
            'relative_time': relative_time
        }
        
        # 保存bug报告
        report_file = Path(self.output_dir) / f"bug_{self.stats['bugs_found']}.json"
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(bug_report, f, indent=2)
        
        bug_msg = f"发现bug: {prover_name} - {result.status.value}"
        if relative_time and relative_time > 1.0:
            bug_msg += f" (相对时间: {relative_time:.1f}x)"
        print(f"    ⚠️  {bug_msg}")
        self.logger.bug_found(result.status.value, f"{seed_name}_mutant_{mutant_id} - {prover_name}: {result.error_message}")
    
    def _report_differential(self, seed_name: str, mutant_id: int, diff_result):
        """报告差异"""
        diff_report = {
            'timestamp': datetime.now().isoformat(),
            'seed': seed_name,
            'mutant_id': mutant_id,
            'prover_results': {k: v.value for k, v in diff_result.prover_results.items()},
            'error_message': diff_result.error_message
        }
        
        # 保存差异报告
        report_file = Path(self.output_dir) / f"differential_{self.stats['differentials']}.json"
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(diff_report, f, indent=2)
        
        diff_msg = f"发现差异: {diff_result.error_message}"
        print(f"    ⚠️  {diff_msg}")
        self.logger.differential_found(f"{seed_name}_mutant_{mutant_id}: {diff_result.error_message}")
    
    def _report_reconstruction_failure(self, seed_name: str, mutant_id: int, 
                                       prover_name: str, recon_result):
        """报告重构失败"""
        recon_report = {
            'timestamp': datetime.now().isoformat(),
            'seed': seed_name,
            'mutant_id': mutant_id,
            'prover': prover_name,
            'bug_type': 'reconstruction_failure',
            'failure_type': recon_result.failure_type.value if recon_result.failure_type else 'unknown',
            'error_message': recon_result.error_message,
            'isabelle_output': recon_result.isabelle_output,
            'execution_time': recon_result.execution_time
        }
        
        # 保存重构失败报告
        report_file = Path(self.output_dir) / f"reconstruction_failure_{self.stats['reconstruction_failures']}.json"
        with open(report_file, 'w', encoding='utf-8') as f:
            json.dump(recon_report, f, indent=2)
        
        failure_type = recon_result.failure_type.value if recon_result.failure_type else 'unknown'
        recon_msg = f"发现重构失败: {prover_name} - {failure_type}"
        print(f"    ⚠️  {recon_msg}")
        self.logger.bug_found('reconstruction_failure', 
                             f"{seed_name}_mutant_{mutant_id} - {prover_name}: {failure_type} - {recon_result.error_message}")
    
    def _print_stats(self):
        """打印统计信息"""
        print("=" * 50)
        print("📊 统计信息:")
        print(f"  总测试数: {self.stats['total_tests']}")
        print(f"  崩溃数: {self.stats['crashes']}")
        print(f"  超时数: {self.stats['timeouts']}")
        print(f"  差异数: {self.stats['differentials']}")
        if self.use_reconstruction_oracle:
            print(f"  重构失败数: {self.stats['reconstruction_failures']}")
        print(f"  发现的bug总数: {self.stats['bugs_found']}")
        print(f"  输出目录: {self.output_dir}")
        print()
        
        # 打印详细统计摘要
        self.stats_collector.print_summary()


def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Isabelle Sledgehammer Fuzzer')
    parser.add_argument('--seed-dir', default='../sledgehammer_export',
                       help='种子文件目录')
    parser.add_argument('--output-dir', default='./fuzzer_results',
                       help='输出目录')
    parser.add_argument('--timeout', type=float, default=30.0,
                        help='超时时间（秒，默认30秒）')
    parser.add_argument('--num-mutants', type=int, default=10,
                       help='每个种子生成的变异体数')
    parser.add_argument('--max-seeds', type=int, default=10,
                       help='最大处理种子数')
    parser.add_argument('--use-parallel', action='store_true',
                       help='使用并行处理')
    parser.add_argument('--num-workers', type=int, default=None,
                       help='并行工作进程数（默认：CPU核心数-1）')
    parser.add_argument('--no-progress', action='store_true',
                       help='不显示进度条')
    parser.add_argument('--generate-viz', action='store_true',
                       help='生成可视化报告')
    parser.add_argument('--use-ast-mutator', action='store_true',
                       help='使用AST级别变异器（默认：Token级别）')
    parser.add_argument('--use-reconstruction-oracle', action='store_true',
                       help='启用重构Oracle检测')
    parser.add_argument('--isabelle-path', default='isabelle',
                       help='Isabelle可执行文件路径（默认：isabelle）')
    parser.add_argument('--reconstruction-timeout', type=float, default=30.0,
                       help='重构超时时间（秒，默认：30.0）')
    parser.add_argument('--use-aggressive-mutator', action='store_true',
                       help='使用激进变异器（包括破坏语法的变异）')
    parser.add_argument('--use-extreme-mutator', action='store_true',
                       help='使用极端变异器（包括极大输入、极深嵌套等）')
    parser.add_argument('--random-seed', type=int, default=None,
                       help='随机数种子（用于可重复性）')
    
    # 新增：种子过滤和相对时间检测参数
    parser.add_argument('--enable-seed-filtering', action='store_true', default=True,
                        help='启用种子预过滤（默认启用）')
    parser.add_argument('--seed-filter-timeout', type=float, default=10.0,
                        help='种子过滤超时阈值（秒）')
    parser.add_argument('--use-relative-time-check', action='store_true', default=True,
                        help='使用相对执行时间检查（默认启用）')
    parser.add_argument('--relative-time-threshold', type=float, default=2.0,
                        help='相对时间阈值（倍数，默认2.0）')
    
    args = parser.parse_args()
    
    config = {
        'seed_dir': args.seed_dir,
        'output_dir': args.output_dir,
        'timeout': args.timeout,
        'num_mutants': args.num_mutants,
        'max_seeds': args.max_seeds,
        'use_parallel': args.use_parallel,
        'num_workers': args.num_workers,
        'show_progress': not args.no_progress,
        'generate_visualization': args.generate_viz,
        'use_ast_mutator': args.use_ast_mutator,
        'use_reconstruction_oracle': args.use_reconstruction_oracle,
        'isabelle_path': args.isabelle_path,
        'reconstruction_timeout': args.reconstruction_timeout,
        'random_seed': args.random_seed,
        'use_aggressive_mutator': args.use_aggressive_mutator if hasattr(args, 'use_aggressive_mutator') else False,
        'use_extreme_mutator': args.use_extreme_mutator if hasattr(args, 'use_extreme_mutator') else False,
        'enable_seed_filtering': args.enable_seed_filtering,
        'seed_filter_timeout': args.seed_filter_timeout,
        'use_relative_time_check': args.use_relative_time_check,
        'relative_time_threshold': args.relative_time_threshold
    }
    
    fuzzer = Fuzzer(config)
    fuzzer.run()


if __name__ == "__main__":
    main()

