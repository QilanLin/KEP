#!/usr/bin/env python3
"""
Integration Bug Testing - 测试Isabelle Sledgehammer接口
"""

import os
import sys
import argparse
import json
import time
from pathlib import Path
from typing import List, Dict, Optional
import logging

# 添加项目路径
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from oracle.isabelle_interface import IsabelleInterface, IsabelleStatus
from oracle.sledgehammer_oracle import SledgehammerOracle, IntegrationBugType
from mutator.ast_mutator import ASTMutator
from parser.tptp_parser import TPTPParser

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("integration_test.log"),
        logging.StreamHandler()
    ]
)

logger = logging.getLogger(__name__)


class IntegrationTester:
    """Integration测试器"""
    
    def __init__(self,
                 theory_dir: str,
                 output_dir: str,
                 timeout: float = 60.0):
        """
        初始化Integration测试器
        
        Args:
            theory_dir: Theory文件目录
            output_dir: 输出目录
            timeout: 超时时间
        """
        self.theory_dir = Path(theory_dir)
        self.output_dir = Path(output_dir)
        self.timeout = timeout
        
        # 创建输出目录
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # 初始化组件
        self.isabelle = IsabelleInterface()
        self.sledgehammer_oracle = SledgehammerOracle(self.isabelle)
        self.mutator = ASTMutator()
        self.parser = TPTPParser()
        
        # 统计数据
        self.stats = {
            "theories_tested": 0,
            "theories_success": 0,
            "theories_failed": 0,
            "bugs_found": 0,
            "bugs_by_type": {},
            "start_time": time.time()
        }
        
        self.bugs = []
    
    def find_theory_files(self) -> List[Path]:
        """查找所有theory文件"""
        theory_files = list(self.theory_dir.glob("*.thy"))
        logger.info(f"找到 {len(theory_files)} 个theory文件")
        return sorted(theory_files)
    
    def test_single_theory(self, thy_file: Path) -> Optional[Dict]:
        """
        测试单个theory文件
        
        Args:
            thy_file: Theory文件路径
            
        Returns:
            如果发现bug返回bug信息，否则返回None
        """
        logger.info(f"\n{'='*60}")
        logger.info(f"测试theory: {thy_file.name}")
        logger.info(f"{'='*60}")
        
        self.stats["theories_tested"] += 1
        
        # 使用Sledgehammer Oracle检查
        bug = self.sledgehammer_oracle.check_theory_file(
            str(thy_file),
            timeout=self.timeout
        )
        
        if bug:
            self.stats["theories_failed"] += 1
            self.stats["bugs_found"] += 1
            
            bug_type = bug.bug_type.value
            self.stats["bugs_by_type"][bug_type] = self.stats["bugs_by_type"].get(bug_type, 0) + 1
            
            logger.warning(f"🐛 发现Integration bug: {bug_type}")
            logger.warning(f"   描述: {bug.description}")
            
            # 保存bug报告
            bug_file = self.output_dir / f"integration_bug_{self.stats['bugs_found']}.json"
            self.sledgehammer_oracle.save_bug_report(bug, str(bug_file))
            
            bug_info = {
                "bug_id": self.stats["bugs_found"],
                "bug_type": bug_type,
                "thy_file": str(thy_file),
                "description": bug.description,
                "execution_time": bug.execution_time
            }
            
            self.bugs.append(bug_info)
            return bug_info
        else:
            self.stats["theories_success"] += 1
            logger.info(f"✅ {thy_file.name}: 通过测试")
            return None
    
    def test_theory_mutation(self, thy_file: Path) -> List[Dict]:
        """
        测试theory文件的变异版本
        
        注意: 这个功能需要先将.thy转换为TPTP，变异后再转回.thy
        目前简化实现，直接测试原始文件
        
        Args:
            thy_file: Theory文件路径
            
        Returns:
            发现的bugs列表
        """
        # TODO: 实现.thy变异测试
        # 1. 将.thy转换为TPTP
        # 2. 变异TPTP
        # 3. 将TPTP转回.thy（或直接测试TPTP）
        # 4. 比较行为差异
        
        logger.info(f"变异测试暂未实现: {thy_file.name}")
        return []
    
    def run_tests(self):
        """运行所有测试"""
        print("\n" + "="*60)
        print("🎯 Integration Bug Testing")
        print("="*60)
        print(f"Theory目录: {self.theory_dir}")
        print(f"输出目录: {self.output_dir}")
        print(f"超时设置: {self.timeout}秒")
        print("="*60)
        print()
        
        # 查找theory文件
        theory_files = self.find_theory_files()
        
        if not theory_files:
            logger.error("未找到theory文件!")
            return
        
        print(f"开始测试 {len(theory_files)} 个theory文件...")
        print()
        
        # 测试每个theory
        for i, thy_file in enumerate(theory_files, 1):
            print(f"[{i}/{len(theory_files)}] ", end="")
            try:
                self.test_single_theory(thy_file)
            except Exception as e:
                logger.error(f"测试失败: {thy_file.name}: {e}")
                import traceback
                traceback.print_exc()
            
            print()
        
        # 显示总结
        self.print_summary()
    
    def print_summary(self):
        """打印测试总结"""
        elapsed_time = time.time() - self.stats["start_time"]
        
        print("\n" + "="*60)
        print("📊 Integration测试总结")
        print("="*60)
        print(f"测试文件数: {self.stats['theories_tested']}")
        print(f"成功: {self.stats['theories_success']}")
        print(f"失败: {self.stats['theories_failed']}")
        print(f"发现Bugs: {self.stats['bugs_found']} 🐛")
        print()
        
        if self.stats["bugs_by_type"]:
            print("按类型分类:")
            for bug_type, count in sorted(self.stats["bugs_by_type"].items()):
                print(f"  {bug_type}: {count}个")
            print()
        
        print(f"测试用时: {elapsed_time:.2f}秒")
        print(f"平均每个文件: {elapsed_time/max(self.stats['theories_tested'], 1):.2f}秒")
        print("="*60)
        
        # 保存统计信息
        stats_file = self.output_dir / "integration_test_stats.json"
        with open(stats_file, 'w') as f:
            json.dump({
                "stats": self.stats,
                "bugs": self.bugs
            }, f, indent=2)
        
        logger.info(f"统计信息已保存: {stats_file}")
        
        if self.stats["bugs_found"] > 0:
            print(f"\n✅ 成功! 发现了 {self.stats['bugs_found']} 个Integration bugs!")
            print(f"Bug报告保存在: {self.output_dir}")
        else:
            print("\n未发现Integration bugs")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="Integration Bug Testing - 测试Isabelle Sledgehammer接口"
    )
    
    parser.add_argument(
        "--theory-dir",
        default="../test_theories",
        help="Theory文件目录 (默认: ../test_theories)"
    )
    
    parser.add_argument(
        "--output-dir",
        default="./integration_test_results",
        help="输出目录 (默认: ./integration_test_results)"
    )
    
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="超时时间(秒) (默认: 60.0)"
    )
    
    args = parser.parse_args()
    
    # 创建测试器
    tester = IntegrationTester(
        theory_dir=args.theory_dir,
        output_dir=args.output_dir,
        timeout=args.timeout
    )
    
    # 运行测试
    tester.run_tests()


if __name__ == "__main__":
    main()

