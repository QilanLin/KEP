#!/usr/bin/env python3
"""
真正的Sledgehammer Integration Testing

测试Sledgehammer接口的真实bugs:
1. Proof reconstruction failures
2. TPTP encoding issues
3. Prover integration problems
"""

import subprocess
import tempfile
from pathlib import Path
import json
import time
import re
from typing import Optional, List, Dict, Tuple

class RealSledgehammerTester:
    """真正的Sledgehammer测试"""
    
    def __init__(self, work_dir: Path):
        self.work_dir = Path(work_dir)
        self.bugs_found = []
        
    def test_sledgehammer_with_goal(self, 
                                   theory_name: str,
                                   imports: str,
                                   goal: str,
                                   goal_statement: str,
                                   timeout: int = 30) -> Dict:
        """
        测试Sledgehammer能否找到并重建proof
        
        这是真正的Integration testing:
        1. 创建有效的theory with goal
        2. 调用Sledgehammer让它找proof
        3. 检查Sledgehammer返回的proof能否工作
        """
        
        # 创建theory文件，使用sledgehammer
        theory_content = f'''theory {theory_name}
imports {imports}
begin

lemma {goal}: "{goal_statement}"
  sledgehammer [timeout={timeout}]
  sorry (* 先用sorry占位，看Sledgehammer的建议 *)

end
'''
        
        theory_file = self.work_dir / f"{theory_name}.thy"
        theory_file.write_text(theory_content)
        
        # 运行Isabelle并捕获Sledgehammer的输出
        try:
            result = subprocess.run(
                ['isabelle', 'jedit', '-b', theory_file.name],
                cwd=self.work_dir,
                capture_output=True,
                text=True,
                timeout=timeout + 10
            )
            
            output = result.stdout + result.stderr
            
            # 解析Sledgehammer的建议
            suggestions = self._parse_sledgehammer_output(output)
            
            if suggestions:
                # 测试每个建议的proof是否真的能工作
                for i, proof_method in enumerate(suggestions):
                    works = self._test_proof_method(
                        theory_name, imports, goal, goal_statement, proof_method
                    )
                    
                    if not works:
                        # 发现真正的bug: Sledgehammer建议的proof不工作!
                        bug = {
                            'type': 'proof_reconstruction_failure',
                            'goal': goal_statement,
                            'suggested_proof': proof_method,
                            'description': f'Sledgehammer建议使用 {proof_method}，但这个proof不能重建',
                            'theory': theory_name
                        }
                        self.bugs_found.append(bug)
                        return bug
                        
            return {'status': 'ok', 'suggestions': suggestions}
            
        except subprocess.TimeoutExpired:
            return {'status': 'timeout'}
        except Exception as e:
            return {'status': 'error', 'message': str(e)}
    
    def _parse_sledgehammer_output(self, output: str) -> List[str]:
        """解析Sledgehammer输出中的proof建议"""
        suggestions = []
        
        # Sledgehammer通常会输出类似:
        # "Try this: by (metis ...)"
        # "Try this: by (smt ...)"
        
        pattern = r'Try this:\s*by\s*\((.*?)\)'
        matches = re.finditer(pattern, output, re.IGNORECASE)
        
        for match in matches:
            proof_method = match.group(1).strip()
            suggestions.append(proof_method)
        
        return suggestions
    
    def _test_proof_method(self, 
                          theory_name: str,
                          imports: str,
                          goal: str,
                          goal_statement: str,
                          proof_method: str) -> bool:
        """
        测试Sledgehammer建议的proof method是否真的能工作
        
        这是检测真实Integration bugs的关键!
        """
        
        # 创建使用建议proof的theory
        theory_content = f'''theory {theory_name}_test
imports {imports}
begin

lemma {goal}: "{goal_statement}"
  by ({proof_method})

end
'''
        
        theory_file = self.work_dir / f"{theory_name}_test.thy"
        theory_file.write_text(theory_content)
        
        # 尝试处理
        try:
            result = subprocess.run(
                ['isabelle', 'process', '-e', f'use_thy "{theory_name}_test";'],
                cwd=self.work_dir,
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # 检查是否成功
            if result.returncode == 0 and 'error' not in result.stderr.lower():
                return True
            else:
                return False
                
        except Exception:
            return False
    
    def test_with_mutation(self, base_theory: Path) -> List[Dict]:
        """
        基于变异的testing
        
        1. 从已知工作的theory开始
        2. 轻微变异
        3. 测试Sledgehammer是否仍然工作
        """
        
        # 读取基础theory
        content = base_theory.read_text()
        
        # TODO: 实现变异逻辑
        # - 修改变量名
        # - 调整类型约束
        # - 改变lemma顺序
        # 等等
        
        return []


def main():
    """运行真正的Sledgehammer Integration testing"""
    
    print("="*70)
    print("🔍 真正的Sledgehammer Integration Bug Testing")
    print("="*70)
    print()
    print("注意: 这个测试需要:")
    print("  1. Isabelle/jEdit (用于交互式Sledgehammer)")
    print("  2. 或者Isabelle server API")
    print("  3. 能够捕获Sledgehammer的输出")
    print()
    print("当前实现的局限:")
    print("  - Sledgehammer是交互式工具，难以从命令行完全捕获输出")
    print("  - 需要使用Isabelle server API或Parse输出")
    print("  - 这是正确的方向，但需要更多工作")
    print()
    print("="*70)
    
    work_dir = Path("../test_theories")
    tester = RealSledgehammerTester(work_dir)
    
    # 测试一些简单的goals
    test_cases = [
        {
            'theory': 'Test_Sledgehammer_1',
            'imports': 'Main',
            'goal': 'simple_impl',
            'statement': 'P \<longrightarrow> P'
        },
        {
            'theory': 'Test_Sledgehammer_2', 
            'imports': 'Main',
            'goal': 'list_append',
            'statement': 'xs @ [] = xs'
        }
    ]
    
    for test in test_cases:
        print(f"\n测试: {test['goal']}")
        result = tester.test_sledgehammer_with_goal(
            test['theory'],
            test['imports'],
            test['goal'],
            test['statement']
        )
        print(f"  结果: {result.get('status', 'unknown')}")
        
        if result.get('type') == 'proof_reconstruction_failure':
            print(f"  🐛 发现真实bug: {result['description']}")
    
    print("\n" + "="*70)
    print(f"总计发现 {len(tester.bugs_found)} 个真实Integration bugs")
    print("="*70)


if __name__ == '__main__':
    main()

