#!/usr/bin/env python3
"""
破坏性 Mutator (方案A)

目标: 创建会触发异常的mutations
方法: 故意注入语法错误、类型错误、引用错误等

这些mutations应该触发Sledgehammer的catch块，
让我们能够验证异常处理是否正常工作。
"""

import re
import random
from pathlib import Path
from typing import List, Optional, Tuple
from dataclasses import dataclass
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger('destructive_mutator')


@dataclass
class DestructiveMutation:
    """破坏性mutation结果"""
    original_theory: str
    mutated_theory: str
    mutation_type: str
    description: str
    line_number: int
    original_line: str
    mutated_line: str


class DestructiveMutator:
    """破坏性 Mutator - 故意创建会出错的代码"""
    
    def __init__(self):
        self.mutation_types = [
            'syntax_error',
            'type_error',
            'reference_error',
            'infinite_recursion',
            'malformed_proof',
            'invalid_import'
        ]
    
    def mutate_theory(self, theory_path: str, 
                     mutations_per_type: int = 2) -> List[DestructiveMutation]:
        """对一个theory文件应用破坏性mutations"""
        
        theory_path = Path(theory_path)
        if not theory_path.exists():
            raise FileNotFoundError(f"Theory file not found: {theory_path}")
        
        content = theory_path.read_text()
        mutations = []
        
        # 对每种mutation类型生成mutations
        mutations.extend(self.inject_syntax_errors(content, mutations_per_type))
        mutations.extend(self.inject_type_errors(content, mutations_per_type))
        mutations.extend(self.inject_reference_errors(content, mutations_per_type))
        mutations.extend(self.inject_infinite_recursion(content, mutations_per_type))
        mutations.extend(self.inject_malformed_proofs(content, mutations_per_type))
        
        return mutations
    
    def inject_syntax_errors(self, content: str, count: int) -> List[DestructiveMutation]:
        """注入语法错误"""
        mutations = []
        lines = content.split('\n')
        
        # 找到包含lemma的行
        lemma_lines = [(i, line) for i, line in enumerate(lines) 
                       if 'lemma' in line and ':' in line]
        
        if not lemma_lines:
            return mutations
        
        selected = random.sample(lemma_lines, min(count, len(lemma_lines)))
        
        for line_idx, original_line in selected:
            # 错误1: 删除关键字 lemma -> lema
            mutated = original_line.replace('lemma', 'lema', 1)
            if mutated != original_line:
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='syntax_error_keyword',
                    description='删除关键字中的字母 (lemma -> lema)',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        # 错误2: 破坏引号
        for line_idx, original_line in selected[:count]:
            if '"' in original_line:
                # 删除一个引号
                mutated = original_line.replace('"', '', 1)
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='syntax_error_quote',
                    description='删除引号',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        # 错误3: 破坏括号匹配
        for line_idx, original_line in selected[:count]:
            if '(' in original_line and ')' in original_line:
                # 删除一个右括号
                idx = original_line.rfind(')')
                mutated = original_line[:idx] + original_line[idx+1:]
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='syntax_error_bracket',
                    description='删除右括号导致不匹配',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        return mutations
    
    def inject_type_errors(self, content: str, count: int) -> List[DestructiveMutation]:
        """注入类型错误"""
        mutations = []
        lines = content.split('\n')
        
        # 找到包含数字的行
        numeric_lines = [(i, line) for i, line in enumerate(lines) 
                        if re.search(r'\b\d+\b', line) and 'lemma' in line]
        
        if not numeric_lines:
            return mutations
        
        selected = random.sample(numeric_lines, min(count, len(numeric_lines)))
        
        for line_idx, original_line in selected:
            # 错误1: 将数字替换为字符串
            mutated = re.sub(r'\b(\d+)\b', r'"\1"', original_line, count=1)
            if mutated != original_line:
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='type_error_nat_to_string',
                    description='将nat类型替换为string类型',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        # 错误2: 类型注解错误
        type_lines = [(i, line) for i, line in enumerate(lines)
                     if '::nat' in line or '::int' in line]
        
        for line_idx, original_line in type_lines[:count]:
            # 将 nat 改为 bool
            mutated = original_line.replace('::nat', '::bool', 1)
            if mutated != original_line:
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='type_error_wrong_annotation',
                    description='错误的类型注解 (nat -> bool)',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        return mutations
    
    def inject_reference_errors(self, content: str, count: int) -> List[DestructiveMutation]:
        """注入引用错误 - 使用不存在的定理/函数"""
        mutations = []
        lines = content.split('\n')
        
        # 找到使用了proof方法的行
        proof_lines = [(i, line) for i, line in enumerate(lines)
                      if any(method in line for method in ['by ', 'apply ', 'using '])]
        
        if not proof_lines:
            return mutations
        
        selected = random.sample(proof_lines, min(count, len(proof_lines)))
        
        for line_idx, original_line in selected:
            # 错误1: 使用不存在的定理
            if 'by ' in original_line:
                mutated = original_line.replace('by ', 'by nonexistent_theorem_xyz ')
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='reference_error_theorem',
                    description='引用不存在的定理',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
            
            # 错误2: 使用不存在的规则
            if 'apply' in original_line:
                mutated = original_line.replace('apply', 'apply (rule nonexistent_rule)')
                new_content = '\n'.join(lines[:line_idx] + [mutated] + lines[line_idx+1:])
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='reference_error_rule',
                    description='引用不存在的规则',
                    line_number=line_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        # 错误3: 错误的imports
        import_line_idx = None
        for i, line in enumerate(lines):
            if line.strip().startswith('imports'):
                import_line_idx = i
                break
        
        if import_line_idx is not None:
            original_line = lines[import_line_idx]
            mutated = original_line + ' NonExistent_Theory'
            new_content = '\n'.join(lines[:import_line_idx] + [mutated] + lines[import_line_idx+1:])
            mutations.append(DestructiveMutation(
                original_theory=content,
                mutated_theory=new_content,
                mutation_type='reference_error_import',
                description='导入不存在的theory',
                line_number=import_line_idx + 1,
                original_line=original_line,
                mutated_line=mutated
            ))
        
        return mutations
    
    def inject_infinite_recursion(self, content: str, count: int) -> List[DestructiveMutation]:
        """注入无限递归定义"""
        mutations = []
        lines = content.split('\n')
        
        # 找到lemma定义
        lemma_lines = [(i, line) for i, line in enumerate(lines)
                      if line.strip().startswith('lemma')]
        
        if not lemma_lines:
            return mutations
        
        # 在第一个lemma之前插入自引用定义
        if lemma_lines:
            insert_idx = lemma_lines[0][0]
            
            # 递归定义1: x = x + 1
            recursive_lemma = '''
(* 破坏性mutation: 无限递归定义 *)
lemma infinite_recursion_test: "\\<forall>x::nat. x = x + 1"
'''
            new_lines = lines[:insert_idx] + [recursive_lemma] + lines[insert_idx:]
            new_content = '\n'.join(new_lines)
            mutations.append(DestructiveMutation(
                original_theory=content,
                mutated_theory=new_content,
                mutation_type='infinite_recursion_self',
                description='自引用定义 (x = x + 1)',
                line_number=insert_idx + 1,
                original_line='',
                mutated_line=recursive_lemma
            ))
            
            # 递归定义2: 循环引用
            if len(lemma_lines) >= 2:
                recursive_lemma2 = '''
(* 破坏性mutation: 循环引用 *)
lemma circular_A: "circular_B"
lemma circular_B: "circular_A"
'''
                new_lines = lines[:insert_idx] + [recursive_lemma2] + lines[insert_idx:]
                new_content = '\n'.join(new_lines)
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='infinite_recursion_circular',
                    description='循环引用 (A -> B -> A)',
                    line_number=insert_idx + 1,
                    original_line='',
                    mutated_line=recursive_lemma2
                ))
        
        return mutations
    
    def inject_malformed_proofs(self, content: str, count: int) -> List[DestructiveMutation]:
        """注入格式错误的证明"""
        mutations = []
        lines = content.split('\n')
        
        # 找到带证明的lemma
        lemma_indices = []
        for i, line in enumerate(lines):
            if line.strip().startswith('lemma') and i + 1 < len(lines):
                lemma_indices.append(i)
        
        if not lemma_indices:
            return mutations
        
        selected = random.sample(lemma_indices, min(count, len(lemma_indices)))
        
        for lemma_idx in selected:
            original_line = lines[lemma_idx]
            
            # 错误1: 删除proof结束标记
            proof_end_idx = None
            for j in range(lemma_idx + 1, min(lemma_idx + 10, len(lines))):
                if 'qed' in lines[j] or 'done' in lines[j]:
                    proof_end_idx = j
                    break
            
            if proof_end_idx:
                # 删除qed/done
                new_lines = lines[:proof_end_idx] + lines[proof_end_idx+1:]
                new_content = '\n'.join(new_lines)
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='malformed_proof_no_end',
                    description='删除proof结束标记 (qed/done)',
                    line_number=proof_end_idx + 1,
                    original_line=lines[proof_end_idx],
                    mutated_line='(deleted)'
                ))
            
            # 错误2: 破坏proof结构
            mutated = original_line.replace('lemma', 'lemma') + '\n  proof\n    sorry\n  (* missing qed *)'
            if lemma_idx + 1 < len(lines):
                new_lines = lines[:lemma_idx+1] + ['  proof', '    sorry'] + lines[lemma_idx+1:]
                new_content = '\n'.join(new_lines)
                mutations.append(DestructiveMutation(
                    original_theory=content,
                    mutated_theory=new_content,
                    mutation_type='malformed_proof_structure',
                    description='不完整的proof结构',
                    line_number=lemma_idx + 1,
                    original_line=original_line,
                    mutated_line=mutated
                ))
        
        return mutations
    
    def save_mutation(self, mutation: DestructiveMutation, 
                     output_dir: Path, base_name: str, mutation_id: int) -> Path:
        """保存mutation到文件"""
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # 生成文件名
        mutation_name = f"{base_name}_destructive_{mutation_id:04d}_{mutation.mutation_type}"
        filename = f"{mutation_name}.thy"
        filepath = output_dir / filename
        
        # 更新theory名称以匹配文件名
        new_theory_name = Path(filename).stem
        mutated_content = re.sub(
            r'theory\s+\S+',
            f'theory {new_theory_name}',
            mutation.mutated_theory,
            count=1
        )
        
        # 保存
        filepath.write_text(mutated_content)
        
        logger.debug(f"Saved mutation: {filepath}")
        return filepath


def main():
    """测试破坏性mutator"""
    import argparse
    
    parser = argparse.ArgumentParser(description='破坏性 Mutator')
    parser.add_argument('--seed-dir', required=True, help='种子理论目录')
    parser.add_argument('--output-dir', default='results/destructive_mutations',
                       help='输出目录')
    parser.add_argument('--mutations-per-type', type=int, default=2,
                       help='每种类型的mutations数量')
    args = parser.parse_args()
    
    mutator = DestructiveMutator()
    seed_dir = Path(args.seed_dir)
    output_dir = Path(args.output_dir)
    
    logger.info(f"Scanning seed directory: {seed_dir}")
    theory_files = list(seed_dir.glob("*.thy"))
    logger.info(f"Found {len(theory_files)} theory files")
    
    all_mutations = []
    for theory_file in theory_files:
        logger.info(f"Mutating: {theory_file.name}")
        mutations = mutator.mutate_theory(theory_file, args.mutations_per_type)
        logger.info(f"  Generated {len(mutations)} mutations")
        
        # 保存mutations
        for i, mutation in enumerate(mutations):
            filepath = mutator.save_mutation(
                mutation, output_dir, theory_file.stem, len(all_mutations) + i
            )
        
        all_mutations.extend(mutations)
    
    logger.info(f"Total mutations generated: {len(all_mutations)}")
    logger.info(f"Mutations saved to: {output_dir}")
    
    # 打印统计
    mutation_types = {}
    for m in all_mutations:
        mutation_types[m.mutation_type] = mutation_types.get(m.mutation_type, 0) + 1
    
    print("\n" + "=" * 60)
    print("Mutation Statistics:")
    print("=" * 60)
    for mtype, count in sorted(mutation_types.items()):
        print(f"  {mtype}: {count}")
    print(f"\nTotal: {len(all_mutations)}")


if __name__ == '__main__':
    main()

