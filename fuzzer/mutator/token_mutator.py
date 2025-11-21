#!/usr/bin/env python3
"""
Token级别变异器
对TPTP文件进行token级别的变异操作
"""

import re
import random
from typing import List, Set
from enum import Enum


class MutationType(Enum):
    """变异类型"""
    VALUE_REPLACE = "value_replace"      # 数值替换
    SYMBOL_REPLACE = "symbol_replace"    # 符号替换
    OPERATOR_REPLACE = "operator_replace" # 操作符替换
    BRACKET_MANIPULATE = "bracket_manipulate" # 括号操作
    STRING_MUTATE = "string_mutate"      # 字符串变异
    LOGICAL_OPERATOR = "logical_operator"  # 逻辑运算符变异（新增）
    QUANTIFIER = "quantifier"            # 量词变异（新增）
    COMPARISON_OPERATOR = "comparison_operator"  # 比较运算符变异（新增）


class TokenMutator:
    """Token级别变异器"""
    
    def __init__(self, seed: int = None):
        """
        初始化变异器
        
        Args:
            seed: 随机数种子（用于可重复性）
        """
        if seed is not None:
            random.seed(seed)
        self.mutation_count = 0
    
    def mutate(self, content: str, mutation_type: MutationType = None) -> str:
        """
        对内容进行变异
        
        Args:
            content: 原始TPTP内容
            mutation_type: 指定的变异类型（None表示随机选择）
            
        Returns:
            变异后的内容
        """
        if mutation_type is None:
            mutation_type = random.choice(list(MutationType))
        
        if mutation_type == MutationType.VALUE_REPLACE:
            return self._mutate_values(content)
        elif mutation_type == MutationType.SYMBOL_REPLACE:
            return self._mutate_symbols(content)
        elif mutation_type == MutationType.OPERATOR_REPLACE:
            return self._mutate_operators(content)
        elif mutation_type == MutationType.BRACKET_MANIPULATE:
            return self._mutate_brackets(content)
        elif mutation_type == MutationType.STRING_MUTATE:
            return self._mutate_strings(content)
        elif mutation_type == MutationType.LOGICAL_OPERATOR:
            return self._mutate_logical_operators(content)
        elif mutation_type == MutationType.QUANTIFIER:
            return self._mutate_quantifiers(content)
        elif mutation_type == MutationType.COMPARISON_OPERATOR:
            return self._mutate_comparison_operators(content)
        else:
            return content
    
    def _mutate_values(self, content: str) -> str:
        """数值替换变异"""
        # 查找数值模式
        number_pattern = r'\b\d+\b'
        numbers = re.findall(number_pattern, content)
        
        if not numbers:
            return content
        
        # 随机选择一个数值进行替换
        old_value = random.choice(numbers)
        new_value = str(random.randint(0, 1000))
        
        self.mutation_count += 1
        return content.replace(old_value, new_value, 1)
    
    def _mutate_symbols(self, content: str) -> str:
        """符号替换变异"""
        # 常见的符号替换
        symbol_replacements = {
            '=': ['!=', '<', '>', '<=', '>='],
            '!=': ['=', '<', '>'],
            '<': ['<=', '>', '>='],
            '>': ['>=', '<', '<='],
        }
        
        for old_symbol, new_symbols in symbol_replacements.items():
            if old_symbol in content:
                new_symbol = random.choice(new_symbols)
                self.mutation_count += 1
                return content.replace(old_symbol, new_symbol, 1)
        
        return content
    
    def _mutate_operators(self, content: str) -> str:
        """操作符替换变异"""
        operator_replacements = {
            '+': ['-', '*'],
            '-': ['+', '*'],
            '*': ['+', '-'],
            '&': ['|'],
            '|': ['&'],
        }
        
        for old_op, new_ops in operator_replacements.items():
            if old_op in content:
                new_op = random.choice(new_ops)
                self.mutation_count += 1
                return content.replace(old_op, new_op, 1)
        
        return content
    
    def _mutate_brackets(self, content: str) -> str:
        """括号操作变异"""
        # 简单实现：添加或删除括号对
        if '(' in content and random.random() < 0.5:
            # 删除一对括号（简化版：只删除最内层的括号）
            pattern = r'\(([^()]+)\)'
            matches = list(re.finditer(pattern, content))
            if matches:
                match = random.choice(matches)
                self.mutation_count += 1
                # 提取括号内的内容（group 1）
                inner_content = match.group(1)
                return content[:match.start()] + inner_content + content[match.end():]
        else:
            # 添加括号（简化版：在数字或变量周围添加）
            number_pattern = r'\b\d+\b'
            numbers = list(re.finditer(number_pattern, content))
            if numbers:
                match = random.choice(numbers)
                self.mutation_count += 1
                return content[:match.start()] + '(' + match.group(0) + ')' + content[match.end():]
        
        return content
    
    def _mutate_strings(self, content: str) -> str:
        """字符串变异"""
        # 字符串翻转或删除字符
        word_pattern = r'\b\w+\b'
        words = re.findall(word_pattern, content)
        
        if not words:
            return content
        
        word = random.choice(words)
        if len(word) > 1:
            # 翻转字符串
            mutated_word = word[::-1]
            self.mutation_count += 1
            return content.replace(word, mutated_word, 1)
        
        return content
    
    def _mutate_logical_operators(self, content: str) -> str:
        """逻辑运算符变异"""
        logical_replacements = {
            '&': ['|', '!'],  # AND → OR, NOT
            '|': ['&', '!'],  # OR → AND, NOT
            '!': ['&', '|'],  # NOT → AND, OR
            '∧': ['∨', '¬'],  # Unicode AND → OR, NOT
            '∨': ['∧', '¬'],  # Unicode OR → AND, NOT
            '¬': ['∧', '∨'],  # Unicode NOT → AND, OR
            '=>': ['<=>', '<='],  # 蕴含 → 等价, 反蕴含
            '<=>': ['=>', '<='],  # 等价 → 蕴含, 反蕴含
            '=>': ['<=>', '!'],  # 蕴含 → 等价, NOT
        }
        
        for old_op, new_ops in logical_replacements.items():
            if old_op in content:
                new_op = random.choice(new_ops)
                self.mutation_count += 1
                return content.replace(old_op, new_op, 1)
        
        return content
    
    def _mutate_quantifiers(self, content: str) -> str:
        """量词变异"""
        quantifier_replacements = {
            'forall': 'exists',  # ∀ → ∃
            'exists': 'forall',  # ∃ → ∀
            '∀': '∃',  # Unicode ∀ → ∃
            '∃': '∀',  # Unicode ∃ → ∀
        }
        
        # 先尝试TPTP格式量词（转义特殊字符）
        tptp_patterns = [
            (r'!\s*\[', '?['),  # forall [...] → exists [...]
            (r'\?\s*\[', '!['),  # exists [...] → forall [...] (转义?)
        ]
        
        for pattern, replacement in tptp_patterns:
            try:
                if re.search(pattern, content):
                    self.mutation_count += 1
                    return re.sub(pattern, replacement, content, count=1)
            except re.error:
                # 如果正则表达式错误，跳过
                continue
        
        # 然后尝试单词量词
        for old_quant, new_quant in quantifier_replacements.items():
            if old_quant in content:
                self.mutation_count += 1
                return content.replace(old_quant, new_quant, 1)
        
        return content
    
    def _mutate_comparison_operators(self, content: str) -> str:
        """比较运算符变异"""
        comparison_replacements = {
            '=': ['!=', '<', '>', '<=', '>='],
            '!=': ['=', '<', '>', '<=', '>='],
            '<': ['>', '<=', '>=', '=', '!='],
            '>': ['<', '<=', '>=', '=', '!='],
            '<=': ['>=', '<', '>', '=', '!='],
            '>=': ['<=', '<', '>', '=', '!='],
            '==': ['!=', '<', '>'],
            '≠': ['=', '<', '>', '≤', '≥'],
            '≤': ['≥', '<', '>', '=', '≠'],
            '≥': ['≤', '<', '>', '=', '≠'],
        }
        
        for old_op, new_ops in comparison_replacements.items():
            if old_op in content:
                new_op = random.choice(new_ops)
                self.mutation_count += 1
                # 使用word boundary确保是完整的操作符
                pattern = r'\b' + re.escape(old_op) + r'\b'
                if re.search(pattern, content):
                    return re.sub(pattern, new_op, content, count=1)
                else:
                    # 如果不是word boundary，直接替换
                    return content.replace(old_op, new_op, 1)
        
        return content
    
    def generate_mutants(self, content: str, count: int = 10) -> List[str]:
        """
        生成多个变异体
        
        Args:
            content: 原始内容
            count: 生成变异体数量
            
        Returns:
            变异体列表
        """
        mutants = []
        seen = set()
        
        for i in range(count):
            mutant = self.mutate(content)
            
            # 避免重复
            if mutant not in seen and mutant != content:
                mutants.append(mutant)
                seen.add(mutant)
            
            # 如果无法生成更多独特的变异体，停止
            if len(mutants) >= count:
                break
        
        return mutants


def main():
    """测试函数"""
    mutator = TokenMutator(seed=42)
    
    # 测试内容
    test_content = """
    fof(test, conjecture, (x + 0 = x)).
    fof(axiom1, axiom, (y * 1 = y)).
    """
    
    print("原始内容:")
    print(test_content)
    print("\n生成5个变异体:\n")
    
    mutants = mutator.generate_mutants(test_content, count=5)
    
    for i, mutant in enumerate(mutants, 1):
        print(f"变异体 {i}:")
        print(mutant)
        print()


if __name__ == "__main__":
    main()

