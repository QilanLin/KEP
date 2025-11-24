#!/usr/bin/env python3
"""
激进的变异器（Aggressive Mutator）
专门设计用于发现crash和timeout bug
包括破坏语法的变异、边界情况、恶意输入等
"""

import re
import random
from typing import List, Optional
from pathlib import Path


class AggressiveMutator:
    """激进变异器 - 专门用于发现bug"""
    
    def __init__(self, seed: int = None):
        """
        初始化激进变异器
        
        Args:
            seed: 随机数种子
        """
        if seed is not None:
            random.seed(seed)
        self.mutation_count = 0
    
    def generate_aggressive_mutants(self, content: str, count: int = 10) -> List[str]:
        """
        生成激进的变异体（包括破坏语法的变异）
        
        策略：
        1. 破坏语法（导致crash）
        2. 超大输入（导致timeout）
        3. 特殊字符（导致解析错误）
        4. 边界情况（空、极值等）
        5. 恶意格式（可能导致漏洞）
        
        Args:
            content: 原始内容
            count: 生成数量
        
        Returns:
            变异体列表
        """
        mutants = []
        strategies = [
            self._corrupt_syntax,
            self._inject_special_chars,
            self._create_huge_formula,
            self._delete_critical_parts,
            self._invert_whole_formula,
            self._create_deeply_nested,
            self._inject_unicode_issues,
            self._create_malformed_quantifiers,
            self._break_brackets,
            self._create_infinite_loops_patterns
        ]
        
        for i in range(count):
            # 随机选择策略
            strategy = random.choice(strategies)
            try:
                mutant = strategy(content)
                if mutant and mutant != content:
                    mutants.append(mutant)
            except Exception:
                # 如果策略失败，尝试下一个
                continue
        
        return mutants[:count]
    
    def _corrupt_syntax(self, content: str) -> str:
        """破坏语法 - 可能导致crash"""
        corruptions = [
            # 删除关键括号
            lambda c: re.sub(r'\(', '', c, count=random.randint(1, 3)),
            lambda c: re.sub(r'\)', '', c, count=random.randint(1, 3)),
            # 替换关键符号
            lambda c: c.replace('.', ''),
            lambda c: c.replace(',', ''),
            # 破坏量词格式
            lambda c: re.sub(r'!\[', '[', c),
            lambda c: re.sub(r'\?\[', '[', c),
            # 添加无效字符
            lambda c: c[:len(c)//2] + '\x00\x01\x02' + c[len(c)//2:],
        ]
        return random.choice(corruptions)(content)
    
    def _inject_special_chars(self, content: str) -> str:
        """注入特殊字符 - 可能导致解析错误"""
        special_chars = ['\x00', '\x01', '\x02', '\xff', '\n\n\n', '\t\t\t']
        pos = random.randint(0, len(content) - 1)
        char = random.choice(special_chars)
        return content[:pos] + char + content[pos:]
    
    def _create_huge_formula(self, content: str) -> str:
        """创建超大公式 - 可能导致timeout"""
        # 找到公式并复制多次
        formula_pattern = r'fof\([^)]+\)\.|cnf\([^)]+\)\.|tff\([^)]+\)\.|thf\([^)]+\)\.'
        formulas = re.findall(formula_pattern, content, re.MULTILINE | re.DOTALL)
        if formulas:
            # 复制公式很多次（创建巨大输入）
            repeated = formulas[0] * random.randint(100, 1000)
            return content + '\n' + repeated
        return content
    
    def _delete_critical_parts(self, content: str) -> str:
        """删除关键部分 - 可能导致解析错误"""
        # 删除文件结束符
        content = content.rstrip('.\n')
        # 删除关键声明
        content = re.sub(r'(fof|cnf|tff|thf)\([^)]+\)\.', '', content, count=random.randint(1, 3))
        return content
    
    def _invert_whole_formula(self, content: str) -> str:
        """反转整个公式 - 可能导致逻辑错误"""
        # 将整个公式取反
        if '~' not in content[:100]:
            return '~(' + content + ')'
        return content
    
    def _create_deeply_nested(self, content: str) -> str:
        """创建深度嵌套 - 可能导致stack overflow"""
        # 找到公式并添加大量嵌套括号
        formula_pattern = r'(fof\([^,]+,[^,]+,)(.+?)(\)\.)'
        match = re.search(formula_pattern, content, re.MULTILINE | re.DOTALL)
        if match:
            formula_body = match.group(2)
            nested = '(' * 200 + formula_body + ')' * 200
            return content[:match.start(2)] + nested + content[match.end(2):]
        return content
    
    def _inject_unicode_issues(self, content: str) -> str:
        """注入Unicode问题 - 可能导致编码错误"""
        unicode_issues = ['\u0000', '\uFFFE', '\uFEFF', '\u200B']  # 零宽字符等
        pos = random.randint(0, len(content) - 1)
        char = random.choice(unicode_issues)
        return content[:pos] + char + content[pos:]
    
    def _create_malformed_quantifiers(self, content: str) -> str:
        """创建格式错误的量词 - 可能导致解析错误"""
        # 破坏量词格式
        content = re.sub(r'!\[', '[!', content)
        content = re.sub(r'\?\[', '[?', content)
        # 删除量词内容
        content = re.sub(r'\[[^\]]+\]', '[]', content, count=random.randint(1, 3))
        return content
    
    def _break_brackets(self, content: str) -> str:
        """破坏括号匹配 - 可能导致解析错误"""
        # 随机删除或添加括号
        if random.random() < 0.5:
            # 删除括号
            content = re.sub(r'\(', '', content, count=random.randint(1, 5))
            content = re.sub(r'\)', '', content, count=random.randint(1, 5))
        else:
            # 添加额外括号
            pos = random.randint(0, len(content) - 1)
            content = content[:pos] + '(' * random.randint(10, 50) + content[pos:]
        return content
    
    def _create_infinite_loops_patterns(self, content: str) -> str:
        """创建可能导致无限循环的模式 - 可能导致timeout"""
        # 创建自引用的递归模式
        patterns = [
            'X(X(X(X(X(',
            'f(f(f(f(f(',
            'p(p(p(p(p(',
        ]
        pos = random.randint(0, len(content) - 1)
        pattern = random.choice(patterns) * 10
        return content[:pos] + pattern + content[pos:]
    
    def generate_edge_case_mutants(self, content: str) -> List[str]:
        """生成边界情况变异体"""
        edge_cases = []
        
        # 空文件
        edge_cases.append('')
        
        # 只有注释
        edge_cases.append('% This is a comment\n% Another comment\n')
        
        # 单个字符
        edge_cases.append('a')
        edge_cases.append('.')
        edge_cases.append('(')
        
        # 极大数字
        huge_number = '9' * 1000
        if re.search(r'\d+', content):
            edge_cases.append(re.sub(r'\d+', huge_number, content, count=1))
        
        # 极长字符串
        long_string = 'a' * 10000
        edge_cases.append(f'fof(test, conjecture, {long_string}).')
        
        # 特殊Unicode
        edge_cases.append('fof(test, conjecture, ∀x: ∀y: x=y).')
        edge_cases.append('fof(test, conjecture, ∃x: ∃y: x≠y).')
        
        return [c for c in edge_cases if c != content]

