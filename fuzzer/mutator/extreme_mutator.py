#!/usr/bin/env python3
"""
极端变异器（Extreme Mutator）
专门设计用于发现最难以触发的bug
包括极端的边界情况、恶意输入等
"""

import re
import random
from typing import List, Optional
from pathlib import Path


class ExtremeMutator:
    """极端变异器 - 用于发现最难以触发的bug"""
    
    def __init__(self, seed: int = None):
        """
        初始化极端变异器
        
        Args:
            seed: 随机数种子
        """
        if seed is not None:
            random.seed(seed)
        self.mutation_count = 0
    
    def generate_extreme_mutants(self, content: str, count: int = 20) -> List[str]:
        """
        生成极端变异体（专门设计用于触发最难以发现的bug）
        
        策略：
        1. 极大输入（100MB+）
        2. 极深嵌套（1000层+）
        3. 极端数值（2^1000等）
        4. 特殊Unicode问题
        5. 恶意格式组合
        
        Args:
            content: 原始内容
            count: 生成数量
        
        Returns:
            变异体列表
        """
        mutants = []
        strategies = [
            self._create_huge_file,  # 极大文件（100MB+）
            self._create_extreme_nesting,  # 极深嵌套（1000层+）
            self._create_extreme_numbers,  # 极端数值（2^1000等）
            self._create_malicious_unicode,  # 恶意Unicode
            self._create_exponential_formula,  # 指数复杂度公式
            self._create_infinite_patterns,  # 无限循环模式
            self._create_malformed_structure,  # 恶意结构
            self._create_extreme_quantifiers,  # 极端量词链
            self._create_zero_byte_injection,  # 空字节注入
            self._create_format_string_attack,  # 格式字符串攻击模式
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
    
    def _create_huge_file(self, content: str) -> str:
        """创建极大文件（100MB+）"""
        # 复制公式100万次
        formula_pattern = r'(fof|cnf|tff|thf)\([^)]+\)\.'
        formulas = re.findall(formula_pattern, content, re.MULTILINE | re.DOTALL)
        if formulas:
            # 复制公式10万次（创建约10-50MB文件）
            repeated = '\n'.join(formulas[0] for _ in range(100000))
            return content + '\n' + repeated
        return content
    
    def _create_extreme_nesting(self, content: str) -> str:
        """创建极深嵌套（1000层+）"""
        # 找到公式并添加极深嵌套
        formula_pattern = r'(fof\([^,]+,[^,]+,)(.+?)(\)\.)'
        match = re.search(formula_pattern, content, re.MULTILINE | re.DOTALL)
        if match:
            formula_body = match.group(2)
            # 添加1000层嵌套
            nested = '(' * 1000 + formula_body + ')' * 1000
            return content[:match.start(2)] + nested + content[match.end(2):]
        return content
    
    def _create_extreme_numbers(self, content: str) -> str:
        """创建极端数值（2^1000等）"""
        # 找到所有数字并替换为极大数值
        number_pattern = r'\b\d+\b'
        
        extreme_numbers = [
            '9' * 1000,  # 1000位数字
            '9' * 10000,  # 10000位数字
            '2' + '0' * 1000,  # 2^1000的近似
        ]
        
        if re.search(number_pattern, content):
            extreme_num = random.choice(extreme_numbers)
            return re.sub(number_pattern, extreme_num, content, count=1)
        return content
    
    def _create_malicious_unicode(self, content: str) -> str:
        """创建恶意Unicode"""
        malicious_unicode = [
            '\u0000',  # 空字节
            '\uFFFE',  # 非字符
            '\uFEFF',  # 字节顺序标记
            '\u200B',  # 零宽空格
            '\u200C',  # 零宽非连接符
            '\u200D',  # 零宽连接符
            '\u202E',  # 从右到左覆盖
            '\uFEFF' * 100,  # 大量BOM
        ]
        
        pos = random.randint(0, len(content) - 1) if len(content) > 0 else 0
        char = random.choice(malicious_unicode)
        return content[:pos] + char + content[pos:]
    
    def _create_exponential_formula(self, content: str) -> str:
        """创建指数复杂度公式"""
        # 创建自引用的递归模式
        exp_patterns = [
            'X(X(X(X(X(' * 100,  # 100层自引用
            'f(f(f(f(f(' * 100,  # 100层函数递归
            'p(p(p(p(p(' * 100,  # 100层谓词递归
        ]
        
        pattern = random.choice(exp_patterns)
        pos = random.randint(0, len(content) - 1) if len(content) > 0 else 0
        return content[:pos] + pattern + content[pos:]
    
    def _create_infinite_patterns(self, content: str) -> str:
        """创建无限循环模式"""
        infinite_patterns = [
            # 自引用的量词链
            '![X]: ![X]: ![X]: ' * 500,
            # 循环的量词嵌套
            '![X]: ?[Y]: ![X]: ?[Y]: ' * 200,
            # 递归的公式定义
            'fof(rec, axiom, rec => rec).',
        ]
        
        pattern = random.choice(infinite_patterns)
        return content + '\n' + pattern
    
    def _create_malformed_structure(self, content: str) -> str:
        """创建恶意结构"""
        malformed = [
            # 缺少结束括号
            content + '(' * 1000,
            # 缺少开始括号
            ')' * 1000 + content,
            # 破坏公式结构
            content.replace('.', '', 1000),  # 删除所有句号
            # 破坏量词格式
            re.sub(r'!\[', '[!', content),  # 破坏forall
            re.sub(r'\?\[', '[?', content),  # 破坏exists
        ]
        
        return random.choice(malformed)
    
    def _create_extreme_quantifiers(self, content: str) -> str:
        """创建极端量词链"""
        # 创建1000层量词链
        quantifier_chain = '![X1]: ![X2]: ![X3]: ' * 333  # 约1000层
        if 'fof(' in content:
            return re.sub(r'fof\(([^,]+),', 
                         lambda m: f'fof({m.group(1)}, {quantifier_chain}',
                         content, count=1)
        return content
    
    def _create_zero_byte_injection(self, content: str) -> str:
        """注入空字节"""
        # 在随机位置注入空字节
        positions = random.sample(range(len(content)), min(100, len(content)))
        result = list(content)
        for pos in positions[:10]:  # 注入10个空字节
            result.insert(pos, '\x00')
        return ''.join(result)
    
    def _create_format_string_attack(self, content: str) -> str:
        """创建格式字符串攻击模式"""
        format_attacks = [
            '%s' * 1000,  # 大量格式字符串
            '%n' * 100,   # 格式化写入
            '%x' * 1000,  # 格式化输出
            '${' * 1000,  # 变量展开
            '$(' * 1000,  # 命令替换
        ]
        
        pattern = random.choice(format_attacks)
        pos = random.randint(0, len(content) - 1) if len(content) > 0 else 0
        return content[:pos] + pattern + content[pos:]
    
    def generate_edge_cases(self, content: str) -> List[str]:
        """生成极端边界情况"""
        edge_cases = []
        
        # 空文件
        edge_cases.append('')
        
        # 只有注释
        edge_cases.append('% Comment\n% Another comment\n' * 100)
        
        # 单个字符
        edge_cases.append('a')
        edge_cases.append('.')
        edge_cases.append('(')
        edge_cases.append(')')
        
        # 极大数字字符串
        huge_number = '9' * 10000
        edge_cases.append(f'fof(test, conjecture, {huge_number} = {huge_number}).')
        
        # 极长字符串
        long_string = 'a' * 100000
        edge_cases.append(f'fof(test, conjecture, {long_string} = {long_string}).')
        
        # 特殊Unicode混合
        edge_cases.append('fof(test, conjecture, ∀x: ∀y: x=y).')
        edge_cases.append('fof(test, conjecture, ∃x: ∃y: x≠y).')
        edge_cases.append('\uFEFF' * 1000)  # 大量BOM
        
        # 恶意格式组合
        edge_cases.append('fof(test, conjecture, )))))))))).')  # 只有结束括号
        edge_cases.append('fof(test, conjecture, (((((((((((.')  # 只有开始括号
        
        return [c for c in edge_cases if c != content]

