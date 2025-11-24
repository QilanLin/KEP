#!/usr/bin/env python3
"""
激进的Bug发现策略
基于研究的改进，专门用于发现更多bug
"""

import re
import random
from typing import List, Dict
from pathlib import Path


class AggressiveBugFindingStrategy:
    """激进的Bug发现策略"""
    
    @staticmethod
    def get_improved_config() -> Dict:
        """
        获取改进的配置（更激进的设置）
        
        基于研究：
        1. 增加超时时间（发现timeout bug）
        2. 添加激进变异策略
        3. 测试边界情况
        4. 增加测试数量
        """
        return {
            'timeout': 30.0,  # 增加超时时间（从5秒到30秒）
            'num_mutants': 50,  # 增加变异体数量（从10到50）
            'use_aggressive_mutator': True,  # 使用激进变异器
            'test_edge_cases': True,  # 测试边界情况
            'increase_reconstruction_timeout': 60.0,  # 增加重构超时
            'generate_malformed_inputs': True,  # 生成恶意格式输入
        }
    
    @staticmethod
    def get_bug_triggering_patterns() -> List[str]:
        """
        获取已知的bug触发模式（基于研究）
        """
        return [
            # 可能导致crash的模式
            'unclosed_brackets',  # 未关闭的括号
            'invalid_quantifiers',  # 无效的量词
            'huge_numbers',  # 超大数字
            'deeply_nested',  # 深度嵌套
            'unicode_issues',  # Unicode问题
            'null_bytes',  # 空字节
            'extremely_long_lines',  # 极长行
            'missing_formula_end',  # 缺少公式结束符
            'malformed_type_declarations',  # 格式错误的类型声明
            'circular_references',  # 循环引用
            
            # 可能导致timeout的模式
            'exponential_complexity',  # 指数复杂度
            'infinite_recursion_patterns',  # 无限递归模式
            'huge_formulas',  # 超大公式
            'deep_quantifier_nesting',  # 深度量词嵌套
        ]
    
    @staticmethod
    def create_crash_triggers(content: str) -> List[str]:
        """
        创建专门用于触发crash的变异体
        """
        triggers = []
        
        # 1. 未关闭的括号
        if '(' in content:
            triggers.append(content + '(' * 100)
            triggers.append(content.rstrip(')'))
        
        # 2. 删除关键标点
        triggers.append(content.replace('.', ''))
        triggers.append(content.replace(',', ''))
        
        # 3. 破坏量词
        triggers.append(re.sub(r'!\[', '[', content))
        triggers.append(re.sub(r'\?\[', '?', content))
        
        # 4. 注入空字节
        if len(content) > 10:
            pos = random.randint(0, len(content) - 1)
            triggers.append(content[:pos] + '\x00' + content[pos:])
        
        # 5. 超大数字
        if re.search(r'\d+', content):
            huge_num = '9' * 500
            triggers.append(re.sub(r'\d+', huge_num, content, count=1))
        
        # 6. 特殊Unicode字符
        triggers.append(content.replace('=', '≠').replace('&', '∧').replace('|', '∨'))
        
        return [t for t in triggers if t and t != content]
    
    @staticmethod
    def create_timeout_triggers(content: str) -> List[str]:
        """
        创建专门用于触发timeout的变异体
        """
        triggers = []
        
        # 1. 复制公式多次
        formula_pattern = r'(fof|cnf|tff|thf)\([^)]+\)\.'
        formulas = re.findall(formula_pattern, content, re.MULTILINE | re.DOTALL)
        if formulas:
            # 复制公式1000次
            repeated = '\n'.join(formulas[0] for _ in range(1000))
            triggers.append(content + '\n' + repeated)
        
        # 2. 深度嵌套
        if '(' in content:
            nested = '(' * 500 + content + ')' * 500
            triggers.append(nested)
        
        # 3. 指数复杂度模式
        exp_pattern = 'X(X(X(X(X(' * 50
        triggers.append(content + exp_pattern)
        
        # 4. 极长的量词链
        quantifier_chain = '![X]: ![Y]: ![Z]: ' * 100
        triggers.append(content.replace('fof(test,', f'fof(test, {quantifier_chain}'))
        
        return [t for t in triggers if t and t != content]
    
    @staticmethod
    def create_syntax_error_triggers(content: str) -> List[str]:
        """
        创建语法错误的变异体（可能导致解析错误）
        """
        triggers = []
        
        # 1. 缺少文件结束符
        triggers.append(content.rstrip('.'))
        
        # 2. 多余的文件结束符
        triggers.append(content + '...')
        
        # 3. 格式错误的公式声明
        triggers.append(content.replace('fof(', 'fof').replace('cnf(', 'cnf'))
        
        # 4. 破坏类型声明
        triggers.append(re.sub(r'type,', 'type', content))
        
        # 5. 破坏role
        triggers.append(re.sub(r',\s*(axiom|conjecture)', ', invalid_role', content))
        
        return [t for t in triggers if t and t != content]

