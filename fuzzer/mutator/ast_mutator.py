#!/usr/bin/env python3
"""
AST级别变异器
对TPTP文件进行AST级别的结构感知变异操作
"""

import re
import random
from typing import List, Dict, Optional, Tuple, Set
from enum import Enum
from dataclasses import dataclass
from pathlib import Path


class ASTNodeType(Enum):
    """AST节点类型"""
    FORMULA = "formula"           # TPTP公式
    ATOM = "atom"                 # 原子公式
    NEGATION = "negation"         # 否定
    CONJUNCTION = "conjunction"   # 合取
    DISJUNCTION = "disjunction"   # 析取
    IMPLICATION = "implication"   # 蕴含
    EQUIVALENCE = "equivalence"   # 等价
    FORALL = "forall"            # 全称量词
    EXISTS = "exists"            # 存在量词
    EQUALITY = "equality"         # 相等
    INEQUALITY = "inequality"     # 不等
    PREDICATE = "predicate"       # 谓词
    FUNCTION = "function"         # 函数
    VARIABLE = "variable"         # 变量
    CONSTANT = "constant"         # 常量


@dataclass
class ASTNode:
    """AST节点"""
    node_type: ASTNodeType
    content: str
    start_pos: int
    end_pos: int
    children: List['ASTNode']
    parent: Optional['ASTNode'] = None
    
    def __post_init__(self):
        """初始化后处理"""
        if self.children is None:
            self.children = []
        # 设置子节点的父节点
        for child in self.children:
            child.parent = self


class ASTMutationType(Enum):
    """AST变异类型"""
    SWAP_SUBTREES = "swap_subtrees"       # 交换子树
    DUPLICATE_SUBTREE = "duplicate_subtree"  # 复制子树
    DELETE_SUBTREE = "delete_subtree"     # 删除子树
    REPLACE_OPERATOR = "replace_operator" # 替换运算符
    INVERT_QUANTIFIER = "invert_quantifier"  # 反转量词
    NEGATE_FORMULA = "negate_formula"     # 否定公式
    SWAP_OPERANDS = "swap_operands"       # 交换操作数


class TPTPASTParser:
    """TPTP AST解析器"""
    
    def __init__(self):
        """初始化解析器"""
        # TPTP公式模式（支持fof、cnf、tff、thf格式）
        # 注意：TPTP格式可能跨多行，需要DOTALL模式
        # 使用简化模式：匹配到下一个句号（处理嵌套括号和换行）
        self.fof_pattern = re.compile(r'fof\(([^,]+),\s*([^,]+),\s*(.*?)\)\.', re.MULTILINE | re.DOTALL)
        self.cnf_pattern = re.compile(r'cnf\(([^,]+),\s*([^,]+),\s*(.*?)\)\.', re.MULTILINE | re.DOTALL)
        self.tff_pattern = re.compile(r'tff\(([^,]+),\s*([^,]+),\s*(.*?)\)\.', re.MULTILINE | re.DOTALL)
        # THF格式（typed higher-order formulas）
        self.thf_pattern = re.compile(r'thf\(([^,]+),\s*([^,]+),\s*(.*?)\)\.', re.MULTILINE | re.DOTALL)
        
        # 逻辑运算符模式
        self.binary_ops = {
            '&': 'conjunction',
            '|': 'disjunction',
            '=>': 'implication',
            '<=>': 'equivalence',
            '=': 'equality',
            '!=': 'inequality',
            '~=': 'inequality'
        }
        
        # 量词模式
        self.quantifier_pattern = re.compile(r'(!\[[^\]]*\]|\?\[[^\]]*\])', re.MULTILINE)
        
    def parse_file(self, content: str) -> List[ASTNode]:
        """
        解析TPTP文件内容为AST（改进：增强容错能力）
        
        Args:
            content: TPTP文件内容
        
        Returns:
            AST节点列表
        """
        nodes = []
        
        # 改进：先尝试标准解析，如果失败再尝试SZS格式
        # 这样可以提高解析成功率
        
        # 解析FOF公式
        for match in self.fof_pattern.finditer(content):
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()
            
            # 解析公式结构
            formula_node = self._parse_formula(formula, match.start(3), match.end(3))
            if formula_node:
                nodes.append(ASTNode(
                    node_type=ASTNodeType.FORMULA,
                    content=formula,
                    start_pos=match.start(3),
                    end_pos=match.end(3),
                    children=[formula_node],
                    parent=None
                ))
        
        # 解析CNF公式
        for match in self.cnf_pattern.finditer(content):
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()
            
            formula_node = self._parse_formula(formula, match.start(3), match.end(3))
            if formula_node:
                nodes.append(ASTNode(
                    node_type=ASTNodeType.FORMULA,
                    content=formula,
                    start_pos=match.start(3),
                    end_pos=match.end(3),
                    children=[formula_node],
                    parent=None
                ))
        
        # 解析TFF公式（TPTP FOF格式）
        for match in self.tff_pattern.finditer(content):
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()
            
            # 跳过type声明（只处理conjecture等）
            if role.strip().lower() in ['conjecture', 'axiom', 'hypothesis', 'negated_conjecture']:
                formula_node = self._parse_formula(formula, match.start(3), match.end(3))
                if formula_node:
                    nodes.append(ASTNode(
                        node_type=ASTNodeType.FORMULA,
                        content=formula,
                        start_pos=match.start(3),
                        end_pos=match.end(3),
                        children=[formula_node],
                        parent=None
                    ))
        
        # 解析THF公式（typed higher-order formulas）
        for match in self.thf_pattern.finditer(content):
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()
            
            # 跳过type声明（只处理conjecture等）
            if role.strip().lower() in ['conjecture', 'axiom', 'hypothesis', 'negated_conjecture']:
                formula_node = self._parse_formula(formula, match.start(3), match.end(3))
                if formula_node:
                    nodes.append(ASTNode(
                        node_type=ASTNodeType.FORMULA,
                        content=formula,
                        start_pos=match.start(3),
                        end_pos=match.end(3),
                        children=[formula_node],
                        parent=None
                    ))
        
        # 方案3: 支持SZS输出格式（改进：即使有节点也尝试SZS解析）
        # 改进：基于研究 - 增强容错能力，即使标准解析成功也尝试SZS
        # 因为SZS格式可能包含额外的公式
        szs_nodes = self._parse_szs_output(content)
        # 合并结果，避免重复
        existing_ids = {f"{n.node_type}:{n.start_pos}" for n in nodes}
        for szs_node in szs_nodes:
            node_id = f"{szs_node.node_type}:{szs_node.start_pos}"
            if node_id not in existing_ids:
                nodes.append(szs_node)
                existing_ids.add(node_id)
        
        return nodes
    
    def _parse_szs_output(self, content: str) -> List[ASTNode]:
        """
        解析SZS输出格式（方案3 - 改进版）
        
        SZS输出格式示例:
        % SZS status Theorem
        % SZS output start Proof
        thf(conj_0, conjecture, ...).
        ...
        % SZS output end Proof
        
        Args:
            content: TPTP文件内容
        
        Returns:
            AST节点列表
        """
        nodes = []
        
        # 检测是否是SZS输出格式
        has_szs_marker = re.search(r'SZS\s+(status|output)', content, re.IGNORECASE)
        if not has_szs_marker:
            return nodes
        
        # 改进：更宽松的SZS格式处理
        # 即使有GaveUp等状态，也尝试查找公式（可能在文件其他位置）
        # 查找SZS输出部分的开始和结束
        # 格式1: % SZS output start Proof
        # 格式2: # SZS output start CNFRefutation
        szs_start_pattern = re.compile(r'[%#]\s*SZS\s+output\s+start\s+', re.IGNORECASE)
        szs_end_pattern = re.compile(r'[%#]\s*SZS\s+output\s+end\s+', re.IGNORECASE)
        
        start_match = szs_start_pattern.search(content)
        if start_match:
            # 找到SZS输出部分的开始位置
            start_pos = start_match.end()
            
            # 查找结束位置（如果有）
            end_match = szs_end_pattern.search(content, start_pos)
            if end_match:
                szs_content = content[start_pos:end_match.start()]
            else:
                # 没有明确的end标记，使用到文件末尾
                szs_content = content[start_pos:]
        else:
            # 如果没有明确的start标记，尝试在SZS标记后的内容中查找
            # 查找所有SZS标记
            szs_markers = list(re.finditer(r'[%#]\s*SZS\s+', content, re.IGNORECASE))
            if szs_markers:
                # 使用最后一个SZS标记后的内容
                last_marker = szs_markers[-1]
                szs_content = content[last_marker.end():]
            else:
                # 如果没有SZS标记，使用整个内容（可能SZS标记格式不同）
                szs_content = content
        
        # 改进：在整个内容中也查找公式（不仅仅是SZS标记后）
        # 有些文件的公式可能在SZS标记之前，或者格式不标准
        search_contents = [szs_content]
        if szs_content != content:
            # 也搜索原始内容，以防有格式问题
            search_contents.append(content)
        
        # 在内容中查找公式
        # 支持THF、TFF、FOF、CNF格式
        # 改进：更智能的公式提取（基于研究）
        seen_formulas = set()  # 避免重复添加
        
        for search_content in search_contents:
            for pattern_name, pattern in [
                ('thf', self.thf_pattern),
                ('tff', self.tff_pattern),
                ('fof', self.fof_pattern),
                ('cnf', self.cnf_pattern)
            ]:
                for match in pattern.finditer(search_content):
                    name = match.group(1).strip()
                    role = match.group(2).strip()
                    formula = match.group(3).strip()
                    
                    # 创建唯一标识符避免重复
                    formula_id = f"{pattern_name}({name},{role})"
                    if formula_id in seen_formulas:
                        continue
                    seen_formulas.add(formula_id)
                    
                    # 改进：更宽松的role匹配（基于研究 - 增强容错能力）
                    role_lower = role.strip().lower()
                    
                    # 改进：排除明确的type声明，其他都尝试（更宽松）
                    if role_lower not in ['type']:
                        # 优先处理这些role，但其他role也尝试
                        priority_roles = ['conjecture', 'axiom', 'hypothesis', 'negated_conjecture', 
                                          'plain', 'lemma', 'theorem', 'definition', 'assumption',
                                          'introduced', 'inference', 'fact', 'negated_conjecture',
                                          'file', 'unknown', 'negated_conjecture']
                        # 改进：更宽松的策略 - 只要不是type就尝试
                        try_parse = role_lower in priority_roles or (len(role_lower) > 0 and role_lower != 'type')
                        
                        if try_parse:
                            # 改进：增强错误处理（基于研究）
                            try:
                                formula_node = self._parse_formula(formula, match.start(3), match.end(3))
                                if formula_node:
                                    nodes.append(ASTNode(
                                        node_type=ASTNodeType.FORMULA,
                                        content=formula,
                                        start_pos=match.start(3),
                                        end_pos=match.end(3),
                                        children=[formula_node],
                                        parent=None
                                    ))
                                else:
                                    # 改进：即使公式解析失败，也尝试创建简单的AST节点
                                    # 增强容错能力（基于研究）
                                    if len(formula.strip()) > 0 and formula.strip() not in ['$false', '$true']:
                                        # 创建原子节点作为备选（允许后续变异）
                                        nodes.append(ASTNode(
                                            node_type=ASTNodeType.ATOM,
                                            content=formula,
                                            start_pos=match.start(3),
                                            end_pos=match.end(3),
                                            children=[],
                                            parent=None
                                        ))
                            except Exception as e:
                                # 改进：增强错误处理，即使解析出错也尝试创建节点
                                if len(formula.strip()) > 0:
                                    try:
                                        nodes.append(ASTNode(
                                            node_type=ASTNodeType.ATOM,
                                            content=formula,
                                            start_pos=match.start(3),
                                            end_pos=match.end(3),
                                            children=[],
                                            parent=None
                                        ))
                                    except Exception as e:
                                        # 如果还是失败，跳过这个公式（记录但不中断）
                                        # 这通常发生在公式格式异常的情况下
                                        pass
        
        return nodes
    
    def _parse_formula(self, formula: str, start: int, end: int) -> Optional[ASTNode]:
        """
        解析公式为AST节点
        
        Args:
            formula: 公式字符串
            start: 起始位置
            end: 结束位置
        
        Returns:
            AST节点或None
        """
        if not formula or formula.strip() == '':
            return None
        
        # 移除外层括号
        formula = formula.strip()
        while formula.startswith('(') and formula.endswith(')'):
            # 检查是否整个公式都被括号包围
            depth = 0
            is_full = True
            for i, char in enumerate(formula):
                if char == '(':
                    depth += 1
                elif char == ')':
                    depth -= 1
                    if depth == 0 and i < len(formula) - 1:
                        is_full = False
                        break
            if is_full:
                formula = formula[1:-1].strip()
            else:
                break
        
        # 检查量词
        quantifier_match = self.quantifier_pattern.search(formula)
        if quantifier_match:
            quantifier = quantifier_match.group(1)
            is_forall = quantifier.startswith('!')
            remaining = formula[quantifier_match.end():].strip()
            
            # 解析量词内的公式
            inner_node = self._parse_formula(remaining, start, end)
            
            return ASTNode(
                node_type=ASTNodeType.FORALL if is_forall else ASTNodeType.EXISTS,
                content=quantifier,
                start_pos=start,
                end_pos=end,
                children=[inner_node] if inner_node else [],
                parent=None
            )
        
        # 检查二元运算符
        for op, op_type in self.binary_ops.items():
            if op in formula:
                # 找到运算符位置（考虑括号）
                op_pos = self._find_operator_position(formula, op)
                if op_pos != -1:
                    left = formula[:op_pos].strip()
                    right = formula[op_pos+len(op):].strip()
                    
                    left_node = self._parse_formula(left, start, start + op_pos)
                    right_node = self._parse_formula(right, start + op_pos + len(op), end)
                    
                    node_type_map = {
                        'conjunction': ASTNodeType.CONJUNCTION,
                        'disjunction': ASTNodeType.DISJUNCTION,
                        'implication': ASTNodeType.IMPLICATION,
                        'equivalence': ASTNodeType.EQUIVALENCE,
                        'equality': ASTNodeType.EQUALITY,
                        'inequality': ASTNodeType.INEQUALITY
                    }
                    
                    return ASTNode(
                        node_type=node_type_map.get(op_type, ASTNodeType.ATOM),
                        content=op,
                        start_pos=start + op_pos,
                        end_pos=start + op_pos + len(op),
                        children=[n for n in [left_node, right_node] if n is not None],
                        parent=None
                    )
        
        # 检查否定
        if formula.startswith('~') or formula.startswith('-'):
            inner = formula[1:].strip()
            inner_node = self._parse_formula(inner, start + 1, end)
            
            return ASTNode(
                node_type=ASTNodeType.NEGATION,
                content=formula[0],
                start_pos=start,
                end_pos=start + 1,
                children=[inner_node] if inner_node else [],
                parent=None
            )
        
        # 原子公式（谓词、函数等）
        return ASTNode(
            node_type=ASTNodeType.ATOM,
            content=formula,
            start_pos=start,
            end_pos=end,
            children=[],
            parent=None
        )
    
    def _find_operator_position(self, formula: str, operator: str) -> int:
        """
        找到运算符的位置（考虑括号）
        
        Args:
            formula: 公式字符串
            operator: 运算符
        
        Returns:
            运算符位置，-1表示未找到
        """
        depth = 0
        i = 0
        while i < len(formula) - len(operator) + 1:
            if formula[i] == '(':
                depth += 1
            elif formula[i] == ')':
                depth -= 1
            elif depth == 0 and formula[i:i+len(operator)] == operator:
                # 检查是否是完整的运算符（不在其他符号中）
                if (i == 0 or formula[i-1] in ' \t(,') and \
                   (i + len(operator) >= len(formula) or formula[i+len(operator)] in ' \t),'):
                    return i
            i += 1
        return -1


class ASTMutator:
    """AST级别变异器"""
    
    def __init__(self, seed: int = None):
        """
        初始化AST变异器
        
        Args:
            seed: 随机数种子
        """
        if seed is not None:
            random.seed(seed)
        self.random_seed = seed
        self.parser = TPTPASTParser()
        self.mutation_count = 0
        self.fallback_count = 0  # 记录回退次数
    
    def mutate(self, content: str, mutation_type: ASTMutationType = None) -> str:
        """
        对内容进行AST级别变异（带回退机制）
        
        Args:
            content: 原始TPTP内容
            mutation_type: 指定的变异类型（None表示随机选择）
        
        Returns:
            变异后的内容
        """
        if mutation_type is None:
            mutation_type = random.choice(list(ASTMutationType))
        
        # 解析为AST
        ast_nodes = self.parser.parse_file(content)
        
        if not ast_nodes:
            # 如果无法解析为AST，回退到token级别变异
            try:
                from mutator.token_mutator import TokenMutator
                token_mutator = TokenMutator(seed=self.random_seed)
                return token_mutator.mutate(content)
            except Exception:
                # 如果Token变异也失败，返回原始内容
                return content
        
        # 选择要变异的节点
        target_node = self._select_random_node(ast_nodes)
        if not target_node:
            return content
        
        # 执行变异
        if mutation_type == ASTMutationType.SWAP_SUBTREES:
            return self._swap_subtrees(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.DUPLICATE_SUBTREE:
            return self._duplicate_subtree(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.DELETE_SUBTREE:
            return self._delete_subtree(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.REPLACE_OPERATOR:
            return self._replace_operator(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.INVERT_QUANTIFIER:
            return self._invert_quantifier(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.NEGATE_FORMULA:
            return self._negate_formula(content, ast_nodes, target_node)
        elif mutation_type == ASTMutationType.SWAP_OPERANDS:
            return self._swap_operands(content, ast_nodes, target_node)
        else:
            return content
    
    def generate_mutants(self, content: str, count: int = 10) -> List[str]:
        """
        生成多个变异体（带自动回退机制和改进的生成逻辑）
        
        Args:
            content: 原始内容
            count: 生成数量
        
        Returns:
            变异体列表
        """
        # 尝试解析为AST
        ast_nodes = self.parser.parse_file(content)
        
        # 方案1: 回退机制 - 如果无法解析为AST，回退到Token级别变异
        if not ast_nodes:
            self.fallback_count += 1
            # 回退到Token级别变异
            try:
                from mutator.token_mutator import TokenMutator
                token_mutator = TokenMutator(seed=self.random_seed)
                mutants = token_mutator.generate_mutants(content, count)
                # 记录回退信息（可选：使用logging）
                if mutants:
                    return mutants
            except Exception as e:
                # 如果Token变异也失败，返回空列表
                # 使用警告信息而不是print（在生产代码中应使用logger）
                # Note: 这里使用warnings是为了避免循环依赖（logger可能依赖其他模块）
                import warnings
                warnings.warn(f"Both AST and Token mutation failed: {e}", RuntimeWarning)
                return []
        
        # 方案2: 改进的生成逻辑
        mutants = set()  # 使用set避免重复
        
        # 步骤1: 分析AST结构，智能选择变异操作
        suitable_mutation_types = self._get_suitable_mutation_types(ast_nodes)
        
        # 步骤2: 为每种合适的变异类型生成多个变异体
        # 改进：动态调整策略（基于研究）
        attempts_per_type = max(3, count // max(1, len(suitable_mutation_types)) + 2) if suitable_mutation_types else count * 2
        
        # 改进：记录每种类型的成功率，动态调整
        mutation_type_success = {}  # 记录每种类型的成功次数
        
        for mutation_type in suitable_mutation_types:
            if len(mutants) >= count:
                break
            
            # 改进：根据历史成功率动态调整尝试次数
            type_success_rate = mutation_type_success.get(mutation_type, 0.5)  # 默认50%
            base_attempts = attempts_per_type
            # 如果成功率低，增加尝试次数；如果成功率高，减少尝试次数
            dynamic_attempts = int(base_attempts * (2.0 - type_success_rate))
            max_attempts_for_type = max(3, dynamic_attempts * 3)
            
            successful_attempts = 0
            consecutive_failures = 0
            max_consecutive_failures = 5
            
            for attempt in range(max_attempts_for_type):
                if len(mutants) >= count:
                    break
                
                mutant = self.mutate(content, mutation_type)
                if mutant != content and mutant not in mutants:
                    mutants.add(mutant)
                    self.mutation_count += 1
                    successful_attempts += 1
                    consecutive_failures = 0
                    # 更新成功率
                    mutation_type_success[mutation_type] = successful_attempts / (attempt + 1)
                    if successful_attempts >= attempts_per_type:
                        break
                else:
                    consecutive_failures += 1
                    if consecutive_failures >= max_consecutive_failures:
                        break
        
        # 步骤3: 如果还不够，使用所有变异类型再次尝试（改进：更激进的策略）
        if len(mutants) < count:
            all_mutation_types = list(ASTMutationType)
            random.shuffle(all_mutation_types)  # 随机顺序增加多样性
            
            attempts = 0
            # 改进：增加尝试次数，提高成功率
            max_additional_attempts = (count - len(mutants)) * 10  # 从5倍增加到10倍
            
            # 改进：使用多种策略
            # 策略1: 随机选择变异类型
            while len(mutants) < count and attempts < max_additional_attempts:
                attempts += 1
                mutation_type = random.choice(all_mutation_types)
                mutant = self.mutate(content, mutation_type)
                if mutant != content and mutant not in mutants:
                    mutants.add(mutant)
                    self.mutation_count += 1
            
            # 策略2: 如果还不够，尝试组合变异（先AST后Token）
            if len(mutants) < count:
                # 尝试对已生成的变异体再次变异
                existing_mutants = list(mutants)
                for existing_mutant in existing_mutants[:min(5, len(existing_mutants))]:
                    if len(mutants) >= count:
                        break
                    # 对变异体再次变异
                    double_mutant = self.mutate(existing_mutant, random.choice(all_mutation_types))
                    if double_mutant != content and double_mutant not in mutants:
                        mutants.add(double_mutant)
                        self.mutation_count += 1
        
        # 步骤4: 如果AST变异仍然无法生成足够的变异体，回退到Token级别
        if len(mutants) < count:
            try:
                from mutator.token_mutator import TokenMutator
                token_mutator = TokenMutator(seed=self.random_seed)
                token_mutants = token_mutator.generate_mutants(content, count - len(mutants))
                # 合并结果
                mutants.update(token_mutants)
                self.fallback_count += 1
            except Exception as e:
                # Token变异回退失败（使用warnings而不是print）
                import warnings
                warnings.warn(f"Token mutation fallback failed: {e}", RuntimeWarning)
        
        return list(mutants)[:count]  # 返回最多count个变异体
    
    def _get_suitable_mutation_types(self, ast_nodes: List[ASTNode]) -> List[ASTMutationType]:
        """
        根据AST结构智能选择适合的变异操作类型
        
        Args:
            ast_nodes: AST节点列表
        
        Returns:
            适合的变异类型列表
        """
        suitable_types = []
        
        # 收集所有节点类型
        node_types = set()
        has_quantifiers = False
        has_operators = False
        has_binary_ops = False
        
        def collect_node_info(nodes: List[ASTNode]):
            """
            递归收集AST节点的类型信息
            
            Args:
                nodes: AST节点列表
            
            Note:
                这是一个内部辅助函数，用于分析AST结构
                并确定适合的变异操作类型
            """
            nonlocal has_quantifiers, has_operators, has_binary_ops
            for node in nodes:
                node_types.add(node.node_type)
                if node.node_type in [ASTNodeType.FORALL, ASTNodeType.EXISTS]:
                    has_quantifiers = True
                if node.node_type in [ASTNodeType.CONJUNCTION, ASTNodeType.DISJUNCTION, 
                                     ASTNodeType.IMPLICATION, ASTNodeType.EQUIVALENCE]:
                    has_operators = True
                    has_binary_ops = True
                if node.children:
                    collect_node_info(node.children)
        
        collect_node_info(ast_nodes)
        
        # 根据节点类型选择适合的变异操作
        if has_quantifiers:
            suitable_types.append(ASTMutationType.INVERT_QUANTIFIER)
        
        if has_operators:
            suitable_types.append(ASTMutationType.REPLACE_OPERATOR)
            suitable_types.append(ASTMutationType.SWAP_OPERANDS)
        
        if has_binary_ops:
            suitable_types.append(ASTMutationType.SWAP_SUBTREES)
        
        # 如果有多个节点，可以使用子树操作
        if len(ast_nodes) > 1:
            suitable_types.append(ASTMutationType.DUPLICATE_SUBTREE)
            suitable_types.append(ASTMutationType.DELETE_SUBTREE)
        
        # 否定操作总是可用
        suitable_types.append(ASTMutationType.NEGATE_FORMULA)
        
        # 如果找不到合适的，返回所有类型
        if not suitable_types:
            suitable_types = list(ASTMutationType)
        
        return suitable_types
    
    def _select_random_node(self, nodes: List[ASTNode]) -> Optional[ASTNode]:
        """
        随机选择一个AST节点
        
        Args:
            nodes: AST节点列表
        
        Returns:
            随机选择的节点或None
        """
        all_nodes = []
        self._collect_all_nodes(nodes, all_nodes)
        
        if not all_nodes:
            return None
        
        # 过滤掉根节点，优先选择内部节点
        internal_nodes = [n for n in all_nodes if n.parent is not None and len(n.children) > 0]
        
        if internal_nodes:
            return random.choice(internal_nodes)
        elif all_nodes:
            return random.choice(all_nodes)
        
        return None
    
    def _collect_all_nodes(self, nodes: List[ASTNode], result: List[ASTNode]):
        """
        收集所有AST节点
        
        Args:
            nodes: 节点列表
            result: 结果列表
        """
        for node in nodes:
            result.append(node)
            self._collect_all_nodes(node.children, result)
    
    def _swap_subtrees(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """交换子树"""
        if not target.children or len(target.children) < 2:
            return content
        
        # 找到兄弟节点或同一父节点的其他子节点
        if target.parent and len(target.parent.children) >= 2:
            siblings = [c for c in target.parent.children if c != target]
            if siblings:
                other = random.choice(siblings)
                # 交换内容和子节点
                target.content, other.content = other.content, target.content
                target.children, other.children = other.children, target.children
        
        return self._reconstruct_content(content, nodes)
    
    def _duplicate_subtree(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """复制子树"""
        if target.parent:
            # 在父节点中复制子节点
            duplicate = ASTNode(
                node_type=target.node_type,
                content=target.content,
                start_pos=target.start_pos,
                end_pos=target.end_pos,
                children=[child for child in target.children],
                parent=target.parent
            )
            target.parent.children.append(duplicate)
        
        return self._reconstruct_content(content, nodes)
    
    def _delete_subtree(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """删除子树"""
        if target.parent:
            target.parent.children = [c for c in target.parent.children if c != target]
        
        return self._reconstruct_content(content, nodes)
    
    def _replace_operator(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """替换运算符"""
        operator_replacements = {
            ASTNodeType.CONJUNCTION: ['|', '=>', '<=>'],
            ASTNodeType.DISJUNCTION: ['&', '=>', '<=>'],
            ASTNodeType.IMPLICATION: ['&', '|', '<=>'],
            ASTNodeType.EQUIVALENCE: ['&', '|', '=>'],
        }
        
        if target.node_type in operator_replacements:
            new_op = random.choice(operator_replacements[target.node_type])
            target.content = new_op
        
        return self._reconstruct_content(content, nodes)
    
    def _invert_quantifier(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """反转量词"""
        if target.node_type == ASTNodeType.FORALL:
            target.node_type = ASTNodeType.EXISTS
            # 将!替换为?
            target.content = target.content.replace('![', '?[')
        elif target.node_type == ASTNodeType.EXISTS:
            target.node_type = ASTNodeType.FORALL
            # 将?替换为!
            target.content = target.content.replace('?[', '![')
        
        return self._reconstruct_content(content, nodes)
    
    def _negate_formula(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """否定公式"""
        if target.node_type != ASTNodeType.NEGATION:
            # 添加否定
            negation_node = ASTNode(
                node_type=ASTNodeType.NEGATION,
                content='~',
                start_pos=target.start_pos,
                end_pos=target.start_pos + 1,
                children=[target],
                parent=target.parent
            )
            if target.parent:
                idx = target.parent.children.index(target)
                target.parent.children[idx] = negation_node
        else:
            # 移除否定（双重否定消除）
            if target.children:
                child = target.children[0]
                if target.parent:
                    idx = target.parent.children.index(target)
                    target.parent.children[idx] = child
        
        return self._reconstruct_content(content, nodes)
    
    def _swap_operands(self, content: str, nodes: List[ASTNode], target: ASTNode) -> str:
        """交换操作数"""
        if len(target.children) == 2:
            target.children[0], target.children[1] = target.children[1], target.children[0]
        
        return self._reconstruct_content(content, nodes)
    
    def _reconstruct_content(self, content: str, nodes: List[ASTNode]) -> str:
        """
        从AST重构内容
        
        Args:
            content: 原始内容
            nodes: AST节点列表
        
        Returns:
            重构后的内容
        """
        if not nodes:
            return content
        
        try:
            # 重构每个公式节点
            reconstructed_parts = []
            
            # 保持原始文件结构（注释、空行等）
            lines = content.split('\n')
            reconstructed_lines = []
            
            # 找到公式部分并替换
            for line in lines:
                if self.parser.fof_pattern.search(line) or self.parser.cnf_pattern.search(line):
                    # 这是公式行，需要重构
                    # 提取公式部分
                    match = self.parser.fof_pattern.search(line) or self.parser.cnf_pattern.search(line)
                    if match:
                        # 重建公式行
                        name = match.group(1).strip()
                        role = match.group(2).strip()
                        
                        # 找到对应的AST节点并重构公式部分
                        formula_text = match.group(3).strip()
                        reconstructed_formula = self._reconstruct_formula_from_ast(nodes, formula_text)
                        
                        # 重建整行
                        prefix = line[:match.start()]
                        suffix = line[match.end():]
                        
                        if self.parser.fof_pattern.search(line):
                            new_line = f"{prefix}fof({name}, {role}, {reconstructed_formula}).{suffix}"
                        else:
                            new_line = f"{prefix}cnf({name}, {role}, {reconstructed_formula}).{suffix}"
                        
                        reconstructed_lines.append(new_line)
                    else:
                        reconstructed_lines.append(line)
                else:
                    # 非公式行（注释、空行等），保持不变
                    reconstructed_lines.append(line)
            
            return '\n'.join(reconstructed_lines)
        
        except Exception as e:
            # 如果重构失败，返回原始内容
            # AST重构失败（使用warnings而不是print）
            import warnings
            warnings.warn(f"AST reconstruction failed: {e}", RuntimeWarning)
            return content
    
    def _reconstruct_formula_from_ast(self, nodes: List[ASTNode], original_formula: str) -> str:
        """
        从AST节点重构公式
        
        Args:
            nodes: AST节点列表
            original_formula: 原始公式字符串
        
        Returns:
            重构后的公式
        """
        if not nodes:
            return original_formula
        
        # 找到匹配的节点（简化：使用第一个FORMULA节点的子节点）
        for node in nodes:
            if node.node_type == ASTNodeType.FORMULA and node.children:
                formula_node = node.children[0]
                return self._reconstruct_node(formula_node)
        
        return original_formula
    
    def _reconstruct_node(self, node: ASTNode) -> str:
        """
        递归重构单个AST节点
        
        Args:
            node: AST节点
        
        Returns:
            重构后的字符串
        """
        if not node:
            return ""
        
        # 根据节点类型重构
        if node.node_type == ASTNodeType.NEGATION:
            # 否定：~(...)
            if node.children:
                child_str = self._reconstruct_node(node.children[0])
                return f"~({child_str})"
            return "~"
        
        elif node.node_type == ASTNodeType.FORALL:
            # 全称量词：![X: type] (...)
            quantifier_str = node.content  # 例如：![X: a]
            if node.children:
                body_str = self._reconstruct_node(node.children[0])
                return f"{quantifier_str}({body_str})"
            return quantifier_str
        
        elif node.node_type == ASTNodeType.EXISTS:
            # 存在量词：?[X: type] (...)
            quantifier_str = node.content  # 例如：?[X: a]
            if node.children:
                body_str = self._reconstruct_node(node.children[0])
                return f"{quantifier_str}({body_str})"
            return quantifier_str
        
        elif node.node_type in [ASTNodeType.CONJUNCTION, ASTNodeType.DISJUNCTION, 
                                ASTNodeType.IMPLICATION, ASTNodeType.EQUIVALENCE]:
            # 二元运算符：(left op right)
            if len(node.children) == 2:
                left_str = self._reconstruct_node(node.children[0])
                right_str = self._reconstruct_node(node.children[1])
                op = node.content
                return f"({left_str} {op} {right_str})"
            elif len(node.children) == 1:
                return self._reconstruct_node(node.children[0])
            return node.content
        
        elif node.node_type in [ASTNodeType.EQUALITY, ASTNodeType.INEQUALITY]:
            # 等式/不等式：(left = right) 或 (left != right)
            if len(node.children) == 2:
                left_str = self._reconstruct_node(node.children[0])
                right_str = self._reconstruct_node(node.children[1])
                op = node.content
                return f"({left_str} {op} {right_str})"
            return node.content
        
        elif node.node_type == ASTNodeType.ATOM:
            # 原子公式：直接返回内容
            return node.content
        
        else:
            # 其他类型：递归重构子节点
            if node.children:
                child_strs = [self._reconstruct_node(child) for child in node.children]
                return ' '.join(child_strs)
            return node.content if node.content else ""

