#!/usr/bin/env python3
"""
TPTP解析器
解析TPTP格式文件并转换为AST表示
"""

import re
import os
from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from enum import Enum


class TPTPFormulaType(Enum):
    """TPTP公式类型"""
    AXIOM = "axiom"
    HYPOTHESIS = "hypothesis"
    CONJECTURE = "conjecture"
    TYPE = "type"
    UNKNOWN = "unknown"


@dataclass
class TPTPFormula:
    """TPTP公式表示"""
    name: str
    formula_type: TPTPFormulaType
    content: str
    line_number: Optional[int] = None


class TPTPParser:
    """TPTP文件解析器"""
    
    def __init__(self):
        self.formulas: List[TPTPFormula] = []
    
    def parse_file(self, file_path: str) -> List[TPTPFormula]:
        """
        解析TPTP文件
        
        Args:
            file_path: TPTP文件路径
            
        Returns:
            TPTP公式列表
        """
        if not os.path.exists(file_path):
            raise FileNotFoundError(f"文件不存在: {file_path}")
        
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        return self.parse(content)
    
    def parse(self, content: str) -> List[TPTPFormula]:
        """
        解析TPTP内容
        
        Args:
            content: TPTP文件内容
            
        Returns:
            TPTP公式列表
        """
        self.formulas = []
        lines = content.split('\n')
        
        current_formula = None
        current_content = []
        in_formula = False
        
        for line_num, line in enumerate(lines, 1):
            # 跳过注释行
            if line.strip().startswith('%'):
                continue
            
            # 检测TPTP公式开始（fof, cnf, tff等）
            formula_match = re.match(r'(fof|cnf|tff)\((\w+),', line)
            if formula_match:
                # 保存之前的公式
                if current_formula and current_content:
                    current_formula.content = ' '.join(current_content)
                    self.formulas.append(current_formula)
                
                # 开始新公式
                formula_type_str = formula_match.group(1)
                formula_name = formula_match.group(2)
                formula_type = self._extract_formula_type(line)
                
                current_formula = TPTPFormula(
                    name=formula_name,
                    formula_type=formula_type,
                    content="",
                    line_number=line_num
                )
                current_content = [line]
                in_formula = True
                continue
            
            # 如果正在解析公式
            if in_formula:
                current_content.append(line)
                # 检查公式是否结束（包含闭合括号和分号）
                if ').' in line or ')).' in line:
                    in_formula = False
        
        # 添加最后一个公式
        if current_formula and current_content:
            current_formula.content = ' '.join(current_content)
            self.formulas.append(current_formula)
        
        return self.formulas
    
    def _extract_formula_type(self, line: str) -> TPTPFormulaType:
        """从行中提取公式类型"""
        line_lower = line.lower()
        
        if 'conjecture' in line_lower:
            return TPTPFormulaType.CONJECTURE
        elif 'axiom' in line_lower:
            return TPTPFormulaType.AXIOM
        elif 'hypothesis' in line_lower:
            return TPTPFormulaType.HYPOTHESIS
        elif 'type' in line_lower:
            return TPTPFormulaType.TYPE
        else:
            return TPTPFormulaType.UNKNOWN
    
    def get_formulas_by_type(self, formula_type: TPTPFormulaType) -> List[TPTPFormula]:
        """按类型获取公式"""
        return [f for f in self.formulas if f.formula_type == formula_type]
    
    def get_conjectures(self) -> List[TPTPFormula]:
        """获取所有猜想（conjecture）"""
        return self.get_formulas_by_type(TPTPFormulaType.CONJECTURE)
    
    def get_axioms(self) -> List[TPTPFormula]:
        """获取所有公理（axiom）"""
        return self.get_formulas_by_type(TPTPFormulaType.AXIOM)


def main():
    """测试函数"""
    parser = TPTPParser()
    
    # 测试解析
    test_file = "../sledgehammer_export/prob4729480_1.p"
    
    if os.path.exists(test_file):
        print(f"解析文件: {test_file}")
        formulas = parser.parse_file(test_file)
        
        print(f"\n找到 {len(formulas)} 个公式:")
        for formula in formulas[:5]:  # 只显示前5个
            print(f"  - {formula.name}: {formula.formula_type.value}")
        
        conjectures = parser.get_conjectures()
        if conjectures:
            print(f"\n找到 {len(conjectures)} 个猜想:")
            for conj in conjectures:
                print(f"  - {conj.name}")
    else:
        print(f"测试文件不存在: {test_file}")
        print("请先运行Sledgehammer导出一些TPTP文件")


if __name__ == "__main__":
    main()

