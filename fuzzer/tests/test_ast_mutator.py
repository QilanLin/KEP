#!/usr/bin/env python3
"""
AST变异器测试
"""

import sys
from pathlib import Path

# 添加项目路径
sys.path.insert(0, str(Path(__file__).parent.parent))

from mutator.ast_mutator import ASTMutator, ASTMutationType, TPTPASTParser


def test_ast_parser():
    """测试AST解析器"""
    print("=" * 50)
    print("测试AST解析器")
    print("=" * 50)
    
    parser = TPTPASTParser()
    
    # 测试简单公式
    test_content = """fof(test, axiom, (x = y)).
cnf(test2, axiom, (p(x) | q(x))).
"""
    
    nodes = parser.parse_file(test_content)
    print(f"解析结果: 找到 {len(nodes)} 个公式节点")
    
    for i, node in enumerate(nodes, 1):
        print(f"节点 {i}: {node.node_type}")
        print(f"  内容: {node.content[:50]}...")
        print(f"  子节点数: {len(node.children)}")
    
    assert len(nodes) > 0, "应该解析出至少一个节点"
    print("✅ AST解析器测试通过\n")


def test_ast_mutator():
    """测试AST变异器"""
    print("=" * 50)
    print("测试AST变异器")
    print("=" * 50)
    
    mutator = ASTMutator(seed=42)
    
    # 测试简单公式
    test_content = """fof(test, axiom, (![X: a]: (p(X) => q(X)))).
cnf(test2, axiom, ((x = y) & (y = z))).
"""
    
    print("原始内容:")
    print(test_content)
    print()
    
    # 测试每种变异类型
    mutation_types = [
        ASTMutationType.INVERT_QUANTIFIER,
        ASTMutationType.REPLACE_OPERATOR,
        ASTMutationType.NEGATE_FORMULA,
        ASTMutationType.SWAP_OPERANDS,
    ]
    
    for mutation_type in mutation_types:
        print(f"变异类型: {mutation_type.value}")
        mutant = mutator.mutate(test_content, mutation_type)
        if mutant != test_content:
            print(f"变异成功:")
            print(mutant[:200])
            print()
        else:
            print("未发生变异\n")
    
    # 测试生成多个变异体
    print("生成多个变异体:")
    mutants = mutator.generate_mutants(test_content, count=5)
    print(f"生成 {len(mutants)} 个变异体")
    
    for i, mutant in enumerate(mutants[:3], 1):  # 只显示前3个
        print(f"变异体 {i}:")
        print(mutant[:150])
        print()
    
    assert len(mutants) > 0, "应该生成至少一个变异体"
    print("✅ AST变异器测试通过\n")


def test_ast_reconstruction():
    """测试AST内容重构"""
    print("=" * 50)
    print("测试AST内容重构")
    print("=" * 50)
    
    parser = TPTPASTParser()
    mutator = ASTMutator(seed=42)
    
    # 测试简单公式
    test_content = """fof(test, axiom, (![X: a]: (p(X) => q(X)))).
"""
    
    print("原始内容:")
    print(test_content)
    
    # 解析为AST
    nodes = parser.parse_file(test_content)
    print(f"解析出 {len(nodes)} 个公式节点")
    
    # 测试重构
    if nodes:
        reconstructed = mutator._reconstruct_content(test_content, nodes)
        print("\n重构后内容:")
        print(reconstructed)
        
        # 验证重构后的内容至少包含原始内容的关键部分
        assert "fof" in reconstructed.lower() or "cnf" in reconstructed.lower()
        print("✅ AST内容重构测试通过\n")
    else:
        print("⚠️ 无法解析AST，跳过重构测试\n")


def main():
    """运行所有测试"""
    print("🧪 AST变异器测试套件")
    print()
    
    try:
        test_ast_parser()
        test_ast_mutator()
        test_ast_reconstruction()
        
        print("=" * 50)
        print("✅ 所有测试通过！")
        print("=" * 50)
        
    except AssertionError as e:
        print(f"❌ 测试失败: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ 测试出错: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()

