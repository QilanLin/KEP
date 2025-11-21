#!/usr/bin/env python3
"""
集成测试：测试AST变异器和重构Oracle在主程序中的集成
"""

import sys
from pathlib import Path

# 添加项目路径
sys.path.insert(0, str(Path(__file__).parent.parent))

from main import Fuzzer


def test_fuzzer_init_with_ast_mutator():
    """测试使用AST变异器初始化Fuzzer"""
    print("=" * 50)
    print("测试：使用AST变异器初始化Fuzzer")
    print("=" * 50)
    
    config = {
        'seed_dir': '../sledgehammer_export',
        'output_dir': './test_results',
        'timeout': 5.0,
        'num_mutants': 5,
        'max_seeds': 2,
        'use_ast_mutator': True,
        'use_reconstruction_oracle': False,
        'show_progress': False
    }
    
    try:
        fuzzer = Fuzzer(config)
        assert fuzzer.use_ast_mutator == True
        assert hasattr(fuzzer.mutator, 'mutate')  # 应该有mutate方法
        assert fuzzer.mutator_type == "AST级别"
        print("✅ AST变异器初始化成功")
        print(f"   变异器类型: {fuzzer.mutator_type}")
        print()
    except Exception as e:
        print(f"❌ 初始化失败: {e}")
        raise


def test_fuzzer_init_with_reconstruction_oracle():
    """测试使用重构Oracle初始化Fuzzer"""
    print("=" * 50)
    print("测试：使用重构Oracle初始化Fuzzer")
    print("=" * 50)
    
    config = {
        'seed_dir': '../sledgehammer_export',
        'output_dir': './test_results',
        'timeout': 5.0,
        'num_mutants': 5,
        'max_seeds': 2,
        'use_ast_mutator': False,
        'use_reconstruction_oracle': True,
        'isabelle_path': 'isabelle',
        'reconstruction_timeout': 30.0,
        'show_progress': False
    }
    
    try:
        fuzzer = Fuzzer(config)
        assert fuzzer.use_reconstruction_oracle == True
        assert fuzzer.reconstruction_oracle is not None
        print("✅ 重构Oracle初始化成功")
        print(f"   Isabelle路径: {fuzzer.isabelle_path}")
        print(f"   重构超时: {fuzzer.reconstruction_timeout}秒")
        print()
    except Exception as e:
        print(f"❌ 初始化失败: {e}")
        raise


def test_fuzzer_init_with_both():
    """测试同时使用AST变异器和重构Oracle"""
    print("=" * 50)
    print("测试：同时使用AST变异器和重构Oracle")
    print("=" * 50)
    
    config = {
        'seed_dir': '../sledgehammer_export',
        'output_dir': './test_results',
        'timeout': 5.0,
        'num_mutants': 5,
        'max_seeds': 2,
        'use_ast_mutator': True,
        'use_reconstruction_oracle': True,
        'isabelle_path': 'isabelle',
        'reconstruction_timeout': 30.0,
        'show_progress': False
    }
    
    try:
        fuzzer = Fuzzer(config)
        assert fuzzer.use_ast_mutator == True
        assert fuzzer.use_reconstruction_oracle == True
        assert fuzzer.reconstruction_oracle is not None
        assert fuzzer.mutator_type == "AST级别"
        print("✅ 同时使用AST变异器和重构Oracle成功")
        print(f"   变异器类型: {fuzzer.mutator_type}")
        print(f"   重构Oracle: 启用")
        print()
    except Exception as e:
        print(f"❌ 初始化失败: {e}")
        raise


def main():
    """运行所有集成测试"""
    print("🧪 集成测试套件")
    print()
    
    try:
        test_fuzzer_init_with_ast_mutator()
        test_fuzzer_init_with_reconstruction_oracle()
        test_fuzzer_init_with_both()
        
        print("=" * 50)
        print("✅ 所有集成测试通过！")
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

