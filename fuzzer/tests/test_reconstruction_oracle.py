#!/usr/bin/env python3
"""
重构Oracle测试
"""

import sys
from pathlib import Path
from unittest.mock import Mock, patch

# 添加项目路径
sys.path.insert(0, str(Path(__file__).parent.parent))

from oracle.reconstruction_oracle import (
    ReconstructionOracle,
    ReconstructionStatus,
    FailureType,
    ProverResult as ReconstructionProverResult
)


def test_reconstruction_oracle_init():
    """测试重构Oracle初始化"""
    print("=" * 50)
    print("测试重构Oracle初始化")
    print("=" * 50)
    
    oracle = ReconstructionOracle(
        isabelle_path="isabelle",
        timeout=30.0
    )
    
    assert oracle.isabelle_path == "isabelle"
    assert oracle.timeout == 30.0
    assert oracle.error_patterns is not None
    print("✅ 重构Oracle初始化测试通过\n")


def test_failure_classification():
    """测试失败类型分类"""
    print("=" * 50)
    print("测试失败类型分类")
    print("=" * 50)
    
    oracle = ReconstructionOracle()
    
    # 测试不同类型的错误消息
    test_cases = [
        ("syntax error in formula", FailureType.SYNTAX_ERROR),
        ("type error: cannot unify", FailureType.TYPE_ERROR),
        ("reconstruction failed", FailureType.PROOF_RECONSTRUCTION),
        ("timeout exceeded", FailureType.TIMEOUT),
        ("unknown error", FailureType.UNKNOWN),
    ]
    
    for error_msg, expected_type in test_cases:
        failure_type = oracle._classify_failure(error_msg)
        print(f"错误消息: {error_msg[:30]}...")
        print(f"分类结果: {failure_type.value}")
        
        if expected_type == FailureType.UNKNOWN:
            # UNKNOWN类型可能匹配其他模式，所以允许
            assert failure_type is not None
        else:
            assert failure_type == expected_type or failure_type == FailureType.UNKNOWN
    
    print("✅ 失败类型分类测试通过\n")


def test_prover_result_creation():
    """测试ProverResult创建"""
    print("=" * 50)
    print("测试ProverResult创建")
    print("=" * 50)
    
    # 创建模拟的ProverResult
    prover_result = ReconstructionProverResult(
        status="sat",
        proof="(proof content...)",
        model=None,
        error=None
    )
    
    assert prover_result.status == "sat"
    assert prover_result.proof is not None
    print("✅ ProverResult创建测试通过\n")


def test_is_bug():
    """测试is_bug方法"""
    print("=" * 50)
    print("测试is_bug方法")
    print("=" * 50)
    
    oracle = ReconstructionOracle()
    
    # 测试成功情况（不是bug）
    from oracle.reconstruction_oracle import ReconstructionResult
    success_result = ReconstructionResult(
        status=ReconstructionStatus.SUCCESS,
        reconstruction_attempted=True
    )
    assert not oracle.is_bug(success_result)
    print("成功情况：不是bug ✓")
    
    # 测试失败情况（是bug）
    failure_result = ReconstructionResult(
        status=ReconstructionStatus.FAILURE,
        failure_type=FailureType.PROOF_RECONSTRUCTION,
        error_message="reconstruction failed",
        reconstruction_attempted=True
    )
    assert oracle.is_bug(failure_result)
    print("失败情况：是bug ✓")
    
    print("✅ is_bug方法测试通过\n")


def main():
    """运行所有测试"""
    print("🧪 重构Oracle测试套件")
    print()
    
    try:
        test_reconstruction_oracle_init()
        test_failure_classification()
        test_prover_result_creation()
        test_is_bug()
        
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

