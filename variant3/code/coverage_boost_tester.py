#!/usr/bin/env python3
"""
覆盖率提升测试器

直接测试Seed_Provable.thy中的可证明lemmas
目标: 触发proof重放、falsification等未覆盖的函数
"""

import subprocess
import time
import logging
from pathlib import Path

# 导入隐藏异常检测器
from hidden_exception_detector import HiddenExceptionDetector

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger('coverage_boost')

# 全局隐藏异常检测器
hidden_detector = HiddenExceptionDetector()


def test_provable_theory(theory_path: str, timeout: int = 300):
    """
    测试包含Sledgehammer调用的theory文件
    这会直接运行Sledgehammer并触发proof重放等功能
    """
    logger.info(f"Testing theory: {theory_path}")
    logger.info(f"This will run Sledgehammer directly (not via Mirabelle)")
    
    # 【重要】测试前清空隐藏异常日志
    hidden_detector.clear_logs()
    
    start_time = time.time()
    hidden_exception_info = ""
    
    try:
        # 使用isabelle build来处理包含sledgehammer调用的theory
        # 这会实际执行sledgehammer命令
        result = subprocess.run(
            ['isabelle', 'jedit', '-b', theory_path],
            capture_output=True,
            text=True,
            timeout=timeout
        )
        
        duration = time.time() - start_time
        
        logger.info(f"Completed in {duration:.2f}s")
        logger.info(f"Return code: {result.returncode}")
        
        # 【重要】检查隐藏异常
        hidden_result = hidden_detector.check_for_exceptions()
        if hidden_result["found_exceptions"]:
            logger.warning(f"🔴 发现隐藏异常: {hidden_result['exception_count']} 个")
            hidden_exception_info = hidden_result["raw_content"][:500]
        else:
            logger.info("✅ 没有发现隐藏异常")
        
        # 检查输出中是否有证明成功的标记
        if 'Sledgehammer found' in result.stdout or 'Try this' in result.stdout:
            logger.info("✅ Sledgehammer found proofs!")
        else:
            logger.info("❌ No proofs found in output")
        
        return result, hidden_exception_info
        
    except subprocess.TimeoutExpired:
        # 即使超时也检查隐藏异常
        hidden_result = hidden_detector.check_for_exceptions()
        if hidden_result["found_exceptions"]:
            hidden_exception_info = hidden_result["raw_content"][:500]
        
        logger.warning(f"⏱️  Timeout after {timeout}s")
        return None, hidden_exception_info
    except Exception as e:
        logger.error(f"❌ Error: {e}")
        return None, ""


def check_coverage_logs():
    """检查覆盖率相关的日志"""
    logger.info("\n" + "=" * 60)
    logger.info("Checking coverage/exception logs...")
    logger.info("=" * 60)
    
    # 使用统一的隐藏异常检测器
    result = hidden_detector.check_for_exceptions()
    
    if result["found_exceptions"]:
        logger.info(f"🎯 发现 {result['exception_count']} 个隐藏异常!")
        for exc in result["exceptions"][:5]:
            logger.info(f"  [{exc.exception_type}] {exc.message[:80]}")
    else:
        logger.info("✅ 没有发现隐藏异常")
    
    # 也检查覆盖率日志
    coverage_log = Path("/tmp/sledgehammer_coverage.log")
    if coverage_log.exists() and coverage_log.stat().st_size > 0:
        lines = coverage_log.read_text().strip().split('\n')
        logger.info(f"📊 覆盖率日志: {len(lines)} 条记录")
    else:
        logger.info("❌ 覆盖率日志为空")


def main():
    logger.info("=" * 60)
    logger.info("🚀 Coverage Boost Test")
    logger.info("=" * 60)
    logger.info("")
    logger.info("Goal: Test provable lemmas to trigger uncovered functions")
    logger.info("  - play_one_line_proofs")
    logger.info("  - select_one_line_proof")
    logger.info("  - check_expected_outcome")
    logger.info("  - analyze_prover_result_for_inconsistency")
    logger.info("")
    
    theory_path = "data/seed_theories/Seed_Provable.thy"
    
    # 测试theory
    result, hidden_exception = test_provable_theory(theory_path)
    
    # 检查日志
    check_coverage_logs()
    
    logger.info("\n" + "=" * 60)
    logger.info("Test completed")
    logger.info("=" * 60)
    
    if hidden_exception:
        logger.warning("\n🔴 发现隐藏异常:")
        logger.warning(hidden_exception)
    
    if result:
        logger.info("\n建议: 检查Isabelle输出，看是否有proof成功")
        logger.info("如果有成功的proof，说明触发了proof重放逻辑")


if __name__ == '__main__':
    main()

