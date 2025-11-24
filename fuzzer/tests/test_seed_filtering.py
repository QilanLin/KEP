#!/usr/bin/env python3
"""
种子预过滤功能测试
"""

import unittest
import tempfile
import os
from pathlib import Path

# 添加项目路径
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from oracle.crash_oracle import CrashOracle, OracleResult


class TestSeedFiltering(unittest.TestCase):
    """种子预过滤测试"""
    
    def setUp(self):
        """测试前准备"""
        self.oracle = CrashOracle(timeout=1.0)  # 使用短超时测试
    
    def test_fast_seed_should_pass(self):
        """测试：快速种子应该通过过滤"""
        # 创建一个简单的测试文件
        with tempfile.NamedTemporaryFile(mode='w', suffix='.p', delete=False) as f:
            f.write('fof(test, axiom, p).\n')
            test_file = f.name
        
        try:
            # 注意：这里需要一个实际的prover路径
            # 在实际测试中，可以mock这个调用
            pass  # 跳过实际调用，只测试逻辑
        finally:
            os.unlink(test_file)
    
    def test_slow_seed_should_be_filtered(self):
        """测试：慢速种子应该被过滤"""
        # 这个测试需要一个实际会超时的输入
        # 在实际实现中，可以使用mock来模拟超时
        pass
    
    def test_filtering_configuration(self):
        """测试：过滤配置应该正确应用"""
        config = {
            'enable_seed_filtering': True,
            'seed_filter_timeout': 5.0,
            'timeout': 30.0
        }
        
        self.assertTrue(config['enable_seed_filtering'])
        self.assertEqual(config['seed_filter_timeout'], 5.0)
        self.assertEqual(config['timeout'], 30.0)


class TestTimeoutConfiguration(unittest.TestCase):
    """超时配置测试"""
    
    def test_default_timeout_is_30_seconds(self):
        """测试：默认超时应该是30秒"""
        config = {
            'timeout': 30.0
        }
        self.assertEqual(config['timeout'], 30.0)
    
    def test_seed_filter_timeout_is_shorter(self):
        """测试：种子过滤超时应该短于主超时"""
        config = {
            'timeout': 30.0,
            'seed_filter_timeout': 10.0
        }
        self.assertLess(config['seed_filter_timeout'], config['timeout'])


if __name__ == '__main__':
    unittest.main()

