#!/usr/bin/env python3
"""
测试pySMT是否能正确解析SMT-LIB文件
"""

import sys
import os

# 添加虚拟环境路径
if os.path.exists('venv'):
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'venv', 'lib', 'python3.13', 'site-packages'))

try:
    from pysmt.smtlib.parser import SmtLibParser
    from pysmt.shortcuts import get_env
    
    print("✅ pySMT导入成功")
    print(f"   版本: {__import__('pysmt').__version__}")
    
    # 创建测试SMT-LIB文件
    test_content = """(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (< y 10))
(check-sat)
"""
    
    test_file = "test_parse.smt2"
    with open(test_file, "w") as f:
        f.write(test_content)
    
    print(f"\n✅ 创建测试文件: {test_file}")
    
    # 尝试解析
    parser = SmtLibParser()
    script = parser.get_script_fname(test_file)
    
    print(f"✅ 成功解析SMT-LIB文件！")
    print(f"   找到 {len(script.commands)} 个命令:")
    for i, cmd in enumerate(script.commands, 1):
        print(f"   {i}. {cmd.name}")
    
    # 清理测试文件
    os.remove(test_file)
    print(f"\n✅ pySMT测试通过！可以用于解析SMT-LIB文件。")
    
except ImportError as e:
    print(f"❌ pySMT导入失败: {e}")
    print("   请确保已安装pySMT:")
    print("   source venv/bin/activate")
    print("   pip install pysmt")
    sys.exit(1)
except Exception as e:
    print(f"❌ 测试失败: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)

