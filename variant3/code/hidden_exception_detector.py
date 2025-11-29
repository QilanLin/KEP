#!/usr/bin/env python3
"""
隐藏异常检测器 (Hidden Exception Detector)

专门用于检测被 Sledgehammer 的 try-catch 块吞掉的异常。

背景：
    Sledgehammer 使用防御性的 try-catch 机制：
    
    catch ERROR msg => 
      (SH_Unknown, fn () => msg ^ "\n")
    | exn => 
      (SH_Unknown, fn () => Runtime.exn_message exn ^ "\n")
    
    这意味着内部异常会被转换为 SH_Unknown 状态，而不是崩溃。
    从外部（如 Mirabelle）只能看到 "没找到证明"，无法区分是：
    - 正常的没找到证明
    - 还是发生了内部异常

解决方案：
    我们在 sledgehammer.ML 中插入了日志代码：
    
    fun log_exception prefix msg =
      File.append (Path.explode "/tmp/sledgehammer_hidden_errors.log") ...
    
    当 catch 块被执行时，会记录到日志文件中。
    
    本检测器负责：
    1. 在测试前清空日志
    2. 在测试后检查日志
    3. 如果有内容，说明发现了隐藏的异常（真正的 Integration Bug）

使用方法：
    detector = HiddenExceptionDetector()
    
    # 测试前
    detector.clear_logs()
    
    # 运行测试...
    
    # 测试后
    result = detector.check_for_exceptions()
    if result["found_exceptions"]:
        print(f"发现 {result['exception_count']} 个隐藏异常！")
        for exc in result["exceptions"]:
            print(f"  - {exc}")
"""

import os
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass
from datetime import datetime
import logging

logger = logging.getLogger(__name__)


@dataclass
class HiddenException:
    """隐藏异常记录"""
    timestamp: str
    exception_type: str  # "ERROR" 或 "EXCEPTION"
    message: str
    source_file: str


class HiddenExceptionDetector:
    """
    隐藏异常检测器
    
    检测被 Sledgehammer 的 catch 块吞掉的异常。
    """
    
    # 插桩日志文件路径
    LOG_FILES = {
        "sledgehammer": "/tmp/sledgehammer_hidden_errors.log",
        "mirabelle": "/tmp/mirabelle_hidden_errors.log",
        "coverage": "/tmp/sledgehammer_coverage.log"
    }
    
    def __init__(self):
        """初始化检测器"""
        logger.info("🔍 HiddenExceptionDetector 初始化")
        logger.info(f"   监控文件: {list(self.LOG_FILES.values())}")
    
    def clear_logs(self) -> None:
        """
        清空所有插桩日志文件
        
        应该在每次测试前调用，确保日志只包含当前测试的异常。
        """
        for name, log_path in self.LOG_FILES.items():
            try:
                path = Path(log_path)
                if path.exists():
                    path.unlink()
                    logger.debug(f"✅ 已清空: {log_path}")
            except Exception as e:
                logger.warning(f"⚠️ 无法清空 {log_path}: {e}")
        
        logger.info("📋 所有插桩日志已清空")
    
    def check_for_exceptions(self) -> Dict:
        """
        检查是否有隐藏异常被记录
        
        Returns:
            {
                "found_exceptions": bool,      # 是否发现异常
                "exception_count": int,        # 异常数量
                "exceptions": List[HiddenException],  # 异常详情
                "raw_content": str             # 原始日志内容
            }
        """
        result = {
            "found_exceptions": False,
            "exception_count": 0,
            "exceptions": [],
            "raw_content": "",
            "source_files": []
        }
        
        # 只检查异常日志（不检查覆盖率日志）
        exception_logs = ["sledgehammer", "mirabelle"]
        
        for name in exception_logs:
            log_path = self.LOG_FILES[name]
            try:
                path = Path(log_path)
                if path.exists():
                    content = path.read_text()
                    if content.strip():
                        result["found_exceptions"] = True
                        result["raw_content"] += f"\n=== {name} ===\n{content}"
                        result["source_files"].append(log_path)
                        
                        # 解析每一行
                        for line in content.strip().split('\n'):
                            exception = self._parse_exception_line(line, log_path)
                            if exception:
                                result["exceptions"].append(exception)
                                result["exception_count"] += 1
                        
                        logger.info(f"🔴 在 {log_path} 中发现 {len(content.strip().split(chr(10)))} 个异常")
            
            except Exception as e:
                logger.warning(f"⚠️ 无法读取 {log_path}: {e}")
        
        if result["found_exceptions"]:
            logger.warning(f"🔴 发现 {result['exception_count']} 个隐藏异常！")
        else:
            logger.info("✅ 没有发现隐藏异常")
        
        return result
    
    def _parse_exception_line(self, line: str, source_file: str) -> Optional[HiddenException]:
        """
        解析异常日志行
        
        格式: "timestamp | TYPE: message"
        例如: "Sat Nov 29 18:12:06 2025 | ERROR: Some error message"
        """
        try:
            if " | " not in line:
                return None
            
            parts = line.split(" | ", 1)
            if len(parts) != 2:
                return None
            
            timestamp = parts[0].strip()
            type_and_msg = parts[1].strip()
            
            if ": " in type_and_msg:
                exc_type, message = type_and_msg.split(": ", 1)
            else:
                exc_type = "UNKNOWN"
                message = type_and_msg
            
            return HiddenException(
                timestamp=timestamp,
                exception_type=exc_type,
                message=message,
                source_file=source_file
            )
        
        except Exception as e:
            logger.debug(f"无法解析行: {line} - {e}")
            return None
    
    def get_exception_summary(self) -> str:
        """
        获取异常摘要（用于报告）
        """
        result = self.check_for_exceptions()
        
        if not result["found_exceptions"]:
            return "✅ 没有发现隐藏异常"
        
        summary = [
            f"🔴 发现 {result['exception_count']} 个隐藏异常！",
            ""
        ]
        
        # 按类型分组
        by_type = {}
        for exc in result["exceptions"]:
            if exc.exception_type not in by_type:
                by_type[exc.exception_type] = []
            by_type[exc.exception_type].append(exc)
        
        for exc_type, exceptions in by_type.items():
            summary.append(f"  [{exc_type}] {len(exceptions)} 个:")
            for exc in exceptions[:3]:  # 只显示前3个
                summary.append(f"    - {exc.message[:80]}...")
            if len(exceptions) > 3:
                summary.append(f"    ... 还有 {len(exceptions) - 3} 个")
        
        return "\n".join(summary)
    
    def generate_report(self, output_file: Optional[str] = None) -> Dict:
        """
        生成详细的异常报告
        """
        result = self.check_for_exceptions()
        
        report = {
            "generated_at": datetime.now().isoformat(),
            "found_exceptions": result["found_exceptions"],
            "exception_count": result["exception_count"],
            "source_files": result["source_files"],
            "exceptions": [
                {
                    "timestamp": exc.timestamp,
                    "type": exc.exception_type,
                    "message": exc.message,
                    "source": exc.source_file
                }
                for exc in result["exceptions"]
            ],
            "raw_content": result["raw_content"]
        }
        
        if output_file:
            import json
            Path(output_file).write_text(
                json.dumps(report, indent=2, ensure_ascii=False)
            )
            logger.info(f"📄 报告已保存: {output_file}")
        
        return report


# 便捷函数
def check_hidden_exceptions() -> Dict:
    """快速检查是否有隐藏异常"""
    detector = HiddenExceptionDetector()
    return detector.check_for_exceptions()


def clear_exception_logs() -> None:
    """清空异常日志"""
    detector = HiddenExceptionDetector()
    detector.clear_logs()


if __name__ == "__main__":
    # 测试代码
    logging.basicConfig(level=logging.INFO)
    
    print("=" * 60)
    print("🔍 隐藏异常检测器测试")
    print("=" * 60)
    
    detector = HiddenExceptionDetector()
    
    # 检查当前状态
    result = detector.check_for_exceptions()
    
    print(f"\n发现异常: {result['found_exceptions']}")
    print(f"异常数量: {result['exception_count']}")
    
    if result["found_exceptions"]:
        print("\n异常详情:")
        for exc in result["exceptions"]:
            print(f"  [{exc.exception_type}] {exc.message}")
    else:
        print("\n✅ 没有发现隐藏异常")
    
    print("\n" + "=" * 60)
    print(detector.get_exception_summary())
    print("=" * 60)

