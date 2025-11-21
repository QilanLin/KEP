#!/bin/bash
# 设置Isabelle Sledgehammer导出目录

EXPORT_DIR="$HOME/Downloads/KEP AWS/sledgehammer_export"
mkdir -p "$EXPORT_DIR"

echo "已创建导出目录: $EXPORT_DIR"
echo ""
echo "在Isabelle GUI中设置导出目录："
echo "1. Tools -> Options -> Isabelle -> General -> Output"
echo "2. 或在theory文件中添加："
echo "   declare [[sledgehammer_atp_problem_dest_dir = \"$EXPORT_DIR\"]]"
echo ""
echo "或在theory文件开头添加配置"
