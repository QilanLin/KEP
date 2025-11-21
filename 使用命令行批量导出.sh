#!/bin/bash
# 使用Isabelle命令行工具批量导出TPTP文件

echo "🔧 使用Isabelle命令行工具批量导出TPTP文件"
echo ""

EXPORT_DIR="sledgehammer_export"
mkdir -p "$EXPORT_DIR"
EXPORT_DIR_ABS="$(cd "$EXPORT_DIR" && pwd)"

echo "📁 导出目录: $EXPORT_DIR_ABS"
echo ""

# 使用isabelle process处理theory文件
echo "1. 使用isabelle process处理Test_Sledgehammer.thy..."
isabelle process -d . -e "
Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir \"$EXPORT_DIR_ABS\";
Config.put Sledgehammer_Prover_ATP.atp_proof_dest_dir \"$EXPORT_DIR_ABS\";
use_thy \"Test_Sledgehammer\";
" 2>&1 | tail -20

echo ""
echo "2. 检查导出的文件..."
TPTP_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "   TPTP文件数量: $TPTP_COUNT"

echo ""
echo "3. 最新导出的文件（前5个）："
ls -lth "$EXPORT_DIR"/*.p 2>/dev/null | head -5

echo ""
echo "✅ 完成！"
