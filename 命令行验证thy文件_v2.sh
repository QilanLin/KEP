#!/bin/bash
# 使用Isabelle命令行工具验证.thy文件（改进版）

echo "🔧 使用命令行验证.thy文件（改进版）"
echo ""

WORK_DIR="$(cd "$(dirname "$0")" && pwd)"
EXPORT_DIR="$WORK_DIR/sledgehammer_export"
mkdir -p "$EXPORT_DIR"

echo "工作目录: $WORK_DIR"
echo "导出目录: $EXPORT_DIR"
echo ""

# 记录开始时的文件数量
INITIAL_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "开始时的TPTP文件数量: $INITIAL_COUNT"
echo ""

# 函数：验证单个theory文件
verify_thy() {
    local THY_FILE="$1"
    local THY_NAME=$(basename "$THY_FILE" .thy)
    
    echo "=========================================="
    echo "验证: $THY_NAME.thy"
    echo "=========================================="
    echo ""
    
    echo "方法1: 使用-T选项加载theory文件..."
    isabelle process -d "$WORK_DIR" -T "$THY_NAME" 2>&1 | tail -30
    
    echo ""
    echo "检查是否有新文件生成..."
    sleep 2
    NEW_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
    ADDED=$((NEW_COUNT - INITIAL_COUNT))
    echo "当前TPTP文件数量: $NEW_COUNT (新增: $ADDED)"
    
    if [ "$ADDED" -gt 0 ]; then
        echo "✅ 生成了 $ADDED 个新文件！"
        echo ""
        echo "最新生成的文件（前3个）："
        ls -lth "$EXPORT_DIR"/*.p 2>/dev/null | head -3
    else
        echo "⚠️  未生成新文件（可能是theory文件已有配置）"
    fi
    
    INITIAL_COUNT=$NEW_COUNT
    echo ""
}

# 验证第一个文件：Test_Sledgehammer.thy
if [ -f "Test_Sledgehammer.thy" ]; then
    verify_thy "Test_Sledgehammer.thy"
else
    echo "❌ 文件不存在: Test_Sledgehammer.thy"
fi

echo ""
echo "等待3秒..."
sleep 3
echo ""

# 验证第二个文件：Test_SMT_Method.thy
if [ -f "Test_SMT_Method.thy" ]; then
    verify_thy "Test_SMT_Method.thy"
else
    echo "❌ 文件不存在: Test_SMT_Method.thy"
fi

echo ""
echo "=========================================="
echo "✅ 验证完成总结"
echo "=========================================="
echo ""
FINAL_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "总TPTP文件数量: $FINAL_COUNT"

echo ""
echo "最新生成的文件（前10个）："
ls -lth "$EXPORT_DIR"/*.p 2>/dev/null | head -10

echo ""
echo "检查是否有SMT-LIB文件："
SMT_COUNT=$(find "$EXPORT_DIR" -name "*.smt2" -o -name "*.smt" 2>/dev/null | wc -l | tr -d ' ')
if [ "$SMT_COUNT" -gt 0 ]; then
    echo "✅ 找到 $SMT_COUNT 个SMT-LIB文件："
    find "$EXPORT_DIR" -name "*.smt2" -o -name "*.smt" 2>/dev/null | head -5
else
    echo "❌ 未找到SMT-LIB文件"
fi

echo ""
echo "✅ 验证完成！"

