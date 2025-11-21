#!/bin/bash
# 从AFP批量提取种子文件

echo "🔧 批量提取AFP种子文件"
echo ""

WORK_DIR="$(cd "$(dirname "$0")" && pwd)"
AFP_DIR="$WORK_DIR/afp-devel"
EXPORT_DIR="$WORK_DIR/sledgehammer_export"
OUTPUT_DIR="$WORK_DIR/afp_seeds"

mkdir -p "$EXPORT_DIR"
mkdir -p "$OUTPUT_DIR"

if [ ! -d "$AFP_DIR" ]; then
    echo "⚠️  AFP目录不存在: $AFP_DIR"
    echo ""
    echo "请先下载AFP，方法："
    echo "1. 运行: isabelle components -a （推荐）"
    echo "2. 或从官方网站下载: https://www.isa-afp.org/download.html"
    echo "3. 或运行: ./下载AFP.sh （尝试Git克隆）"
    echo ""
    echo "💡 提示: 当前已有480个TPTP种子文件，AFP下载不是必需的"
    echo ""
    read -p "是否继续（将跳过AFP处理）？(y/n): " continue_choice
    if [ "$continue_choice" != "y" ]; then
        exit 1
    fi
    echo "跳过AFP处理，使用已有种子..."
    exit 0
fi

echo "工作目录: $WORK_DIR"
echo "AFP目录: $AFP_DIR"
echo "导出目录: $EXPORT_DIR"
echo "输出目录: $OUTPUT_DIR"
echo ""

# 记录开始时的文件数量
INITIAL_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "开始时的TPTP文件数量: $INITIAL_COUNT"
echo ""

# 查找所有.thy文件（限制数量以避免处理时间过长）
echo "查找AFP中的.thy文件..."
THY_FILES=$(find "$AFP_DIR" -name "*.thy" -type f | head -10)
THY_COUNT=$(echo "$THY_FILES" | wc -l | tr -d ' ')

echo "找到 $THY_COUNT 个.thy文件（限制为前10个）"
echo ""

# 创建临时ROOT文件
TEMP_ROOT="$OUTPUT_DIR/ROOT"
cat > "$TEMP_ROOT" << 'ROOTEOF'
session AFP_Seeds = HOL +
  theories
ROOTEOF

# 添加到ROOT文件
echo "$THY_FILES" | while read -r thy_file; do
    if [ -n "$thy_file" ]; then
        # 获取相对于AFP目录的路径
        rel_path=$(echo "$thy_file" | sed "s|$AFP_DIR/||")
        thy_name=$(basename "$thy_file" .thy)
        echo "    $thy_name" >> "$TEMP_ROOT"
    fi
done

echo "生成的ROOT文件内容："
cat "$TEMP_ROOT"
echo ""

echo "⚠️  注意：完整批量处理可能需要很长时间"
echo "当前脚本只处理前10个文件作为示例"
echo ""
echo "要处理更多文件，请："
echo "1. 修改脚本中的 'head -10' 为更大数量"
echo "2. 或指定特定的theory文件列表"
echo ""

read -p "是否继续？(y/n): " confirm
if [ "$confirm" != "y" ]; then
    echo "已取消"
    exit 0
fi

echo ""
echo "使用isabelle build处理..."
cd "$WORK_DIR"
isabelle build -d "$AFP_DIR" -d "$OUTPUT_DIR" AFP_Seeds 2>&1 | tail -30

echo ""
echo "检查结果..."
FINAL_COUNT=$(ls -1 "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
ADDED=$((FINAL_COUNT - INITIAL_COUNT))
echo "最终TPTP文件数量: $FINAL_COUNT (新增: $ADDED)"

echo ""
echo "✅ 提取完成！"

