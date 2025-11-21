#!/bin/bash
# 下载AFP (Archive of Formal Proofs)
# 提供多种下载方法

echo "📥 下载AFP (Archive of Formal Proofs)"
echo ""

WORK_DIR="$(cd "$(dirname "$0")" && pwd)"
AFP_DIR="$WORK_DIR/afp-devel"

if [ -d "$AFP_DIR" ]; then
    echo "⚠️  AFP目录已存在: $AFP_DIR"
    echo "AFP已下载，跳过下载步骤"
    echo ""
    echo "统计信息："
    cd "$AFP_DIR"
    echo "文件数: $(find . -type f 2>/dev/null | wc -l | tr -d ' ')"
    echo ".thy文件数: $(find . -name "*.thy" 2>/dev/null | wc -l | tr -d ' ')"
    exit 0
fi

echo "⚠️  注意: AFP Git仓库可能不可用"
echo ""
echo "📋 推荐方法："
echo ""
echo "方法1: 使用Isabelle组件工具（最推荐）"
echo "  运行: isabelle components -a"
echo "  AFP会下载到Isabelle组件目录"
echo ""
echo "方法2: 从官方网站下载tar包"
echo "  访问: https://www.isa-afp.org/download.html"
echo "  下载: afp-current.tar.gz"
echo "  解压: tar -xzf afp-current.tar.gz"
echo ""
echo "方法3: 尝试Git克隆（可能失败）"
echo ""

read -p "是否尝试方法3（Git克隆）？(y/n): " try_clone

if [ "$try_clone" != "y" ]; then
    echo ""
    echo "💡 提示:"
    echo "  当前已有480个TPTP种子文件"
    echo "  足够开始MVP开发，AFP下载不是必需的"
    echo ""
    echo "请使用方法1或方法2下载AFP，或继续使用已有种子"
    exit 0
fi

echo ""
echo "尝试多种可能的仓库URL..."

# 尝试方法1: foss.heptapod.net (浅克隆)
echo ""
echo "尝试1: foss.heptapod.net (浅克隆)..."
git clone --depth 1 https://foss.heptapod.net/isa-afp/afp-devel.git "$AFP_DIR" 2>&1 | tail -3

if [ $? -eq 0 ] && [ -d "$AFP_DIR" ]; then
    echo "✅ 成功从foss.heptapod.net下载"
    cd "$AFP_DIR"
    echo ""
    echo "统计信息："
    echo "文件数: $(find . -type f 2>/dev/null | wc -l | tr -d ' ')"
    echo "总大小: $(du -sh . 2>/dev/null | cut -f1)"
    echo ".thy文件数: $(find . -name "*.thy" 2>/dev/null | wc -l | tr -d ' ')"
    exit 0
fi

# 尝试方法2: 完整克隆
echo ""
echo "尝试2: 完整克隆（可能需要更长时间）..."
rm -rf "$AFP_DIR" 2>/dev/null
git clone https://foss.heptapod.net/isa-afp/afp-devel.git "$AFP_DIR" 2>&1 | tail -3

if [ $? -eq 0 ] && [ -d "$AFP_DIR" ]; then
    echo "✅ 成功完整克隆"
    cd "$AFP_DIR"
    echo ""
    echo "统计信息："
    echo "文件数: $(find . -type f 2>/dev/null | wc -l | tr -d ' ')"
    echo "总大小: $(du -sh . 2>/dev/null | cut -f1)"
    echo ".thy文件数: $(find . -name "*.thy" 2>/dev/null | wc -l | tr -d ' ')"
    exit 0
fi

echo ""
echo "❌ Git克隆失败"
echo ""
echo "💡 建议："
echo "1. 使用方法1: isabelle components -a （推荐）"
echo "2. 使用方法2: 从官方网站下载tar包"
echo "3. 继续使用已有种子: 当前已有480个TPTP文件，足够MVP开发"
echo ""
echo "⚠️  AFP下载不是必需的，可以继续研究进度"
exit 1
