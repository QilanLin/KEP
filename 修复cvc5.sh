#!/bin/bash
# 修复cvc5安装脚本
# 需要sudo权限

echo "🔧 修复cvc5安装"
echo ""

CVC5_SOURCE="$(cd "$(dirname "$0")" && pwd)/cvc5-macOS-arm64-shared-gpl/bin/cvc5"
CVC5_TARGET="/opt/homebrew/bin/cvc5"

echo "源文件: $CVC5_SOURCE"
echo "目标: $CVC5_TARGET"
echo ""

# 检查源文件是否存在
if [ ! -f "$CVC5_SOURCE" ]; then
    echo "❌ 错误: 源文件不存在: $CVC5_SOURCE"
    exit 1
fi

echo "✅ 源文件存在"
echo ""

# 检查当前文件状态
if [ -f "$CVC5_TARGET" ]; then
    FILE_SIZE=$(stat -f%z "$CVC5_TARGET" 2>/dev/null || stat -c%s "$CVC5_TARGET" 2>/dev/null)
    echo "当前文件大小: $FILE_SIZE bytes"
    
    if [ "$FILE_SIZE" -lt 100 ]; then
        echo "⚠️  检测到损坏的文件，将删除..."
        sudo rm -f "$CVC5_TARGET"
        echo "✅ 已删除损坏的文件"
    else
        echo "⚠️  目标文件已存在且不为空，将备份..."
        sudo mv "$CVC5_TARGET" "$CVC5_TARGET.backup"
        echo "✅ 已备份到: $CVC5_TARGET.backup"
    fi
fi

echo ""
echo "创建符号链接..."
sudo ln -s "$CVC5_SOURCE" "$CVC5_TARGET"

if [ $? -eq 0 ]; then
    echo "✅ 符号链接创建成功！"
    echo ""
    echo "验证修复..."
    cvc5 --version 2>&1 | head -3
    echo ""
    echo "✅ cvc5修复完成！"
else
    echo "❌ 符号链接创建失败，可能需要手动修复"
    exit 1
fi

