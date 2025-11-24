#!/bin/bash
# 安装新Prover脚本 (E Prover, Vampire, SPASS)

echo "═══════════════════════════════════════════════════════"
echo "📦 安装新的Prover (E Prover, Vampire, SPASS)"
echo "═══════════════════════════════════════════════════════"
echo ""

# 检查系统
if [[ "$OSTYPE" == "darwin"* ]]; then
    echo "检测到系统: macOS"
    HAS_BREW=$(command -v brew)
else
    echo "检测到系统: Linux"
    HAS_BREW=""
fi

echo ""

# 1. 安装 E Prover
echo "═══════════════════════════════════════════════════════"
echo "1️⃣  安装 E Prover"
echo "═══════════════════════════════════════════════════════"
echo ""

if command -v eprover &> /dev/null; then
    echo "✅ E Prover 已安装"
    eprover --version
else
    echo "❌ E Prover 未找到，开始安装..."
    
    # 尝试使用Homebrew (macOS)
    if [ -n "$HAS_BREW" ]; then
        echo "尝试使用 Homebrew 安装..."
        if brew search eprover 2>/dev/null | grep -q eprover; then
            brew install eprover
        else
            echo "⚠️  Homebrew 中没有 eprover，尝试手动安装..."
            # 从源码编译
            cd /tmp
            if [ ! -d "eprover" ]; then
                echo "下载 E Prover 源码..."
                wget -q http://www.eprover.org/eprover-release.tgz -O eprover-release.tgz || curl -L http://www.eprover.org/eprover-release.tgz -o eprover-release.tgz
                tar -xzf eprover-release.tgz 2>/dev/null || echo "下载失败，请手动下载: http://www.eprover.org/"
            fi
        fi
    else
        echo "⚠️  未检测到 Homebrew，请手动安装 E Prover"
        echo "   下载地址: http://www.eprover.org/"
        echo "   或使用包管理器: apt-get install eprover (Debian/Ubuntu)"
    fi
    
    # 验证安装
    if command -v eprover &> /dev/null; then
        echo "✅ E Prover 安装成功"
        eprover --version
    else
        echo "⚠️  E Prover 安装失败，请手动安装"
    fi
fi

echo ""

# 2. 安装 Vampire
echo "═══════════════════════════════════════════════════════"
echo "2️⃣  安装 Vampire"
echo "═══════════════════════════════════════════════════════"
echo ""

if command -v vampire &> /dev/null; then
    echo "✅ Vampire 已安装"
    vampire --version 2>&1 | head -1
else
    echo "❌ Vampire 未找到，开始安装..."
    
    cd /tmp
    echo "下载 Vampire 预编译版本..."
    
    # 检测系统架构
    ARCH=$(uname -m)
    if [[ "$OSTYPE" == "darwin"* ]]; then
        if [[ "$ARCH" == "arm64" ]]; then
            VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire-macos"
        else
            VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire-mac"
        fi
    else
        VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire"
    fi
    
    wget -q "$VAMPIRE_URL" -O vampire 2>/dev/null || curl -L "$VAMPIRE_URL" -o vampire 2>/dev/null
    
    if [ -f "vampire" ]; then
        chmod +x vampire
        sudo mv vampire /usr/local/bin/vampire || mv vampire ~/.local/bin/vampire 2>/dev/null || echo "请手动将vampire复制到PATH中"
        echo "✅ Vampire 安装成功"
        vampire --version 2>&1 | head -1
    else
        echo "⚠️  Vampire 下载失败，请手动安装"
        echo "   下载地址: https://github.com/vprover/vampire/releases"
    fi
fi

echo ""

# 3. 安装 SPASS
echo "═══════════════════════════════════════════════════════"
echo "3️⃣  安装 SPASS"
echo "═══════════════════════════════════════════════════════"
echo ""

if command -v spass &> /dev/null; then
    echo "✅ SPASS 已安装"
    spass --version 2>&1 | head -1 || spass 2>&1 | head -1
else
    echo "❌ SPASS 未找到，开始安装..."
    
    # 尝试使用包管理器
    if [ -n "$HAS_BREW" ]; then
        echo "尝试使用 Homebrew 安装..."
        if brew search spass 2>/dev/null | grep -q spass; then
            brew install spass
        else
            echo "⚠️  Homebrew 中没有 spass"
        fi
    fi
    
    # 从源码编译（如果需要）
    if ! command -v spass &> /dev/null; then
        echo "⚠️  SPASS 需要手动安装"
        echo "   下载地址: https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench/"
        echo "   或使用包管理器: apt-get install spass (Debian/Ubuntu)"
    fi
    
    # 验证安装
    if command -v spass &> /dev/null; then
        echo "✅ SPASS 安装成功"
        spass --version 2>&1 | head -1 || spass 2>&1 | head -1
    else
        echo "⚠️  SPASS 安装失败，请手动安装"
    fi
fi

echo ""

# 总结
echo "═══════════════════════════════════════════════════════"
echo "📊 安装总结"
echo "═══════════════════════════════════════════════════════"
echo ""

PROVERS_STATUS=0

if command -v eprover &> /dev/null; then
    echo "✅ E Prover: 已安装"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ E Prover: 未安装"
fi

if command -v vampire &> /dev/null; then
    echo "✅ Vampire: 已安装"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ Vampire: 未安装"
fi

if command -v spass &> /dev/null; then
    echo "✅ SPASS: 已安装"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ SPASS: 未安装"
fi

echo ""
echo "已安装: $PROVERS_STATUS/3 个prover"
echo ""

if [ $PROVERS_STATUS -eq 3 ]; then
    echo "🎉 所有prover已成功安装！"
    echo ""
    echo "现在可以运行fuzzer测试新的prover："
    echo "  cd fuzzer"
    echo "  python3 main.py --max-seeds 5 --num-mutants 3"
else
    echo "⚠️  部分prover未安装，请手动安装后再运行fuzzer"
    echo ""
    echo "详细安装指南请参考："
    echo "  - fuzzer/SUPPORTED_PROVERS.md"
    echo "  - fuzzer/添加新Prover指南.md"
fi

echo ""
echo "✅ 安装脚本完成"

