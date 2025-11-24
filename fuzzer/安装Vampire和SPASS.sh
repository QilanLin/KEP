#!/bin/bash
# 手动安装Vampire和SPASS（从GitHub/官网下载二进制文件）

echo "═══════════════════════════════════════════════════════"
echo "🔧 手动安装 Vampire 和 SPASS"
echo "═══════════════════════════════════════════════════════"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)
LOCAL_BIN="$HOME/.local/bin"

# 创建本地bin目录
mkdir -p "$LOCAL_BIN"

echo "工作目录: $WORK_DIR"
echo "本地bin目录: $LOCAL_BIN"
echo ""

# 确保在PATH中
if [[ ":$PATH:" != *":$LOCAL_BIN:"* ]]; then
    echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
    export PATH="$HOME/.local/bin:$PATH"
    echo "✅ 已将 $LOCAL_BIN 添加到PATH"
    echo ""
fi

# ============================================
# 1. 安装 Vampire
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "1️⃣  安装 Vampire..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v vampire &> /dev/null; then
    echo "✅ Vampire已安装: $(which vampire)"
    vampire --version 2>&1 | head -1 || echo "版本信息不可用"
else
    echo "📥 开始下载Vampire..."
    
    # 检测系统架构
    ARCH=$(uname -m)
    echo "系统架构: $ARCH"
    
    # 确定下载URL
    if [[ "$OSTYPE" == "darwin"* ]]; then
        if [[ "$ARCH" == "arm64" ]]; then
            # Apple Silicon (M1/M2/M3)
            VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire-macos"
            VAMPIRE_NAME="vampire"
            echo "检测到: macOS (Apple Silicon)"
        else
            # Intel Mac
            VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire-mac"
            VAMPIRE_NAME="vampire"
            echo "检测到: macOS (Intel)"
        fi
    else
        # Linux
        VAMPIRE_URL="https://github.com/vprover/vampire/releases/download/v4.8/vampire"
        VAMPIRE_NAME="vampire"
        echo "检测到: Linux"
    fi
    
    echo "下载URL: $VAMPIRE_URL"
    echo ""
    
    # 下载Vampire
    cd /tmp
    if command -v wget &> /dev/null; then
        wget -q "$VAMPIRE_URL" -O "$VAMPIRE_NAME" 2>&1
    elif command -v curl &> /dev/null; then
        curl -L "$VAMPIRE_URL" -o "$VAMPIRE_NAME" 2>&1
    else
        echo "❌ 错误: 未找到wget或curl"
        exit 1
    fi
    
    if [ -f "$VAMPIRE_NAME" ] && [ -s "$VAMPIRE_NAME" ]; then
        chmod +x "$VAMPIRE_NAME"
        
        # 移动到本地bin目录
        mv "$VAMPIRE_NAME" "$LOCAL_BIN/vampire"
        
        if command -v vampire &> /dev/null; then
            echo "✅ Vampire安装成功: $(which vampire)"
            vampire --version 2>&1 | head -1 || echo "版本信息不可用"
        else
            echo "⚠️  Vampire已复制但未在PATH中找到"
            echo "   文件位置: $LOCAL_BIN/vampire"
            echo "   请运行: source ~/.zshrc"
        fi
    else
        echo "❌ Vampire下载失败"
        echo "   请手动下载: $VAMPIRE_URL"
        echo "   并复制到: $LOCAL_BIN/vampire"
    fi
fi

echo ""

# ============================================
# 2. 安装 SPASS
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "2️⃣  安装 SPASS..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v spass &> /dev/null; then
    echo "✅ SPASS已安装: $(which spass)"
    spass --version 2>&1 | head -1 || echo "版本信息不可用"
else
    echo "📥 开始下载SPASS..."
    echo "   ⚠️  注意: SPASS可能没有预编译的macOS版本"
    echo "   推荐方法: 从官网下载或使用源码编译"
    echo ""
    
    # SPASS官网下载（如果有macOS版本）
    echo "⚠️  SPASS需要手动安装"
    echo ""
    echo "方法1: 从官网下载（推荐）"
    echo "   1. 访问: https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/spass-workbench/"
    echo "   2. 下载适合macOS的版本（如果有）"
    echo "   3. 解压后将SPASS二进制文件复制到: $LOCAL_BIN/spass"
    echo ""
    echo "方法2: 使用Docker（如果已安装Docker）"
    echo "   docker pull spass/spass"
    echo ""
    echo "方法3: 从源码编译（复杂）"
    echo "   git clone https://github.com/Spass-prover/spass.git"
    echo "   cd spass && make"
    echo ""
    
    # 检查是否有本地的SPASS二进制文件
    SPASS_DIR="$WORK_DIR/../spass"
    if [ -d "$SPASS_DIR" ]; then
        SPASS_BIN=$(find "$SPASS_DIR" -name "SPASS" -o -name "spass" 2>/dev/null | head -1)
        if [ -n "$SPASS_BIN" ] && [ -f "$SPASS_BIN" ]; then
            echo "✅ 找到本地SPASS二进制文件: $SPASS_BIN"
            chmod +x "$SPASS_BIN"
            ln -sf "$SPASS_BIN" "$LOCAL_BIN/spass"
            
            if command -v spass &> /dev/null; then
                echo "✅ SPASS安装成功: $(which spass)"
            else
                echo "⚠️  SPASS已链接但未在PATH中找到"
                echo "   文件位置: $LOCAL_BIN/spass"
            fi
        else
            echo "❌ 未找到SPASS二进制文件"
        fi
    else
        echo "❌ 未找到SPASS目录，需要手动安装"
    fi
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "安装结果验证"
echo "═══════════════════════════════════════════════════════"
echo ""

PROVERS_STATUS=0

if command -v eprover &> /dev/null; then
    echo "✅ E Prover: $(which eprover)"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ E Prover: 未安装"
fi

if command -v vampire &> /dev/null; then
    echo "✅ Vampire: $(which vampire)"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ Vampire: 未安装"
fi

if command -v spass &> /dev/null; then
    echo "✅ SPASS: $(which spass)"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ SPASS: 未安装"
fi

echo ""
echo "📊 可用ATP Prover: $PROVERS_STATUS/3"
echo ""

if [ "$PROVERS_STATUS" -ge 1 ]; then
    echo "✅ 至少有1个ATP prover可用，differential testing可以工作"
else
    echo "⚠️  没有ATP prover可用，但Z3和cvc5已足够"
fi

echo ""
echo "💡 提示:"
echo "  - 如果刚安装的prover未找到，运行: source ~/.zshrc"
echo "  - 或重新打开终端"
echo "  - 测试脚本会自动检测可用的prover"
echo ""
echo "✅ 安装脚本完成"

