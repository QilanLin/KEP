#!/bin/bash
# 安装ATP Provers (E Prover, Vampire, SPASS)
# 用于增强Differential Testing能力

echo "═══════════════════════════════════════════════════════"
echo "🔧 安装ATP Provers (E Prover, Vampire, SPASS)"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "📋 将安装："
echo "  1. E Prover - 自动定理证明器"
echo "  2. Vampire - 高性能ATP prover"
echo "  3. SPASS - 另一个ATP prover"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

# 检测操作系统
if [[ "$OSTYPE" == "darwin"* ]]; then
    OS="macOS"
    echo "✅ 检测到系统: macOS"
elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    OS="Linux"
    echo "✅ 检测到系统: Linux"
else
    echo "⚠️  未识别的系统: $OSTYPE"
    echo "将尝试通用安装方法"
    OS="Unknown"
fi

echo ""

# 检查Homebrew (macOS)
if [[ "$OS" == "macOS" ]]; then
    if ! command -v brew &> /dev/null; then
        echo "⚠️  Homebrew未安装"
        echo "   建议先安装Homebrew: /bin/bash -c \"\$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)\""
        echo ""
        read -p "是否继续尝试其他安装方法？(y/n): " continue_choice
        if [ "$continue_choice" != "y" ]; then
            exit 1
        fi
    else
        echo "✅ Homebrew已安装"
        BREW_PREFIX=$(brew --prefix)
        echo "   Homebrew前缀: $BREW_PREFIX"
    fi
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "开始安装ATP Provers..."
echo "═══════════════════════════════════════════════════════"
echo ""

INSTALLED=0
FAILED=0

# ============================================
# 1. 安装 E Prover
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "1️⃣  安装 E Prover..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v eprover &> /dev/null; then
    E_VERSION=$(eprover --version 2>&1 | head -1)
    echo "✅ E Prover已安装: $E_VERSION"
    INSTALLED=$((INSTALLED + 1))
else
    echo "📥 开始安装E Prover..."
    
    if [[ "$OS" == "macOS" ]] && command -v brew &> /dev/null; then
        # macOS使用Homebrew
        echo "   使用Homebrew安装..."
        if brew install eprover; then
            if command -v eprover &> /dev/null; then
                E_VERSION=$(eprover --version 2>&1 | head -1)
                echo "✅ E Prover安装成功: $E_VERSION"
                INSTALLED=$((INSTALLED + 1))
            else
                echo "⚠️  E Prover安装后未在PATH中找到"
                echo "   尝试添加到PATH..."
                # E Prover通常安装在 /usr/local/bin 或 /opt/homebrew/bin
                if [ -f "/opt/homebrew/bin/eprover" ]; then
                    echo 'export PATH="/opt/homebrew/bin:$PATH"' >> ~/.zshrc
                    echo "✅ 已添加到PATH（需要重新加载shell）"
                fi
            fi
        else
            echo "❌ E Prover安装失败"
            FAILED=$((FAILED + 1))
            echo "   备选方案：从源码编译（需要较长时间）"
        fi
    elif [[ "$OS" == "Linux" ]]; then
        # Linux使用包管理器
        echo "   使用包管理器安装..."
        if command -v apt-get &> /dev/null; then
            if sudo apt-get update && sudo apt-get install -y eprover; then
                echo "✅ E Prover安装成功"
                INSTALLED=$((INSTALLED + 1))
            else
                echo "❌ E Prover安装失败"
                FAILED=$((FAILED + 1))
            fi
        elif command -v yum &> /dev/null; then
            if sudo yum install -y eprover; then
                echo "✅ E Prover安装成功"
                INSTALLED=$((INSTALLED + 1))
            else
                echo "❌ E Prover安装失败"
                FAILED=$((FAILED + 1))
            fi
        else
            echo "⚠️  未找到包管理器（apt-get或yum）"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "⚠️  未识别的系统，无法自动安装"
        echo "   请手动安装：https://www.eprover.org/"
        FAILED=$((FAILED + 1))
    fi
fi

echo ""

# ============================================
# 2. 安装 Vampire
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "2️⃣  安装 Vampire..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v vampire &> /dev/null || command -v vampire_z3 &> /dev/null; then
    if command -v vampire &> /dev/null; then
        V_VERSION=$(vampire --version 2>&1 | head -1)
        echo "✅ Vampire已安装: $V_VERSION"
    else
        V_VERSION=$(vampire_z3 --version 2>&1 | head -1)
        echo "✅ Vampire已安装: $V_VERSION (vampire_z3)"
    fi
    INSTALLED=$((INSTALLED + 1))
else
    echo "📥 开始安装Vampire..."
    echo "   ⚠️  注意: Vampire可能不在标准包管理器中"
    echo "   推荐方法: 从官网下载二进制文件"
    echo ""
    
    # 检查是否有本地二进制文件
    VAMPIRE_DIR="$WORK_DIR/../vampire"
    if [ -d "$VAMPIRE_DIR" ] && [ -f "$VAMPIRE_DIR/bin/vampire" ]; then
        echo "✅ 找到本地Vampire二进制文件"
        VAMPIRE_BIN="$VAMPIRE_DIR/bin/vampire"
        chmod +x "$VAMPIRE_BIN"
        
        # 创建符号链接到PATH
        LOCAL_BIN="$HOME/.local/bin"
        mkdir -p "$LOCAL_BIN"
        ln -sf "$VAMPIRE_BIN" "$LOCAL_BIN/vampire"
        
        # 添加到PATH
        if [[ ":$PATH:" != *":$LOCAL_BIN:"* ]]; then
            echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
            export PATH="$HOME/.local/bin:$PATH"
            echo "✅ 已添加到PATH"
        fi
        
        if command -v vampire &> /dev/null; then
            echo "✅ Vampire安装成功"
            INSTALLED=$((INSTALLED + 1))
        else
            echo "⚠️  Vampire添加到PATH后仍无法找到（可能需要重新加载shell）"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "❌ 未找到Vampire二进制文件"
        echo "   请从官网下载: https://vprover.github.io/download.html"
        echo "   或使用: wget https://github.com/vprover/vampire/releases/download/v4.8/vampire-mac.zip"
        FAILED=$((FAILED + 1))
    fi
fi

echo ""

# ============================================
# 3. 安装 SPASS
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "3️⃣  安装 SPASS..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v spass &> /dev/null; then
    SPASS_VERSION=$(spass --version 2>&1 | head -1 || echo "已安装")
    echo "✅ SPASS已安装: $SPASS_VERSION"
    INSTALLED=$((INSTALLED + 1))
else
    echo "📥 开始安装SPASS..."
    echo "   ⚠️  注意: SPASS可能不在标准包管理器中"
    echo "   推荐方法: 从官网下载"
    echo ""
    
    # 检查是否有本地二进制文件
    SPASS_DIR="$WORK_DIR/../spass"
    if [ -d "$SPASS_DIR" ] && [ -f "$SPASS_DIR/bin/SPASS" ] || [ -f "$SPASS_DIR/SPASS" ]; then
        echo "✅ 找到本地SPASS二进制文件"
        if [ -f "$SPASS_DIR/bin/SPASS" ]; then
            SPASS_BIN="$SPASS_DIR/bin/SPASS"
        else
            SPASS_BIN="$SPASS_DIR/SPASS"
        fi
        chmod +x "$SPASS_BIN"
        
        # 创建符号链接到PATH（使用小写）
        LOCAL_BIN="$HOME/.local/bin"
        mkdir -p "$LOCAL_BIN"
        ln -sf "$SPASS_BIN" "$LOCAL_BIN/spass"
        
        # 添加到PATH
        if [[ ":$PATH:" != *":$LOCAL_BIN:"* ]]; then
            echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
            export PATH="$HOME/.local/bin:$PATH"
            echo "✅ 已添加到PATH"
        fi
        
        if command -v spass &> /dev/null; then
            echo "✅ SPASS安装成功"
            INSTALLED=$((INSTALLED + 1))
        else
            echo "⚠️  SPASS添加到PATH后仍无法找到（可能需要重新加载shell）"
            FAILED=$((FAILED + 1))
        fi
    else
        echo "❌ 未找到SPASS二进制文件"
        echo "   请从官网下载: https://www.spass-prover.org/download.html"
        echo "   或使用源码编译"
        FAILED=$((FAILED + 1))
    fi
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "安装结果总结"
echo "═══════════════════════════════════════════════════════"
echo ""

# 验证安装
echo "🔍 验证安装状态："
echo ""

PROVERS_STATUS=0

if command -v eprover &> /dev/null; then
    echo "✅ E Prover: 已安装 ($(which eprover))"
    eprover --version 2>&1 | head -1
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ E Prover: 未安装"
fi

echo ""

if command -v vampire &> /dev/null; then
    echo "✅ Vampire: 已安装 ($(which vampire))"
    vampire --version 2>&1 | head -1 || echo "版本信息不可用"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
elif command -v vampire_z3 &> /dev/null; then
    echo "✅ Vampire: 已安装 (vampire_z3) ($(which vampire_z3))"
    vampire_z3 --version 2>&1 | head -1 || echo "版本信息不可用"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ Vampire: 未安装"
fi

echo ""

if command -v spass &> /dev/null; then
    echo "✅ SPASS: 已安装 ($(which spass))"
    spass --version 2>&1 | head -1 || echo "版本信息不可用"
    PROVERS_STATUS=$((PROVERS_STATUS + 1))
else
    echo "❌ SPASS: 未安装"
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 安装统计："
echo "  成功安装: $INSTALLED/3"
echo "  安装失败: $FAILED/3"
echo "  当前可用: $PROVERS_STATUS/3"
echo ""

if [ "$PROVERS_STATUS" -eq 0 ]; then
    echo "⚠️  警告: 没有ATP prover可用"
    echo "   建议: 手动安装至少一个ATP prover以增强differential testing能力"
elif [ "$PROVERS_STATUS" -lt 3 ]; then
    echo "⚠️  部分ATP prover未安装"
    echo "   💡 提示: 即使部分prover未安装，测试仍可继续"
    echo "   Z3和cvc5已足够进行基本的differential testing"
else
    echo "✅ 所有ATP prover已安装！"
    echo "   differential testing能力已增强"
fi

echo ""
echo "💡 提示："
echo "  - 如果某些prover刚安装，可能需要重新加载shell: source ~/.zshrc"
echo "  - 或者重新打开终端"
echo "  - 测试脚本会自动检测可用的prover"
echo ""
echo "✅ ATP Prover安装脚本完成"

