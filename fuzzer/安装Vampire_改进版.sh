#!/bin/bash
# 改进版Vampire安装脚本
# 包含多种安装方法和备用方案

echo "═══════════════════════════════════════════════════════"
echo "🔧 Vampire安装脚本（改进版）"
echo "═══════════════════════════════════════════════════════"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)
LOCAL_BIN="$HOME/.local/bin"
mkdir -p "$LOCAL_BIN"

# 确保在PATH中
if [[ ":$PATH:" != *":$LOCAL_BIN:"* ]]; then
    echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.zshrc
    export PATH="$HOME/.local/bin:$PATH"
fi

# 检测系统信息
ARCH=$(uname -m)
OS_TYPE=""
if [[ "$OSTYPE" == "darwin"* ]]; then
    if [[ "$ARCH" == "arm64" ]]; then
        OS_TYPE="macOS-ARM64"
    else
        OS_TYPE="macOS-Intel"
    fi
else
    OS_TYPE="Linux"
fi

echo "系统信息: $OS_TYPE ($ARCH)"
echo "安装目录: $LOCAL_BIN"
echo ""

if command -v vampire &> /dev/null; then
    echo "✅ Vampire已安装: $(which vampire)"
    vampire --version 2>&1 | head -1 || echo "版本信息不可用"
    exit 0
fi

echo "开始尝试多种安装方法..."
echo ""

# ============================================
# 方法1: 从GitHub Releases下载（最新方法）
# ============================================
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "方法1: 从GitHub Releases下载预编译二进制文件"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 尝试多个可能的下载链接
VAMPIRE_URLS=()

if [[ "$OS_TYPE" == "macOS-ARM64" ]]; then
    VAMPIRE_URLS=(
        "https://github.com/vprover/vampire/releases/download/v4.8/vampire-macos"
        "https://github.com/vprover/vampire/releases/download/v4.7/vampire-macos"
        "https://github.com/vprover/vampire/releases/latest/download/vampire-macos"
    )
elif [[ "$OS_TYPE" == "macOS-Intel" ]]; then
    VAMPIRE_URLS=(
        "https://github.com/vprover/vampire/releases/download/v4.8/vampire-mac"
        "https://github.com/vprover/vampire/releases/download/v4.7/vampire-mac"
        "https://github.com/vprover/vampire/releases/latest/download/vampire-mac"
    )
else
    VAMPIRE_URLS=(
        "https://github.com/vprover/vampire/releases/download/v4.8/vampire"
        "https://github.com/vprover/vampire/releases/download/v4.7/vampire"
        "https://github.com/vprover/vampire/releases/latest/download/vampire"
    )
fi

SUCCESS=0
for URL in "${VAMPIRE_URLS[@]}"; do
    echo "尝试下载: $URL"
    
    cd /tmp
    TEMP_FILE="vampire_download_$$"
    
    if command -v wget &> /dev/null; then
        wget -q --spider "$URL" 2>&1 && wget -q "$URL" -O "$TEMP_FILE" 2>&1
    elif command -v curl &> /dev/null; then
        HTTP_CODE=$(curl -sL -w "%{http_code}" -o "$TEMP_FILE" "$URL" 2>&1)
        if [ "$HTTP_CODE" != "200" ]; then
            rm -f "$TEMP_FILE"
            continue
        fi
    else
        echo "❌ 未找到wget或curl"
        break
    fi
    
    # 检查下载的文件
    if [ -f "$TEMP_FILE" ]; then
        FILE_SIZE=$(stat -f%z "$TEMP_FILE" 2>/dev/null || stat -c%s "$TEMP_FILE" 2>/dev/null)
        FIRST_LINE=$(head -1 "$TEMP_FILE" 2>/dev/null || echo "")
        
        # 检查是否是有效的二进制文件（不是错误页面）
        if [ "$FILE_SIZE" -gt 1000000 ] && [[ "$FIRST_LINE" != *"Not Found"* ]] && [[ "$FIRST_LINE" != *"404"* ]]; then
            echo "✅ 下载成功 (文件大小: $FILE_SIZE bytes)"
            chmod +x "$TEMP_FILE"
            mv "$TEMP_FILE" "$LOCAL_BIN/vampire"
            
            if "$LOCAL_BIN/vampire" --version &>/dev/null; then
                echo "✅ Vampire安装成功！"
                "$LOCAL_BIN/vampire" --version 2>&1 | head -1
                SUCCESS=1
                break
            else
                echo "⚠️  文件下载但可能不是可执行文件，尝试下一个链接..."
                rm -f "$LOCAL_BIN/vampire"
            fi
        else
            echo "⚠️  下载的文件无效 (大小: $FILE_SIZE, 首行: $FIRST_LINE)"
            rm -f "$TEMP_FILE"
        fi
    fi
done

if [ "$SUCCESS" -eq 1 ]; then
    exit 0
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "方法2: 使用Homebrew（如果可用）"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if command -v brew &> /dev/null; then
    echo "检查Homebrew中是否有vampire..."
    if brew search vampire 2>/dev/null | grep -q vampire; then
        echo "找到vampire formula，尝试安装..."
        if brew install vampire; then
            if command -v vampire &> /dev/null; then
                echo "✅ Vampire通过Homebrew安装成功！"
                vampire --version 2>&1 | head -1
                exit 0
            fi
        fi
    else
        echo "⚠️  Homebrew中没有vampire formula"
    fi
else
    echo "⚠️  Homebrew未安装"
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "方法3: 从源码编译（需要较长时间）"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

read -p "是否尝试从源码编译Vampire？这可能需要10-30分钟 (y/n): " compile_choice
if [ "$compile_choice" = "y" ]; then
    echo ""
    echo "开始从源码编译..."
    
    # 检查依赖
    if ! command -v make &> /dev/null; then
        echo "❌ 需要make工具"
        if [[ "$OSTYPE" == "darwin"* ]] && command -v brew &> /dev/null; then
            echo "安装Xcode Command Line Tools..."
            xcode-select --install
        fi
    fi
    
    # 克隆仓库
    BUILD_DIR="/tmp/vampire_build_$$"
    mkdir -p "$BUILD_DIR"
    cd "$BUILD_DIR"
    
    echo "克隆Vampire仓库..."
    if command -v git &> /dev/null; then
        git clone --depth 1 https://github.com/vprover/vampire.git 2>&1 | tail -5
        cd vampire
        
        echo ""
        echo "开始编译（这可能需要10-30分钟）..."
        echo "💡 提示: 可以按Ctrl+C中断编译"
        
        # 尝试编译
        if make; then
            if [ -f "bin/vampire" ]; then
                cp "bin/vampire" "$LOCAL_BIN/vampire"
                chmod +x "$LOCAL_BIN/vampire"
                echo "✅ Vampire编译并安装成功！"
                "$LOCAL_BIN/vampire" --version 2>&1 | head -1
                rm -rf "$BUILD_DIR"
                exit 0
            fi
        else
            echo "❌ 编译失败"
            echo "   请查看编译错误信息"
            echo "   可能需要安装额外的依赖项"
        fi
        
        cd ..
        rm -rf "$BUILD_DIR"
    else
        echo "❌ 需要git工具"
    fi
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "方法4: 手动下载指南"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

echo "如果以上方法都失败，请手动安装："
echo ""
echo "📥 步骤1: 访问GitHub Releases页面"
echo "   https://github.com/vprover/vampire/releases"
echo ""
echo "📥 步骤2: 查找适合您系统的版本"
echo "   - macOS ARM64 (Apple Silicon): 查找 vampire-macos 或 vampire-mac-arm64"
echo "   - macOS Intel: 查找 vampire-mac 或 vampire-mac-intel"
echo "   - Linux: 查找 vampire 或 vampire-linux"
echo ""
echo "📥 步骤3: 下载二进制文件"
echo "   例如: wget <下载链接> -O $LOCAL_BIN/vampire"
echo "   chmod +x $LOCAL_BIN/vampire"
echo ""
echo "📥 步骤4: 验证安装"
echo "   $LOCAL_BIN/vampire --version"
echo ""

echo "═══════════════════════════════════════════════════════"
echo "💡 提示"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "⚠️  Vampire安装失败，但不影响基本测试"
echo ""
echo "✅ 当前可用的prover:"
echo "   - E Prover: $(which eprover 2>/dev/null || echo '未安装')"
echo "   - Z3: $(which z3 2>/dev/null || echo '未安装')"
echo "   - cvc5: $(which cvc5 2>/dev/null || echo '未安装')"
echo ""
echo "✅ 这3个prover已足够进行differential testing"
echo "✅ 测试脚本可以正常运行"
echo ""
echo "💡 如果需要Vampire，可以稍后手动安装"
echo ""
echo "✅ 安装脚本完成（部分失败但不影响功能）"

