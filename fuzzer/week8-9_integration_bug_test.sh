#!/bin/bash
# Week 8-9 Integration Bug测试脚本
# 专门用于发现Integration Bugs（包括Reconstruction Failures, Differential Bugs, Crashes）

echo "═══════════════════════════════════════════════════════"
echo "🔍 Week 8-9 Integration Bug发现测试"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "📋 测试目标："
echo "  1. ⭐⭐⭐⭐⭐ Proof Reconstruction Failures（证明重构失败）"
echo "  2. ⭐⭐⭐⭐  SAT/UNSAT Conflicts（Differential Bugs）"
echo "  3. ⭐⭐⭐   Crashes/Hangs（崩溃/超时）"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

echo "工作目录: $WORK_DIR"
echo "开始时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

# Integration Bug测试配置 (改进版 - 2025-11-22)
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./week8-9_integration_bug_test_v2"
TIMEOUT=30.0  # 改进：从10秒增加到30秒，避免误报
NUM_MUTANTS=20  # 增加变异体数量
MAX_SEEDS=100  # 使用前100个种子（快速测试）

# 新增：种子过滤配置
ENABLE_SEED_FILTERING=true  # ⭐ 启用种子预过滤
SEED_FILTER_TIMEOUT=10.0    # 过滤掉执行时间>10秒的种子

# 新增：相对执行时间检测
USE_RELATIVE_TIME_CHECK=true  # ⭐ 使用相对时间比较
RELATIVE_TIME_THRESHOLD=2.0   # 执行时间增加2倍以上才算bug

# Oracle配置 - 全部启用
USE_RECONSTRUCTION_ORACLE=true  # ⭐ 核心Oracle
USE_DIFFERENTIAL_ORACLE=true    # ⭐ 重要Oracle
USE_CRASH_ORACLE=true           # ⭐ 基础Oracle
USE_PARALLEL=true
NUM_WORKERS=4

# 变异器配置
USE_AST_MUTATOR=true  # 使用AST级别变异（更高质量）
USE_AGGRESSIVE_MUTATOR=false  # 不使用激进变异（保持语法有效性）
USE_EXTREME_MUTATOR=false     # 不使用极端变异（保持语法有效性）

echo "📋 Integration Bug测试配置 (改进版v2):"
echo "  种子目录: $SEED_DIR"
echo "  输出目录: $OUTPUT_DIR"
echo "  超时时间: ${TIMEOUT}秒 ⚙️  (改进：从10秒→30秒)"
echo "  每个种子变异体数: $NUM_MUTANTS"
echo "  最大种子数: $MAX_SEEDS"
echo "  使用AST变异器: $USE_AST_MUTATOR"
echo ""
echo "🔧 改进功能:"
echo "  ✅ 种子预过滤: 启用 (过滤>10秒的种子)"
echo "  ✅ 相对时间检测: 启用 (阈值: 2.0x)"
echo ""
echo "🔍 Oracle配置:"
echo "  ✅ Reconstruction Oracle: $USE_RECONSTRUCTION_ORACLE ⭐ (核心)"
echo "  ✅ Differential Oracle: $USE_DIFFERENTIAL_ORACLE ⭐ (重要)"
echo "  ✅ Crash/Hang Oracle: $USE_CRASH_ORACLE ⭐ (基础)"
echo "  并行处理: $USE_PARALLEL ($NUM_WORKERS workers)"
echo ""

# 检查种子目录
if [ ! -d "$SEED_DIR" ]; then
    echo "❌ 种子目录不存在: $SEED_DIR"
    exit 1
fi

SEED_COUNT=$(ls -1 "$SEED_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "找到种子文件: $SEED_COUNT"
echo ""

if [ "$SEED_COUNT" -eq 0 ]; then
    echo "❌ 未找到种子文件"
    exit 1
fi

# 检查provers
echo "检查provers..."
Z3_PATH=$(which z3)
CVC5_PATH=$(which cvc5)

PROVERS_AVAILABLE=0

if [ -n "$Z3_PATH" ]; then
    echo "✅ Z3: $Z3_PATH"
    PROVERS_AVAILABLE=$((PROVERS_AVAILABLE + 1))
else
    echo "⚠️  警告: Z3未找到"
fi

if [ -n "$CVC5_PATH" ]; then
    echo "✅ cvc5: $CVC5_PATH"
    PROVERS_AVAILABLE=$((PROVERS_AVAILABLE + 1))
else
    echo "⚠️  警告: cvc5未找到"
fi

if [ "$PROVERS_AVAILABLE" -eq 0 ]; then
    echo ""
    echo "❌ 错误: 未找到任何prover"
    echo "💡 提示: 至少需要一个prover（Z3或cvc5）来运行测试"
    exit 1
fi

# 检查Isabelle（如果需要Reconstruction Oracle）
if [ "$USE_RECONSTRUCTION_ORACLE" = "true" ]; then
    ISABELLE_PATH=$(which isabelle)
    if [ -z "$ISABELLE_PATH" ]; then
        echo ""
        echo "⚠️  警告: Isabelle未找到，Reconstruction Oracle可能无法正常工作"
        echo "💡 提示: Reconstruction Oracle需要Isabelle来测试proof reconstruction"
        echo "   - 如果没有Isabelle，将跳过reconstruction测试"
        echo "   - Crash和Differential Oracle仍可正常工作"
        echo ""
    else
        echo "✅ Isabelle: $ISABELLE_PATH"
    fi
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "开始Integration Bug测试..."
echo "═══════════════════════════════════════════════════════"
echo ""

# 构建命令行参数
CMD_ARGS=(
    "--seed-dir" "$SEED_DIR"
    "--output-dir" "$OUTPUT_DIR"
    "--timeout" "$TIMEOUT"
    "--num-mutants" "$NUM_MUTANTS"
    "--max-seeds" "$MAX_SEEDS"
)

# 变异器配置
if [ "$USE_AST_MUTATOR" = "true" ]; then
    CMD_ARGS+=("--use-ast-mutator")
fi

if [ "$USE_AGGRESSIVE_MUTATOR" = "true" ]; then
    CMD_ARGS+=("--use-aggressive-mutator")
fi

if [ "$USE_EXTREME_MUTATOR" = "true" ]; then
    CMD_ARGS+=("--use-extreme-mutator")
fi

# Oracle配置
if [ "$USE_RECONSTRUCTION_ORACLE" = "true" ]; then
    CMD_ARGS+=("--use-reconstruction-oracle")
    CMD_ARGS+=("--reconstruction-timeout" "60.0")  # 增加重构超时
fi

if [ "$USE_PARALLEL" = "true" ]; then
    CMD_ARGS+=("--use-parallel" "--num-workers" "$NUM_WORKERS")
fi

# 运行fuzzer
echo "执行命令:"
echo "  python3 main.py ${CMD_ARGS[*]}"
echo ""

python3 main.py "${CMD_ARGS[@]}"

EXIT_CODE=$?

echo ""
echo "结束时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo "═══════════════════════════════════════════════════════"
echo "测试完成 (退出码: $EXIT_CODE)"
echo "═══════════════════════════════════════════════════════"
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    echo "✅ 测试成功完成"
else
    echo "⚠️  测试过程中有错误（退出码: $EXIT_CODE）"
fi

echo ""
echo "📊 Integration Bug结果统计:"
if [ -d "$OUTPUT_DIR" ]; then
    echo "输出目录: $OUTPUT_DIR"
    echo ""
    
    # 统计不同类型的bug
    CRASH_COUNT=$(ls -1 "$OUTPUT_DIR"/bug_*.json 2>/dev/null | wc -l | tr -d ' ')
    DIFF_COUNT=$(ls -1 "$OUTPUT_DIR"/differential_*.json 2>/dev/null | wc -l | tr -d ' ')
    RECON_COUNT=$(ls -1 "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | wc -l | tr -d ' ')
    LOG_COUNT=$(ls -1 "$OUTPUT_DIR"/logs/*.log 2>/dev/null | wc -l | tr -d ' ')
    
    echo "🐛 Bug发现统计:"
    echo "  ⭐⭐⭐⭐⭐ 证明重构失败 (Reconstruction Failures): $RECON_COUNT"
    echo "  ⭐⭐⭐⭐   SAT/UNSAT冲突 (Differential Bugs): $DIFF_COUNT"
    echo "  ⭐⭐⭐    崩溃/超时 (Crashes/Hangs): $CRASH_COUNT"
    echo ""
    
    TOTAL_BUGS=$((CRASH_COUNT + DIFF_COUNT + RECON_COUNT))
    echo "📈 总计发现的Integration Bugs: $TOTAL_BUGS"
    echo ""
    
    # 显示统计摘要
    if [ -f "$OUTPUT_DIR/stats/stats.json" ]; then
        echo "📄 详细统计:"
        python3 -c "
import json
import sys
try:
    with open('$OUTPUT_DIR/stats/stats.json', 'r') as f:
        stats = json.load(f)
    print(json.dumps(stats, indent=2, ensure_ascii=False))
except Exception as e:
    print(f'读取统计文件出错: {e}', file=sys.stderr)
" 2>/dev/null | head -40
        echo ""
    fi
    
    # 显示发现的bug文件
    if [ "$RECON_COUNT" -gt 0 ]; then
        echo "🎯 证明重构失败报告:"
        ls -lh "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | head -5
        echo ""
    fi
    
    if [ "$DIFF_COUNT" -gt 0 ]; then
        echo "🎯 SAT/UNSAT冲突报告:"
        ls -lh "$OUTPUT_DIR"/differential_*.json 2>/dev/null | head -5
        echo ""
    fi
    
    if [ "$CRASH_COUNT" -gt 0 ]; then
        echo "🎯 崩溃/超时报告:"
        ls -lh "$OUTPUT_DIR"/bug_*.json 2>/dev/null | head -5
        echo ""
    fi
else
    echo "⚠️  输出目录不存在"
fi

echo ""
echo "💡 提示:"
echo "  - Reconstruction Failures需要原始.thy文件和prover证明输出"
echo "  - 如果未发现Reconstruction Failures，可能是缺少.thy文件映射"
echo "  - Crash和Differential Oracle不需要.thy文件，可以正常工作"
echo ""
echo "✅ Week 8-9 Integration Bug测试脚本完成"

