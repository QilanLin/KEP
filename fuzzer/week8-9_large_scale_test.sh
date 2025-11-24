#!/bin/bash
# Week 8-9 大规模测试脚本

echo "═══════════════════════════════════════════════════════"
echo "🚀 Week 8-9 大规模Bug发现活动"
echo "═══════════════════════════════════════════════════════"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

echo "工作目录: $WORK_DIR"
echo "开始时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

# Week 8-9 测试配置
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./week8-9_large_scale_test"
TIMEOUT=5.0
NUM_MUTANTS=10
MAX_SEEDS=480  # 使用所有种子文件

# Oracle配置
USE_RECONSTRUCTION_ORACLE=true
USE_PARALLEL=true
NUM_WORKERS=4

echo "📋 Week 8-9 测试配置:"
echo "  种子目录: $SEED_DIR"
echo "  输出目录: $OUTPUT_DIR"
echo "  超时时间: ${TIMEOUT}秒"
echo "  每个种子变异体数: $NUM_MUTANTS"
echo "  最大种子数: $MAX_SEEDS"
echo "  使用AST变异器: true (with fallback)"
echo "  使用Reconstruction Oracle: $USE_RECONSTRUCTION_ORACLE"
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

if [ -z "$Z3_PATH" ]; then
    echo "⚠️  警告: Z3未找到"
else
    echo "✅ Z3: $Z3_PATH"
fi

if [ -z "$CVC5_PATH" ]; then
    echo "⚠️  警告: cvc5未找到"
else
    echo "✅ cvc5: $CVC5_PATH"
fi

if [ -z "$Z3_PATH" ] && [ -z "$CVC5_PATH" ]; then
    echo ""
    echo "❌ 错误: 未找到任何prover"
    exit 1
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "开始大规模测试..."
echo "═══════════════════════════════════════════════════════"
echo ""

# 构建命令行参数
CMD_ARGS=(
    "--seed-dir" "$SEED_DIR"
    "--output-dir" "$OUTPUT_DIR"
    "--timeout" "$TIMEOUT"
    "--num-mutants" "$NUM_MUTANTS"
    "--max-seeds" "$MAX_SEEDS"
    "--use-ast-mutator"
)

if [ "$USE_RECONSTRUCTION_ORACLE" = "true" ]; then
    CMD_ARGS+=("--use-reconstruction-oracle")
fi

if [ "$USE_PARALLEL" = "true" ]; then
    CMD_ARGS+=("--use-parallel" "--num-workers" "$NUM_WORKERS")
fi

# 运行fuzzer
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
echo "📊 结果统计:"
if [ -d "$OUTPUT_DIR" ]; then
    echo "输出目录: $OUTPUT_DIR"
    echo ""
    
    # 统计文件
    BUG_COUNT=$(ls -1 "$OUTPUT_DIR"/bug_*.json 2>/dev/null | wc -l | tr -d ' ')
    DIFF_COUNT=$(ls -1 "$OUTPUT_DIR"/differential_*.json 2>/dev/null | wc -l | tr -d ' ')
    RECON_COUNT=$(ls -1 "$OUTPUT_DIR"/reconstruction_*.json 2>/dev/null | wc -l | tr -d ' ')
    LOG_COUNT=$(ls -1 "$OUTPUT_DIR"/logs/*.log 2>/dev/null | wc -l | tr -d ' ')
    
    echo "Bug报告 (Crashes/Hangs): $BUG_COUNT"
    echo "差异报告 (Differential): $DIFF_COUNT"
    echo "重构失败报告 (Reconstruction): $RECON_COUNT"
    echo "日志文件: $LOG_COUNT"
    echo ""
    
    # 显示统计摘要
    if [ -f "$OUTPUT_DIR/stats/stats.json" ]; then
        echo "📄 统计摘要:"
        python3 -c "import json; data=json.load(open('$OUTPUT_DIR/stats/stats.json')); print(json.dumps(data, indent=2))" 2>/dev/null | head -30
    fi
else
    echo "⚠️  输出目录不存在"
fi

echo ""
echo "✅ Week 8-9 大规模测试脚本完成"
