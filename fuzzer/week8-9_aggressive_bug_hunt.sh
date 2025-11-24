#!/bin/bash
# 激进的Bug发现测试脚本
# 基于深度研究的改进策略

echo "═══════════════════════════════════════════════════════"
echo "🔍 Isabelle Sledgehammer Fuzzer - 激进Bug发现测试"
echo "═══════════════════════════════════════════════════════"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

echo "工作目录: $WORK_DIR"
echo ""

# 激进的配置参数（基于研究）
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./week8-9_aggressive_bug_hunt"
TIMEOUT=30.0  # 增加超时时间（从5秒到30秒）以发现timeout bug
NUM_MUTANTS=50  # 增加变异体数量（从10到50）以提高bug发现率
MAX_SEEDS=100  # 先测试100个种子，如果找到bug再扩大规模

echo "📋 激进测试配置:"
echo "  种子目录: $SEED_DIR"
echo "  输出目录: $OUTPUT_DIR"
echo "  超时时间: ${TIMEOUT}秒（增加以发现timeout bug）"
echo "  每个种子变异体数: $NUM_MUTANTS（增加以提高bug发现率）"
echo "  最大种子数: $MAX_SEEDS"
echo ""

# 检查种子目录
if [ ! -d "$SEED_DIR" ]; then
    echo "❌ 种子目录不存在: $SEED_DIR"
    exit 1
fi

SEED_COUNT=$(ls -1 "$SEED_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "找到种子文件: $SEED_COUNT"
echo ""

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
echo "🚀 开始激进bug发现测试..."
echo "开始时间: $(date)"
echo ""
echo "策略说明:"
echo "  1. 增加超时时间到30秒（发现timeout bug）"
echo "  2. 增加变异体数量到50（提高bug发现率）"
echo "  3. 使用AST和Token双重变异策略"
echo "  4. 启用Reconstruction Oracle"
echo "  5. 并行处理以提高效率"
echo ""

# 运行fuzzer（使用激进配置）
python3 main.py \
    --seed-dir "$SEED_DIR" \
    --output-dir "$OUTPUT_DIR" \
    --timeout "$TIMEOUT" \
    --num-mutants "$NUM_MUTANTS" \
    --max-seeds "$MAX_SEEDS" \
    --use-ast-mutator \
    --use-reconstruction-oracle \
    --reconstruction-timeout 60.0 \
    --use-parallel \
    --num-workers 4

EXIT_CODE=$?

echo ""
echo "结束时间: $(date)"
echo "═══════════════════════════════════════════════════════"
echo "测试完成"
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
    RECON_COUNT=$(ls -1 "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | wc -l | tr -d ' ')
    LOG_COUNT=$(ls -1 "$OUTPUT_DIR"/logs/*.log 2>/dev/null | wc -l | tr -d ' ')
    STATS_COUNT=$(ls -1 "$OUTPUT_DIR"/stats/*.json 2>/dev/null | wc -l | tr -d ' ')
    
    echo "Bug报告 (Crash/Timeout): $BUG_COUNT"
    echo "差异报告: $DIFF_COUNT"
    echo "重构失败报告: $RECON_COUNT"
    echo "日志文件: $LOG_COUNT"
    echo "统计文件: $STATS_COUNT"
    echo ""
    
    # 显示发现的bug详情
    if [ "$BUG_COUNT" -gt 0 ] || [ "$DIFF_COUNT" -gt 0 ] || [ "$RECON_COUNT" -gt 0 ]; then
        echo "🎉 发现bug！详情如下："
        echo ""
        
        if [ "$BUG_COUNT" -gt 0 ]; then
            echo "Crash/Timeout Bug:"
            ls -lh "$OUTPUT_DIR"/bug_*.json 2>/dev/null | head -5
            echo ""
        fi
        
        if [ "$DIFF_COUNT" -gt 0 ]; then
            echo "Differential Bug:"
            ls -lh "$OUTPUT_DIR"/differential_*.json 2>/dev/null | head -5
            echo ""
        fi
        
        if [ "$RECON_COUNT" -gt 0 ]; then
            echo "Reconstruction Failure:"
            ls -lh "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | head -5
            echo ""
        fi
    else
        echo "⚠️  未发现bug（但这很正常，继续测试更多种子或调整策略）"
    fi
    
    # 显示统计摘要
    if [ -f "$OUTPUT_DIR/stats/stats.json" ]; then
        echo "📄 统计摘要:"
        cat "$OUTPUT_DIR/stats/stats.json" | python3 -m json.tool 2>/dev/null | head -30
    fi
else
    echo "⚠️  输出目录不存在"
fi

echo ""
echo "✅ 激进bug发现测试完成"
echo ""
echo "💡 提示："
echo "  - 如果发现bug，查看 $OUTPUT_DIR/bug_*.json"
echo "  - 如果未发现bug，可以："
echo "    1. 增加 MAX_SEEDS 数量"
echo "    2. 增加 NUM_MUTANTS 数量"
echo "    3. 进一步增加 TIMEOUT"
echo "    4. 使用激进的变异策略（破坏语法的变异）"

