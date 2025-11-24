#!/bin/bash
# 极端Bug发现测试脚本
# 使用最激进的策略，测试所有480个种子

echo "═══════════════════════════════════════════════════════"
echo "🔥 Isabelle Sledgehammer Fuzzer - 极端Bug发现测试"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "⚠️  警告：此测试将使用最极端的策略，可能需要很长时间！"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

echo "工作目录: $WORK_DIR"
echo ""

# 极端配置参数
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./week8-9_extreme_bug_hunt"
TIMEOUT=60.0  # 极端超时时间（60秒）
NUM_MUTANTS=100  # 极端变异体数量（100个/种子）
MAX_SEEDS=480  # 测试所有480个种子

echo "📋 极端测试配置:"
echo "  种子目录: $SEED_DIR"
echo "  输出目录: $OUTPUT_DIR"
echo "  超时时间: ${TIMEOUT}秒（极端超时）"
echo "  每个种子变异体数: $NUM_MUTANTS（极端数量）"
echo "  最大种子数: $MAX_SEEDS（所有种子）"
echo ""
echo "⚠️  预期执行时间: 数小时（取决于系统性能）"
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
read -p "⚠️  确认开始极端测试吗？(y/N): " -n 1 -r
echo ""
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "❌ 测试已取消"
    exit 1
fi

echo ""
echo "🚀 开始极端bug发现测试..."
echo "开始时间: $(date)"
echo ""
echo "策略说明:"
echo "  1. 超时时间60秒（发现timeout bug）"
echo "  2. 每个种子100个变异体（提高bug发现率）"
echo "  3. 测试所有480个种子（最大覆盖）"
echo "  4. 使用AST和Token双重变异策略"
echo "  5. 启用Reconstruction Oracle"
echo "  6. 使用激进和极端变异策略"
echo "  7. 并行处理以提高效率"
echo ""
echo "💡 提示: 可以随时按 Ctrl+C 中断测试"
echo ""

# 运行fuzzer（使用极端配置）
python3 main.py \
    --seed-dir "$SEED_DIR" \
    --output-dir "$OUTPUT_DIR" \
    --timeout "$TIMEOUT" \
    --num-mutants "$NUM_MUTANTS" \
    --max-seeds "$MAX_SEEDS" \
    --use-ast-mutator \
    --use-reconstruction-oracle \
    --reconstruction-timeout 120.0 \
    --use-aggressive-mutator \
    --use-extreme-mutator \
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
            ls -lh "$OUTPUT_DIR"/bug_*.json 2>/dev/null | head -10
            echo ""
        fi
        
        if [ "$DIFF_COUNT" -gt 0 ]; then
            echo "Differential Bug:"
            ls -lh "$OUTPUT_DIR"/differential_*.json 2>/dev/null | head -10
            echo ""
        fi
        
        if [ "$RECON_COUNT" -gt 0 ]; then
            echo "Reconstruction Failure:"
            ls -lh "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | head -10
            echo ""
        fi
    else
        echo "⚠️  未发现bug"
        echo ""
        echo "💡 分析:"
        echo "  - 可能Prover鲁棒性很强"
        echo "  - 可能变异策略还不够极端"
        echo "  - 可能测试时间还不够长"
        echo "  - 这个结果本身也是有价值的（验证了Prover的鲁棒性）"
    fi
    
    # 显示统计摘要
    if [ -f "$OUTPUT_DIR/stats/stats.json" ]; then
        echo "📄 统计摘要:"
        cat "$OUTPUT_DIR/stats/stats.json" | python3 -m json.tool 2>/dev/null | head -40
    fi
else
    echo "⚠️  输出目录不存在"
fi

echo ""
echo "✅ 极端bug发现测试完成"
echo ""
echo "💡 提示："
echo "  - 如果发现bug，查看 $OUTPUT_DIR/bug_*.json"
echo "  - 详细分析见: BUG_FINDING_RESULTS_ANALYSIS.md"

