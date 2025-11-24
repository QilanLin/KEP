#!/bin/bash

# Phase 2: 激进变异Bug发现测试

echo "═══════════════════════════════════════════════════════"
echo "🎯 Phase 2: 激进变异Bug发现测试"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "目标: 使用激进策略找到crash bugs!"
echo ""

# 配置
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./aggressive_bug_hunt"
TIMEOUT=30.0
NUM_MUTANTS=50  # 更多变异体
MAX_SEEDS=200   # 前200个种子
NUM_WORKERS=8

echo "📋 测试配置:"
echo "  种子数量: $MAX_SEEDS"
echo "  变异体/种子: $NUM_MUTANTS"
echo "  总测试数: $((MAX_SEEDS * NUM_MUTANTS)) = 10,000个"
echo "  超时: ${TIMEOUT}秒"
echo ""
echo "🔧 激进策略:"
echo "  ✅ AST Mutator (结构感知)"
echo "  ✅ Aggressive Mutator (语法破坏) ⚡"
echo "  ✅ Extreme Mutator (极端输入) ⚡⚡"
echo "  ✅ 并行处理: $NUM_WORKERS workers"
echo ""
echo "🎯 目标:"
echo "  - Crash Bugs (prover崩溃)"
echo "  - Parser Bugs (语法错误处理)"
echo "  - Memory Bugs (超大输入)"
echo "  - Edge Case Bugs (边界条件)"
echo ""

# 检查种子目录
if [ ! -d "$SEED_DIR" ]; then
    echo "❌ 种子目录不存在: $SEED_DIR"
    exit 1
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "开始激进测试... (预计需要 6-8 小时)"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "开始时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

# 运行fuzzer with aggressive strategies
python3 main.py \
    --seed-dir "$SEED_DIR" \
    --output-dir "$OUTPUT_DIR" \
    --timeout $TIMEOUT \
    --num-mutants $NUM_MUTANTS \
    --max-seeds $MAX_SEEDS \
    --use-ast-mutator \
    --use-aggressive-mutator \
    --use-extreme-mutator \
    --enable-seed-filtering \
    --seed-filter-timeout 10.0 \
    --use-parallel \
    --num-workers $NUM_WORKERS

EXIT_CODE=$?

echo ""
echo "结束时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo "═══════════════════════════════════════════════════════"
echo "测试完成 (退出码: $EXIT_CODE)"
echo "═══════════════════════════════════════════════════════"
echo ""

# 统计结果
if [ -d "$OUTPUT_DIR" ]; then
    echo "📊 Bug发现统计:"
    echo ""
    
    CRASH_COUNT=$(ls -1 "$OUTPUT_DIR"/bug_*.json 2>/dev/null | wc -l | tr -d ' ')
    DIFF_COUNT=$(ls -1 "$OUTPUT_DIR"/differential_*.json 2>/dev/null | wc -l | tr -d ' ')
    
    echo "  🐛 Crash/Timeout Bugs: $CRASH_COUNT"
    echo "  🐛 Differential Bugs: $DIFF_COUNT"
    echo ""
    
    TOTAL_BUGS=$((CRASH_COUNT + DIFF_COUNT))
    echo "  🎯 总计发现的Bugs: $TOTAL_BUGS"
    echo ""
    
    if [ "$TOTAL_BUGS" -gt 0 ]; then
        echo "🎉 成功! 找到了 $TOTAL_BUGS 个bug!"
    else
        echo "⚠️  Phase 2 未找到bug"
        echo ""
        echo "💡 这可能意味着:"
        echo "  1. 这些provers非常成熟和稳定"
        echo "  2. 需要更针对性的测试策略"
        echo "  3. Integration bugs可能更难找到"
        echo ""
    fi
fi

echo "✅ Phase 2 完成"
echo ""

