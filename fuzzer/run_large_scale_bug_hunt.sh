#!/bin/bash

# 大规模Bug发现测试
# Phase 1: 全面的AST变异测试

echo "═══════════════════════════════════════════════════════"
echo "🎯 Phase 1: 大规模Bug发现测试"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "目标: 找到真实的Integration Bugs!"
echo ""

# 配置
SEED_DIR="../sledgehammer_export"
OUTPUT_DIR="./large_scale_bug_hunt"
TIMEOUT=30.0
NUM_MUTANTS=30  # 每个种子30个变异体
MAX_SEEDS=480   # 全部种子
NUM_WORKERS=8   # 最大化并行

echo "📋 测试配置:"
echo "  种子数量: $MAX_SEEDS (全部)"
echo "  变异体/种子: $NUM_MUTANTS"
echo "  总测试数: $((MAX_SEEDS * NUM_MUTANTS)) = 14,400个"
echo "  超时: ${TIMEOUT}秒"
echo "  并行workers: $NUM_WORKERS"
echo ""
echo "🔧 优化设置:"
echo "  ✅ 种子过滤: 启用 (10秒阈值)"
echo "  ✅ 相对时间检测: 启用 (3.0x阈值)"
echo "  ✅ 并行处理: 启用"
echo ""
echo "🎯 目标:"
echo "  - Differential Bugs (SAT/UNSAT冲突)"
echo "  - Performance Bugs (相对执行时间 >3x)"
echo "  - Crash Bugs (prover崩溃)"
echo ""

# 检查种子目录
if [ ! -d "$SEED_DIR" ]; then
    echo "❌ 种子目录不存在: $SEED_DIR"
    exit 1
fi

SEED_COUNT=$(ls -1 "$SEED_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "找到种子文件: $SEED_COUNT"

if [ "$SEED_COUNT" -eq 0 ]; then
    echo "❌ 未找到种子文件"
    exit 1
fi

echo ""
echo "═══════════════════════════════════════════════════════"
echo "开始测试... (预计需要 4-6 小时)"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "开始时间: $(date '+%Y-%m-%d %H:%M:%S')"
echo ""

# 运行fuzzer
python3 main.py \
    --seed-dir "$SEED_DIR" \
    --output-dir "$OUTPUT_DIR" \
    --timeout $TIMEOUT \
    --num-mutants $NUM_MUTANTS \
    --max-seeds $MAX_SEEDS \
    --enable-seed-filtering \
    --seed-filter-timeout 10.0 \
    --use-relative-time-check \
    --relative-time-threshold 3.0 \
    --use-ast-mutator \
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
    RECON_COUNT=$(ls -1 "$OUTPUT_DIR"/reconstruction_failure_*.json 2>/dev/null | wc -l | tr -d ' ')
    
    echo "  🐛 Crash/Timeout Bugs: $CRASH_COUNT"
    echo "  🐛 Differential Bugs: $DIFF_COUNT"
    echo "  🐛 Reconstruction Failures: $RECON_COUNT"
    echo ""
    
    TOTAL_BUGS=$((CRASH_COUNT + DIFF_COUNT + RECON_COUNT))
    echo "  🎯 总计发现的Bugs: $TOTAL_BUGS"
    echo ""
    
    if [ "$TOTAL_BUGS" -gt 0 ]; then
        echo "🎉 成功! 找到了 $TOTAL_BUGS 个bug!"
        echo ""
        echo "📄 Bug报告位置:"
        echo "  $OUTPUT_DIR/bug_*.json"
        echo "  $OUTPUT_DIR/differential_*.json"
        echo ""
    else
        echo "⚠️  Phase 1 未找到bug"
        echo ""
        echo "💡 建议:"
        echo "  1. 运行 Phase 2: ./run_aggressive_bug_hunt.sh"
        echo "  2. 使用更激进的变异策略"
        echo "  3. 增加测试时间（降低超时阈值）"
        echo ""
    fi
    
    # 显示统计摘要
    if [ -f "$OUTPUT_DIR/stats/stats.json" ]; then
        echo "📈 详细统计:"
        python3 -c "
import json
try:
    with open('$OUTPUT_DIR/stats/stats.json', 'r') as f:
        stats = json.load(f)
    print(f\"  总测试数: {stats.get('total_tests', 0)}\")
    print(f\"  种子处理数: {stats.get('seeds_processed', 0)}\")
    print(f\"  变异体生成数: {stats.get('mutants_generated', 0)}\")
except Exception as e:
    print(f'读取统计出错: {e}')
" 2>/dev/null
        echo ""
    fi
fi

echo "✅ Phase 1 完成"
echo ""

