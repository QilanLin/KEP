#!/bin/bash
# Week 8-9 小规模验证测试（10个种子）

echo "═══════════════════════════════════════════════════════"
echo "🧪 Week 8-9 小规模验证测试"
echo "═══════════════════════════════════════════════════════"
echo ""

cd "$(dirname "$0")"

# 小规模测试配置（验证用）
python3 main.py \
    --seed-dir "../sledgehammer_export" \
    --output-dir "./week8-9_validation_test" \
    --timeout 5.0 \
    --num-mutants 10 \
    --max-seeds 10 \
    --use-ast-mutator \
    --use-reconstruction-oracle \
    --use-parallel \
    --num-workers 4

echo ""
echo "✅ 验证测试完成"
