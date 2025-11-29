#!/bin/bash
# 策略2: 使用假prover测试异常处理

set -e

EPROVER_PATH="/Applications/Isabelle2025.app/contrib/e-3.1-1/arm64-darwin/eprover"
FAKE_PROVER="/tmp/fake_prover.sh"
BACKUP_PATH="${EPROVER_PATH}.backup"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "🚀 【策略2: 外部Prover崩溃测试】"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "警告: 这将临时替换真实的E prover"
echo ""
echo "E prover 路径: $EPROVER_PATH"
echo "假 prover 路径: $FAKE_PROVER"
echo ""

# Step 1: 备份真实prover
echo "Step 1: 备份真实prover..."
if [ ! -f "$BACKUP_PATH" ]; then
    cp "$EPROVER_PATH" "$BACKUP_PATH"
    echo "✅ 已备份到: $BACKUP_PATH"
else
    echo "✅ 备份已存在: $BACKUP_PATH"
fi

# Step 2: 替换为假prover
echo ""
echo "Step 2: 替换为假prover..."
cp "$FAKE_PROVER" "$EPROVER_PATH"
chmod +x "$EPROVER_PATH"
echo "✅ 已替换prover"

# Step 3: 清空异常日志
echo ""
echo "Step 3: 清空异常日志..."
rm -f /tmp/sledgehammer_hidden_errors.log /tmp/mirabelle_hidden_errors.log
echo "✅ 日志已清空"

# Step 4: 运行小规模测试
echo ""
echo "Step 4: 运行测试（5个mutations）..."
echo "开始时间: $(date '+%H:%M:%S')"
echo ""

cd "/Users/linqilan/Downloads/KEP AWS/variant3"
timeout 300 python3 code/fuzzing_campaign.py \
  --campaign-name "fake_prover_test" \
  --seed-dir data/seed_theories \
  --output-dir results/fake_prover_test \
  --mutations-per-seed 1 \
  --verify-bugs \
  --timeout 30 \
  2>&1 | tee results/fake_prover_test.log

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Step 5: 检查异常日志..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ -f /tmp/sledgehammer_hidden_errors.log ]; then
    echo "🎯 Sledgehammer异常日志:"
    cat /tmp/sledgehammer_hidden_errors.log
else
    echo "❌ 没有Sledgehammer异常日志"
fi

if [ -f /tmp/mirabelle_hidden_errors.log ]; then
    echo ""
    echo "🎯 Mirabelle异常日志:"
    cat /tmp/mirabelle_hidden_errors.log
else
    echo "❌ 没有Mirabelle异常日志"
fi

# Step 6: 恢复真实prover
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Step 6: 恢复真实prover..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ -f "$BACKUP_PATH" ]; then
    cp "$BACKUP_PATH" "$EPROVER_PATH"
    echo "✅ 已恢复真实prover"
else
    echo "❌ 备份文件不存在！"
    exit 1
fi

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ 测试完成"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "查看结果:"
echo "  - 测试日志: results/fake_prover_test.log"
echo "  - 异常日志: /tmp/sledgehammer_hidden_errors.log"
echo "  - 统计数据: results/fake_prover_test/fake_prover_test_stats.json"
echo ""

