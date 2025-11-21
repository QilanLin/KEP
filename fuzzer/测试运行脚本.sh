#!/bin/bash
# 运行Fuzzer测试脚本

echo "🧪 Isabelle Sledgehammer Fuzzer 测试"
echo ""

cd "$(dirname "$0")"
WORK_DIR=$(pwd)

echo "工作目录: $WORK_DIR"
echo ""

# 检查种子目录
SEED_DIR="../sledgehammer_export"
if [ ! -d "$SEED_DIR" ]; then
    echo "❌ 种子目录不存在: $SEED_DIR"
    exit 1
fi

SEED_COUNT=$(ls -1 "$SEED_DIR"/*.p 2>/dev/null | wc -l | tr -d ' ')
echo "种子文件数: $SEED_COUNT"
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
    echo "请确保z3或cvc5在PATH中"
    exit 1
fi

echo ""
echo "开始运行测试..."
echo ""

# 运行fuzzer
python3 main.py \
    --seed-dir "$SEED_DIR" \
    --output-dir "./test_results" \
    --timeout 3.0 \
    --num-mutants 3 \
    --max-seeds 2

EXIT_CODE=$?

echo ""
echo "=========================================="
echo "测试完成"
echo "=========================================="
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    echo "✅ 测试成功完成"
else
    echo "⚠️  测试过程中有错误（退出码: $EXIT_CODE）"
fi

echo ""
echo "检查结果..."
if [ -d "./test_results" ]; then
    echo "输出目录: ./test_results"
    echo ""
    echo "文件列表:"
    ls -lh ./test_results/ 2>/dev/null | head -10
    
    BUG_COUNT=$(ls -1 ./test_results/bug_*.json 2>/dev/null | wc -l | tr -d ' ')
    DIFF_COUNT=$(ls -1 ./test_results/differential_*.json 2>/dev/null | wc -l | tr -d ' ')
    
    echo ""
    echo "统计:"
    echo "  Bug报告: $BUG_COUNT"
    echo "  差异报告: $DIFF_COUNT"
else
    echo "⚠️  输出目录不存在"
fi

echo ""
echo "✅ 测试脚本完成"

