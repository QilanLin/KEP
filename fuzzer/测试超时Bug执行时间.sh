#!/bin/bash

# 批量测试35个超时Bug的原始种子和变异文件执行时间对比

echo "═══════════════════════════════════════════════════════"
echo "🔍 批量测试超时Bug执行时间对比"
echo "═══════════════════════════════════════════════════════"
echo ""

BUG_DIR="./week8-9_integration_bug_test"
SEED_DIR="../sledgehammer_export"
OUTPUT_FILE="./超时Bug执行时间对比报告.txt"

# 清空输出文件
> "$OUTPUT_FILE"

echo "测试时间: $(date)" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"

# 统计变量
TOTAL_BUGS=0
ORIGINAL_FAST=0  # 原始文件快速完成的数量
ORIGINAL_TIMEOUT=0  # 原始文件也超时的数量
ORIGINAL_ERROR=0  # 原始文件错误的数量

echo "开始测试35个超时Bug..." | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"

# 遍历所有bug文件
for bug_file in "$BUG_DIR"/bug_*.json; do
    if [ ! -f "$bug_file" ]; then
        continue
    fi
    
    TOTAL_BUGS=$((TOTAL_BUGS + 1))
    bug_name=$(basename "$bug_file" .json)
    
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" | tee -a "$OUTPUT_FILE"
    echo "🔍 测试 $bug_name" | tee -a "$OUTPUT_FILE"
    echo "" | tee -a "$OUTPUT_FILE"
    
    # 从JSON中提取种子名称
    seed_name=$(grep '"seed"' "$bug_file" | sed 's/.*"seed": "\(.*\)".*/\1/')
    mutant_id=$(grep '"mutant_id"' "$bug_file" | sed 's/.*"mutant_id": \(.*\),/\1/')
    prover=$(grep '"prover"' "$bug_file" | sed 's/.*"prover": "\(.*\)".*/\1/')
    
    echo "  种子: $seed_name" | tee -a "$OUTPUT_FILE"
    echo "  变异体ID: $mutant_id" | tee -a "$OUTPUT_FILE"
    echo "  Prover: $prover" | tee -a "$OUTPUT_FILE"
    echo "" | tee -a "$OUTPUT_FILE"
    
    # 构造原始种子文件路径
    original_file="$SEED_DIR/${seed_name}.p"
    
    # 查找变异文件
    mutant_file=$(find "$BUG_DIR/mutants" -name "${seed_name}_mutant_${mutant_id}.p" 2>/dev/null | head -1)
    
    if [ ! -f "$original_file" ]; then
        echo "  ⚠️  原始种子文件不存在: $original_file" | tee -a "$OUTPUT_FILE"
        echo "" | tee -a "$OUTPUT_FILE"
        ORIGINAL_ERROR=$((ORIGINAL_ERROR + 1))
        continue
    fi
    
    # 测试原始种子文件
    echo "  📊 测试原始种子文件..." | tee -a "$OUTPUT_FILE"
    
    # 使用timeout命令限制10秒
    start_time=$(date +%s.%N)
    timeout 10 eprover --auto --tstp-format "$original_file" > /dev/null 2>&1
    exit_code=$?
    end_time=$(date +%s.%N)
    original_time=$(echo "$end_time - $start_time" | bc)
    
    if [ $exit_code -eq 124 ]; then
        # 超时
        echo "  ⚠️  原始文件执行时间: >10秒 (超时)" | tee -a "$OUTPUT_FILE"
        ORIGINAL_TIMEOUT=$((ORIGINAL_TIMEOUT + 1))
    elif [ $exit_code -eq 0 ] || [ $exit_code -eq 1 ]; then
        # 正常完成（退出码0或1都可能是正常的）
        echo "  ✅ 原始文件执行时间: ${original_time}秒" | tee -a "$OUTPUT_FILE"
        ORIGINAL_FAST=$((ORIGINAL_FAST + 1))
    else
        # 其他错误
        echo "  ❌ 原始文件执行错误 (退出码: $exit_code)" | tee -a "$OUTPUT_FILE"
        ORIGINAL_ERROR=$((ORIGINAL_ERROR + 1))
    fi
    
    # 测试变异文件（如果存在）
    if [ -f "$mutant_file" ]; then
        echo "  📊 测试变异文件..." | tee -a "$OUTPUT_FILE"
        
        start_time=$(date +%s.%N)
        timeout 10 eprover --auto --tstp-format "$mutant_file" > /dev/null 2>&1
        exit_code=$?
        end_time=$(date +%s.%N)
        mutant_time=$(echo "$end_time - $start_time" | bc)
        
        if [ $exit_code -eq 124 ]; then
            echo "  ⚠️  变异文件执行时间: >10秒 (超时)" | tee -a "$OUTPUT_FILE"
        elif [ $exit_code -eq 0 ] || [ $exit_code -eq 1 ]; then
            echo "  ✅ 变异文件执行时间: ${mutant_time}秒" | tee -a "$OUTPUT_FILE"
        else
            echo "  ❌ 变异文件执行错误 (退出码: $exit_code)" | tee -a "$OUTPUT_FILE"
        fi
        
        # 对比分析
        echo "" | tee -a "$OUTPUT_FILE"
        if [ $exit_code -eq 124 ] && [ $(echo "$original_time < 5.0" | bc) -eq 1 ]; then
            echo "  🎯 结论: 原始文件快速完成，变异后超时 → 这是Bug！" | tee -a "$OUTPUT_FILE"
        elif [ $exit_code -eq 124 ]; then
            echo "  🤔 结论: 变异文件超时（原始文件可能也较慢）" | tee -a "$OUTPUT_FILE"
        fi
    else
        echo "  ⚠️  变异文件不存在: $mutant_file" | tee -a "$OUTPUT_FILE"
    fi
    
    echo "" | tee -a "$OUTPUT_FILE"
done

# 生成统计报告
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" | tee -a "$OUTPUT_FILE"
echo "📊 统计报告" | tee -a "$OUTPUT_FILE"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"
echo "总Bug数量: $TOTAL_BUGS" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"
echo "原始种子文件测试结果:" | tee -a "$OUTPUT_FILE"
echo "  ✅ 快速完成 (<10秒): $ORIGINAL_FAST" | tee -a "$OUTPUT_FILE"
echo "  ⚠️  超时 (>10秒): $ORIGINAL_TIMEOUT" | tee -a "$OUTPUT_FILE"
echo "  ❌ 错误/不存在: $ORIGINAL_ERROR" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"

# 计算百分比
if [ $TOTAL_BUGS -gt 0 ]; then
    FAST_PERCENT=$(echo "scale=1; $ORIGINAL_FAST * 100 / $TOTAL_BUGS" | bc)
    TIMEOUT_PERCENT=$(echo "scale=1; $ORIGINAL_TIMEOUT * 100 / $TOTAL_BUGS" | bc)
    
    echo "百分比分布:" | tee -a "$OUTPUT_FILE"
    echo "  快速完成: ${FAST_PERCENT}%" | tee -a "$OUTPUT_FILE"
    echo "  超时: ${TIMEOUT_PERCENT}%" | tee -a "$OUTPUT_FILE"
    echo "" | tee -a "$OUTPUT_FILE"
fi

# 结论
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" | tee -a "$OUTPUT_FILE"
echo "✅ 结论" | tee -a "$OUTPUT_FILE"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"

if [ $ORIGINAL_FAST -gt 0 ]; then
    echo "🎯 关键发现:" | tee -a "$OUTPUT_FILE"
    echo "  有 $ORIGINAL_FAST 个bug的原始种子文件快速完成，但变异后超时。" | tee -a "$OUTPUT_FILE"
    echo "  这证明了变异引入了性能问题，确认这些是真正的Integration Bugs！" | tee -a "$OUTPUT_FILE"
    echo "" | tee -a "$OUTPUT_FILE"
fi

if [ $ORIGINAL_TIMEOUT -gt 0 ]; then
    echo "🤔 需要注意:" | tee -a "$OUTPUT_FILE"
    echo "  有 $ORIGINAL_TIMEOUT 个bug的原始种子文件本身也超时。" | tee -a "$OUTPUT_FILE"
    echo "  这些可能不是变异引入的问题，而是原始种子本身的问题。" | tee -a "$OUTPUT_FILE"
    echo "" | tee -a "$OUTPUT_FILE"
fi

echo "" | tee -a "$OUTPUT_FILE"
echo "📄 详细报告已保存到: $OUTPUT_FILE" | tee -a "$OUTPUT_FILE"
echo "" | tee -a "$OUTPUT_FILE"
echo "测试完成时间: $(date)" | tee -a "$OUTPUT_FILE"

