#!/bin/bash
# 大规模 Fuzzing 进度监控脚本

LOG_FILE="results/large_scale_batch1.log"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 【大规模 Fuzzing 进度监控】"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ ! -f "$LOG_FILE" ]; then
    echo "⚠️  日志文件不存在: $LOG_FILE"
    exit 1
fi

# 检查进程
if ps aux | grep -q "[p]ython3.*fuzzing_campaign.*large_scale"; then
    echo "✅ 测试进程正在运行"
else
    echo "⚠️  测试进程未找到（可能已完成或失败）"
fi

echo ""
echo "【进度统计】"

# 提取总mutations数
total=$(grep "Total mutations:" "$LOG_FILE" | tail -1 | grep -o "[0-9]*" | tail -1)
if [ -z "$total" ]; then
    echo "   总Mutations: 未知（Phase 1进行中）"
else
    echo "   总Mutations: $total"
    
    # 计算已测试数量
    tested=$(grep -c "Testing:" "$LOG_FILE")
    completed=$(grep -c "No bug detected\|Bug detected" "$LOG_FILE")
    bugs=$(grep -c "Bug detected" "$LOG_FILE")
    
    echo "   已测试: $completed / $total"
    
    if [ "$total" -gt 0 ]; then
        progress=$(awk "BEGIN {printf \"%.1f\", ($completed/$total)*100}")
        echo "   进度: $progress%"
    fi
    
    echo "   发现Bugs: $bugs"
    
    # 估算剩余时间
    if [ "$completed" -gt 0 ] && [ "$total" -gt "$completed" ]; then
        # 计算平均测试时间
        avg_time=$(grep "tested in" "$LOG_FILE" | grep -o "[0-9.]*s" | sed 's/s//' | awk '{sum+=$1; count++} END {if(count>0) print sum/count; else print 8}')
        remaining=$((total - completed))
        remaining_seconds=$(awk "BEGIN {printf \"%.0f\", $remaining * $avg_time}")
        remaining_minutes=$((remaining_seconds / 60))
        
        echo "   剩余时间: 约 $remaining_minutes 分钟"
    fi
fi

echo ""
echo "【最新日志（最后10行）】"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
tail -10 "$LOG_FILE"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "使用 'bash check_progress.sh' 再次查看进度"
echo "使用 'tail -f $LOG_FILE' 查看实时日志"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"


