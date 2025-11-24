#!/bin/bash

# Campaign监控脚本

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║          Fuzzing Campaign Monitor                             ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo

# Check if campaigns are running
echo "📊 Running Campaigns:"
ps aux | grep "[p]ython3 fuzzing_campaign.py" | awk '{print "  PID " $2 ": " $11 " " $12 " " $13 " " $14}'
echo

# Quick Test Results
if [ -f "quick_test_results/quick_test_stats.json" ]; then
    echo "✅ Quick Test (completed):"
    python3 << 'EOF'
import json
with open('quick_test_results/quick_test_stats.json') as f:
    stats = json.load(f)
print(f"   Mutations: {stats['mutations_tested']}")
print(f"   Bugs: {stats['bugs_found']}")
print(f"   Time: {stats['total_time']:.1f}s")
EOF
    echo
fi

# Medium Scale Results
if [ -f "../fuzzing_results/medium_scale/medium_scale_stats.json" ]; then
    echo "✅ Medium Scale (completed):"
    python3 << 'EOF'
import json
with open('../fuzzing_results/medium_scale/medium_scale_stats.json') as f:
    stats = json.load(f)
print(f"   Mutations: {stats['mutations_tested']}")
print(f"   Bugs: {stats['bugs_found']}")
print(f"   Time: {stats['total_time']:.1f}s")
EOF
    echo
fi

# Large Scale Progress
if [ -f "large_campaign.log" ]; then
    echo "🔄 Large Scale (running):"
    
    # Count phases
    phase1_done=$(grep -c "✅ Phase 1 Complete" large_campaign.log || echo "0")
    phase2_done=$(grep -c "✅ Phase 2 Complete" large_campaign.log || echo "0")
    
    if [ "$phase1_done" = "1" ]; then
        echo "   ✅ Phase 1: Mutations generated"
        mutations=$(grep "Total mutations:" large_campaign.log | tail -1 | awk '{print $NF}')
        echo "      Total mutations: $mutations"
    else
        echo "   🔄 Phase 1: Generating mutations..."
    fi
    
    if [ "$phase2_done" = "1" ]; then
        echo "   ✅ Phase 2: Testing complete"
    elif [ "$phase1_done" = "1" ]; then
        echo "   🔄 Phase 2: Testing mutations..."
        tested=$(grep -c "Testing:" large_campaign.log || echo "0")
        echo "      Tests run: ~$tested"
    fi
    
    # Check for bugs
    bugs=$(grep -c "🐛 Bug found" large_campaign.log || echo "0")
    if [ "$bugs" != "0" ]; then
        echo "   🐛 Bugs found: $bugs"
    fi
    
    echo
fi

echo "📁 Generated Files:"
echo "   Mutations: $(find quick_test_results/mutations/ ../fuzzing_results/*/mutations/ -name "*.thy" 2>/dev/null | wc -l | tr -d ' ')"
if [ -d "../fuzzing_results/large_scale/bugs" ]; then
    echo "   Bug reports: $(ls ../fuzzing_results/large_scale/bugs/*.json 2>/dev/null | wc -l | tr -d ' ')"
fi

echo
echo "To view live logs:"
echo "  tail -f large_campaign.log"

