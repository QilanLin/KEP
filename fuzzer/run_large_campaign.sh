#!/bin/bash

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║       🚀 Large Scale Fuzzing Campaign                         ║"
echo "╠════════════════════════════════════════════════════════════════╣"
echo "║  Seeds: 10 theories                                           ║"
echo "║  Mutations per seed: 30                                       ║"
echo "║  Expected tests: ~300                                         ║"
echo "║  Estimated time: 15-20 minutes                                ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo

python3 fuzzing_campaign.py \
  --campaign-name "large_scale_v1" \
  --seed-dir ../seed_theories \
  --output-dir ../fuzzing_results/large_scale \
  --mutations-per-seed 30 \
  --verify-bugs \
  --timeout 120

