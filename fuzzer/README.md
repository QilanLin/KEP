# 🔧 Fuzzer Implementation

This directory contains the core fuzzing and testing implementation.

---

## 📁 Directory Structure

```
fuzzer/
├── Core Fuzzing
│   ├── ast_mutator.py              # AST-based mutation fuzzer
│   ├── fuzzing_campaign.py         # Fuzzing campaign framework
│   └── two_phase_verification.py   # Two-phase validation
│
├── Oracle Implementation
│   └── oracle/
│       ├── isabelle_interface.py   # Isabelle integration (improved)
│       ├── sledgehammer_oracle.py  # Integration bug detection (improved)
│       └── bug_verifier.py         # Mirabelle verifier
│
├── Testing
│   └── tests/
│       ├── test_isabelle_interface.py  # 20+ unit tests
│       └── __init__.py
│
├── Scripts & Utilities
│   ├── run_prover_tests.py         # Prover differential testing
│   ├── monitor_campaign.sh         # Campaign monitoring
│   ├── generate_final_report.py   # Report generation
│   └── run_large_campaign.sh       # Large campaign runner
│
├── Documentation (Core)
│   ├── Bug发现最终报告_v2.md      # 519 Prover bugs
│   ├── Oracle改进前后对比报告.md   # Oracle improvement
│   ├── Mirabelle验证结果对比.md    # Verification results
│   ├── Oracle_vs_Mirabelle_使用策略.md  # Strategy guide
│   ├── 完整Fuzzing方案实施计划.md  # Implementation plan
│   ├── 真实Bug发现总结_最终版.md   # Bug summary
│   └── 项目最终总结.md             # Project summary
│
├── Code Quality Examples
│   └── 改进示例/
│       ├── improved_isabelle_interface.py  # Best practices
│       ├── config_example.py
│       └── README.md
│
├── Historical Documentation
│   └── archive_old_docs/           # Archived old docs
│
└── Results
    ├── quick_test_results/         # Quick test results
    ├── two_phase_results/          # Two-phase results
    └── integration_test_results_new/  # Integration test results
```

---

## 🚀 Quick Start

### 1. Run Fuzzing Campaign

```bash
# Quick test (5 min)
python3 fuzzing_campaign.py \
  --campaign-name "test" \
  --seed-dir ../seed_theories \
  --mutations-per-seed 5

# Full campaign (30 min)
python3 fuzzing_campaign.py \
  --campaign-name "full" \
  --seed-dir ../seed_theories \
  --mutations-per-seed 30 \
  --verify-bugs
```

### 2. Run Prover Testing

```bash
python3 run_prover_tests.py \
  --test-dir ../TPTP-test \
  --provers eprover cvc5 z3 \
  --timeout 10
```

### 3. Two-Phase Verification

```bash
python3 two_phase_verification.py \
  --theories-dir ../test_theories \
  --output-dir two_phase_results
```

---

## 🎯 Key Features

### AST Mutator

- 10 intelligent mutation operators
- Grammar-aware mutation
- Validity tracking
- Batch processing

### Fuzzing Campaign

- End-to-end automation
- Statistics collection
- Bug verification
- Comprehensive reporting

### Improved Oracle

- 0% false positive rate (verified)
- Contextual error analysis
- Multi-layered filtering
- Mirabelle-aligned

### Bug Verifier

- Official Mirabelle integration
- Batch verification
- Precision metrics
- Automated ROOT file generation

---

## 📊 Results Summary

### Prover Bugs: 519

See `Bug发现最终报告_v2.md` for details.

### Integration Bugs: 0

- 130 mutations tested
- 0 bugs found (Sledgehammer is stable)
- Verified with Mirabelle
- See `Mirabelle验证结果对比.md`

### Oracle Accuracy: 100%

- False positive rate: 0%
- Precision: 100%
- See `Oracle改进前后对比报告.md`

---

## 🔧 Development

### Running Tests

```bash
# Unit tests
cd tests
pytest test_isabelle_interface.py -v

# Integration tests
cd ..
python3 test_integration.py
```

### Code Quality

- Type annotations: 95%+ coverage
- Error handling: Comprehensive
- Documentation: Complete docstrings
- See `代码质量改进总结.md`

---

## 📖 Documentation Guide

### For Quick Start
→ Read `../FUZZING_QUICKSTART.md`

### For Implementation Details
→ Read `完整Fuzzing方案实施计划.md`

### For Bug Reports
→ Read `Bug发现最终报告_v2.md`

### For Oracle Improvement
→ Read `Oracle改进前后对比报告.md`

### For Verification Methodology
→ Read `Mirabelle验证结果对比.md`

### For Project Summary
→ Read `项目最终总结.md` or `../PROJECT_STATUS_COMPLETE.md`

---

## 🎓 Academic Use

### Key Contributions

1. **Novel AST-based mutation** for Isabelle
2. **Two-phase verification** workflow
3. **519 real bugs** discovered
4. **0% false positive** oracle

### Reproducibility

All code, data, and documentation are provided for:
- Reproducing experiments
- Extending the work
- Building upon methodology

---

**For more information, see the parent README.md or individual documentation files.**
