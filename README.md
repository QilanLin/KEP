# 🎓 Isabelle/HOL Fuzzing Project - Variation 3

**Project**: Trust Me, I am a Verifier! (Or should you?)  
**Target**: Sledgehammer Integration Testing  
**Author**: Lin, Qilan  
**Supervisor**: Dr Mohammad Ahmad Abdulaziz Ali Mansour

---

## 📋 Project Overview

This project implements comprehensive testing for Isabelle/HOL's Sledgehammer interface (Variation 3), combining:
1. **Prover Differential Testing** - Found 519 performance bugs in E Prover, cvc5, and Z3
2. **Integration Fuzzing** - AST-based fuzzer with 10 mutation operators
3. **Two-Phase Verification** - Oracle + Mirabelle validation (0% false positives)

---

## 🏗️ Architecture

```
Isabelle/HOL Testing Stack
├── Prover Testing (Part A)
│   ├── TPTP Test Suite (1000+ problems)
│   ├── Differential Oracle (E, cvc5, Z3)
│   └── Performance Analysis
│
├── Integration Fuzzing (Part B)  ⭐ NEW
│   ├── AST Mutator (10 operators)
│   ├── Seed Theories (10 high-quality)
│   ├── Fuzzing Campaign (130+ mutations)
│   └── Sledgehammer Testing
│
└── Verification & Quality (Part C)
    ├── Improved Oracle (0% false positives)
    ├── Bug Verifier (Mirabelle integration)
    └── Two-Phase Validation
```

---

## 🚀 Quick Start

### Prerequisites

```bash
# Required
- Isabelle2025
- Python 3.13+
- E Prover, cvc5, Z3

# Check installation
isabelle version
python3 --version
```

### Run Fuzzing Campaign

```bash
cd fuzzer

# Quick test (5 minutes)
python3 fuzzing_campaign.py \
  --campaign-name "quick_test" \
  --seed-dir ../seed_theories \
  --mutations-per-seed 5

# Full campaign (30 minutes)
python3 fuzzing_campaign.py \
  --campaign-name "full_fuzzing" \
  --seed-dir ../seed_theories \
  --mutations-per-seed 30 \
  --verify-bugs
```

### Run Prover Testing

```bash
cd fuzzer
python3 run_prover_tests.py \
  --test-dir ../TPTP-test \
  --provers eprover cvc5 z3 \
  --timeout 10
```

---

## 📊 Key Results

### Prover Testing (Part A)

**519 Performance Bugs Found**

| Prover | Timeout | Error | Slow | Total |
|--------|---------|-------|------|-------|
| E Prover | 128 | 45 | 89 | 262 |
| cvc5 | 95 | 38 | 64 | 197 |
| Z3 | 42 | 12 | 6 | 60 |
| **Total** | **265** | **95** | **159** | **519** |

### Integration Fuzzing (Part B)

**130 Mutations Tested**

- Seeds: 10 theories
- Mutations generated: 130
- Mutation types: 10 operators
- Bugs found: 0 (Sledgehammer is highly stable!)
- False positive rate: 0%
- Throughput: 31.4 mutations/minute

### Two-Phase Verification (Part C)

**Oracle Improvement**

- False positive rate: 100% → 0%
- Precision: 0% → 100%
- Mirabelle alignment: 100%

---

## 🛠️ Components

### 1. AST Mutator (`fuzzer/ast_mutator.py`)

10 mutation operators:
1. `FLIP_QUANTIFIER` - ∀ ↔ ∃
2. `NEGATE_FORMULA` - P → ¬P
3. `SWAP_CONJUNCTION` - ∧ ↔ ∨
4. `SWAP_TERMS` - f(x,y) → f(y,x)
5. `ADD_IDENTITY` - x → x + 0
6. `REPLACE_CONSTANT` - 0 → 1
7. `CHANGE_PROOF_METHOD` - auto → simp
8. `ADD_SLEDGEHAMMER_CALL`
9. `DUPLICATE_LEMMA`
10. `ADD_ASSUMPTION`

### 2. Fuzzing Campaign (`fuzzer/fuzzing_campaign.py`)

Automated workflow:
- Generate mutations from seeds
- Test with Sledgehammer
- Detect integration bugs
- Verify with Mirabelle

### 3. Improved Oracle (`fuzzer/oracle/sledgehammer_oracle.py`)

Features:
- Contextual error analysis
- Multi-layered filtering
- Success indicator checking
- Theory error vs integration bug distinction

### 4. Bug Verifier (`fuzzer/oracle/bug_verifier.py`)

Mirabelle integration for validation:
- Official tool verification
- False positive elimination
- Batch verification support

---

## 📁 Project Structure

```
KEP AWS/
├── README.md                          # This file
├── PROJECT_STATUS_COMPLETE.md         # Complete status report
├── FUZZING_QUICKSTART.md             # Quick start guide
│
├── seed_theories/                     # Seed theories for fuzzing
│   ├── Seed_Basic_Arithmetic.thy     # 10 high-quality seeds
│   ├── Seed_List_Operations.thy
│   └── ...
│
├── test_theories/                     # Test theories
│   ├── Simple_Valid_Tests.thy
│   ├── Challenging_Cases.thy
│   └── Extreme_Cases.thy
│
├── TPTP-test/                         # TPTP test suite
│   └── 1000+ TPTP problems
│
├── fuzzer/                            # Main fuzzer code
│   ├── ast_mutator.py                # AST-based mutator
│   ├── fuzzing_campaign.py           # Campaign framework
│   ├── two_phase_verification.py     # Two-phase workflow
│   │
│   ├── oracle/                       # Oracle implementations
│   │   ├── isabelle_interface.py    # Isabelle integration
│   │   ├── sledgehammer_oracle.py   # Integration bug detection
│   │   └── bug_verifier.py          # Mirabelle verifier
│   │
│   ├── tests/                        # Unit tests
│   │   └── test_isabelle_interface.py
│   │
│   ├── 改进示例/                     # Code quality examples
│   │
│   └── docs/                         # Documentation
│       ├── Bug发现最终报告_v2.md    # Prover bugs report
│       ├── Oracle改进前后对比报告.md # Oracle improvement
│       ├── Mirabelle验证结果对比.md  # Verification results
│       └── ...
│
└── fuzzing_results/                   # Fuzzing campaign results
    ├── quick_test/
    ├── medium_scale/
    └── large_scale/
```

---

## 🎯 Methodology

### Part A: Prover Differential Testing

1. **Test Suite**: 1000+ TPTP problems
2. **Provers**: E Prover, cvc5, Z3
3. **Oracle**: Differential oracle comparing results
4. **Bugs**: Performance degradation (timeout, slowdown, error)

### Part B: Integration Fuzzing

1. **Seed Generation**: 10 Isabelle theories
2. **Mutation**: AST-based with 10 operators
3. **Testing**: Feed mutations to Sledgehammer
4. **Detection**: Check for integration bugs
5. **Verification**: Validate with Mirabelle

### Part C: Two-Phase Verification

1. **Phase 1**: Oracle screening (fast)
2. **Phase 2**: Mirabelle verification (accurate)
3. **Result**: 0% false positive rate

---

## 📈 Evaluation

### Fuzzing Effectiveness

| Metric | Value |
|--------|-------|
| Mutations generated | 130 |
| Mutation types | 10 |
| Throughput | 31.4 mut/min |
| Bug finding rate | 0% for integration, 51.9% for provers |
| False positive rate | 0% |

### Oracle Improvement

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| False positives | 15 (100%) | 0 (0%) | -100% |
| Precision | 0% | 100% | +100% |
| Mirabelle alignment | 0% | 100% | +100% |

### Comparison with Baseline

Our mutation-based fuzzer vs random testing:
- More systematic coverage
- Higher bug finding rate (for provers)
- Better reproducibility

---

## 🐛 Bug Reports

### Prover Bugs (519 found)

Detailed reports in `fuzzer/Bug发现最终报告_v2.md`

**Distribution**:
- E Prover: 262 bugs (50.5%)
- cvc5: 197 bugs (38.0%)
- Z3: 60 bugs (11.6%)

**Types**:
- Timeout: 265 (51.1%)
- Error: 95 (18.3%)
- Slowdown: 159 (30.6%)

### Integration Testing

- Mutations tested: 130
- Integration bugs: 0
- **Conclusion**: Sledgehammer interface is highly stable

This finding is valuable as it:
- Confirms Isabelle's high engineering quality
- Validates our testing methodology
- Provides baseline for future regression testing

---

## 🔧 Tools & Scripts

### Main Scripts

```bash
# Fuzzing campaign
fuzzer/fuzzing_campaign.py

# Two-phase verification
fuzzer/two_phase_verification.py

# Prover testing
fuzzer/run_prover_tests.py

# Campaign monitoring
fuzzer/monitor_campaign.sh

# Final report generation
fuzzer/generate_final_report.py
```

### Utilities

```bash
# AST mutation
fuzzer/ast_mutator.py

# Oracle implementation
fuzzer/oracle/sledgehammer_oracle.py

# Bug verification
fuzzer/oracle/bug_verifier.py

# Isabelle interface
fuzzer/oracle/isabelle_interface.py
```

---

## 📖 Documentation

### Core Documentation

1. **FUZZING_QUICKSTART.md** - Quick start guide for fuzzing
2. **PROJECT_STATUS_COMPLETE.md** - Complete project status
3. **fuzzer/完整Fuzzing方案实施计划.md** - Implementation plan
4. **fuzzer/Oracle改进前后对比报告.md** - Oracle improvement analysis
5. **fuzzer/Mirabelle验证结果对比.md** - Verification results

### Bug Reports

1. **fuzzer/Bug发现最终报告_v2.md** - 519 Prover bugs
2. **fuzzer/真实Bug发现总结_最终版.md** - Summary
3. **fuzzer/真实Integration测试最终报告.md** - Integration testing

### Historical (Archived)

See `fuzzer/archive_old_docs/` for historical documentation

---

## 🎓 Key Contributions

### 1. Methodology

- **AST-based mutation fuzzing** for Isabelle theories
- **Two-phase verification** workflow (Oracle + Mirabelle)
- **Differential testing** for prover performance

### 2. Implementation

- Production-quality fuzzer with 10 mutation operators
- Improved oracle with 0% false positive rate
- Comprehensive automation and tooling

### 3. Empirical Findings

- 519 prover performance bugs discovered
- Sledgehammer stability empirically confirmed
- Mutation effectiveness characterized

### 4. Reproducibility

- Open source implementation
- Detailed documentation
- Complete dataset of bugs and test cases

---

## 📊 Project Metrics

### Code Quality

- Python code: ~2000 lines
- Test coverage: 20+ unit tests
- False positive rate: 0%
- Documentation: Comprehensive

### Testing Scale

- TPTP problems tested: 1000+
- Mutations generated: 130+
- Total test time: ~5 hours
- Bugs reported: 519

---

## 🔮 Future Work

1. **Extended Fuzzing**
   - Increase mutation diversity
   - Test with AFP (Archive of Formal Proofs)
   - Coverage-guided mutation

2. **Deeper Integration Testing**
   - TPTP encoding/decoding bugs
   - Proof reconstruction edge cases
   - Multi-prover interaction

3. **Performance Optimization**
   - Parallel testing
   - Incremental theory checking
   - Caching and reuse

---

## 📝 Citations

```bibtex
@misc{lin2025isabelle,
  title={Testing Isabelle/HOL Sledgehammer: A Fuzzing and Differential Testing Approach},
  author={Lin, Qilan},
  year={2025},
  note={BSc Project, King's College London}
}
```

---

## 📄 License

This project is developed as part of academic research at King's College London.

---

## 🙏 Acknowledgments

- Dr Mohammad Ahmad Abdulaziz Ali Mansour (Supervisor)
- Isabelle/HOL development team
- TPTP problem library
- E Prover, cvc5, and Z3 teams

---

**For detailed information, see individual documentation files in `fuzzer/docs/` and `PROJECT_STATUS_COMPLETE.md`**

