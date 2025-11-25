# Variant 3: Sledgehammer Integration Testing Framework

**Testing the Isabelle Sledgehammer Ecosystem through AST-based Fuzzing**

## Project Information

**Title**: Testing the Isabelle Sledgehammer Ecosystem: A Dual Approach to Prover and Integration Fuzzing

**Author**: Qilan Lin

**Supervisors**: 
- Dr. Mohammad Ahmad Abdulaziz Ali Mansour
- Dr. Karine Even Mendoza

**Institution**: King's College London

**Program**: BSc Project - Compiler and Verifier Reliability and Testing (2025/6)

**Project Variant**: Variant 3 - Isabelle ↔ external provers (Sledgehammer interfaces)

**Date**: November 24, 2025

**Status**: Complete and Ready for Publication

---

## Project Overview

This repository contains a complete implementation of an AST-based fuzzing framework for testing the integration layer between Isabelle/HOL and external automated theorem provers (E Prover, cvc5, Z3).

### Key Findings

- **519 prover bugs** discovered through differential testing
  - E Prover: 349 bugs (67.2%)
  - cvc5: 143 bugs (27.6%)
  - Z3: 27 bugs (5.2%)

- **0 integration bugs** found in 214 mutation tests (validated by Mirabelle)

- **3 Sledgehammer timeout cases** identified as capability boundaries (mutual recursion, custom induction, complex nested operations)

- **214 mutations tested** using Mirabelle (Isabelle's official testing tool)

- **0 integration bugs found** across all mutations

- **100% authoritative validation** using official Mirabelle tool

---

## Environment Setup & Installation

### Step 1: System Prerequisites

**Minimum Requirements:**
- OS: macOS or Linux (tested on macOS 26.1 with Apple M3 Max, 64GB RAM)
- Python: 3.13 or later
- RAM: 8GB minimum (16GB recommended)
- Disk: 10GB free space minimum
- Shell: bash or zsh

### Step 2: Install Python 3.13+

**macOS:**
```bash
# Using Homebrew
brew install python@3.13
python3.13 --version  # Verify
```

**Linux:**
```bash
# Ubuntu/Debian
sudo apt update
sudo apt install python3.13 python3.13-venv
python3.13 --version  # Verify
```

**Other systems:** Download from https://www.python.org/downloads/

### Step 3: Install Isabelle 2025

**macOS:**
```bash
# Download
cd /tmp
curl -O https://isabelle.in.tum.de/dist/Isabelle2025_macos.tar.gz

# Extract
tar xzf Isabelle2025_macos.tar.gz
sudo mv Isabelle2025 /opt/

# Add to PATH
export PATH="/opt/Isabelle2025/bin:$PATH"
echo 'export PATH="/opt/Isabelle2025/bin:$PATH"' >> ~/.zshrc

# Verify
isabelle version
```

**Linux:**
```bash
# Download
cd /tmp
wget https://isabelle.in.tum.de/dist/Isabelle2025_linux.tar.gz

# Extract
tar xzf Isabelle2025_linux.tar.gz
sudo mv Isabelle2025 /opt/

# Add to PATH
export PATH="/opt/Isabelle2025/bin:$PATH"
echo 'export PATH="/opt/Isabelle2025/bin:$PATH"' >> ~/.bashrc

# Verify
isabelle version
```

### Step 4: Install External Provers

**E Prover 3.1:**

macOS:
```bash
brew install eprover
eprover --version
```

Linux:
```bash
sudo apt install eprover
eprover --version
```

Or from source: https://www.eprover.org/

**cvc5 1.0.8:**

macOS:
```bash
brew install cvc5
cvc5 --version
```

Linux:
```bash
sudo apt install cvc5
cvc5 --version
```

Or from source: https://cvc5.github.io/

**Z3 4.12.2:**

macOS:
```bash
brew install z3
z3 --version
```

Linux:
```bash
sudo apt install z3
z3 --version
```

Or from source: https://github.com/Z3Prover/z3

### Step 5: Setup Python Environment

Navigate to this repository:
```bash
cd variant3

# Create virtual environment (optional but recommended)
python3.13 -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install Python dependencies
pip install --upgrade pip
pip install -r requirements.txt

# Verify installation
python3 -c "import pytest; print(f'pytest {pytest.__version__} installed')"
```

### Step 6: Verify Complete Setup

```bash
# Check Python
python3 --version

# Check Isabelle
isabelle version

# Check provers
eprover --version
cvc5 --version
z3 --version

# Check Python packages
pip list | grep pytest

# Run unit tests
pytest tests/ -v

# Expected: All 15 tests should PASS
```

---

## Quick Start

Once environment is set up:

```bash
# Run tests
pytest tests/ -v

# Run quick fuzzing campaign
python3 code/fuzzing_campaign.py \
  --campaign-name "quick_test" \
  --seed-dir data/seed_theories \
  --output-dir results/quick_test \
  --mutations-per-seed 5 \
  --timeout 30

# Expected output:
# - Fuzzing campaign: quick_test
# - Total mutations: 6 (or similar)
# - Bugs found: 0 (this is normal!)
# - Time: ~30 seconds
```

---

## Directory Structure

```
variant3/
├── README.md                    # This file
├── code/                        # Core implementation (~3800 lines)
│   ├── ast_mutator.py          # 10 mutation operators for Isabelle theories
│   ├── fuzzing_campaign.py     # Main fuzzing orchestration engine
│   ├── crash_oracle.py         # Crash and timeout detection
│   ├── differential_oracle.py  # Multi-prover comparison (519 bugs found)
│   ├── bug_verifier.py         # Mirabelle integration for validation
│   └── isabelle_interface.py   # Isabelle command-line interface
├── tests/                       # Unit test suite (15 tests)
│   ├── test_isabelle_interface.py
│   └── __init__.py
├── data/                        # Test data
│   ├── seed_theories/          # 10 high-quality seed Isabelle theories
│   │   ├── Seed_Basic_Arithmetic.thy
│   │   ├── Seed_List_Operations.thy
│   │   ├── Seed_Set_Operations.thy
│   │   ├── Seed_Logic_Formulas.thy
│   │   ├── Seed_Inductive_Proofs.thy
│   │   ├── Seed_Functions.thy
│   │   ├── Seed_Options.thy
│   │   ├── Seed_Pairs.thy
│   │   ├── Seed_Numbers.thy
│   │   └── Seed_Relations.thy
│   └── test_theories/          # 39 test theories
│       ├── Simple_Valid_Tests.thy
│       ├── Challenging_Cases.thy
│       ├── Extreme_Cases.thy
│       ├── ROOT                # Isabelle session definition
│       └── (35 additional test theories)
├── results/                     # Output directory for bug reports
├── requirements.txt             # Python package dependencies
└── pytest.ini                   # Pytest configuration
```

## Core Modules

| Module | Lines | Purpose |
|--------|-------|---------|
| `ast_mutator.py` | ~712 | AST-based mutation with 10 operators |
| `isabelle_interface.py` | ~800 | Isabelle CLI interface with error handling |
| `fuzzing_campaign.py` | ~494 | Main orchestration engine |
| `bug_verifier.py` | ~464 | Mirabelle integration for bug detection |
| `differential_oracle.py` | ~249 | Multi-prover comparison (discovered 519 bugs) |
| `crash_oracle.py` | ~236 | Crash/timeout detection |
| **Total** | **~3800** | **Production-grade implementation** |

## Methodology

### Phase 1: Prover Differential Testing
- Tested 1000+ TPTP problems across E Prover, cvc5, and Z3
- Compared results to find performance bugs
- Discovered 519 total bugs across all provers

### Phase 2: Integration Fuzzing
- Generated 214 mutations from 10 seed Isabelle theories
- Used 10 AST-level mutation operators:
  1. FLIP_QUANTIFIER (∀ ↔ ∃)
  2. NEGATE_FORMULA (P → ¬P)
  3. SWAP_CONJUNCTION (∧ ↔ ∨)
  4. SWAP_TERMS (f(x,y) → f(y,x))
  5. ADD_IDENTITY (x → x+0)
  6. REPLACE_CONSTANT (0 → 1)
  7. CHANGE_PROOF_METHOD (auto → simp)
  8. ADD_SLEDGEHAMMER_CALL
  9. DUPLICATE_LEMMA
  10. ADD_ASSUMPTION

### Phase 3: Mirabelle Validation
- **Mirabelle validation**: Using Mirabelle (Isabelle's official tool)
  - Theory error filtering
  - Integration bug detection  
  - Authoritative judgments
  - Direct validation (no custom oracle needed)
  
- Result: 214 mutations tested, 0 integration bugs found

## System Requirements

### Minimum Configuration
- Python 3.13+
- macOS or Linux
- 8GB RAM
- 10GB disk space

### Recommended Configuration
- Python 3.13+
- macOS or Linux with SSD
- 16GB RAM
- 20GB disk space

### External Dependencies
- **Isabelle 2025** (https://isabelle.in.tum.de/)
- **E Prover 3.1** (https://www.eprover.org/)
- **cvc5 1.0.8** (https://cvc5.github.io/)
- **Z3 4.12.2** (https://github.com/Z3Prover/z3)

### Tested Configuration
- macOS 26.1 (Apple M3 Max, 64GB RAM)
- Python 3.13.0
- Isabelle 2025
- E Prover 3.1, cvc5 1.0.8, Z3 4.12.2
- Timeout threshold: 30 seconds per test (on Apple M3 Max hardware)

### Environment Variables

```bash
# Add to ~/.bashrc or ~/.zshrc
export ISABELLE_HOME="/opt/Isabelle2025"
export PATH="$ISABELLE_HOME/bin:$PATH"
export PYTHONPATH="${PWD}/variant3:$PYTHONPATH"
```

## Installation Troubleshooting

### Issue: "isabelle command not found"
```bash
# Find Isabelle installation
find / -name "isabelle" -type f 2>/dev/null

# Add to PATH
export PATH="/path/to/isabelle/bin:$PATH"

# Verify
isabelle version
```

### Issue: "eprover/cvc5/z3 command not found"
```bash
# Check installation
which eprover
which cvc5
which z3

# If not found, install via package manager or source
# macOS: brew install eprover cvc5 z3
# Linux: sudo apt install eprover cvc5 z3
```

### Issue: "Python 3.13 not found"
```bash
# Check available Python versions
python3 --version
python3.13 --version

# Use python3 or python3.13 explicitly
python3 -m venv venv
```

### Issue: "ModuleNotFoundError" when running code
```bash
# Set PYTHONPATH correctly
export PYTHONPATH="${PWD}/variant3:$PYTHONPATH"

# Or run from variant3 directory
cd variant3
python3 code/fuzzing_campaign.py ...
```

### Issue: Tests timeout or fail
```bash
# Increase timeout
pytest tests/ -v --tb=short

# Or run specific test
pytest tests/test_isabelle_interface.py::test_name -v

# Check individual prover
eprover --version
cvc5 --version
z3 --version
```

## Usage Examples

### Run Differential Testing (Prover Bug Discovery)

**Step 1: Download TPTP Problems**

TPTP (Thousands of Problems for Theorem Provers) is the standard benchmark suite. To reproduce the 519 prover bugs, you need to download the TPTP library.

**Option 1: Download from Official TPTP Website (Recommended)**

```bash
# 1. Visit the TPTP distribution page
# URL: https://www.tptp.org/TPTP/Distribution/

# 2. Download the latest version (recommended: TPTP v7.5.0 or later)
# Direct download link: https://www.tptp.org/TPTP/Distribution/TPTP-v7.5.0.tgz
# Or use wget/curl:
cd ~/Downloads  # or any directory you prefer
wget https://www.tptp.org/TPTP/Distribution/TPTP-v7.5.0.tgz

# 3. Extract the archive
tar -xzf TPTP-v7.5.0.tgz

# 4. Move to a convenient location (optional)
mv TPTP-v7.5.0 ~/tptp/

# 5. Verify the download
ls ~/tptp/TPTP-v7.5.0/Problems/
# You should see directories like: Axioms/, Problems/, etc.
# The Problems/ directory contains the actual problem files (.p files)
```

**Option 2: Use a Subset for Quick Testing**

If you only want to test the differential oracle functionality without downloading the full library:

```bash
# Download a small subset (50-100 problems) for testing
# You can manually download individual problems from:
# https://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=FOF

# Or use TPTP's problem browser:
# https://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems

# Focus on FOF (First-Order Form) problems for ATP provers
# Save them to a directory, e.g., ~/tptp_sample/
```

**Option 3: Use Isabelle's TPTP Integration (If Available)**

Some TPTP problems may be available through Isabelle's examples or distribution, but this is not guaranteed.

**Note**: The full TPTP library is several GB in size. For reproducing the 519 bugs reported in the paper, you need the complete library with 1000+ problems. The Problems/ directory typically contains thousands of .p files organized by domain.

**Step 2: Run Differential Testing**

```bash
# Create a script to run differential testing
# Example usage of differential_oracle.py:

python3 -c "
from code.differential_oracle import DifferentialOracle
from code.crash_oracle import CrashOracle, ProverResult, OracleResult
import subprocess
import os

# Example: Test a single TPTP problem
tptp_file = 'path/to/problem.p'

oracle = DifferentialOracle()
crash_oracle = CrashOracle()

# Run each prover
results = {}
for prover in ['eprover', 'cvc5', 'z3']:
    # Run prover (implementation depends on your setup)
    # This is a simplified example
    result = crash_oracle.test_prover(prover, tptp_file, timeout=30)
    results[prover] = result

# Check for differential bugs
diff_result = oracle.check(results)
if diff_result.is_differential:
    print(f'Bug detected: {diff_result.error_message}')
"

# For full-scale testing (1000+ problems), you would:
# 1. Iterate through all TPTP problems
# 2. Run each problem with all three provers
# 3. Compare results using DifferentialOracle
# 4. Collect bug reports
# Expected: 519 bugs across E Prover (349), cvc5 (143), Z3 (27)
```

**Note**: A complete differential testing script is not included in this repository due to the large size of TPTP library (several GB). Researchers should download TPTP problems separately and implement the testing loop based on the provided `differential_oracle.py` module.

### Run Quick Fuzzing Campaign (5 minutes)
```bash
python3 code/fuzzing_campaign.py \
  --campaign-name "quick_test" \
  --seed-dir data/seed_theories \
  --output-dir results/quick_test \
  --mutations-per-seed 5 \
  --timeout 30 \
  --verbose
```

### Run Full Integration Test with Mirabelle
```bash
python3 code/fuzzing_campaign.py \
  --campaign-name "full_test" \
  --seed-dir data/seed_theories \
  --output-dir results/full_test \
  --mutations-per-seed 20 \
  --verify-bugs \
  --timeout 30
```

### Run Large-Scale Campaign (60 minutes)
```bash
python3 code/fuzzing_campaign.py \
  --campaign-name "large_scale" \
  --seed-dir data/seed_theories \
  --output-dir results/large_scale \
  --mutations-per-seed 30 \
  --timeout 60 \
  --verbose
```

### Run Unit Tests with Coverage
```bash
pytest tests/ -v --cov=code --cov-report=html
# Coverage report: htmlcov/index.html
```

## Expected Results

### Running Differential Testing (1000+ TPTP Problems)
```
total_tptp_problems: 1000+
provers_tested: E Prover, cvc5, Z3
timeout_per_test: 30 seconds

Expected bug distribution:
- Total bugs: 519
  - E Prover: 349 bugs (67.2%)
  - cvc5: 143 bugs (27.6%)
  - Z3: 27 bugs (5.2%)

Bug types:
- Timeouts: 288 (55.5%)
- Errors: 115 (22.2%)
- Slowdowns: 116 (22.3%)

Note: Actual numbers may vary slightly depending on:
- TPTP problem selection
- Prover versions
- Hardware configuration
- Timeout settings
```

### Running Quick Test
```
campaign_name: quick_test
total_seeds: 5
total_mutations: 6
bugs_found: 0
execution_time: ~30 seconds
throughput: ~12 tests/minute
```

### Running Full Integration Test
```
mutations_tested: 214
integration_bugs_found: 0
validation_method: Mirabelle (official tool)
validation_coverage: 100%
```

### Running Unit Tests
```
collected 15 items
test_isabelle_interface.py::... PASSED [100%]
===================== 15 passed in X.XXs =====================
```

## Results Summary

### Bug Discovery
- **Prover Differential Testing**: 519 bugs found
  - Timeouts: 288 (55.5%)
  - Errors: 115 (22.2%)
  - Slowdowns: 116 (22.3%)

- **Integration Fuzzing**: 0 bugs found in 214 mutations
  - Confirms Sledgehammer interface stability
  - 100% alignment with Mirabelle validation

- **Sledgehammer Capability Boundaries**: 3 timeout cases identified
  - Mutual recursion patterns (even_or_odd lemma in Extreme_Cases.thy, line 24)
  - Custom induction rules (fib_positive lemma in Extreme_Cases.thy, line 55)
  - Complex nested set operations
  - These represent Sledgehammer's practical limitations, not integration bugs
  - Provide guidance for when to use native Isabelle tactics instead
  
  To reproduce these timeout cases:
  ```bash
  cd data/test_theories
  isabelle mirabelle -T 30 Extreme_Cases.thy
  # Expected: 3 timeouts on even_or_odd, fib_positive, and complex nested operations
  ```

### Performance Metrics
- **Testing Throughput**: 8.3 tests/minute (with Mirabelle validation)
- **Average Test Time**: 7.2 seconds/test
- **Mutations Tested**: 214
- **Integration Bugs Found**: 0

### Code Quality
The implementation includes comprehensive type annotations, extensive inline documentation, unit test coverage, and custom exception hierarchy for robust error handling.

## Reproducibility Checklist

For researchers wanting to reproduce this work:

### Phase 1: Prover Differential Testing
- [ ] Install Python 3.13+
- [ ] Install E Prover, cvc5, Z3
- [ ] Download TPTP library (1000+ problems) from https://www.tptp.org/
- [ ] Clone/download this repository
- [ ] Run `pip install -r requirements.txt`
- [ ] Implement differential testing loop using `code/differential_oracle.py`
- [ ] Run differential testing on TPTP problems
- [ ] Verify bug discovery (expected: ~519 bugs across all provers)
- [ ] Compare bug distribution with reported statistics

### Phase 2: Integration Fuzzing
- [ ] Install Isabelle 2025
- [ ] Run `pytest tests/ -v` (verify installation)
- [ ] Run `python3 code/fuzzing_campaign.py --campaign-name test ...`
- [ ] Verify 0 integration bugs found
- [ ] Verify Mirabelle validation completes successfully
- [ ] Compare results with this README

### Phase 3: Sledgehammer Timeout Cases
- [ ] Navigate to `data/test_theories/`
- [ ] Run `isabelle mirabelle -T 30 Extreme_Cases.thy`
- [ ] Verify 3 timeout cases (even_or_odd, fib_positive, complex nested operations)
- [ ] Compare with reported timeout cases

## Code Documentation

Each Python module includes:
- Complete docstring explaining purpose and usage
- Type annotations (95%+ coverage)
- Detailed inline comments
- Error handling with custom exceptions
- Comprehensive logging

Example:
```python
def mutate_theory(theory_content: str, mutation_type: MutationType) -> str:
    """
    Apply a specific mutation to an Isabelle theory.
    
    Args:
        theory_content: Raw Isabelle theory text
        mutation_type: Type of mutation to apply
        
    Returns:
        Modified theory text
        
    Raises:
        ValueError: If mutation fails
    """
```

## Dependencies

### Python Packages (in requirements.txt)
- pytest>=7.4.0 (testing framework)
- pytest-cov>=4.1.0 (coverage reporting)
- colorlog>=6.7.0 (colored logging)
- typing-extensions>=4.8.0 (type hints)
- pathlib>=1.0.1 (path operations)

### System Dependencies
- Isabelle 2025
- E Prover 3.1
- cvc5 1.0.8
- Z3 4.12.2
- Unix/Linux tools (bash, grep, sed, etc.)

## Related Documentation

For complete methodology, experimental design, results analysis, and theoretical background:
- Academic paper in project root directory (17 pages)
- Project description: `project_description.md`

## Support & Questions

### For Setup Issues
1. Check "Installation Troubleshooting" section above
2. Run `pytest tests/ -v` to verify environment
3. Check external tool versions match requirements

### For Usage Questions
1. Read module docstrings: `python3 -c "import code.module; help(code.module)"`
2. Check command-line help: `python3 code/fuzzing_campaign.py --help`
3. Review inline code comments in relevant modules

### For Reproduction Issues
1. Verify all external tools installed correctly
2. Check Python version: `python3 --version`
3. Verify dependencies: `pip list | grep pytest`
4. Run quick test to isolate issue

## Contact & Attribution

**Author**: Qilan Lin

**Supervisors**: 
- Dr. Mohammad Ahmad Abdulaziz Ali Mansour
- Dr. Karine Even Mendoza

**Institution**: King's College London

**Acknowledgments**: King's College London, Knowledge Exchange Program with Amazon

---

Last Updated: November 24, 2025
