# 📚 Documentation Index

Quick reference for all project documentation.

---

## 🚀 Getting Started

**New to this project? Start here:**

1. **README.md** - Project overview and quick start
2. **FUZZING_QUICKSTART.md** - 5-minute fuzzing guide
3. **PROJECT_STATUS_COMPLETE.md** - Complete project status

---

## 📖 Core Documentation

### Main Directory

| Document | Purpose |
|----------|---------|
| `README.md` | Project overview, architecture, results |
| `FUZZING_QUICKSTART.md` | Quick start guide for fuzzing |
| `PROJECT_STATUS_COMPLETE.md` | Complete project status and roadmap |
| `project_description.md` | Original project requirements |
| `AWS个人项目描述.md` | Project assignment details |
| `AFP下载指南.md` | AFP (Archive of Formal Proofs) guide |
| `术语与背景知识指南.md` | Terminology and background |

### Fuzzer Documentation (`fuzzer/docs/`)

| Document | Purpose |
|----------|---------|
| **Bug Reports** | |
| `Bug发现最终报告_v2.md` | 519 Prover bugs - complete report |
| | |
| **Oracle & Verification** | |
| `Oracle改进前后对比报告.md` | Oracle improvement (100% FP → 0%) |
| `Oracle改进完成总结.md` | Oracle improvement summary |
| `Oracle_vs_Mirabelle_使用策略.md` | Strategy: Oracle vs Mirabelle |
| `Mirabelle验证结果对比.md` | Mirabelle verification results |
| | |
| **Implementation** | |
| `完整Fuzzing方案实施计划.md` | Complete fuzzing implementation plan |

---

## 🔧 Technical Documentation

### Code Documentation

All code files contain comprehensive docstrings:

| File | Key Documentation |
|------|-------------------|
| `fuzzer/ast_mutator.py` | 10 mutation operators, usage examples |
| `fuzzer/fuzzing_campaign.py` | Campaign workflow, configuration |
| `fuzzer/oracle/isabelle_interface.py` | Isabelle integration, custom exceptions |
| `fuzzer/oracle/sledgehammer_oracle.py` | Bug detection logic, classification |
| `fuzzer/oracle/bug_verifier.py` | Mirabelle verification, batch processing |

### Code Examples

See `fuzzer/改进示例/README.md` for:
- Best practices examples
- Configuration patterns
- Unit testing examples

---

## 📊 Results & Analysis

### Quick Reference

| What | Where |
|------|-------|
| **519 Prover bugs** | `fuzzer/docs/Bug发现最终报告_v2.md` |
| **Fuzzing results** | `fuzzer/FINAL_FUZZING_REPORT.txt` |
| **Oracle improvement** | `fuzzer/docs/Oracle改进前后对比报告.md` |
| **Verification** | `fuzzer/docs/Mirabelle验证结果对比.md` |
| **Complete status** | `PROJECT_STATUS_COMPLETE.md` |

---

## 🗂️ Historical Documentation

Archived documentation (for reference only):

### Main Archive (`archive/`)

21 historical documents including:
- Setup guides (Week 1)
- Installation instructions
- Early testing reports
- LaTeX formatting guides

### Fuzzer Archive (`fuzzer/archive_old_docs/`)

18 historical documents including:
- Week 3-9 progress reports
- Early bug discovery reports
- Implementation details
- Intermediate analysis

**Note**: These are kept for historical reference but superseded by current documentation.

---

## 🎯 Documentation by Use Case

### I want to...

**Understand the project**
→ `README.md` + `PROJECT_STATUS_COMPLETE.md`

**Run fuzzing**
→ `FUZZING_QUICKSTART.md`

**See bug reports**
→ `fuzzer/docs/Bug发现最终报告_v2.md`

**Understand Oracle improvement**
→ `fuzzer/docs/Oracle改进前后对比报告.md`

**Learn verification methodology**
→ `fuzzer/docs/Mirabelle验证结果对比.md`

**Extend the fuzzer**
→ `fuzzer/docs/完整Fuzzing方案实施计划.md`

**Understand terminology**
→ `术语与背景知识指南.md`

**Review code examples**
→ `fuzzer/改进示例/README.md`

---

## 📝 Documentation Standards

### What's in Each Type

**README files**
- Overview and quick start
- Directory structure
- Usage examples

**Report files (报告)**
- Detailed analysis and findings
- Statistics and metrics
- Conclusions

**Guide files (指南)**
- Step-by-step instructions
- Reference information
- Troubleshooting

**Summary files (总结)**
- High-level overview
- Key takeaways
- Status updates

---

## 🔄 Document Updates

### Latest Updates

- **2025-11-23**: Documentation reorganization
  - Deleted ~40 outdated docs
  - Archived 39 historical docs
  - Created unified README
  - Organized fuzzer/docs/

### Maintained Documents

Only these documents are actively maintained:
- `README.md`
- `PROJECT_STATUS_COMPLETE.md`
- `FUZZING_QUICKSTART.md`
- `fuzzer/README.md`
- `fuzzer/docs/*`

---

**For the most up-to-date information, always refer to `README.md` and `PROJECT_STATUS_COMPLETE.md`**

