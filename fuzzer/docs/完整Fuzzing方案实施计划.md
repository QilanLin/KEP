# 🚀 完整Fuzzing方案实施计划

**目标**: 让项目100%符合Variation 3要求  
**状态**: 时间充裕，可以做得完美  
**预计完成时间**: 2-3周

---

## 📋 总体策略

### 保留 + 扩展

```
Phase 1 (已完成) ✅
├─ Prover Differential Testing
├─ 519个Prover bugs
├─ Improved Oracle
└─ Two-phase verification

Phase 2 (新增) 🆕
├─ AST-based Fuzzer
├─ Grammar-based Mutation
├─ Sledgehammer Integration Testing
└─ 完整的Fuzzing Campaign

最终报告 📝
├─ Part A: Prover Testing (已完成)
├─ Part B: Integration Fuzzing (新增)
└─ Part C: Comprehensive Evaluation
```

---

## 🎯 Phase 2 实施步骤

### Step 1: AST Mutator (已创建) ✅

**文件**: `fuzzer/ast_mutator.py`

**功能**:
- 10种mutation operators:
  1. `FLIP_QUANTIFIER` - 翻转量词 (∀ ↔ ∃)
  2. `NEGATE_FORMULA` - 否定公式
  3. `SWAP_CONJUNCTION` - 交换连接词 (∧ ↔ ∨)
  4. `SWAP_TERMS` - 交换函数参数
  5. `ADD_IDENTITY` - 添加恒等操作
  6. `REPLACE_CONSTANT` - 替换常数
  7. `CHANGE_PROOF_METHOD` - 改变证明方法
  8. `ADD_SLEDGEHAMMER_CALL` - 添加sledgehammer调用
  9. `DUPLICATE_LEMMA` - 复制lemma
  10. `ADD_ASSUMPTION` - 添加假设

**使用方法**:
```python
from ast_mutator import IsabelleTheoryMutator

mutator = IsabelleTheoryMutator()
mutations = mutator.mutate_theory(
    "test_theories/Simple_Valid_Tests.thy",
    num_mutations=20
)

# 保存mutations
for mutation in mutations:
    mutator.save_mutation(mutation, "mutated_theories/")
```

---

### Step 2: Fuzzing Campaign Framework (已创建) ✅

**文件**: `fuzzer/fuzzing_campaign.py`

**功能**:
- 完整的fuzzing workflow
- 自动化测试流程
- 统计和评估
- Bug验证

**运行方法**:
```bash
cd fuzzer

python3 fuzzing_campaign.py \
  --campaign-name "sledgehammer_fuzzing" \
  --seed-dir ../test_theories \
  --output-dir fuzzing_results \
  --mutations-per-seed 20 \
  --verify-bugs \
  --timeout 120
```

---

### Step 3: 准备Seed Theories (需要做) 🔲

**目标**: 创建高质量的seed theories

**计划创建**:
```
seed_theories/
├─ Basic_Operations.thy      # 基本操作
├─ List_Functions.thy         # List操作
├─ Set_Operations.thy         # Set操作
├─ Number_Theory.thy          # 数论
├─ Inductive_Proofs.thy       # 归纳证明
├─ Higher_Order_Functions.thy # 高阶函数
├─ Type_Classes.thy           # Type classes
├─ Record_Types.thy           # Record types
├─ Datatype_Definitions.thy   # Datatype
└─ Complex_Lemmas.thy         # 复杂lemmas
```

**每个seed应该**:
- ✅ 有效的Isabelle theory
- ✅ 包含5-10个lemmas
- ✅ 覆盖不同的proof patterns
- ✅ 适合mutation

**时间**: 2-3天

---

### Step 4: 运行Fuzzing Campaign (需要做) 🔲

**目标**: 生成大量mutations并测试

**计划**:
```
Campaign 1: Small Scale Test
├─ Seeds: 10个
├─ Mutations per seed: 10
├─ Total tests: 100
├─ 目的: 验证workflow
└─ 时间: 半天

Campaign 2: Medium Scale
├─ Seeds: 20个
├─ Mutations per seed: 20
├─ Total tests: 400
├─ 目的: 收集初步数据
└─ 时间: 1天

Campaign 3: Large Scale
├─ Seeds: 30个
├─ Mutations per seed: 50
├─ Total tests: 1500
├─ 目的: 全面测试
└─ 时间: 2-3天
```

**时间**: 4-5天

---

### Step 5: 分析结果 (需要做) 🔲

**目标**: 分析fuzzing发现的bugs

**任务**:
1. 统计bugs数量和类型
2. 分类bugs (interface vs theory errors)
3. 用Mirabelle验证真实bugs
4. 分析mutation effectiveness
5. 对比不同mutation types的效果

**输出**:
- `Fuzzing_Results_Analysis.md`
- `Bug_Reports/` (每个bug一个JSON)
- `Mutation_Effectiveness.md`

**时间**: 2-3天

---

### Step 6: Baseline对比 (需要做) 🔲

**目标**: 证明fuzzer比baseline更有效

**Baseline选择**:
1. **Random Testing**
   - 随机生成Isabelle theories
   - 不使用mutation operators
   
2. **Manual Testing**
   - 只用原始的test theories
   - 不生成mutations

**对比指标**:
```
Metrics:
├─ Bug finding rate (bugs / tests)
├─ Time to first bug
├─ Code coverage (如果能获取)
├─ Unique bug types
└─ Cost-effectiveness (bugs / hour)
```

**时间**: 2天

---

### Step 7: 评估Coverage (可选，加分项) 🌟

**目标**: 证明fuzzer的覆盖率

**方法**:
1. **Sledgehammer Code Coverage**
   - 如果可以instrument Sledgehammer
   - 记录哪些code paths被触发
   
2. **Input Space Coverage**
   - 统计测试了多少种input patterns
   - Mutation types的组合

3. **Error Path Coverage**
   - 触发了多少种error handling paths

**工具** (可能需要):
- `gcov` / `lcov` for code coverage
- 自定义的input space analysis

**时间**: 3-5天 (如果要做)

---

## 📊 预期成果

### Phase 2 完成后的项目结构

```
项目完整成果:
├─ Part A: Prover Testing
│   ├─ 519个Prover bugs ✅
│   ├─ Differential oracle ✅
│   └─ Bug reports ✅
│
├─ Part B: Integration Fuzzing 🆕
│   ├─ AST-based fuzzer
│   ├─ 10种mutation operators
│   ├─ X个Integration bugs (实际运行后得到)
│   └─ Fuzzing campaign reports
│
└─ Part C: Comprehensive Evaluation
    ├─ Baseline对比
    ├─ Effectiveness证明
    ├─ Coverage分析
    └─ 完整的metrics
```

### 预期Bugs数量

**保守估计**:
- 通过1500个mutations
- 可能发现: 5-20个真实integration bugs
- False positive rate: <10% (因为improved Oracle)

**如果不理想** (0-5个bugs):
- 也是有价值的发现
- 证明Sledgehammer非常稳定
- 仍然有完整的fuzzing methodology

---

## 📝 最终报告结构

### 完美的项目报告

```markdown
1. Introduction
   - Proof assistants and reliability
   - Variation 3: Sledgehammer integration
   - Project goals

2. Background
   - Isabelle/HOL architecture
   - Sledgehammer interface
   - Related work in fuzzing

3. Methodology
   
   3.1 Prover Testing (Phase 1)
       - Differential testing approach
       - TPTP test suite
       - Crash oracle
   
   3.2 Integration Fuzzing (Phase 2) 🆕
       - AST-based mutation
       - Grammar-based generation
       - Fuzzing campaign design
   
   3.3 Verification
       - Improved Oracle
       - Two-phase verification
       - Mirabelle validation

4. Implementation
   
   4.1 Fuzzer Architecture
       - AST Mutator (10 operators)
       - Mutation strategies
       - Test case generation
   
   4.2 Oracle Implementation
       - Bug detection logic
       - False positive reduction
       - Verification workflow
   
   4.3 Infrastructure
       - Automated testing pipeline
       - Results collection
       - Bug reporting

5. Evaluation
   
   5.1 Prover Testing Results
       - 519 Prover bugs
       - Performance degradation analysis
       - Bug distribution
   
   5.2 Integration Fuzzing Results 🆕
       - X mutations generated
       - Y bugs found
       - Z bugs verified
       - Bug types analysis
   
   5.3 Effectiveness Comparison
       - vs Random testing
       - vs Manual testing
       - Coverage achieved
       - Cost-effectiveness
   
   5.4 Oracle Accuracy
       - False positive rate: 0%
       - Precision: 100%
       - Two-phase verification

6. Bugs Found
   
   6.1 Prover Bugs (519)
       - Type distribution
       - Severity analysis
       - Example bugs
   
   6.2 Integration Bugs (X) 🆕
       - Bug reports
       - Root cause analysis
       - Reproducibility

7. Discussion
   - Key findings
   - Limitations
   - Threats to validity
   - Lessons learned

8. Related Work
   - Compiler fuzzing
   - Proof assistant testing
   - Differential testing

9. Conclusion & Future Work

10. References

Appendices:
A. Complete bug list
B. Fuzzing campaign logs
C. Code coverage data
D. Mutation examples
```

---

## ⏱️ 时间规划

### 2-3周完成计划

```
Week 1:
├─ Day 1-2: 创建seed theories
├─ Day 3-4: 运行small & medium campaigns
├─ Day 5-7: 运行large scale campaign
└─ 产出: Mutations生成，初步bug reports

Week 2:
├─ Day 1-3: 分析fuzzing results
├─ Day 4-5: Mirabelle验证bugs
├─ Day 6-7: Baseline对比
└─ 产出: 完整的evaluation data

Week 3 (optional):
├─ Day 1-3: Coverage分析 (如果做)
├─ Day 4-5: 撰写报告
├─ Day 6-7: 准备presentation
└─ 产出: 完整报告和展示
```

---

## 🎯 成功标准

### 项目被认为成功如果

**Must Have**:
- ✅ 构建了真正的fuzzer (AST mutator)
- ✅ 生成了大量test cases (>500)
- ✅ 测试了Sledgehammer integration
- ✅ 有完整的evaluation
- ✅ 证明了fuzzer effectiveness

**Nice to Have**:
- ✅ 找到真实integration bugs (>5)
- ✅ Coverage分析
- ✅ 与其他fuzzer对比
- ✅ 公开发布dataset

### 即使bugs很少也OK

**关键**: 即使只发现0-5个bugs，项目仍然成功，因为:
1. 有完整的fuzzing infrastructure
2. 证明了Sledgehammer的稳定性
3. 建立了testing methodology
4. 有519个Prover bugs作为backup

---

## 🚀 下一步行动

### 立即开始

1. **今天**: 创建10个seed theories
   ```bash
   cd test_theories
   # 创建 seed_theories/ 目录
   # 开始写第一批seeds
   ```

2. **明天**: 测试AST mutator
   ```bash
   cd fuzzer
   python3 ast_mutator.py
   # 验证mutations生成正确
   ```

3. **后天**: 运行第一个campaign
   ```bash
   python3 fuzzing_campaign.py \
     --mutations-per-seed 10 \
     --seed-dir ../test_theories
   ```

---

## 💡 Pro Tips

### 写Seed Theories技巧

1. **从简单开始**
   - 先写基本的arithmetic lemmas
   - 然后逐渐增加复杂度

2. **确保valid**
   - 每个seed都应该能通过Isabelle
   - 用 `isabelle build` 验证

3. **覆盖diversity**
   - 不同的data types
   - 不同的proof methods
   - 不同的lemma structures

4. **参考现有theories**
   - 从Isabelle library复制简单lemmas
   - 修改使其适合fuzzing

### Mutation策略

1. **先测试单个mutation type**
   - 看哪个type最有效
   - Focus on最productive的types

2. **组合mutations**
   - 尝试apply多个mutations
   - 可能找到更深的bugs

3. **记录所有结果**
   - 即使没找到bugs
   - 数据对evaluation很重要

---

## ✅ 总结

### 您现在拥有

1. ✅ **完整的AST Mutator** (`ast_mutator.py`)
   - 10种mutation operators
   - 可扩展的架构
   
2. ✅ **Fuzzing Campaign Framework** (`fuzzing_campaign.py`)
   - 自动化workflow
   - 完整的统计
   - Bug verification
   
3. ✅ **清晰的实施计划**
   - 分步骤的roadmap
   - 时间估计
   - 成功标准

### 您需要做的

1. 🔲 创建seed theories (2-3天)
2. 🔲 运行fuzzing campaigns (4-5天)
3. 🔲 分析和验证结果 (2-3天)
4. 🔲 Baseline对比 (2天)
5. 🔲 撰写报告 (可选，如果需要)

### 预期成果

**最终项目**:
- ✅ 519个Prover bugs (已有)
- ✅ X个Integration bugs (fuzzing发现)
- ✅ 完整的fuzzer实现
- ✅ 全面的evaluation
- ✅ 100%符合项目要求

**分数预期**: 95-100%

---

**准备好了吗？让我们开始创建第一批seed theories！** 🚀

