# 🔄 Oracle vs Mirabelle: 使用策略分析

**问题**: 是否应该弃用我们的Oracle，只用Mirabelle？

**答案**: ❌ **不应该完全弃用，而是改进并结合使用**

---

## 📊 两者对比

### Oracle (我们的实现)

```
类型: Fuzzing Oracle
目标: 检测变异后theories的问题
方法: 
  - AST mutation生成新的test cases
  - 运行Isabelle命令
  - 分析输出和return codes
  - 分类错误类型

优势:
  ✅ 可以自定义fuzzing策略
  ✅ 可以测试任意变异的theories
  ✅ 灵活性高，可以扩展
  ✅ 符合项目要求 (build a fuzzer)

劣势:
  ❌ 当前实现有误分类问题
  ❌ 关键字matching太简单
  ❌ 可能产生false positives
  ❌ 需要验证
```

### Mirabelle (官方工具)

```
类型: Official Testing Tool
目标: 测试Sledgehammer在有效theories上的表现
方法:
  - 在已有的有效theories上运行
  - 测试proof automation tools
  - 收集性能数据
  - 官方支持和维护

优势:
  ✅ 官方认可，可靠性高
  ✅ 专门为testing设计
  ✅ 准确性高
  ✅ 可以作为ground truth

劣势:
  ❌ 不是fuzzer
  ❌ 主要用于有效theories
  ❌ 不能自定义fuzzing策略
  ❌ 不符合项目要求 (build a fuzzer)
```

---

## 🎯 项目要求分析

### 项目明确要求

根据 `project_description.md`:

```
"You shall build a new fuzzer (e.g. by writing a new set of 
code mutations to AFL) or extend significantly an existing 
fuzzer and show your extension led to more efficient testing 
of the target compiler as part of the evaluation of your project."
```

**关键点**:
1. ✅ 必须build或extend一个fuzzer
2. ✅ 必须show fuzzing的有效性
3. ✅ 必须有evaluation

**如果只用Mirabelle**:
- ❌ 不是building a fuzzer
- ❌ 不符合项目要求
- ❌ Mirabelle是现成的工具，不是你的contribution

**如果用Oracle + Mirabelle**:
- ✅ Oracle是你的fuzzer实现
- ✅ Mirabelle用于验证
- ✅ 符合项目要求

---

## 💡 推荐策略：两阶段验证流程

### Phase 1: Fuzzing (使用Oracle)

```python
# 1. 生成变异的test cases
mutated_theories = ast_mutator.generate_mutations(seed_theory)

# 2. 使用Oracle检测问题
for theory in mutated_theories:
    result = oracle.check_theory(theory)
    if result.has_issue:
        potential_bugs.append(result)
```

**目标**: 快速筛选出可能有问题的test cases

### Phase 2: Verification (使用Mirabelle)

```bash
# 3. 对Oracle发现的bugs进行官方验证
for bug in potential_bugs:
    # 用Mirabelle验证
    mirabelle_result = run_mirabelle(bug.theory)
    
    if mirabelle_result.confirms_bug:
        real_bugs.append(bug)  # ✅ 真实bug
    else:
        false_positives.append(bug)  # ❌ 假bug
```

**目标**: 确认哪些是真实的bugs

### Phase 3: Refinement

```python
# 4. 根据验证结果改进Oracle
oracle.learn_from_false_positives(false_positives)
oracle.learn_from_true_bugs(real_bugs)

# 5. 重新运行fuzzing
# 提高Oracle的准确性
```

**目标**: 持续改进Oracle的准确性

---

## 🔧 具体改进建议

### 1. 改进Oracle的分类逻辑

**当前问题**:
```python
# 太简单了
if "某关键字" in output:
    return BUG_TYPE
```

**改进方案**:
```python
def classify_error(self, output: str, returncode: int) -> BugType:
    # 1. 先检查是否是真正的error
    if self._is_success(output, returncode):
        return None  # 不是bug
    
    # 2. 使用更sophisticated的分析
    if self._has_syntax_error(output):
        return BugType.SYNTAX_ERROR
    
    # 3. 使用AST分析而不是keyword matching
    # ...
```

### 2. 建立Mirabelle验证流程

```python
class BugVerifier:
    """使用Mirabelle验证Oracle发现的bugs"""
    
    def verify_bug(self, theory_file: str) -> VerificationResult:
        # 1. 准备theory for Mirabelle
        self._prepare_theory(theory_file)
        
        # 2. 运行Mirabelle
        mirabelle_output = self._run_mirabelle(theory_file)
        
        # 3. 分析结果
        if "Finished" in mirabelle_output and "FAILED" not in mirabelle_output:
            return VerificationResult(is_real_bug=False)
        else:
            return VerificationResult(is_real_bug=True)
    
    def batch_verify(self, potential_bugs: List[Bug]) -> Dict[Bug, bool]:
        """批量验证bugs"""
        results = {}
        for bug in potential_bugs:
            result = self.verify_bug(bug.theory_file)
            results[bug] = result.is_real_bug
        return results
```

### 3. 统计和报告

```python
class FuzzingReport:
    """综合报告：Oracle + Mirabelle"""
    
    def generate_report(self):
        print(f"""
        📊 Fuzzing Campaign Results
        
        Oracle Fuzzing Phase:
          - Test cases generated: {self.total_tests}
          - Potential bugs found: {self.oracle_bugs}
          - False positive rate: {self.fp_rate}%
        
        Mirabelle Verification Phase:
          - Bugs verified: {self.mirabelle_verified}
          - Real bugs confirmed: {self.real_bugs}
          - False positives: {self.false_positives}
        
        Final Results:
          - True bugs: {self.real_bugs}
          - Oracle accuracy: {self.accuracy}%
          - Fuzzing efficiency: {self.efficiency}
        """)
```

---

## 📋 实施计划

### Week 1: Oracle改进

1. ✅ 改进`_classify_error`方法
2. ✅ 减少false positives
3. ✅ 添加更多上下文分析
4. ✅ 使用AST而不是keyword matching

### Week 2: Mirabelle集成

1. ✅ 创建`BugVerifier`类
2. ✅ 实现自动验证流程
3. ✅ 批量验证所有Oracle发现的bugs
4. ✅ 分析false positive patterns

### Week 3: 持续改进

1. ✅ 根据验证结果调整Oracle
2. ✅ 重新运行fuzzing campaign
3. ✅ 对比改进前后的准确性
4. ✅ 生成最终报告

---

## 🎓 学术角度

### 这样做的好处

1. **符合项目要求**
   - ✅ 你build了一个fuzzer (Oracle)
   - ✅ 你extended了testing方法
   - ✅ 你evaluated了effectiveness

2. **增加研究价值**
   - ✅ 展示了Oracle的局限性
   - ✅ 提出了验证方法
   - ✅ 改进了工具

3. **诚实的研究**
   - ✅ 承认false positives
   - ✅ 使用官方工具验证
   - ✅ 展示改进过程

### 报告中应该这样写

```
"我们开发了一个基于AST mutation的fuzzing oracle来检测
Isabelle-Sledgehammer集成中的潜在bugs。初始实现发现了15个
潜在问题，但经过Mirabelle官方工具验证后，我们发现这些都是
false positives。这一发现促使我们改进了Oracle的分类逻辑，
并建立了一个two-phase verification流程。

改进后的Oracle [如果有时间改进的话] 将false positive rate
从100%降低到XX%，并成功发现了YY个真实的integration issues。

这个过程展示了：
1. Fuzzing oracle设计的挑战
2. 官方验证工具的重要性
3. 迭代改进的必要性"
```

---

## ✅ 最终建议

### 不要弃用Oracle，而是：

1. **保留Oracle作为fuzzing tool**
   - 这是你的主要contribution
   - 符合项目要求

2. **使用Mirabelle作为验证标准**
   - Ground truth
   - Quality assurance

3. **建立two-phase workflow**
   - Phase 1: Oracle fuzzing (fast, 可能有false positives)
   - Phase 2: Mirabelle verification (slow, 但accurate)

4. **持续改进Oracle**
   - 根据Mirabelle feedback
   - 提高准确性
   - 减少false positives

5. **诚实报告结果**
   - 说明Oracle的局限
   - 展示改进过程
   - 报告真实的bug数量

---

## 🔄 工作流程总结

```
┌─────────────────────────────────────────────────────┐
│  1. Generate Test Cases (AST Mutation)             │
│     ↓                                               │
│  2. Oracle Fuzzing (Fast screening)                │
│     ├─ Found 100 potential issues                  │
│     ↓                                               │
│  3. Mirabelle Verification (Accurate validation)   │
│     ├─ Confirmed: 5 real bugs ✅                   │
│     ├─ Rejected: 95 false positives ❌             │
│     ↓                                               │
│  4. Oracle Refinement                              │
│     ├─ Analyze false positive patterns             │
│     ├─ Improve classification logic                │
│     ↓                                               │
│  5. Re-run Fuzzing Campaign                        │
│     ├─ Higher accuracy                             │
│     └─ More efficient bug finding                  │
└─────────────────────────────────────────────────────┘
```

---

**结论**: 

❌ **不要弃用Oracle**  
✅ **改进Oracle + 使用Mirabelle验证**  
✅ **建立two-phase流程**  
✅ **符合项目要求，增加研究价值**

这样做既满足了项目要求（build a fuzzer），又保证了结果的准确性（Mirabelle验证），还展示了科学的研究过程（发现问题、验证、改进）。

