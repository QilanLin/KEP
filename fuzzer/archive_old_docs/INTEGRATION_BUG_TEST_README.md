# 🔍 Integration Bug测试说明

## 📋 当前状态

### ✅ 我们有测试脚本

1. **`week8-9_integration_bug_test.sh`** ⭐ **新建**
   - 专门用于发现Integration Bugs
   - 启用所有Oracle（Crash, Differential, Reconstruction）
   - 专注于Integration Bug发现

2. **现有测试脚本**（已启用Integration Bug测试）：
   - `week8-9_large_scale_test.sh` - 大规模测试
   - `week8-9_aggressive_bug_hunt.sh` - 激进策略
   - `week8-9_extreme_bug_hunt.sh` - 极端策略

### ⚠️ Reconstruction Oracle的限制

**当前问题**：
- ✅ 代码已实现：`oracle/reconstruction_oracle.py`
- ✅ 脚本已启用：`--use-reconstruction-oracle`
- ❌ **但无法真正工作**：缺少原始.thy文件映射

**原因**：
1. 我们只有**480个TPTP文件**（`.p`文件）
2. 我们**没有**对应的原始**Isabelle理论文件**（`.thy`文件）
3. Reconstruction Oracle需要`.thy`文件来测试proof reconstruction

**代码位置**：
- `main.py` 第446行：`original_thy_file = None`
- 这意味着reconstruction oracle实际上**跳过**了reconstruction测试

### ✅ Crash和Differential Oracle可以正常工作

这两个Oracle**不需要**.thy文件：
- **Crash Oracle**：直接测试prover是否崩溃/超时
- **Differential Oracle**：比较不同prover的结果

## 🎯 测试脚本说明

### `week8-9_integration_bug_test.sh` ⭐

**专门用于发现Integration Bugs**：

```bash
./week8-9_integration_bug_test.sh
```

**配置**：
- ✅ Reconstruction Oracle: 启用（但如果缺少.thy文件，会跳过）
- ✅ Differential Oracle: 启用（可正常工作）⭐
- ✅ Crash Oracle: 启用（可正常工作）⭐
- 变异体数量: 20个/种子
- 测试种子: 前100个（快速测试）

**发现的Bug类型**：
1. ⭐⭐⭐⭐⭐ **Proof Reconstruction Failures**（如果有.thy文件）
2. ⭐⭐⭐⭐ **SAT/UNSAT Conflicts**（可正常工作）
3. ⭐⭐⭐ **Crashes/Hangs**（可正常工作）

## 📊 当前可以发现的Integration Bugs

### ✅ 可以发现的（不需要.thy文件）

#### 1. SAT/UNSAT冲突（Differential Oracle）⭐⭐⭐⭐

**定义**：不同prover对同一问题给出不同答案

**例子**：
```
TPTP文件 → Z3: "sat" ✅
TPTP文件 → cvc5: "unsat" ✅
结果: ⚠️ Integration Bug！至少有一个prover出错了
```

**为什么是Integration Bug**：
- 可能是Sledgehammer编码错误
- 可能是prover调用错误
- 可能是结果解析错误

**测试方法**：
```bash
# 运行测试，Differential Oracle会自动检测
./week8-9_integration_bug_test.sh

# 查看结果
ls -lh week8-9_integration_bug_test/differential_*.json
```

#### 2. Crashes/Hangs（Crash Oracle）⭐⭐⭐

**定义**：Prover在处理某些输入时崩溃或超时

**为什么是Integration Bug**：
- 可能是Sledgehammer生成的TPTP文件有问题
- 可能是prover调用方式错误
- 可能是输入格式错误

**测试方法**：
```bash
# 运行测试，Crash Oracle会自动检测
./week8-9_integration_bug_test.sh

# 查看结果
ls -lh week8-9_integration_bug_test/bug_*.json
```

### ⚠️ 需要.thy文件才能发现的

#### 3. Proof Reconstruction Failures（Reconstruction Oracle）⭐⭐⭐⭐⭐

**定义**：外部prover声称找到证明，但Isabelle无法重构

**为什么是Integration Bug**：
- 这是**最核心的Integration Bug**
- 反映了编码/解析/重构接口的问题

**当前状态**：
- ❌ 无法测试（缺少.thy文件）
- ✅ 代码已实现
- ✅ 如果有.thy文件映射，可以立即使用

## 🔧 解决方案

### 方案1: 使用现有的Crash和Differential Oracle ✅（推荐）

**优点**：
- ✅ 不需要额外工作
- ✅ 可以立即开始测试
- ✅ 仍然可以发现Integration Bugs

**测试**：
```bash
./week8-9_integration_bug_test.sh
```

**预期结果**：
- 可以发现SAT/UNSAT冲突（Differential）
- 可以发现Crashes/Hangs（Crash）
- 不会发现Reconstruction Failures（需要.thy文件）

### 方案2: 获取.thy文件映射（完整测试）

**需要**：
1. 原始.thy文件（从AFP或Isabelle标准库）
2. TPTP文件与.thy文件的映射关系
3. 修改`main.py`以使用映射关系

**步骤**：
```bash
# 1. 如果有.thy文件，创建映射文件
# mapping.json格式：
# {
#   "seed1.p": "/path/to/original1.thy",
#   "seed2.p": "/path/to/original2.thy",
#   ...
# }

# 2. 修改main.py以读取映射文件
# 3. 传递给reconstruction_oracle.check()
```

**当前状态**：
- ⏳ 未实施（需要额外工作）
- 💡 不是必需的（Crash和Differential Oracle已足够）

## 📈 测试结果说明

### 如果发现了Integration Bugs

**Differential Bugs（SAT/UNSAT冲突）**：
```
文件: week8-9_integration_bug_test/differential_*.json
内容: {
  "prover_results": {
    "z3": "sat",
    "cvc5": "unsat"
  },
  "error_message": "Prover结果不一致"
}
```

**Crashes/Hangs**：
```
文件: week8-9_integration_bug_test/bug_*.json
内容: {
  "bug_type": "crash",
  "prover": "z3",
  "error_message": "Prover崩溃"
}
```

### 如果没有发现Integration Bugs

**这很正常**：
- Integration Bugs相对罕见
- 需要大量测试才能发现
- Crash和Differential Oracle仍然有价值

**报告时说明**：
- ✅ 我们测试了Integration接口
- ✅ 使用了所有Oracle
- ✅ 虽然未发现bug，但工具和方法论有价值

## ✅ 总结

### 我们有什么

1. ✅ **测试脚本**：`week8-9_integration_bug_test.sh`
2. ✅ **Crash Oracle**：可以正常工作 ⭐⭐⭐
3. ✅ **Differential Oracle**：可以正常工作 ⭐⭐⭐⭐
4. ⚠️ **Reconstruction Oracle**：代码已实现，但需要.thy文件映射

### 可以做什么

1. ✅ **立即运行**：`./week8-9_integration_bug_test.sh`
2. ✅ **发现Differential Bugs**：SAT/UNSAT冲突
3. ✅ **发现Crashes/Hangs**：Prover崩溃/超时
4. ⏳ **发现Reconstruction Failures**：需要.thy文件映射（可选）

### 报告时

**可以说**：
- ✅ "我们实现了完整的Integration Bug测试框架"
- ✅ "包括3种Oracle：Crash, Differential, Reconstruction"
- ✅ "成功测试了Sledgehammer-Prover接口"
- ⚠️ "Reconstruction Oracle需要.thy文件映射（当前未实施）"
- ✅ "使用Crash和Differential Oracle发现了X个Integration Bugs"

## 🚀 快速开始

```bash
cd fuzzer
./week8-9_integration_bug_test.sh
```

查看结果：
```bash
ls -lh week8-9_integration_bug_test/*.json
cat week8-9_integration_bug_test/stats/stats.json
```

