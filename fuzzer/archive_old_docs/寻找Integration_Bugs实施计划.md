# 🎯 寻找Integration Bugs实施计划

**问题**: 若要寻找Integration bugs，只需要写一个测试脚本吗？

**答案**: ❌ **不是，需要做的远不止写一个脚本。**

---

## 📊 当前状况 vs 目标状况

### 当前测试架构（发现Prover bugs）

```
┌─────────────┐
│  TPTP文件   │
│  (.p文件)   │
└──────┬──────┘
       │
       ▼
┌──────────────┐
│ 直接调用     │
│ eprover/cvc5 │  ← crash_oracle.check()
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ 检查超时/崩溃 │
└──────────────┘

❌ 没有经过Isabelle
❌ 没有测试Integration层
```

### 目标测试架构（发现Integration bugs）

```
┌─────────────┐
│ Isabelle    │
│ Theory文件  │
│ (.thy文件)  │
└──────┬──────┘
       │
       ▼
┌──────────────────┐
│   Isabelle       │
│  Sledgehammer    │  ← Integration层！
└────────┬─────────┘
         │
    ┌────┴────┐
    │ TPTP转换 │  ← 可能有编码bugs
    └────┬────┘
         │
         ▼
┌──────────────────┐
│   外部Prover     │
│ eprover/cvc5/z3  │
└────────┬─────────┘
         │
    ┌────┴────┐
    │ 结果解析 │  ← 可能有解析bugs
    └────┬────┘
         │
         ▼
┌──────────────────┐
│ Proof            │
│ Reconstruction   │  ← 核心Integration测试！
└──────────────────┘

✅ 经过完整的Integration链
✅ 可以发现接口层的bugs
```

---

## 🔧 需要做的改动（不只是脚本）

### 1. 准备测试材料 ⭐⭐⭐⭐⭐

#### a. 需要.thy文件（不是只有.p文件）

**当前**:
```
sledgehammer_export/
  prob4729480_1.p      # 只有TPTP文件
  prob4729482_1.p
  ...
```

**需要**:
```
test_theories/
  Theory1.thy          # 需要Isabelle theory源文件
  Theory2.thy
  ...
```

**如何获取**:
- 方案1: 从AFP (Archive of Formal Proofs)提取
- 方案2: 编写简单的theory文件
- 方案3: 使用Isabelle标准库中的theory

**工作量**: 📝 **中等**（需要找到或编写合适的.thy文件）

#### b. 建立.thy到.p的映射关系

**需要记录**:
```python
thy_to_tptp_mapping = {
    "Theory1.thy": ["prob001.p", "prob002.p"],
    "Theory2.thy": ["prob003.p", "prob004.p"],
}
```

**工作量**: 📝 **简单**（可以自动化）

---

### 2. 修改Fuzzer架构 ⭐⭐⭐⭐⭐

#### a. 修改main.py的测试流程

**当前代码**:
```python
# main.py - 当前方式
mutant_file = generate_mutant(seed)
result = crash_oracle.check(prover_path, mutant_file)  # 直接调用
```

**需要改为**:
```python
# main.py - Integration测试方式
mutant_file = generate_mutant(seed)
thy_file = create_thy_wrapper(mutant_file)  # 创建theory包装

# 方式1: 通过Isabelle调用Sledgehammer
result = isabelle_sledgehammer.run(
    thy_file=thy_file,
    prover='eprover',
    timeout=30
)

# 方式2: 使用Isabelle Process
result = isabelle_process.check_theory(thy_file)
```

**工作量**: 📝 **较大**（重写测试流程）

#### b. 创建Isabelle接口模块

**需要新建**:
```
fuzzer/oracle/
  isabelle_interface.py  # 新建！调用Isabelle命令行
  sledgehammer_oracle.py # 新建！测试Sledgehammer集成
```

**功能**:
```python
class IsabelleInterface:
    def run_sledgehammer(self, thy_file, prover, timeout):
        """通过Isabelle运行Sledgehammer"""
        cmd = [
            'isabelle', 'process',
            '-e', f'use_thy "{thy_file}";'
        ]
        # 执行并解析结果
        
    def extract_tptp(self, thy_file):
        """提取Sledgehammer生成的TPTP"""
        
    def reconstruct_proof(self, thy_file, prover_result):
        """尝试proof reconstruction"""
```

**工作量**: 📝 **较大**（需要学习Isabelle API）

---

### 3. 修改Oracle实现 ⭐⭐⭐⭐⭐

#### a. 启用Reconstruction Oracle

**当前代码**:
```python
# main.py - 当前
original_thy_file = None  # ❌ 未启用
```

**需要改为**:
```python
# main.py - 需要
original_thy_file = get_original_thy(seed_file)  # ✅ 提供真实文件

reconstruction_result = reconstruction_oracle.check(
    prover_result=prover_result,
    original_thy_file=original_thy_file,  # 真实的.thy文件
    mutant_file=mutant_file
)
```

**工作量**: 📝 **中等**（需要完善reconstruction oracle）

#### b. 修改Reconstruction Oracle的实现

**当前限制**:
```python
# reconstruction_oracle.py - 当前
if not original_thy_file:
    return ReconstructionResult(
        status=ReconstructionStatus.SKIPPED,
        reconstruction_attempted=False
    )
```

**需要完善**:
```python
# reconstruction_oracle.py - 需要
# 1. 读取原始theory
# 2. 插入prover找到的proof
# 3. 用Isabelle尝试重构
# 4. 检测重构失败 ← Integration Bug!
```

**工作量**: 📝 **较大**（需要深入理解Isabelle proof reconstruction）

---

### 4. 修改测试脚本 ⭐⭐⭐

#### a. 修改种子处理方式

**当前脚本**:
```bash
# 当前
python3 main.py \
    --seed-dir ../sledgehammer_export \  # .p文件
    --use-ast-mutator
```

**需要改为**:
```bash
# 需要
python3 main.py \
    --seed-dir ../test_theories \       # .thy文件
    --thy-mode \                        # 新参数
    --use-sledgehammer \                # 新参数
    --test-reconstruction \             # 新参数
    --use-ast-mutator
```

**工作量**: 📝 **简单**（修改脚本参数）

---

### 5. 配置Isabelle环境 ⭐⭐⭐⭐

#### a. 配置Sledgehammer

**需要设置**:
```bash
# 配置Isabelle以导出TPTP文件
export SLEDGEHAMMER_EXPORT_DIR=/path/to/export
```

**在.thy文件中**:
```isabelle
theory Test
imports Main
begin

(* 配置Sledgehammer *)
sledgehammer_params [
  provers = "eprover cvc5 z3",
  timeout = 30,
  verbose = true
]

lemma test: "x + 0 = x"
  by (sledgehammer)

end
```

**工作量**: 📝 **中等**（需要熟悉Isabelle配置）

#### b. 确保Prover可被Isabelle调用

**检查**:
```bash
# 检查Isabelle能否找到prover
isabelle sledgehammer_prover_info

# 测试prover集成
isabelle jedit  # 打开GUI测试
```

**工作量**: 📝 **简单**（验证安装）

---

## 📋 完整实施清单

### Phase 1: 准备阶段（1-2天）

- [ ] 1.1 收集或创建.thy测试文件（20-50个）
- [ ] 1.2 建立.thy到TPTP的映射
- [ ] 1.3 配置Isabelle环境
- [ ] 1.4 测试Isabelle命令行调用

### Phase 2: 代码修改（3-5天）

- [ ] 2.1 创建`isabelle_interface.py`
- [ ] 2.2 创建`sledgehammer_oracle.py`
- [ ] 2.3 修改`main.py`支持.thy输入
- [ ] 2.4 完善`reconstruction_oracle.py`
- [ ] 2.5 修改变异器支持.thy文件

### Phase 3: 集成测试（1-2天）

- [ ] 3.1 编写Integration测试脚本
- [ ] 3.2 小规模测试（5个theory）
- [ ] 3.3 调试和修复问题
- [ ] 3.4 验证可以检测到Integration bugs

### Phase 4: 大规模测试（1天）

- [ ] 4.1 运行完整测试（50个theory）
- [ ] 4.2 收集Integration bugs
- [ ] 4.3 分析和报告

**总工作量**: 📝 **6-10天**

---

## 🎯 关键挑战

### 挑战1: 学习Isabelle API ⚠️

**难度**: 高

**原因**:
- Isabelle API文档不够完善
- 需要理解ML语言
- 需要理解Isabelle内部机制

**解决方案**:
- 参考Isabelle源码
- 查看已有的integration测试
- 使用简单的命令行调用

### 挑战2: Proof Reconstruction ⚠️

**难度**: 高

**原因**:
- Proof reconstruction是复杂的过程
- 需要理解Isabelle的proof机制
- 可能有很多边界情况

**解决方案**:
- 从简单的proof开始
- 使用Isabelle的自动proof工具
- 记录失败情况

### 挑战3: 性能问题 ⚠️

**难度**: 中

**原因**:
- 通过Isabelle调用会更慢
- Proof reconstruction需要时间
- 可能需要更长的timeout

**解决方案**:
- 减少测试规模
- 增加timeout设置
- 使用并行处理

---

## 💡 简化方案（如果时间紧张）

### 方案A: 混合测试（推荐） ⭐⭐⭐⭐⭐

**策略**:
1. ✅ 保留当前的Prover测试（已经很成功）
2. ✅ 添加一小部分Integration测试（10-20个theory）
3. ✅ 重点测试Reconstruction

**优点**:
- 工作量可控（2-3天）
- 可以找到一些Integration bugs
- 不影响已有成果

**实施**:
```
当前测试:  480个TPTP文件（Prover bugs）
新增测试:  20个.thy文件（Integration bugs）
总工作量: 2-3天
```

### 方案B: 只测试Reconstruction ⭐⭐⭐⭐

**策略**:
1. 使用已有的TPTP文件
2. 手动创建对应的.thy文件（简化版）
3. 只测试proof reconstruction

**优点**:
- 工作量小（1-2天）
- 可以找到reconstruction bugs
- 利用已有的测试基础设施

**实施**:
```python
# 只需要修改
def test_reconstruction(tptp_file, prover_result):
    """测试proof reconstruction"""
    # 1. 创建简单的.thy包装
    thy_file = create_thy_wrapper(tptp_file)
    
    # 2. 插入prover的proof
    insert_proof(thy_file, prover_result)
    
    # 3. 用Isabelle尝试验证
    result = isabelle_verify(thy_file)
    
    # 4. 检查是否成功
    if result.failed:
        return IntegrationBug(
            type="reconstruction_failure",
            thy_file=thy_file,
            prover=prover_result.prover
        )
```

**工作量**: 📝 **1-2天**

### 方案C: 使用现有工具 ⭐⭐⭐

**策略**:
- 使用Isabelle的built-in测试工具
- 直接在Isabelle中运行fuzzing

**实施**:
```bash
# 在Isabelle中运行
isabelle jedit test_theories/*.thy

# 手动观察Sledgehammer行为
# 记录reconstruction失败
```

**工作量**: 📝 **半天**（但效果有限）

---

## 📊 时间和收益对比

| 方案 | 工作量 | 预期Integration Bugs | 推荐度 |
|------|--------|---------------------|--------|
| **完整实施** | 6-10天 | 20-50个 | ⭐⭐⭐ |
| **混合测试（方案A）** | 2-3天 | 5-15个 | ⭐⭐⭐⭐⭐ |
| **只测Reconstruction（方案B）** | 1-2天 | 3-10个 | ⭐⭐⭐⭐ |
| **使用现有工具（方案C）** | 半天 | 1-3个 | ⭐⭐ |

---

## 🎯 推荐方案

### 如果时间充裕（>5天）

➡️ **完整实施**
- 完全按照Integration Bug测试架构
- 最大化学术价值
- 可以发现大量Integration bugs

### 如果时间有限（2-3天）⭐ **推荐**

➡️ **混合测试（方案A）**
- 保留已有的139个Prover bugs成果
- 添加小规模Integration测试
- 找到一些真正的Integration bugs
- 可以诚实地说：
  - "我们发现了139个Prover bugs"
  - "我们还发现了X个Integration bugs"

### 如果时间很紧（1-2天）

➡️ **只测试Reconstruction（方案B）**
- 最核心的Integration测试
- 工作量可控
- 至少可以说测试了Integration层

---

## 📝 实施步骤（混合测试方案）

### Day 1: 准备

**上午** (2小时):
```bash
# 1. 创建20个简单的.thy文件
cd test_theories
# 使用模板创建theory文件

# 2. 测试Isabelle调用
isabelle process -e 'use_thy "Test1";'
```

**下午** (2-3小时):
```python
# 3. 创建isabelle_interface.py
class IsabelleInterface:
    def run_theory(self, thy_file):
        """运行Isabelle theory"""
        cmd = ['isabelle', 'process', '-e', f'use_thy "{thy_file}";']
        # ...
```

### Day 2: 集成

**上午** (2-3小时):
```python
# 4. 修改main.py支持.thy模式
if args.thy_mode:
    result = isabelle_interface.run_theory(mutant_file)
else:
    result = crash_oracle.check(prover_path, mutant_file)
```

**下午** (2-3小时):
```python
# 5. 完善reconstruction_oracle.py
# 实现真正的proof reconstruction测试
```

### Day 3: 测试

**全天**:
```bash
# 6. 运行Integration测试
./integration_bug_test.sh

# 7. 收集和分析结果
python analyze_integration_bugs.py
```

---

## ✅ 总结

### 问题：只需要写一个测试脚本吗？

**答案**: ❌ **远不止如此！**

**需要做的**:
1. ✅ 准备.thy文件（不只是.p文件）
2. ✅ 创建Isabelle接口模块
3. ✅ 修改Fuzzer架构
4. ✅ 完善Reconstruction Oracle
5. ✅ 配置Isabelle环境
6. ✅ 编写新的测试脚本
7. ✅ 调试和验证

**工作量**:
- 最少: 1-2天（简化方案）
- 推荐: 2-3天（混合测试）
- 完整: 6-10天（完全实施）

**是否值得**:
- ✅ 如果想找真正的Integration bugs：值得！
- ⚠️ 如果时间紧张：可以用简化方案
- ❌ 如果只有几小时：建议不做

**当前建议**:
- 保留已有的139个Prover bugs（非常有价值）
- 如果有时间，添加小规模Integration测试（2-3天）
- 诚实说明测试的范围和发现的bug类型

