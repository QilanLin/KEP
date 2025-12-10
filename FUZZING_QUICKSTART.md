# 🚀 Fuzzing Quickstart Guide

**您现在已经拥有完整的Fuzzing基础设施！**

---

## ✅ 您现在拥有什么

```
完整的Fuzzing工具链:
├─ AST Mutator (ast_mutator.py)          ✅
├─ Fuzzing Campaign (fuzzing_campaign.py) ✅
├─ Improved Oracle (sledgehammer_oracle.py) ✅
├─ Bug Verifier (bug_verifier.py)        ✅
├─ Seed Theories (5个高质量seeds)       ✅
└─ 实施计划文档                          ✅
```

---

## 🎯 立即开始 (5分钟测试)

### Step 1: 验证环境

```bash
cd "/Users/linqilan/Downloads/KEP AWS"

# 检查Isabelle
isabelle version

# 检查Python
python3 --version
```

### Step 2: 测试AST Mutator

```bash
cd fuzzer

# 生成5个mutations
python3 -c "
from ast_mutator import IsabelleTheoryMutator

mutator = IsabelleTheoryMutator()
mutations = mutator.mutate_theory('../seed_theories/Seed_Basic_Arithmetic.thy', num_mutations=5)

print(f'✅ Generated {len(mutations)} mutations')
for i, m in enumerate(mutations, 1):
    print(f'{i}. {m.mutation_type.value}: {m.description}')
"
```

**预期输出**: 应该看到5个mutations生成

### Step 3: 运行Mini Campaign (10分钟)

```bash
# 运行一个小型campaign
python3 fuzzing_campaign.py \
  --campaign-name "test_run" \
  --seed-dir ../seed_theories \
  --output-dir test_fuzzing_results \
  --mutations-per-seed 5 \
  --timeout 60
```

**预期输出**:
```
✅ Generated 25 mutations (5 seeds × 5 mutations)
✅ Tested 25 mutations
✅ Found X bugs
✅ Campaign complete
```

---

## 📋 完整Workflow (正式运行)

### Phase 1: 准备更多Seeds (推荐)

```bash
cd seed_theories

# 你已经有5个seeds了:
ls -la
# Seed_Basic_Arithmetic.thy
# Seed_List_Operations.thy
# Seed_Set_Operations.thy
# Seed_Logic_Formulas.thy
# Seed_Inductive_Proofs.thy

# 建议再添加5-10个:
# - Seed_Higher_Order_Functions.thy
# - Seed_Type_Classes.thy
# - Seed_Record_Types.thy
# - Seed_Datatype_Definitions.thy
# - Seed_Complex_Lemmas.thy
```

**可以从现有test_theories/复制并修改**:
```bash
# 例如
cp ../test_theories/Test_Functions.thy Seed_Functions.thy
# 然后编辑Seed_Functions.thy
```

### Phase 2: 运行Large Scale Campaign

```bash
cd fuzzer

# 正式的大规模campaign
python3 fuzzing_campaign.py \
  --campaign-name "sledgehammer_fuzzing_v1" \
  --seed-dir ../seed_theories \
  --output-dir ../fuzzing_results \
  --mutations-per-seed 20 \
  --verify-bugs \
  --timeout 120
```

**参数说明**:
- `mutations-per-seed 20`: 每个seed生成20个mutations
- `verify-bugs`: 用Mirabelle验证发现的bugs
- `timeout 120`: 每个test最多120秒

**预期运行时间**:
- 10 seeds × 20 mutations = 200 tests
- ~2-3分钟/test = 6-10小时

### Phase 3: 分析结果

```bash
cd fuzzing_results

# 查看统计
cat sledgehammer_fuzzing_v1_stats.json

# 查看发现的bugs
ls bugs/
```

---

## 📊 理解输出

### Campaign Stats (sledgehammer_fuzzing_v1_stats.json)

```json
{
  "campaign_name": "sledgehammer_fuzzing_v1",
  "seed_theories": 10,
  "mutations_generated": 200,
  "mutations_tested": 200,
  "bugs_found": 15,
  "bugs_verified": 8,
  "false_positives": 7,
  "unique_error_types": 5,
  "mutation_types_used": 10,
  "bug_finding_rate": 0.075,
  "verification_precision": 0.533
}
```

**关键指标**:
- `bug_finding_rate`: 发现bugs的比率 (越高越好)
- `verification_precision`: 真实bugs占比 (越高越好)
- `unique_error_types`: 发现的不同bug类型

### Bug Reports (bugs/*.json)

每个bug一个JSON文件:
```json
{
  "bug_type": "proof_reconstruction_failed",
  "description": "Sledgehammer proof重构失败",
  "thy_file": "mutations/Seed_Basic_Arithmetic_mut0042_negate_formula.thy",
  "mutation_type": "negate_formula",
  "execution_time": 45.2,
  "isabelle_output": "..."
}
```

---

## 🎓 进阶用法

### 只测试特定类型的Mutations

```python
from ast_mutator import MutationType, IsabelleTheoryMutator
from fuzzing_campaign import FuzzingCampaign

# 只测试逻辑相关的mutations
logical_mutations = [
    MutationType.FLIP_QUANTIFIER,
    MutationType.NEGATE_FORMULA,
    MutationType.SWAP_CONJUNCTION
]

campaign = FuzzingCampaign("logical_only")
stats = campaign.run_campaign(
    mutations_per_seed=30,
    mutation_types=logical_mutations
)
```

### Batch Processing

```bash
# 运行多个campaigns
for seed_count in 5 10 20; do
  python3 fuzzing_campaign.py \
    --campaign-name "campaign_${seed_count}_seeds" \
    --mutations-per-seed 20 \
    --seed-dir ../seed_theories
done
```

---

## 📈 评估和对比

### Baseline: Random Testing

创建一个random baseline:
```python
# random_baseline.py
import random
import string

def generate_random_theory(n=10):
    """生成随机theory (不使用mutation)"""
    content = "theory Random_Test imports Main begin\n"
    
    for i in range(n):
        # 随机生成lemma
        var1 = random.choice(string.ascii_lowercase)
        var2 = random.choice(string.ascii_lowercase)
        op = random.choice(['+', '*', '-'])
        
        content += f'lemma "({var1}::{random.choice(['nat', 'int'])}) {op} {var2} = {var2} {op} {var1}" by auto\n'
    
    content += "end"
    return content

# 生成100个random theories并测试
# 对比发现bugs的数量
```

### 对比指标

```python
results = {
    'mutation_fuzzing': {
        'tests': 200,
        'bugs_found': 15,
        'time': 600  # minutes
    },
    'random_testing': {
        'tests': 200,
        'bugs_found': 3,
        'time': 400
    }
}

# Bug finding rate
mutation_rate = 15 / 200  # 7.5%
random_rate = 3 / 200     # 1.5%

print(f"Mutation fuzzing is {mutation_rate / random_rate:.1f}x more effective")
# Output: "Mutation fuzzing is 5.0x more effective"
```

---

## 🐛 Troubleshooting

### 问题1: Mutations生成失败

```bash
# 检查seed theory是否valid
cd seed_theories
isabelle build -d . -b Seed_Basic_Arithmetic
```

### 问题2: Timeout太多

```bash
# 增加timeout
python3 fuzzing_campaign.py --timeout 300  # 5分钟
```

### 问题3: False positives太多

```python
# Oracle已经改进，但如果还是太多:
# 调整Oracle的detection threshold
# 或者只关注verified bugs
```

---

## ✅ 成功标准

### 你的项目成功如果

**最低要求** (60-70分):
- ✅ 生成了 >100 mutations
- ✅ 测试了所有mutations
- ✅ 有基本的bug报告
- ✅ 有简单的评估

**良好完成** (70-85分):
- ✅ 生成了 >500 mutations
- ✅ 找到了 >5 个bugs
- ✅ 用Mirabelle验证了bugs
- ✅ 有baseline对比

**优秀完成** (85-95分):
- ✅ 生成了 >1000 mutations
- ✅ 找到了 >10 个真实bugs
- ✅ 证明了fuzzer effectiveness
- ✅ 有完整的evaluation

**完美完成** (95-100分):
- ✅ 上述所有 + Coverage分析
- ✅ 与其他fuzzer对比
- ✅ 公开发布dataset
- ✅ 高质量的报告和presentation

---

## 📝 报告建议

### 一定要包含的

1. **Methodology Section**
   ```
   3.2 Integration Fuzzing
   
   We developed an AST-based fuzzer for Isabelle theories with 10 
   mutation operators:
   - FLIP_QUANTIFIER: ∀ ↔ ∃ 
   - NEGATE_FORMULA: P → ¬P
   - ...
   
   Each mutation is designed to test specific aspects of the 
   Sledgehammer interface...
   ```

2. **Implementation Details**
   ```
   4.1 Fuzzer Architecture
   
   Our fuzzer consists of three components:
   - AST Parser: extracts lemmas from theories
   - Mutation Engine: applies 10 mutation operators
   - Test Harness: feeds mutations to Sledgehammer
   
   [Include code snippets and diagrams]
   ```

3. **Evaluation Results**
   ```
   5.2 Fuzzing Results
   
   We ran a campaign with 200 mutations and found:
   - 15 potential bugs (7.5% bug finding rate)
   - 8 verified bugs (53.3% precision)
   - 5 unique error types
   
   [Include tables and graphs]
   ```

4. **Effectiveness Comparison**
   ```
   5.3 Comparison with Baseline
   
   Our mutation-based fuzzer found 5x more bugs than random 
   testing with the same number of tests.
   
   [Include comparison table]
   ```

---

## 🎯 下一步行动

### 今天 (现在！)

```bash
# 1. 测试mini campaign (5分钟)
cd fuzzer
python3 fuzzing_campaign.py \
  --campaign-name "quick_test" \
  --seed-dir ../seed_theories \
  --mutations-per-seed 3 \
  --timeout 60

# 2. 检查结果
ls test_fuzzing_results/
cat test_fuzzing_results/quick_test_stats.json
```

### 明天

1. 创建3-5个更多的seed theories
2. 运行medium scale campaign (50 mutations)
3. 分析初步结果

### 本周

1. 运行large scale campaign (200+ mutations)
2. 用Mirabelle验证所有bugs
3. 开始baseline对比

### 下周

1. 完成evaluation
2. 写报告的methodology和implementation sections
3. 准备bug reports

---

## 💬 需要帮助？

如果遇到问题:

1. **检查日志**: `fuzzing_results/fuzzing_campaign.log`
2. **查看文档**: `完整Fuzzing方案实施计划.md`
3. **Debug single mutation**:
   ```python
   # 单独测试一个mutation
   from oracle.sledgehammer_oracle import SledgehammerOracle
   oracle = SledgehammerOracle()
   result = oracle.check_theory_file("mutations/some_mutation.thy")
   ```

---

**🚀 准备好了吗？开始您的第一个fuzzing campaign！**

```bash
cd fuzzer
python3 fuzzing_campaign.py --mutations-per-seed 5
```

