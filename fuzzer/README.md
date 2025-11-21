# Isabelle Sledgehammer Fuzzer

Isabelle/HOL Sledgehammer接口模糊测试框架 - 用于发现ATP/SMT solver的bug和异常行为。

## 📋 项目概述

本项目是一个专门针对Isabelle/HOL Sledgehammer接口的fuzzing框架，通过自动生成变异测试用例来发现外部prover（如Z3、cvc5）的崩溃、超时和结果不一致等问题。

### 核心特性

- ✅ **TPTP解析器**: 解析和处理TPTP格式文件
- ✅ **Token级别变异器**: 多种变异策略（数值、符号、操作符等）
- ✅ **Crash/Hang Oracle**: 检测prover崩溃和超时
- ✅ **Differential Oracle**: 检测多个prover结果不一致
- ✅ **统计和日志**: 完整的测试统计和日志记录
- ✅ **批量测试**: 支持大规模自动化测试

## 📁 项目结构

```
fuzzer/
├── parser/                   # TPTP解析器
│   └── tptp_parser.py       # TPTP文件解析
├── mutator/                  # 变异引擎
│   └── token_mutator.py     # Token级别变异
├── oracle/                   # Oracle实现
│   ├── crash_oracle.py      # Crash/Hang检测
│   └── differential_oracle.py  # 差异检测
├── utils/                    # 工具函数
│   ├── stats.py             # 统计分析
│   ├── logger.py            # 日志记录
│   └── __init__.py
├── main.py                   # 主程序入口
├── 批量测试脚本.sh          # 大规模测试脚本
├── 分析结果.py              # 结果分析工具
└── README.md                 # 本文件
```

## 🚀 快速开始

### 前置要求

- Python 3.8+
- Z3 或 cvc5（在PATH中）
- TPTP格式的种子文件

### 基本使用

```bash
# 进入fuzzer目录
cd fuzzer

# 运行基本测试
python3 main.py \
    --seed-dir ../sledgehammer_export \
    --output-dir ./results \
    --max-seeds 5 \
    --num-mutants 10 \
    --timeout 5.0
```

### 大规模测试

```bash
# 使用批量测试脚本
./批量测试脚本.sh
```

### 分析结果

```bash
# 分析测试结果
python3 分析结果.py ./results
```

## 📖 详细文档

### 命令行选项

```bash
python3 main.py --help
```

**参数说明**:

- `--seed-dir`: 种子文件目录（默认: `../sledgehammer_export`）
- `--output-dir`: 输出目录（默认: `./fuzzer_results`）
- `--timeout`: 超时时间（秒，默认: 5.0）
- `--num-mutants`: 每个种子生成的变异体数（默认: 10）
- `--max-seeds`: 最大处理种子数（默认: 10）

### 输出结构

```
results/
├── logs/                    # 日志文件
│   └── fuzzer_YYYYMMDD_HHMMSS.log
├── stats/                   # 统计信息
│   └── stats.json
├── bug_*.json              # Bug报告
└── differential_*.json     # 差异报告
```

## 🔧 核心组件

### 1. TPTP解析器 (`parser/tptp_parser.py`)

解析TPTP格式文件，提取公式和类型信息。

```python
from parser.tptp_parser import TPTPParser

parser = TPTPParser()
formulas = parser.parse(content)
```

### 2. Token变异器 (`mutator/token_mutator.py`)

生成多种变异策略的测试用例。

```python
from mutator.token_mutator import TokenMutator

mutator = TokenMutator()
mutants = mutator.generate_mutants(seed_content, count=10)
```

**变异策略**:
- 数值替换
- 符号替换
- 操作符替换
- 括号操作
- 字符串变异

### 3. Crash Oracle (`oracle/crash_oracle.py`)

检测prover崩溃和超时。

```python
from oracle.crash_oracle import CrashOracle

oracle = CrashOracle(timeout=5.0)
result = oracle.check(prover_path, test_file)
```

### 4. Differential Oracle (`oracle/differential_oracle.py`)

检测多个prover结果不一致。

```python
from oracle.differential_oracle import DifferentialOracle

oracle = DifferentialOracle()
diff_result = oracle.check(prover_results)
```

### 5. 统计和日志工具 (`utils/`)

自动收集统计信息和记录日志。

```python
from utils.stats import StatsCollector
from utils.logger import FuzzerLogger

logger = FuzzerLogger(log_dir="./logs")
stats = StatsCollector(output_dir="./stats")
```

## 📊 使用示例

### 示例1: 基本测试

```bash
# 测试5个种子，每个生成10个变异体
python3 main.py --max-seeds 5 --num-mutants 10
```

### 示例2: 大规模测试

```bash
# 使用批量测试脚本
./批量测试脚本.sh
```

### 示例3: 结果分析

```python
from utils.stats import analyze_results

results = analyze_results('./results')
print(f"总Bug数: {results['total_bugs']}")
print(f"总差异数: {results['total_differentials']}")
```

### 示例4: 自定义配置

```python
from main import Fuzzer

config = {
    'seed_dir': '../seeds',
    'output_dir': './custom_results',
    'timeout': 10.0,
    'num_mutants': 20,
    'max_seeds': 50
}

fuzzer = Fuzzer(config)
fuzzer.run()
```

## 🧪 测试

### 运行组件测试

```bash
# 测试TPTP解析器
python3 parser/tptp_parser.py

# 测试变异器
python3 mutator/token_mutator.py

# 测试Oracle
python3 oracle/crash_oracle.py

# 测试工具
python3 utils/stats.py
python3 utils/logger.py
```

### 端到端测试

```bash
# 小规模测试
python3 main.py --max-seeds 2 --num-mutants 3

# 中等规模测试
python3 main.py --max-seeds 10 --num-mutants 10

# 大规模测试
./批量测试脚本.sh
```

## 📈 统计报告

### 查看统计信息

```bash
# 查看JSON统计文件
cat results/stats/stats.json | python3 -m json.tool

# 使用分析工具
python3 分析结果.py ./results
```

### 统计内容

- 总测试数
- 崩溃数
- 超时数
- 差异数
- 执行时间
- Bug类型分布
- Prover使用统计

## 🔍 故障排查

### 常见问题

1. **Prover未找到**
   - 确保Z3或cvc5在PATH中
   - 检查`which z3`或`which cvc5`

2. **种子文件不存在**
   - 检查`--seed-dir`路径
   - 确保种子文件是`.p`格式

3. **权限错误**
   - 确保输出目录可写
   - 检查脚本执行权限

### 调试技巧

```bash
# 启用详细日志
# 日志文件在输出目录的logs/子目录中

# 查看最新日志
tail -f results/logs/fuzzer_*.log

# 检查统计信息
cat results/stats/stats.json
```

## 🛠️ 开发

### 添加新的变异策略

编辑`mutator/token_mutator.py`，在`TokenMutator`类中添加新的变异方法。

### 添加新的Oracle

创建新的oracle文件，实现类似`crash_oracle.py`的接口。

### 扩展统计功能

编辑`utils/stats.py`，添加新的统计收集方法。

## 📚 相关文档

- [项目完整进度报告](../研究进展完整总结.md)
- [Week 3-4工作计划](../Week3-4工作计划.md)
- [下一步行动计划](../下一步行动计划.md)

## 📝 许可证

本项目为研究项目，仅供学习和研究使用。

## 👥 作者

Qilan Lin - KEP AWS Project Variant 3

## 📅 更新历史

- **2025-11-20**: MVP框架完成，工具集成
- **2025-11-20**: 添加统计和日志功能
- **2025-11-20**: 创建批量测试和分析工具

---

**当前版本**: 0.1.0 (MVP)  
**状态**: ✅ 可用，持续开发中
