# Week 5-7 新功能使用指南

## 🚀 快速开始

### 使用AST级别变异器

```bash
# 基本使用
python3 main.py --use-ast-mutator --max-seeds 50 --num-mutants 20

# 与并行处理结合
python3 main.py --use-ast-mutator --use-parallel --num-workers 4
```

### 使用重构Oracle

```bash
# 基本使用
python3 main.py --use-reconstruction-oracle --max-seeds 50

# 自定义Isabelle路径和超时
python3 main.py \
    --use-reconstruction-oracle \
    --isabelle-path isabelle \
    --reconstruction-timeout 60.0
```

### 组合使用

```bash
# 使用AST变异器 + 重构Oracle + 可视化
python3 main.py \
    --use-ast-mutator \
    --use-reconstruction-oracle \
    --max-seeds 100 \
    --num-mutants 15 \
    --generate-viz
```

## 📊 功能对比

### Token vs AST变异器

| 场景 | 推荐使用 |
|------|---------|
| 快速测试 | Token级别（默认） |
| 深度测试 | AST级别 |
| 大规模测试 | 组合使用 |

### Oracle对比

| Oracle | 启用方式 | 检测内容 |
|--------|---------|---------|
| Crash/Hang | 默认 | 崩溃、超时 |
| Differential | 默认 | Prover结果不一致 |
| Reconstruction | `--use-reconstruction-oracle` | 重构失败 |

## ⚙️ 配置选项

### AST变异器选项
- `--use-ast-mutator`: 启用AST级别变异器
- `--random-seed SEED`: 设置随机种子（可重复性）

### 重构Oracle选项
- `--use-reconstruction-oracle`: 启用重构Oracle
- `--isabelle-path PATH`: Isabelle可执行路径
- `--reconstruction-timeout SECONDS`: 重构超时时间

## 📝 测试

```bash
# 运行单元测试
python3 tests/test_ast_mutator.py
python3 tests/test_reconstruction_oracle.py

# 运行集成测试
python3 tests/test_integration.py
```

## 🎯 预期效果

### AST变异器
- 产生更多语法有效的变异体
- 更深入的变异（结构级别）
- 预期更高的bug发现率

### 重构Oracle
- 发现"证明找到但重构失败"的问题
- 这是Sledgehammer的常见bug类型
- 提供详细的失败分类

