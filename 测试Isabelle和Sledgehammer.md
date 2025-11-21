# 测试Isabelle和Sledgehammer指南

## Isabelle已成功安装 ✅

- **版本**: Isabelle2025
- **位置**: `/Applications/Isabelle2025.app`
- **命令行**: `/opt/homebrew/bin/isabelle`

## Sledgehammer验证方法

Sledgehammer不是独立的命令行工具，而是Isabelle的内部功能。验证方法：

### 方法1：使用Isabelle GUI

```bash
# 打开Isabelle GUI
isabelle jedit

# 或直接打开应用
open /Applications/Isabelle2025.app
```

在GUI中：
1. 创建或打开一个.thy文件
2. 输入一个需要证明的lemma
3. 使用 `apply sledgehammer`
4. 观察Sledgehammer是否工作

### 方法2：使用Isabelle批处理模式

```bash
# 在test_isabelle_sledgehammer.thy所在目录运行
isabelle build -D . Test_Sledgehammer
```

### 方法3：查找导出功能

Sledgehammer的导出功能可能在以下位置：
1. **ML脚本**: `/Applications/Isabelle2025.app/src/HOL/Tools/Sledgehammer/`
2. **文档**: `/Applications/Isabelle2025.app/doc/sledgehammer.pdf`

可能的导出方法：
- 在ML中使用 `Sledgehammer_Export.export_goal`
- 使用Isabelle的批处理API
- 从Isabelle的输出日志中解析

### 方法4：创建测试ML脚本

创建 `export_test.ML`:
```ml
(* export_test.ML *)
val goal = Syntax.read_prop @{context} "x + 0 = x"
val result = Sledgehammer_Export.export goal
```

## 推荐测试流程

1. **打开Isabelle GUI**:
   ```bash
   isabelle jedit
   ```

2. **加载测试文件**: 打开 `test_isabelle_sledgehammer.thy`

3. **观察Sledgehammer输出**: 
   - 查看是否调用外部prover
   - 查看生成的SMT-LIB/TPTP文件位置（可能在临时目录）

4. **查找导出API**:
   - 查看Sledgehammer的ML源码
   - 查找 `export` 相关的函数

## 备用方案准备

如果无法直接导出，准备以下备用方案：

### 方案A：从Isabelle日志提取
- 启用详细日志模式
- 从日志中解析生成的SMT-LIB内容

### 方案B：编写ML脚本
- 直接调用Sledgehammer的内部API
- 使用 `Sledgehammer_Export` 模块

### 方案C：使用AFP已有的测试集
- 从AFP下载session
- 查找是否有预导出的SMT-LIB文件

### 方案D：手工创建种子
- 创建10-20个简单的SMT-LIB文件作为初始种子
- 从这些开始fuzzing，后续再扩展

## 下一步

1. 打开Isabelle GUI测试Sledgehammer
2. 查看Sledgehammer的文档和源码
3. 如果找不到导出命令，立即准备备用方案
4. 不要等待太长时间，MVP可以用手工种子开始

