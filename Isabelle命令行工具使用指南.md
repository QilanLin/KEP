# 🔧 Isabelle命令行工具使用指南

**日期**: 2025年11月20日  
**目的**: 使用Isabelle命令行工具批量处理theory文件并导出TPTP/SMT-LIB文件

---

## ✅ 发现

### Isabelle确实有命令行工具！

- **命令位置**: `/opt/homebrew/bin/isabelle` (已在PATH中)
- **版本**: Isabelle2025
- **状态**: ✅ 已安装并可用

---

## 📋 主要命令行工具

### 1. `isabelle build` - 构建会话

**用途**: 构建Isabelle会话，处理theory文件

**基本语法**:
```bash
isabelle build [OPTIONS] [SESSIONS ...]
```

**常用选项**:
- `-d DIR` - 包含会话目录
- `-e` - 从会话规范导出文件到文件系统
- `-o OPTION` - 覆盖Isabelle系统选项
- `-v` - 详细输出
- `-j INT` - 并行任务数

**示例**:
```bash
# 注意：isabelle build需要ROOT文件来定义会话
# 如果只有.thy文件，应该使用 isabelle process

# 构建会话（需要ROOT文件）
isabelle build -d . My_Session

# 构建并导出文件（需要ROOT文件）
isabelle build -d . -e My_Session
```

### 2. `isabelle process` - 批处理模式

**用途**: 在批处理模式下运行Isabelle ML进程

**基本语法**:
```bash
isabelle process [OPTIONS]
```

**常用选项**:
- `-T THEORY` - 加载theory文件
- `-e ML_EXPR` - 在启动时评估ML表达式
- `-f ML_FILE` - 在启动时评估ML文件
- `-d DIR` - 包含会话目录
- `-o OPTION` - 覆盖Isabelle系统选项

**示例**:
```bash
# 处理theory文件 ✅ 推荐 - 不需要ROOT文件
isabelle process -T Test_Sledgehammer -d .

# 运行ML表达式（设置导出目录并处理theory）
isabelle process -d . -e "
Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir \"/path/to/export\";
use_thy \"Test_Sledgehammer\";
"
```

**⚠️ 重要**: `isabelle process` 不需要ROOT文件，可以直接处理.thy文件！

---

## 🎯 批量导出方案

### 方案1: 使用 `isabelle build` 批量构建 ✅ **推荐**

```bash
#!/bin/bash
# 批量构建多个theory文件

for thy in *.thy; do
    base=$(basename "$thy" .thy)
    echo "构建 $base..."
    isabelle build -d . "$base"
done
```

**优点**:
- ✅ 简单直接
- ✅ 自动处理依赖
- ✅ 支持并行构建

### 方案2: 使用 `isabelle process` 批处理

```bash
#!/bin/bash
# 使用process命令批处理

isabelle process -T Test_Sledgehammer -d . -e '
    Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir "/path/to/export";
    use_thy "Test_Sledgehammer";
'
```

**优点**:
- ✅ 可以执行ML代码
- ✅ 更灵活的控制
- ✅ 可以设置配置选项

### 方案3: 编写ML脚本批量处理

创建ML脚本文件 `batch_export.ML`:

```ml
val export_dir = "/path/to/export"
val _ = Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir export_dir

fun process_thy thy_name =
  let val thy = thy_name ^ ".thy"
  in use_thy thy_name end

val theories = ["Test_Sledgehammer", "Test_SMT_Method"]
val _ = map process_thy theories
```

然后运行:
```bash
isabelle process -f batch_export.ML -d .
```

---

## 🛠️ 实际使用示例

### 示例1: 批量导出当前目录的所有theory文件

```bash
#!/bin/bash
# 批量导出脚本

EXPORT_DIR="sledgehammer_export"
mkdir -p "$EXPORT_DIR"

# 设置导出目录配置
cat > export_config.ML << EOF
val _ = Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir "$EXPORT_DIR"
val _ = Config.put Sledgehammer_Prover_ATP.atp_proof_dest_dir "$EXPORT_DIR"
EOF

# 批量处理所有.thy文件
for thy in *.thy; do
    base=$(basename "$thy" .thy)
    echo "处理 $base..."
    isabelle build -d . "$base" 2>&1 | tail -5
done

echo "✅ 完成！导出文件在 $EXPORT_DIR/"
ls -lh "$EXPORT_DIR"/*.p 2>/dev/null | wc -l | xargs echo "TPTP文件数量:"
```

### 示例2: 使用process命令处理单个文件

```bash
#!/bin/bash
# 使用process命令处理

EXPORT_DIR="/Users/linqilan/Downloads/KEP AWS/sledgehammer_export"

isabelle process -d . -e "
Config.put Sledgehammer_Prover_ATP.atp_problem_dest_dir \"$EXPORT_DIR\";
Config.put Sledgehammer_Prover_ATP.atp_proof_dest_dir \"$EXPORT_DIR\";
use_thy \"Test_Sledgehammer\";
"
```

---

## 📊 优势对比

### 命令行 vs GUI

| 特性 | 命令行 | GUI |
|------|--------|-----|
| 批处理 | ✅ 优秀 | ❌ 需要手动操作 |
| 自动化 | ✅ 容易脚本化 | ❌ 困难 |
| 无需图形界面 | ✅ 支持 | ❌ 需要 |
| 服务器环境 | ✅ 适合 | ❌ 不适合 |
| 并行处理 | ✅ 支持 | ⚠️ 有限 |

---

## 🎯 对于我们的研究

### 使用命令行的优势

1. **批量提取种子**: 
   - 可以批量处理多个theory文件
   - 自动收集所有导出的TPTP文件

2. **自动化流程**: 
   - 编写脚本自动化整个提取流程
   - 可以定期运行或集成到CI/CD

3. **扩展性强**: 
   - 可以轻松扩展到更多文件
   - 可以从AFP下载并批量处理

4. **可编程**: 
   - 可以集成到Python脚本
   - 可以与其他工具配合使用

---

## 📝 下一步建议

### 1. 测试基本命令

```bash
# 测试构建
isabelle build -d . Test_Sledgehammer

# 检查导出文件
ls -lh sledgehammer_export/
```

### 2. 创建批量处理脚本

使用提供的脚本模板创建自己的批量处理脚本。

### 3. 批量处理更多文件

从Isabelle标准库或AFP下载更多theory文件进行批量处理。

---

## 📚 参考资源

- Isabelle系统手册（命令行部分）
- `isabelle help` - 查看帮助信息
- `isabelle build --help` - 查看build命令帮助
- `isabelle process --help` - 查看process命令帮助

---

**创建时间**: 2025-11-20  
**状态**: ✅ 命令行工具可用，可以开始批量处理

