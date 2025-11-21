# 🔧 Isabelle命令行工具指南

**日期**: 2025年11月20日  
**目的**: 使用Isabelle命令行工具批量处理theory文件并导出TPTP/SMT-LIB文件

---

## ✅ 发现

### Isabelle确实有命令行工具！

- **命令位置**: `/opt/homebrew/bin/isabelle`
- **版本**: Isabelle2025
- **状态**: ✅ 已安装并可用

---

## 📋 Isabelle命令行工具

### 主要命令

根据Isabelle文档，主要的命令行工具包括：

1. **`isabelle build`** - 构建Isabelle会话
   - 用于构建theory文件
   - 支持批处理模式

2. **`isabelle process`** - 批处理模式运行Isabelle进程
   - 可以在命令行中处理theory文件
   - 适合自动化任务

3. **`isabelle jedit`** - 启动jEdit界面
   - 命令行启动GUI

4. **`isabelle server`** - 启动Isabelle服务器
   - 支持TCP连接
   - 允许其他程序与Isabelle交互

5. **`isabelle tool`** - 访问各种工具
   - 列出可用工具
   - 运行特定工具

---

## 🎯 批量导出方案

### 方案1: 使用 `isabelle build` 批量处理

```bash
# 构建所有theory文件，触发Sledgehammer
isabelle build Test_Sledgehammer
```

### 方案2: 使用 `isabelle process` 批处理

```bash
# 处理theory文件
isabelle process -e 'use_thy "Test_Sledgehammer";'
```

### 方案3: 编写ML脚本批量处理

创建ML脚本，使用`Sledgehammer_Export`批量导出：

```bash
# 运行ML脚本
isabelle process -e 'use_thy "Test_Sledgehammer"; Sledgehammer_Export.export_all();'
```

### 方案4: 使用Python/Shell脚本自动化

创建一个脚本，批量处理多个theory文件：

```bash
#!/bin/bash
for thy in *.thy; do
    echo "Processing $thy..."
    isabelle build "$(basename $thy .thy)"
done
```

---

## 📝 测试步骤

### 步骤1: 测试基本命令

```bash
# 查看可用工具
isabelle tool list

# 查看帮助
isabelle help

# 测试构建
isabelle build Test_Sledgehammer
```

### 步骤2: 测试批量导出

创建测试脚本，批量处理theory文件并收集导出的文件。

### 步骤3: 检查导出文件

运行后检查`sledgehammer_export/`目录是否有新文件生成。

---

## 🛠️ 优势

### 使用命令行的优势

1. **批处理**: 可以批量处理多个theory文件
2. **自动化**: 可以编写脚本自动化整个流程
3. **无需GUI**: 不需要图形界面，适合服务器环境
4. **可编程**: 可以集成到其他工具或工作流中

---

## 💡 建议

### 对于我们的研究

1. **批量提取种子**: 使用命令行批量处理多个theory文件
2. **自动化流程**: 编写脚本自动化整个提取流程
3. **扩展性强**: 可以轻松扩展到更多文件

---

## 📚 参考资源

- Isabelle系统手册（命令行部分）
- `isabelle help` - 查看帮助信息
- `isabelle tool list` - 列出可用工具

---

**创建时间**: 2025-11-20  
**下一步**: 测试使用命令行批量处理theory文件并导出TPTP/SMT-LIB文件

