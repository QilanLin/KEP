# 📥 AFP下载指南

**问题**: AFP仓库URL不正确，直接克隆可能失败

---

## ✅ 推荐的下载方法

### **方法1: 使用Isabelle的AFP工具（最推荐）** ✅

Isabelle提供了内置的AFP下载工具：

```bash
# 下载AFP组件
isabelle components -a

# 或更新AFP组件
isabelle components -u
```

**优点**:
- ✅ 官方支持的方法
- ✅ 自动下载和配置
- ✅ 与Isabelle版本匹配

**位置**: AFP会下载到Isabelle的组件目录中

---

### **方法2: 从官方网站下载tar包** ✅

1. 访问AFP官方网站:
   ```
   https://www.isa-afp.org/download.html
   ```

2. 下载最新的tar包:
   ```
   afp-current.tar.gz
   ```

3. 解压到项目目录:
   ```bash
   tar -xzf afp-current.tar.gz
   mv afp-devel /path/to/project/
   ```

**优点**:
- ✅ 稳定可靠
- ✅ 包含完整历史
- ✅ 不依赖Git

---

### **方法3: 使用Isabelle的AFP构建工具** ✅

```bash
# 构建AFP的所有sessions
isabelle afp_build -D /path/to/afp
```

**前提**: 需要先通过方法1或2获取AFP

---

## ❌ 不推荐的方法

### **直接Git克隆** ❌

以下URL可能不可用：

- ❌ `https://github.com/isa-afp/afp-devel.git` (不存在)
- ❌ `https://foss.heptapod.net/isa-afp/afp-devel.git` (可能不可访问)

**原因**: AFP现在主要使用Mercurial，Git仓库可能是镜像，可能不稳定

---

## 💡 备选方案

### **如果不需要完整的AFP**

对于我们的研究（种子提取），不一定需要完整的AFP仓库：

1. **使用已提取的种子**: 我们已经有480个TPTP文件，足够开始fuzzing
2. **从Isabelle标准库提取**: 从Isabelle安装目录中的examples提取
3. **手工创建测试用例**: 创建10-20个手工种子文件

---

## 🎯 对于我们的研究

### **当前状态**

- ✅ **已有480个TPTP种子文件**: 足够开始MVP开发
- ⚠️ **AFP下载可选**: 不是必需的，可以在后续阶段添加

### **建议**

1. **立即**: 使用已有的480个种子文件开始MVP开发
2. **Week 3-4**: 如果需要更多种子，再尝试下载AFP
3. **Week 8-9**: 大规模测试时再考虑AFP

---

## 📝 总结

**推荐操作**:
1. ✅ 优先使用: `isabelle components -a`
2. ✅ 备选: 从官方网站下载tar包
3. ⏸️ 可选: 当前已有480个种子，AFP不是必需

**对于MVP开发**: 480个种子文件已经足够！

---

**更新日期**: 2025-11-20  
**状态**: AFP下载可选，不影响MVP开发

