# Week 1 环境搭建指南
## 立即行动项实施步骤

---

## 📋 **当前状态检查**

### 已检查的工具：
- ❌ Isabelle: 未安装
- ❌ Z3: 未安装  
- ❌ cvc5: 未安装
- ❌ pySMT: 未安装

---

## 🚀 **P0任务：核心工具安装（最高优先级）**

### **1. 安装Isabelle/HOL**

#### **macOS安装步骤**：

**选项A：使用Homebrew（推荐，最简单）**
```bash
# 1. 如果还没有Homebrew，先安装：
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# 2. 安装Isabelle
brew install --cask isabelle
```

**选项B：手动下载安装**
1. 访问：https://isabelle.in.tum.de/download.html
2. 下载 macOS 版本（推荐最新稳定版，如 Isabelle2024）
3. 解压到 `/Applications/Isabelle2024/`
4. 添加到PATH：
   ```bash
   echo 'export PATH="/Applications/Isabelle2024/bin:$PATH"' >> ~/.zshrc
   source ~/.zshrc
   ```

**验证安装**：
```bash
isabelle version
# 应该输出Isabelle版本号
```

#### **安装后下一步**：
1. 运行一次Isabelle：`isabelle jedit` 或使用图形界面
2. 测试Sledgehammer是否能运行

---

### **2. 验证Sledgehammer导出功能**

这是**最关键**的验证步骤！

#### **步骤1：运行一次Sledgehammer**

创建一个测试文件 `test_sledgehammer.thy`:
```isabelle
theory Test_Sledgehammer
imports Main
begin

lemma "x + 0 = x"
  by sledgehammer

end
```

在Isabelle中打开并运行，观察输出。

#### **步骤2：查找导出命令**

在Isabelle中尝试：
```bash
# 查找可能的导出命令
isabelle sledgehammer --help 2>&1 | head -20

# 或者搜索文档
isabelle doc sledgehammer
```

或者查看Isabelle源码中的导出功能：
```bash
# 如果Isabelle安装在标准位置
find /Applications/Isabelle* -name "*sledgehammer*" -type f | head -10
```

#### **步骤3：尝试导出SMT-LIB**

可能的命令（需要验证）：
```bash
# 选项1：如果sledgehammer_export存在
isabelle sledgehammer_export --format smt-lib test.thy

# 选项2：在Isabelle中使用ML脚本
# 创建export_test.ML文件并运行

# 选项3：从Isabelle日志中提取（如果命令不存在）
```

#### **备用方案准备**（如果导出命令不存在）：

**方案A：编写简单ML脚本**
```ml
(* export_smt.ML *)
fun export_smt goal = 
  let val problem = Sledgehammer_Export.export_goal goal
  in File.write (Path.explode "output.smt2") problem
  end
```

**方案B：使用Isabelle的批处理模式**
```bash
isabelle build -o system_heaps -v Test_Sledgehammer 2>&1 | grep -A 100 "SMT"
```

**方案C：从AFP已有的测试集中提取**
- AFP可能包含已导出的SMT-LIB文件
- 或从Isabelle的测试套件中提取

---

### **3. 安装Z3和cvc5**

#### **macOS安装（使用Homebrew）**：

```bash
# 安装Z3
brew install z3

# 安装cvc5
brew install cvc5

# 验证安装
z3 --version
cvc5 --version
```

#### **如果没有Homebrew，手动安装**：

**Z3**:
1. 访问：https://github.com/Z3Prover/z3/releases
2. 下载macOS版本
3. 解压并添加到PATH

**cvc5**:
1. 访问：https://github.com/cvc5/cvc5/releases
2. 下载macOS版本
3. 解压并添加到PATH

**验证安装**：
```bash
# 创建测试SMT-LIB文件 test.smt2
echo "(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)" > test.smt2

# 测试Z3
z3 test.smt2
# 应该输出: sat 或 unsat

# 测试cvc5
cvc5 test.smt2
# 应该输出: sat 或 unsat
```

---

## 🛠️ **P1任务：Python工具安装（高优先级）**

### **1. 安装pySMT**

```bash
# 确保有pip
python3 --version

# 安装pySMT
pip3 install pysmt

# 验证安装
python3 -c "import pysmt; print('pySMT版本:', pysmt.__version__)"
```

**测试pySMT解析SMT-LIB**：
```python
# test_parser.py
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import get_env

# 创建测试文件
smt_content = """
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
"""

with open("test_parse.smt2", "w") as f:
    f.write(smt_content)

# 尝试解析
parser = SmtLibParser()
try:
    script = parser.get_script_fname("test_parse.smt2")
    print("✅ pySMT可以成功解析SMT-LIB文件")
    print(f"找到 {len(script.commands)} 个命令")
except Exception as e:
    print(f"❌ 解析失败: {e}")
```

运行：
```bash
python3 test_parser.py
```

---

### **2. 下载AFP session测试**

#### **步骤1：检查网络连接**

```bash
# 测试AFP网站可访问性
curl -I https://www.isa-afp.org/ 2>&1 | head -3
```

#### **步骤2：下载一个小的AFP session**

```bash
# 方法1：使用git克隆整个AFP（较大，~500MB+）
cd ~/Downloads
git clone https://github.com/isa-afp/afp-devel.git
cd afp-devel/thys

# 选择一个小的session测试，例如：
# Collections 或 List-Index
cd Collections

# 方法2：只下载一个特定的session（更小）
# 访问 https://www.isa-afp.org/browser_info/current/
# 选择一个session下载
```

#### **步骤3：在Isabelle中加载session**

```bash
# 在Isabelle中打开AFP session
isabelle jedit -l Collections
```

**推荐的小sessions用于测试**：
- `List-Index`: 非常小，适合快速测试
- `Collections`: 中等大小，常用
- `AVL-Trees`: 经典数据结构

---

## ✅ **验证清单**

完成安装后，运行以下命令验证：

```bash
# P0验证
echo "=== P0验证 ==="
isabelle version && echo "✅ Isabelle已安装" || echo "❌ Isabelle未安装"
z3 --version 2>&1 | head -1 && echo "✅ Z3已安装" || echo "❌ Z3未安装"
cvc5 --version 2>&1 | head -1 && echo "✅ cvc5已安装" || echo "❌ cvc5未安装"

# P1验证
echo ""
echo "=== P1验证 ==="
python3 -c "import pysmt; print('✅ pySMT已安装')" 2>&1 || echo "❌ pySMT未安装"
ls -d ~/Downloads/afp-devel 2>/dev/null && echo "✅ AFP已下载" || echo "⚠️ AFP未下载（可选）"
```

---

## 📝 **记录验证结果**

创建一个验证报告文件，记录每个步骤的结果：

```bash
# 创建验证报告
cat > Week1_验证报告.md << 'EOF'
# Week 1 验证报告
日期: $(date)

## 工具安装状态

### Isabelle
- [ ] 已安装
- [ ] 版本: _______
- [ ] 可以运行: _______

### Z3
- [ ] 已安装
- [ ] 版本: _______
- [ ] 测试通过: _______

### cvc5
- [ ] 已安装
- [ ] 版本: _______
- [ ] 测试通过: _______

### pySMT
- [ ] 已安装
- [ ] 版本: _______
- [ ] 解析测试: _______

## Sledgehammer导出功能验证

### 导出命令查找
- [ ] sledgehammer_export存在: _______
- [ ] 命令路径: _______
- [ ] 帮助信息: _______

### 导出测试
- [ ] 能否导出SMT-LIB: _______
- [ ] 导出的文件示例: _______
- [ ] 备用方案准备: _______

## 问题记录

### 遇到的问题
1. _______
2. _______

### 解决方案
1. _______
2. _______

## 下一步计划

- [ ] 完成P0所有任务
- [ ] 完成P1所有任务
- [ ] 准备Week 2任务
EOF
```

---

## 🚨 **常见问题解决**

### **问题1：Isabelle安装失败**
- 检查磁盘空间（需要至少2GB）
- 检查网络连接（下载较大）
- 尝试使用手动下载方式

### **问题2：找不到sledgehammer_export命令**
- 这是**关键风险点**！
- 立即准备备用方案（ML脚本）
- 或在Isabelle邮件列表/论坛询问

### **问题3：Z3/cvc5编译错误**
- 确保Xcode命令行工具已安装：`xcode-select --install`
- 或使用Homebrew安装（更简单）

### **问题4：pySMT解析失败**
- 检查Python版本（需要3.6+）
- 尝试更新：`pip3 install --upgrade pysmt`
- 或使用其他解析库（如直接字符串解析）

---

## 📞 **获取帮助**

如果遇到问题：
1. Isabelle文档: https://isabelle.in.tum.de/documentation.html
2. Isabelle邮件列表: isabelle-users@cl.cam.ac.uk
3. Z3 GitHub: https://github.com/Z3Prover/z3
4. pySMT文档: https://github.com/pysmt/pysmt

---

**下一步**: 开始安装Isabelle，这是最关键的步骤！

