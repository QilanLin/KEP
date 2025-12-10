# cvc5手动安装指南

由于自动安装脚本需要sudo权限，请按以下步骤手动安装：

## 方法1：从GitHub下载预编译版本（推荐）

1. **访问cvc5发布页面**:
   https://github.com/cvc5/cvc5/releases

2. **下载macOS版本**:
   - Apple Silicon (M1/M2/M3): 下载 `cvc5-macOS-arm64`
   - Intel: 下载 `cvc5-macOS`

3. **安装步骤**:
   ```bash
   # 下载后，移动到可执行目录
   # Apple Silicon:
   sudo mv ~/Downloads/cvc5-macOS-arm64 /opt/homebrew/bin/cvc5
   sudo chmod +x /opt/homebrew/bin/cvc5
   
   # 或Intel:
   sudo mv ~/Downloads/cvc5-macOS /usr/local/bin/cvc5
   sudo chmod +x /usr/local/bin/cvc5
   ```

4. **验证**:
   ```bash
   cvc5 --version
   ```

## 方法2：使用Homebrew（如果可用）

检查是否有tap：
```bash
brew tap cvc5/cvc5  # 如果这个tap存在
brew install cvc5
```

## 方法3：从源码编译（不推荐，复杂）

如果需要，可以参考cvc5的GitHub仓库说明。

## 快速验证cvc5是否已安装

运行：
```bash
which cvc5
cvc5 --version
```

如果显示版本号，说明已安装。

