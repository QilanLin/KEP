# 🔧 AFP下载修复说明

**问题**: GitHub仓库URL不正确

## ❌ 错误的URL

```
https://github.com/isa-afp/afp-devel.git
```

这个仓库不存在或已被移动。

## ✅ 正确的URL

```
https://foss.heptapod.net/isa-afp/afp-devel.git
```

AFP现在托管在Heptapod上。

## 🔧 修复

已更新 `下载AFP.sh` 脚本，使用正确的URL。

## 📥 使用方法

```bash
./下载AFP.sh
```

脚本会使用浅克隆（只下载最新提交）以加快速度。

## 📚 其他获取AFP的方法

1. **从官方网站下载tar包**:
   - 访问: https://www.isa-afp.org/download.html
   - 下载最新的tar.gz文件

2. **完整克隆（如果浅克隆失败）**:
   ```bash
   git clone https://foss.heptapod.net/isa-afp/afp-devel.git
   ```

3. **使用Isabelle的AFP工具**:
   ```bash
   isabelle afp_build
   ```

## ⚠️ 注意事项

- AFP仓库较大（500MB-1GB），下载可能需要时间
- 浅克隆（--depth 1）只下载最新提交，速度较快但可能缺少历史记录
- 如果需要完整历史，请使用完整克隆

