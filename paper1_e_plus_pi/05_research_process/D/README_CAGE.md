# e+π 研究项目 · Cage Linux 环境说明

本目录（guest：`/home/cage/epi_work`）是论文与 Lean 形式化工程的完整 Linux 副本，
运行于 Cage 隔离虚拟机（Ubuntu 22.04.5 LTS，x86_64）。源文件未改动；本副本已做 Linux 适配与去指纹。

## 一、目录结构

```
epi_work/
├── 论文一_e_plus_pi/            # 论文全文（40 文件）
│   ├── 第一阶段_e_plus_pi.tex   # 主稿（含命题 8.1、定理 12 依赖）
│   ├── 第一阶段_e_plus_pi.pdf   # 已在 guest 编译验证（36 页）
│   ├── 第二阶段修订/Phase2_revised.{tex,pdf}
│   ├── Parallel_Research_Plan.md
│   ├── DenominatorCertificate.lean / UnweightedCorrection.lean
│   └── parallel_work/{A,B,C,D,E,integration}/   # 各代理工作与交接
└── epi_formal/                  # 共享 Lean 工程（52 源文件）
    ├── lakefile.toml / lake-manifest.json / lean-toolchain
    ├── EpiFormal.lean / Audit.lean
    ├── EpiFormal/*.lean         # 43 个模块
    ├── README.md / PROOF_GAPS.md / LEMMA_AUDIT.md / FINAL_REVIEW.md
    ├── .github/workflows/ .gitignore
    └── .lake/                   # 依赖与缓存（guest 内重建，见下）
```

## 二、工具链（已装、已适配）

| 工具 | 版本 | 用途 |
|------|------|------|
| elan | 4.4.0 | Lean 工具链管理 |
| lean / lake | 4.35.0（v4.35.0，与主稿 pin 一致） | 形式化验证 |
| mathlib | v4.35.0 rev 56a00585 | 8643 个 olean 缓存就位 |
| pdflatex / xelatex | TeX Live 2022 | 论文编译（已验证） |
| python3 | 3.10 + sympy/mpmath/numpy | 数值试验 |
| git / gcc / g++ / make / cmake / curl / rsync | 系统自带 | 通用 |

PATH 已持久化（.bashrc 首行 + .zshenv）。elan 默认工具链已设为 v4.35.0。

## 三、Linux 适配（已完成）

- 8 个 CRLF 文本文件已转 LF（3 个 .lean、2 个 .tex、其余 txt）。
- 移除拷贝带入的 `.git` 元数据、Windows `__pycache__`、TeX 辅助文件（.aux/.log/.out）。
- 中文文件名在 guest 完好（UTF-8）。
- 注意：guest 默认 shell 为 **zsh**，`==X==` 会触发 equals 展开、引号易被破坏；
  复杂命令请写 `.sh` 用 `bash` 执行；从宿主传脚本用 `scp`（管道传中文会乱码）。

## 四、去指纹（已完成）

git 身份改 `cage <cage@localhost>`；gh 已 logout、token 删除；hostname 改 `ubuntu-dev`；
machine-id 随机重生成；时区/语言保持 Cage 伪装（America/Vancouver / en_CA.UTF-8）；
Claude 旧会话缓存/scratch/git-shadow 已清除（登录态保留）。配置层复扫无真实身份。

## 五、验证命令

```bash
# 论文编译
cd ~/epi_work/论文一_e_plus_pi && pdflatex -interaction=nonstopmode 第一阶段_e_plus_pi.tex

# Lean 验证（命题 8.1，D 组）
cd ~/epi_work/epi_formal
lake env lean ~/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean
```

说明：mathlib olean 已就位；项目自身模块（EpiFormal.*）部分 olean 已编译，
其余可用 `lake build +EpiFormal.<模块>:olean` 增量补齐（不要全量 `lake build`，
Windows 来源的 trace 在 Linux 不被 lake 认可，全量会触发重编）。

## 六、诚实声明

e+π 无理性仍开放。命题 8.1 为条件性整除限制（已机器验证），定理 12 为测度论 spin-off（纸面）。
本环境不声称解决中心问题。
