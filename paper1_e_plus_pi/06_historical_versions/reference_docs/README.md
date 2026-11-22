# 论文与文档索引

本目录集中存放 $e+\pi$ 项目的两篇论文、严格数学证明与审查报告。
**先读 `project_handover.md`**——它是全项目状态的唯一权威入口（含环境命令、成果清单、
未闭合义务、敌意审查协议、踩坑记录）。

## 论文

> **2026-11-21 注**：重组后本目录已不存放论文 tex/pdf，只保留参考 md 文档；论文现行版在 `..\..\01_main_paper\`（主论文）与 `..\..\..\paper2_spectral_gap_dimension\`（论文二）。下表为旧版内容描述快照。

| 文件 | 页数 | 内容 | 状态 |
|---|---|---|---|
| `第一阶段_e_plus_pi.tex` / `.pdf` | 42 | 已证结果、归约链（含 P1 换靶与连分数窗口判据）、系统性障碍分析、Lean 形式化记录 | **不声称解决 $e+\pi$ 无理性** |
| `第二阶段_谱隙与维数.tex` / `.pdf` | 12 | 谱隙定理、T-finite（一切实数 $c$，$\dim_H\{\Lambda\le c\}=0$）、加权上界 $\le1-\alpha$（Lean 层 A）与次临界 Moran 下界、临界规范 $h_k$、短/发散窗口维数、模 4 周期维数认证 | 关键基础与维数上界已机器验证；其余纸面/整数认证 |

两篇 tex **自包含**（无 `\input`/`\includegraphics`/`\bibliography`），可直接
`pdflatex <文件>.tex` 编译两遍（历史核验结论；2026-11-21 起文件已移至上文新位置）。

**两篇论文现行版位置**（2026-11-21 英文化重组后）：
- 主论文（第一阶段）：`..\..\01_main_paper\paper1_e_plus_pi.tex` / `.pdf`
- 论文二：`..\..\..\paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex` / `.pdf`

独立复核材料（源码说明、公理审计日志、复现指南）见 `..\verification\`；
形式化源码以 `..\epi_formal\` 为唯一权威原件。

## 严格数学证明（人类可读，非 tactic 脚本）

| 文件 | 内容 |
|---|---|
| `δ符号交替定理的严格数学证明.md` | Hermite 积分表示：$(-1)^n n!\delta_n=\int_0^1 e^t t^n(1-t)^n dt$。含分部积分合法性、边界零点重数、关键代数 $(1-2t)^2=1-4t(1-t)$、正性论证、递推匹配归纳、符号⇒正项和⇒上界；附「哪些是数学洞察、哪些是机械核验」对照表 |
| `加权相变上界定理.md` | $\dim_H\{\Lambda_\alpha\le c\}\le1-\alpha$ 的严格证明；**纠正原猜想**「$\alpha<1$ 维数 1」之错误（正确临界指数随 $\alpha$ 线性变化） |

## 审查报告

| 文件 | 内容 |
|---|---|
| `两篇论文审查总结.md` | 七类敌意攻击逐条审查结论 |
| `存量审计报告.md` | claim → 依赖 → 判决全表（含 T-finite 判决更新） |

## 子目录

- `archive/` 与 `numerics/` 已于 2026-11-21 重组迁出：`paper_merged.tex` 及旧编译辅助文件在
  `..\archive_snapshots\papers_old\`；数值脚本在 `..\..\..\paper2_spectral_gap_dimension\historical_versions\numerics\`。
  **数值仅佐证，永不参与证明**；mpmath 需 300–500 位 guard、绝对容差 1e-100。

## 形式化代码位置

不在本目录，在 `..\..\..\epi_formal\`：
- `EpiFormal\*.lean`：全部模块
- `Audit.lean`：公理审计入口
- `PROOF_GAPS.md`：缺口与进展登记（M1–M33），**最重要的治理文档**

当前审计状态（2026-11-19 实测）：`lake build` 9090 jobs 零错误；`Audit.lean` 退出码 0；**全项目 sorryAx = 0**；
剩余公理仅 3 条经典事实（$e$、$\pi$ 超越，$\mu(e)=2$），两条 $\delta$ 公理已证明并物理删除。

## 诚实边界

$e+\pi$ 无理性**仍开放**，本目录任何文件都不声称解决它。
谱隙现象与覆盖论证、Hermite 积分法均为**经典方法**；新颖性只在具体实例签名
（$e$ 选定子列 + 权重 $j$ + 格 $L$ + sharp $1/4$）与精确标度 $1-\alpha$。
**形式化 ≠ 新数学定理。** 加权相变的下界 $\ge1-\alpha$ 仍开放。

## 2026-11-21 实测附记

- `lake env lean Audit.lean` 当日复跑：退出码 0；**349 条审计声明 = 327 纯基础 + 22 白名单（`e_transcendental` / `pi_transcendental` / `mu_e_eq_two`）+ 0 项目自加**；`sorryAx = 0`。原始输出：`..\..\..\verification\audit_recheck_20261121.log`。
- `meiburg_criterion` 经 lean-lsp `lean_verify` 实测为**定理**（仅依赖 `pi_transcendental` + 基础三公理），不再是公理；`proposition_H'` 仅依赖白名单 2 条（`mu_e_eq_two`、`pi_transcendental`）。
