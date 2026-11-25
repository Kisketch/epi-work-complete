# 仓库全局结构与版本守恒导航（`epi_work` Architecture Map）

> 本文件作为全仓库层次化结构说明与零遗漏快速入口（只增不减原则；与 [`README.md`](README.md) 互补），遵循 [`AGENTS.md`](AGENTS.md) 诚实基线：**$e+\pi$ 及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个的无理性仍为公开问题，本仓库不宣称解决该问题。**

---

## 一、快速选择入口（你想做什么？）

| 需求场景 | 直达文件 / 命令 | 说明 |
| :--- | :--- | :--- |
| 阅读总览、成果五分法分类与边界 | [`README.md`](README.md) | 全仓权威中文总览，对照表遵循 `AGENTS.md` 五分法 |
| 阅读**论文一**（仿射窗口、$B=1\text{--}6$、大分子排除与 $e+\pi$ 障碍分析，75 页） | [`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf) | TeX 源码：[`paper1_e_plus_pi.tex`](paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex)；子索引：[`00_PROJECT_INDEX.md`](paper1_e_plus_pi/00_PROJECT_INDEX.md) |
| 阅读**论文二**（谱离散化、临界规范、一般递推与多残差渐近，65 页） | [`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf) | 分节目录见 [`paper2_spectral_gap_dimension/README.md`](paper2_spectral_gap_dimension/README.md)；拆分三轨见 [`split/README.md`](paper2_spectral_gap_dimension/split/README.md) |
| 检查全部 **344** 个 Lean 4 模块与 **988** 条审计声明 | [`epi_formal/Audit.lean`](epi_formal/Audit.lean) + [`AuditResidueCert.lean`](epi_formal/AuditResidueCert.lean) + [`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean) | `Audit.lean` 937 条 + `AuditResidueCert.lean` 27 条 + `AuditResidueMultiAsymptotic.lean` 24 条；0 `sorryAx`、0 逃逸关键字 |
| 检索全部核验脚本、日志、证明记录与一次文献 PDF | [`verification/README.md`](verification/README.md) | 分类导航 `verification/` 下 450+ 文件及全部增量留痕 |
| **一条命令**校验全库零遗漏、审计对账、论文切片、拆分引用与 Markdown 链接 | `python verification\verify_repo_integrity.py` | 报告落盘 [`verification/verify_repo_integrity.log`](verification/verify_repo_integrity.log) |

---

## 二、六层目录结构与功能边界

| 层级 | 目录 / 核心文件 | 定位与文件规模 |
| :--- | :--- | :--- |
| **L1：主论文（论文一与论文二）** | [`paper1_e_plus_pi/`](paper1_e_plus_pi/00_PROJECT_INDEX.md)（`01_main_paper/`、`02_companion_paper/`、`03_submission_prep/`、`04_formalization_audits/`）<br>[`paper2_spectral_gap_dimension/`](paper2_spectral_gap_dimension/README.md) | 论文一 75 页最新定稿与历史 B 稿 `Phase2_revised`（65 页）；论文二 65 页完整合稿及其编译日志与补丁脚本 |
| **L2：论文二无损切片与三轨一补工程** | [`paper2_spectral_gap_dimension/split/`](paper2_spectral_gap_dimension/split/README.md)（`src_sections/`、`2A_core_gauge_trichotomy/`、`2B_general_theory/`、`2C_windows_residues_finstate/`、`S_supplement/`） | 11 个主切片拼接与主 `.tex` 逐字节一致（`286,520` 字节）；2A（25 页）/ 2B（16 页）/ 2C（26 页）均 0 未定义引用；S（7 页）为独立 Supplement 轨 |
| **L3：Lean 4 `v4.35.0` 形式化工程** | [`epi_formal/`](epi_formal/README.md)（7 个顶层 `.lean` 文件 + `EpiFormal/` 下 337 个子模块，共 344 `.lean` 文件） | `lakefile.toml` 通过 `globs = ["EpiFormal.+"]` 收录 `EpiFormal/` 全模块；三条核心/独立 Layer A 审计入口共计 988 条声明，另含 `EpiFormal2{A,B,C}_Draft.lean` 三轨评审草案入口 |
| **L4：核验脚本、审计日志与一次文献** | [`verification/`](verification/README.md)（450+ 顶层文件 + `reference_pdfs/` + `lean_drafts/`） | 总台账 [`全工作区总索引与留痕台账.md`](verification/全工作区总索引与留痕台账.md)、一致性/对账脚本、Arb 有限排除脚本、`N=512` 证书与 32/50/450/2500 位数值脚本、证据深调与前沿记忆报告、5 份一次文献 PDF |
| **L5：研究过程演化与历史快照归档** | [`paper1_e_plus_pi/05_research_process/`](paper1_e_plus_pi/05_research_process/)、[`06_historical_versions/`](paper1_e_plus_pi/06_historical_versions/)、[`paper2_spectral_gap_dimension/historical_versions/`](paper2_spectral_gap_dimension/historical_versions/)、[`downloads/`](downloads/)、[`papers/`](papers/README.md)、[`scripts/`](scripts/)、`*.ps1`、[`progress_and_path_analysis.md`](progress_and_path_analysis.md) | 保留全部分轮目录（A–E 等）、演化快照（`.zip` / 冻结 `.tex`：`ed61a92`、`1e91028`、`7ece3b9`、`20261118`、`old`）及重组可追溯脚本，零删除以保证内部互引不失效 |
| **L6：治理纪律、Agent 技能与本地忽略缓存** | [`AGENTS.md`](AGENTS.md)、[`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md)、[`.agents/skills/`](.agents/skills/)、[`.claude/skills/README.md`](.claude/skills/README.md)、[`.licenses/`](.licenses/)、[`.gitignore`](.gitignore) | `AGENTS.md` 与 `.agents/rules/next-step-workflow.md` 为项目研究与门禁纪律；双根技能镜像同步维护（含 `mathodology-evidence-search`、`verified-research`、`leanprover/skills`）；`.lake/`、`.venv/`、`__pycache__/`、`*.aux/*.out/*.toc` 与 `split/*/build/*.pdf` 均在 `.gitignore` 中排除 |

---

## 三、版本守恒谱系（只增不减核查结论）

按 Git 树全量比对与工作区盘点验证：
1. `6847c74`（2026-11-22 初版全库归档）→ `ed61a92` → `1e91028`（**890** 个跟踪文件）：收录双论文、872→937 条 `Audit.lean` 及论文一/二核心材料。
2. `1e91028` → `7ece3b9`（GitHub 远端合并版，**1,230** 个跟踪文件）：`1e91028` 的 **890 个文件 100% 保留（0 删除）**，净增论文二 `split/` 工程、`ResidueCertGen/`（200+ 模块）与 `AuditResidueCert.lean`、论文一/二审校补丁、Colab 独立全量复现审计，以及新文献记录。
3. `7ece3b9` → `ae3c48c`（多残差推广与 GitHub 推送版，**1,237** 个跟踪文件）：`7ece3b9` 的 **1,230 个文件 100% 保留（0 删除）**，净增 [`ResidueMultiAsymptotic.lean`](epi_formal/EpiFormal/ResidueMultiAsymptotic.lean)（5,039 行，Part 1–6）、[`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean)（24/24）、[`audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)、[`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py)（含 `.log`/`.json`）与证明记录；并将 `thm:multi-residue-asymptotic` 合入论文二与 2C 轨（仅增改对应段落，无任何定理、证明或引文删除）。
4. 本轮仓库整合（`190c02c`，严格只增不减）：恢复了此前 `README.md` 漏列的 `residue_certificate_general.*` 与两条运行命令，补齐各子目录 `README` / `MANIFEST` / 台账索引与 `7ece3b9` 冻结快照，刷新陈旧 `undef_ref_audit.log` 与 `paperS_draft.log`，并引入一站式机器核查脚本 [`verify_repo_integrity.py`](verification/verify_repo_integrity.py)。
5. `d920a81` → `f345d60`（2026-11-24）→ **2026-11-25 证据深调与规范硬化**：合入 `prop:denominator-bounds` Arb 严格分母排除、`rem:fourth-term` 与第二次 Colab 复建审计；随后完成双通道证据深调报告与记忆文件、Paper 1/2 外部前沿对照与勘误规范化（`286,520` 字节 11 切片同步 + 22/22 全引用）、本地 `epi_formal` 9384-job `lake build` + 988 条声明全核实、双根技能镜像及 [`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md) 规则落地（0 文件删除）。
