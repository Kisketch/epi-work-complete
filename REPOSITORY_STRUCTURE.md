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
| **L1：主论文（论文一与论文二系列）** | [`paper1_e_plus_pi/`](paper1_e_plus_pi/00_PROJECT_INDEX.md)（`01_main_paper/`、`02_companion_paper/`、`03_submission_prep/`、`04_formalization_audits/`、`07_research_log_and_guide/`）<br>[`paper2_spectral_gap_dimension/`](paper2_spectral_gap_dimension/README.md)（含 `spinoff_*/` 与 `00_research_log_and_guide/`） | 论文一 75 页定稿与历史 B 稿 `Phase2_revised`（65 页）+ 分离台账目录 `07_research_log_and_guide/`；论文二 66 页主稿、**Paper 2D**（18 页）与 **Paper 2E**（8 页）独立衍生论文 + `00_research_log_and_guide/` + `drafts_v3_critical_scaling/` |
| **L2：论文二无损切片与三轨一补工程** | [`paper2_spectral_gap_dimension/split/`](paper2_spectral_gap_dimension/split/README.md)（`src_sections/`、`2A_core_gauge_trichotomy/`、`2B_general_theory/`、`2C_windows_residues_finstate/`、`S_supplement/`） | 11 个主切片拼接与主 `.tex` 逐字节一致（`293,395` 字节）；2A（`*-2Apub`）/ 2B / 2C 均 `0/0` 未定义引用；S 为独立 Supplement 轨；含 `2A+2B` 与 `2C` 诚实版英文 Cover Letter 草稿 [`cover_letters_2AB_and_2C_draft_20261125.md`](paper2_spectral_gap_dimension/split/cover_letters_2AB_and_2C_draft_20261125.md) |
| **L3：Lean 4 `v4.35.0` 形式化工程** | [`epi_formal/`](epi_formal/README.md)（13 个顶层 `.lean` 文件 + `EpiFormal/` 下 343 个子模块，共 356 `.lean` 文件） | `lakefile.toml` 收录 `EpiFormal/` 全模块；`Audit.lean` (**937**) + 8 个独立 Layer A 审计（**156**：`27+24+22+9+15+6+13+40`）共计 **1,093** 条声明，彻底消去 R1 与 R3，0 `sorryAx` / 0 逃逸；分篇接口草案 [`Paper2{A,B,C}.lean`](verification/lean_drafts/README.md) 隔离存于 `verification/lean_drafts/` |
| **L4：新研究与全量核验档案（`research/` + `verification/`）** | [`research/`](research/README.md)（`kahane_q6_note_20261125.md`、`kahane_q6_addendum_20261125.md` 与 `planning_20261124/`）<br>[`verification/`](verification/README.md)（500+ 文件 + `reference_pdfs/` + `lean_drafts/`） | Kahane Q6 笔记与增补（D′/R 否证 + 确定性 K-1/K-2）；总台账、一致性/对账脚本、Round-2 M1/M2/BLR/超临界/Kahane 核验包、5 份一次文献 PDF |
| **L5：研究过程演化与历史快照归档** | [`paper1_e_plus_pi/05_research_process/`](paper1_e_plus_pi/05_research_process/)、[`06_historical_versions/`](paper1_e_plus_pi/06_historical_versions/)、[`paper2_spectral_gap_dimension/historical_versions/`](paper2_spectral_gap_dimension/historical_versions/)、[`downloads/`](downloads/)、[`papers/`](papers/README.md)、[`scripts/`](scripts/)、`*.ps1`、[`progress_and_path_analysis.md`](progress_and_path_analysis.md) | 保留全部分轮目录（A–E 等）、演化快照（`.zip` / 冻结 `.tex`：`ed61a92`、`1e91028`、`7ece3b9`、`20261118`、`old`）及重组可追溯脚本，零删除以保证内部互引不失效 |
| **L6：治理纪律、CI、跨平台依赖与技能** | [`AGENTS.md`](AGENTS.md)、[`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md)、[`.github/workflows/`](.github/workflows/lean-audit.yml)、[`requirements.txt`](requirements.txt)、[`pyproject.toml`](pyproject.toml)、[`.agents/skills/`](.agents/skills/)、[`.claude/skills/README.md`](.claude/skills/README.md)、[`.licenses/`](.licenses/)、[`.gitignore`](.gitignore) | `AGENTS.md` 与 `.agents/rules/next-step-workflow.md` 为研究与门禁纪律；根 `.github/workflows/` 提供 Lean 与 Python CI（已于 `833845f` 验证绿灯）；`requirements.txt`/`pyproject.toml` 锁定跨平台 Python 依赖；双根技能镜像同步维护；`.lake/`、`.venv/`、`.zcode/`、`.zwork/`、`Python/`、`__pycache__/`、`*.aux/*.out/*.toc` 与 `split/*/build/*.pdf` 由 `.gitignore` 排除 |
| **L7：P1 围攻战役（2026-11-25 起，Commander/Sonnet 子代理协议）** | [`logs/`](logs/README.md)（账本、交接、蓝图、评审、证据、验证日志）<br>[`artifacts/`](artifacts/README.md)（THM-0001..0006）<br>[`registry/results.csv`](registry/results.csv)<br>`epi_formal/EpiFormal/{RationalSpan,KappaSharp,GeneralDichotomy}.lean` + 4 个 `Audit*.lean` | 6 个定理单元经双检；4 个通过 Lean 门禁（CI siege 公理门禁：15 个定理只依赖 `propext/Classical.choice/Quot.sound`）；THM-0005（κ=1/4 尖锐可达）为类别 1 候选；**P1 与 e+π 仍 OPEN**。总结见 [`logs/CAMPAIGN_SUMMARY.md`](logs/CAMPAIGN_SUMMARY.md) |

---

## 三、版本守恒谱系（只增不减核查结论）

按 Git 树全量比对与工作区盘点验证：
1. `6847c74`（2026-11-22 初版全库归档）→ `ed61a92` → `1e91028`（**890** 个跟踪文件）：收录双论文、872→937 条 `Audit.lean` 及论文一/二核心材料。
2. `1e91028` → `7ece3b9`（GitHub 远端合并版，**1,230** 个跟踪文件）：`1e91028` 的 **890 个文件 100% 保留（0 删除）**，净增论文二 `split/` 工程、`ResidueCertGen/`（200+ 模块）与 `AuditResidueCert.lean`、论文一/二审校补丁、Colab 独立全量复现审计，以及新文献记录。
3. `7ece3b9` → `ae3c48c`（多残差推广与 GitHub 推送版，**1,237** 个跟踪文件）：`7ece3b9` 的 **1,230 个文件 100% 保留（0 删除）**，净增 [`ResidueMultiAsymptotic.lean`](epi_formal/EpiFormal/ResidueMultiAsymptotic.lean)（5,039 行，Part 1–6）、[`AuditResidueMultiAsymptotic.lean`](epi_formal/AuditResidueMultiAsymptotic.lean)（24/24）、[`audit_residue_multi_asymptotic_20261123.log`](verification/audit_residue_multi_asymptotic_20261123.log)、[`verify_residue_multi_asymptotic.py`](verification/verify_residue_multi_asymptotic.py)（含 `.log`/`.json`）与证明记录；并将 `thm:multi-residue-asymptotic` 合入论文二与 2C 轨（仅增改对应段落，无任何定理、证明或引文删除）。
4. 本轮仓库整合（`190c02c`，严格只增不减）：恢复了此前 `README.md` 漏列的 `residue_certificate_general.*` 与两条运行命令，补齐各子目录 `README` / `MANIFEST` / 台账索引与 `7ece3b9` 冻结快照，刷新陈旧 `undef_ref_audit.log` 与 `paperS_draft.log`，并引入一站式机器核查脚本 [`verify_repo_integrity.py`](verification/verify_repo_integrity.py)。
5. `d920a81` → `f345d60`（2026-11-24）→ **2026-11-25 证据深调与规范硬化**：合入 `prop:denominator-bounds` Arb 严格分母排除、`rem:fourth-term` 与第二次 Colab 复建审计；随后完成双通道证据深调报告与记忆文件、Paper 1/2 外部前沿对照与勘误规范化（`286,520` 字节 11 切片同步 + 22/22 全引用）、本地 `epi_formal` 9384-job `lake build` + 988 条声明全核实、双根技能镜像及 [`.agents/rules/next-step-workflow.md`](.agents/rules/next-step-workflow.md) 规则落地（0 文件删除）。
6. **2026-11-25 续（CI 工作流、跨平台依赖与分拆投稿信草稿）**：合入根 CI [`.github/workflows/lean-audit.yml`](.github/workflows/lean-audit.yml)、[`compare_audit_logs.py`](verification/compare_audit_logs.py) 与 Linux 路径兼容补丁；新增快速门禁 [`.github/workflows/python-checks.yml`](.github/workflows/python-checks.yml)、跨平台依赖 [`requirements.txt`](requirements.txt) / [`pyproject.toml`](pyproject.toml) 与 `2A+2B` / `2C` 投稿信草稿，并于 `main@833845f` 实测 GitHub Actions 双 workflow 绿灯（0 文件删除）。
7. **2026-11-25 合流整理与展望定稿（本地/GitHub 完全统一）**：合入 PR #1 (`b6e7e48`) 与 PR #2 (`edc7673`，论文二投稿前新颖性核查、BLR 措辞修正、2A `*-2Apub` 投稿版、Kahane Q6 研究笔记与价值评级），零损失整编归档本地 `epi_work` 的 `75` 份独特产物至 [`research/`](research/README.md)、[`paper2_spectral_gap_dimension/drafts_v3_critical_scaling/`](paper2_spectral_gap_dimension/drafts_v3_critical_scaling/README.md)、[`verification/`](verification/README.md) 与 [`verification/lean_drafts/paper_interfaces_20261124/`](verification/lean_drafts/README.md)，并将主文 Paper 2 统一重建为 **28/28** 全引用、**`289,499` 字节**（66 页，0 错误 / 0 Overfull）同步真源（0 文件删除）。
8. **2026-11-25 Round 2 演化收敛（衍生论文 2D/2E + Lean R1/R3/L1/L5 闭合 + 对抗试错留痕）**：严格保留全部历史文件（0 删除），新增总指挥技能（四方字节一致）、分离式台账与 20 项 11 维清单 [`MASTER_INVENTORY_LIST.md`](paper1_e_plus_pi/07_research_log_and_guide/MASTER_INVENTORY_LIST.md)；新增 **Paper 2D**（18 页，临界标度修复与超临界精确常数）与 **Paper 2E**（8 页，$e$ 全收敛谱与无 Brouwer Perron–Frobenius）；`epi_formal/` 扩展至 **356 `.lean` / 1,093 audited 声明**（`Audit.lean` 937 + 8 独立 Layer A 入口 156，彻底消除 R1/R3 与证明 $\mu(e)=2$）；通过 [`patch_round2_20261125.py`](paper2_spectral_gap_dimension/patch_round2_20261125.py) 同步 Paper 2 主文与四轨（`293,395` 字节）；补齐 Kahane D′/R 否证、确定性定理 K-1/K-2、非线性 BLR 三漏洞审计与 Paper 1 M1/M2 验证，同步更新双 CI 工作流与 `verify_repo_integrity.py`。
9. **2026-11-25—26 P1 围攻战役 Rounds 1–4**（PR #3/#4/#5，0 文件删除）：新增 [`logs/`](logs/README.md)、[`artifacts/`](artifacts/README.md)、[`registry/`](registry/results.csv)、3 个 Lean 模块与 4 个审计入口，CI 新增 siege 公理门禁；P1 仍 OPEN。
