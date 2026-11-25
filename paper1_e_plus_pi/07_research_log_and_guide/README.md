# 论文一独立研究日志、试错历程与总指南（`paper1_e_plus_pi/07_research_log_and_guide/`）

> **学术正文与过程日志严格物理分离声明（供同行学者与审阅人阅读）**：
> 本目录存放围绕 **$e+\pi$ 无理性主问题** 及整个研究项目的**详尽思路历程、路线试错记录、数学障碍坐标、未完成项台账、全库总清单与总指挥指南**，与下列权威学术内容严格分开放置、互不混杂：
> - **Paper 1 权威学术正文**：[`../01_main_paper/paper1_e_plus_pi.tex`](../01_main_paper/paper1_e_plus_pi.tex) / [`.pdf`](../01_main_paper/paper1_e_plus_pi.pdf)（75 页）
> - **Lean 4 权威形式化工程**：[`../../epi_formal/`](../../epi_formal/README.md)（344 个 `.lean` 文件，988 条已核 Layer A 审计声明）
> - **Paper 2 系列学术正文**：[`../../paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`](../../paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex) 及 [`../../paper2_spectral_gap_dimension/split/`](../../paper2_spectral_gap_dimension/split/README.md)
>
> **诚实基线（[`../../AGENTS.md`](../../AGENTS.md) §4）**：截至 2026-11-25，**$e+\pi$（及 $e\pi, e-\pi, \pi/e, \pi^e$ 单个）的无理性仍是公开问题**；当前唯一无条件硬结论是 $e+\pi$ 与 $e\pi$ 至少其一超越。本目录记录的全部尝试均严格标注 `AGENTS.md` 五分法类别、失败原因与精确数学障碍坐标，绝不把等价改写或有限计算包装为对原问题的证明进展。

---

## 本目录文件导航

| 文件 | 定位与核心内容 | 面向读者 |
| :--- | :--- | :--- |
| [`MASTER_GUIDE_SKILL.md`](MASTER_GUIDE_SKILL.md) | **总研究指南技能（`epi-research-commander`）完整本地副本**（与 [`.agents/skills/epi-research-commander/SKILL.md`](../../.agents/skills/epi-research-commander/SKILL.md) 及 [`.claude/skills/epi-research-commander/SKILL.md`](../../.claude/skills/epi-research-commander/SKILL.md) 逐字节一致）：汇总先前研究、本地工具链/MCP、11 项双根技能、SSOT/CI/投稿门禁与 5 套 `hydrogen` 并行派活提示词模板 | 总指挥、后续 AI 代理、复现者 |
| [`MASTER_INVENTORY_LIST.md`](MASTER_INVENTORY_LIST.md) | **全仓库成果与资产总清单（11 维完整对照表）**：逐项登记 Paper 1、Paper 2 (2A/2B/2C/S)、Paper 2D（临界与超临界精确常数独立稿）、Lean 4 体系、Kahane Q6、数值套件与治理技能的简介、文件位置、结构、方法、核心定理、五分法价值评级、投稿评估、未来展望与局限不足 | 同行学者、审稿人、项目总控 |
| [`PAPER1_ATTACK_AND_TRIAL_LOG.md`](PAPER1_ATTACK_AND_TRIAL_LOG.md) | **论文一（$e+\pi$）全周期攻关与试错日志**：按时间线完整记录云端 1–9 轮、本机第 10 轮、并行五支线 A–E、黄金比与二次轨道深化、2026-11-24/25 Arb 百万位排除与六方向前沿核查的每一条成功副产物、失败障碍坐标、未完成项与下一轮 `hydrogen` 试错任务书 | 研究 $e+\pi$ 或丢番图障碍的同行学者 |

---

## 关联日志与历史档案入口

- **Paper 2 系列衍生与试错日志**：[`../../paper2_spectral_gap_dimension/00_research_log_and_guide/README.md`](../../paper2_spectral_gap_dimension/00_research_log_and_guide/README.md)（与本目录成对维护）
- **Paper 1 历史分轮过程档案（只读保留）**：[`../05_research_process/`](../05_research_process/Parallel_Research_Plan.md)（A–E 支线、`round10_advance/`、`golden_finite_spectrum/` 等）与 [`../06_historical_versions/`](../06_historical_versions/)
- **全库早期进度记录与台账**：[`../../progress_and_path_analysis.md`](../../progress_and_path_analysis.md)、[`../../verification/全工作区总索引与留痕台账.md`](../../verification/全工作区总索引与留痕台账.md)、[`../../verification/value_rating_and_top_journal_gap_20261125.md`](../../verification/value_rating_and_top_journal_gap_20261125.md)
