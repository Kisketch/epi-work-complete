# 论文二系列独立研究日志、衍生脉络与试错指南（`paper2_spectral_gap_dimension/00_research_log_and_guide/`）

> **学术正文与过程日志严格物理分离声明（供同行学者与审阅人阅读）**：
> 本目录存放 **Paper 2 系列**（`2A` / `2B` / `2C` / `S` 及独立衍生定理论文 `2D`）的**思路演化日志、由 Paper 1 衍生出的全部定理论文脉络、对抗性审查抓虫记录、未完成项与每项成果评估**，与下列权威学术稿件和真源切片严格物理隔离：
> - **Paper 2 完整合稿与 11 切片真源（SSOT）**：[`../paper2_spectral_gap_dimension.tex`](../paper2_spectral_gap_dimension.tex) / [`.pdf`](../paper2_spectral_gap_dimension.pdf) 及 [`../split/src_sections/slice_index.csv`](../split/src_sections/slice_index.csv)
> - **Paper 2 四轨拆分工程**：[`../split/README.md`](../split/README.md)（`2A` / `2B` / `2C` / `S`）
> - **Paper 2D 新独立定理论文（2026-11-25 临界标度修复与超临界精确常数）**：[`../spinoff_critical_and_supercritical_exact_20261125/README.md`](../spinoff_critical_and_supercritical_exact_20261125/README.md)
> - **Lean 4 权威形式化工程**：[`../../epi_formal/README.md`](../../epi_formal/README.md)
>
> **诚实基线（[`../../AGENTS.md`](../../AGENTS.md)）**：Paper 2 系列研究的是连分数、稀疏增长递推与转移算子的谱/维数理论，**不解决 $e+\pi$ 的无理性问题**（后者仍为公开问题）。

---

## 本目录文件导航

| 文件 | 定位与核心内容 |
| :--- | :--- |
| [`MASTER_GUIDE_SKILL.md`](MASTER_GUIDE_SKILL.md) | **总研究指南技能（`epi-research-commander`）完整本地副本**（与 [`.agents/skills/epi-research-commander/SKILL.md`](../../.agents/skills/epi-research-commander/SKILL.md) 及 [`.claude/skills/epi-research-commander/SKILL.md`](../../.claude/skills/epi-research-commander/SKILL.md) 逐字节一致） |
| [`SPINOFF_AND_TRIAL_LOG.md`](SPINOFF_AND_TRIAL_LOG.md) | **Paper 2 系列衍生演化与试错日志**：完整追踪 Paper 2 如何从 Paper 1 裂变、历次新颖性重审纠偏（BLR / CMMS / DFSU / HU02 / CLN 2026 / Brown 2026）、T6 临界标度 7 处数学缺陷发现与彻底修复、超临界精确常数 $\frac{d\kappa\zeta(2s_0)}{2}$ 新定理、稀疏字母表反例精确澄清、L1/L2/L3 并行 Lean 强化线、未完成项与逐项价值评估 |

---

## 关联入口

- **全仓库成果 11 维总清单（位于 Paper 1 日志目录）**：[`../../paper1_e_plus_pi/07_research_log_and_guide/MASTER_INVENTORY_LIST.md`](../../paper1_e_plus_pi/07_research_log_and_guide/MASTER_INVENTORY_LIST.md)
- **Paper 1 攻关与试错日志**：[`../../paper1_e_plus_pi/07_research_log_and_guide/PAPER1_ATTACK_AND_TRIAL_LOG.md`](../../paper1_e_plus_pi/07_research_log_and_guide/PAPER1_ATTACK_AND_TRIAL_LOG.md)
- **T6 历史实验稿对照档案（留存原始缺陷版本备查）**：[`../drafts_v3_critical_scaling/README.md`](../drafts_v3_critical_scaling/README.md)
- **投稿信草稿与价值评级**：[`../split/cover_letters_2AB_and_2C_draft_20261125.md`](../split/cover_letters_2AB_and_2C_draft_20261125.md)、[`../../verification/value_rating_and_top_journal_gap_20261125.md`](../../verification/value_rating_and_top_journal_gap_20261125.md)
