# flash 执行任务书 v3（2026-11-24）——T6 定理化支持批 + 两主稿装配批

> **指挥关系**：主会话（GLM-5.4）定方法/路径/目标/验收并逐条验收；GLM-5.3-Flash 执行。本文件是派给 flash 的任务书原文，每条含**任务、方法、路径、目标、验收**五项。
> **全局硬规则（每条适用）**：只增不减——只允许新建文件，禁止修改/删除任何既有文件；禁止 git 写操作（add/commit/push/checkout/restore/stash）；禁止 lake/build；禁止 pdflatex/tectonic；禁止 pip install；禁止删除目录（含 `Python/`）；联网仅 E14、E16 允许；先读 `AGENTS.md`；回答 ≤1000 字并列出产出文件的 workspace 相对路径。
> **工作区**：`<repo-root>`（PowerShell 5.1）。写文件统一 UTF-8 无 BOM：`[IO.File]::WriteAllText($p,$s,[Text.UTF8Encoding]::new($false))`。
> **执行顺序**：E11 → E12 → E14（P0 支撑）→ E13 → E16（P1）→ E15（P2）。额度不足按此顺序保前几条；每条独立落盘，做完一条即可回报。
> **本批不做**：不写 T6 证明；不改任何 `.lean`；不编译；不 git commit；不删 `Python/`；不评价论文。

## 批次总览

| # | 任务 | 服务于 | 类型 | 产出 |
|---|---|---|---|---|
| E11 | CLU Thm 2.3/2.4 与压力定义原文抽取 | P0 T6 缺口 (c) | 本地 PDF | `verification/clu_thm23_extract_20261124.md` |
| E12 | Lean 锚点与公理清单抽取 | P0 T6 Lean 陈述 | 只读 rg | `verification/lean_anchor_extract_T6_20261124.md` |
| E13 | 主稿 A / 主稿 B tex 包装草案 | P1 两主稿装配 | 新文件 | `split/mainA_critical_scaling_wrapper_20261124.tex`、`split/mainB_unified_wrapper_20261124.tex`、`split/mainAB_assembly_report_20261124.md` |
| E14 | T6 引文核验包 | P0 T6 缺口 (a)(b) | 联网 | `verification/T6_citation_pack_20261124.md` |
| E15 | 工程卫生预检 | P2 卫生三项 | 只读 | `verification/hygiene_precheck_20261124.md` |
| E16 | KMS 补齐（Stratmann 线索） | P1 E9 尾巴 | 联网 | `verification/kms_comparison_materials_addendum_20261124.md` |

---

## E11｜CLU 定理 2.3/2.4 与压力定义原文抽取（本地 PDF，只读）

- **任务**：从 `verification/reference_pdfs/CLU_1805_11904.pdf` 逐字抽取 Theorem 2.3、Theorem 2.4、压力 $P(t)$ 与「strongly regular」的定义段，以及（若文中出现）conformal IFS 的 Bowen 型维数公式。这是 T6 极点分解引理缺口 (c)——$\rho_S(2s_0)=1$ 与 $s_0(S)$ 同一性——的外部陈述底稿。
- **方法**：
  1. `pdftotext -layout verification\reference_pdfs\CLU_1805_11904.pdf $env:TEMP\epi_clu\clu.txt`（已实测可抽出 1809 行；`$env:TEMP\epi_clu` 不存在则先建）。
  2. 页码映射：`pdftotext` 以换页符 `\f` 分页，`$t -split "\`f"` 的第 $i$ 段即第 $i$ 页；写一个小 PowerShell 脚本把「clu.txt 行号 → PDF 页码」存成新文件 `verification/clu_page_map_20261124.csv`（列：line,page）。
  3. 逐字照录（英文原文，不改写、不翻译）：Theorem 2.3 全文（含括号引用 `[24]`）、Theorem 2.4 全文（含 characteristic Lyapunov exponent $\chi_S$ 的定义句）、压力 $P(t)$ 的定义段、「strongly regular」的定义句。
  4. 记录 PDF 版本：首页的 arXiv 编号/版本/日期逐字照录；若 PDF 内含期刊卷页或 DOI 也照录，**没有就写「未核到」**（不得凭记忆补 Trans. AMS 373 (2020) 1009–）。
  5. 每条引用标注：PDF 页码 + clu.txt 行号范围。
- **路径（产出）**：`verification/clu_thm23_extract_20261124.md`（正文）、`verification/clu_page_map_20261124.csv`（页码表）、可选 `verification/clu_extract_20261124.ps1`（提取脚本）。
- **目标**：T6 引理缺口 (c) 的原文依据页；为「内核无 Bowen 版 `dimH_cfAlphabetSet_finset_eq_poincareAbscissa` 与 CLU 路线相容」的桥接引理提供确切外部陈述与假设清单。
- **验收**：Theorem 2.3/2.4 有逐字英文原文与页码；PDF 版本明确；期刊字段缺失处写「未核到」；`git status --porcelain=v1` 只有 `??`；不改既有文件。

## E12｜Lean 锚点与公理清单抽取（只读 rg，禁止 lake）

- **任务**：抽取 T6 的 Lean 陈述与桥接引理所需的精确签名：`poincareAbscissa`、`wordSum`、`multiC`、`multiResolventV`、`dimH_cfAlphabetSet_finset_eq_poincareAbscissa`、`tendsto_dimH_multiResidueSet`，以及超临界 $\Theta(m^{-2s_0})$ 定理；并列出全库 `axiom` 声明与 `sorry` 计数。
- **方法**：
  1. `rg -n "def poincareAbscissa|def wordSum|def multiC|def multiResolventV|theorem dimH_cfAlphabetSet_finset_eq_poincareAbscissa|theorem tendsto_dimH_multiResidueSet" epi_formal/EpiFormal/ResidueMultiAsymptotic.lean`，逐条照录完整签名与 docstring（含行号范围）。
  2. 超临界定理：`rg -n "poincareAbscissa S\) ≤|K₂|K_2" epi_formal/EpiFormal/ResidueMultiAsymptotic.lean`，定位 L4652–4678 附近的 `∃ K₂ > 0 ... m ^ (-(2 * poincareAbscissa S))` 与对偶下界，照录两条完整 theorem。
  3. 公理：`rg -n "axiom" epi_formal/EpiFormal -g "*.lean"`，逐条照录（预期 3 条经典白名单；与 README 口径不一致处明写）。
  4. `rg -n "sorry" epi_formal/EpiFormal -g "*.lean" | Measure-Object -Line` 给总数；抽样 3 条确认全在注释（照录含上下文）。
  5. 只读：不运行 `lake`、不构建、不改任何 `.lean`。
- **路径（产出）**：`verification/lean_anchor_extract_T6_20261124.md`。
- **目标**：T6 Lean 陈述（务实路径：一条新白名单公理 `C_S_pole_decomposition`）与桥接引理的签名底稿；给出公理清单三层级（Lean 基础 / 经典白名单 / 项目自加）。
- **验收**：每条含行号 + 逐字代码；axiom 清单完整；sorry 计数与 3 条样例在案；`git status` 无 ` M`。

## E13｜主稿 A / 主稿 B tex 包装草案（新文件）

- **任务**：为拆分后的两篇主稿各写一个**只含包装**的 .tex（不写正文、不写证明），复用既有切片，供主会话替换两处占位后进入编译验证。
- **方法**：
  1. 先读 `split/slice_index_20261124.csv`、`split/2A_core_gauge_trichotomy/paper2A_draft.tex`、`split/2B_general_theory/paper2B_draft.tex`、`split/2C_windows_residues_finstate/paper2C_draft.tex`，照其 wiring 风格。**包装文件放在 `split/` 目录，因此 `\input` 用 `src_sections/xxx.tex`（无 `../`）；frontmatter 用 `frontmatter-2X-v2.tex`（同目录）。**
  2. **主稿 A（2C + T6）**：新建 `split/mainA_critical_scaling_wrapper_20261124.tex`，依次 `\input`：`src_sections/preamble.tex` → 标题/作者占位（`[Author name]`、`[Affiliation]`）→ `frontmatter-2C-v2.tex` → `src_sections/intro-2C.tex` → `src_sections/prereq-2C.tex` → `sec-finstate.tex` → `sec-windows.tex` → `sec-resasymp.tex` → **新增** `\section{Critical scaling at the phase boundary}\label{sec:critical-scaling}`，节内只放一行注释占位 `% [T6: pole decomposition lemma and Theorem C2 to be inserted by main session]` → `src_sections/refs.tex` → `\end{document}`。**不要**把 `sec-num.tex` 纳入（沿用 2C 草案口径），在报告里标注它是待主会话决定的候选。
  3. **主稿 B（2A + 2B 融合，e 降为旗舰推论）**：新建 `split/mainB_unified_wrapper_20261124.tex`，依次：`src_sections/preamble.tex` → 标题/作者占位 → `frontmatter-2B-v2.tex` → `src_sections/intro-2B.tex` → 2A 正文 `sec-class.tex`、`sec-spectrum-2A.tex`、`sec-finite.tex`、`sec-weights.tex`、`sec-gauge-core.tex`、`sec-num-2A.tex` → 2B 正文 `sec-poly.tex`、`sec-growing.tex` → **新增** `\begin{remark}[Flagship corollary: $e$]\label{rem:e-flagship}`，节内只放注释占位 `% [e flagship corollary: to be inserted; demoted from main theorem]` + `\end{remark}` → `src_sections/refs.tex` → `\end{document}`。**跳过 `prereq-2B.tex`**（2A 正文已全量纳入，复述会重复），在报告里写明该决策待主会话确认。
  4. 自检：对每个 `\input{...}` 用 `Test-Path` 确认目标存在；统计 `{` 与 `}` 数量相等；对全部被纳入文件扫 `\label{...}`，列出出现在 ≥2 个文件中的重复标签（预期无；有则列出）。**不得编译。**
  5. 报告：逐节归属表（paper | section | slice file | 主稿行号 | 是否纳入 | 理由），占位符清单，重复标签结果，`prereq-2B` 与 `sec-num` 两处待决事项。
- **路径（产出）**：`split/mainA_critical_scaling_wrapper_20261124.tex`、`split/mainB_unified_wrapper_20261124.tex`、`split/mainAB_assembly_report_20261124.md`。
- **目标**：两篇主稿的 tex 骨架；主会话只需替换 T6 与 e 推论两处占位即可进入编译验证。
- **验收**：所有 `\input` 目标存在；花括号配对；报告含逐节行号映射与两处待决事项；T6/e 处只有占位、无证明文字；`git status` 只有 `??`。

## E14｜T6 引文核验包（需联网）

- **任务**：把 T6 草案中 `[THEOREM-known, reference unverified]` 的引文逐条核到原始页面，产出可引用/不可引用清单。
- **方法**：逐条检索并**实际打开**出版商页、zbMATH、arXiv 摘要页或作者主页；每条记录：作者、题名、刊名、卷、页、年、DOI、URL、与 T6 相关的 1–2 句**英文原文**摘录（照录）、可引用的定理编号（若有）。目标条目：
  1. Ruelle 算子谱隙：Parry–Pollicott, *Zeta functions and the periodic orbit structure of hyperbolic dynamics*, Astérisque 187–188 (1990)；或 Ruelle 1968 原始论文。
  2. Bowen, *Equilibrium states and the ergodic theory of Anosov diffeomorphisms*, LNM 470, Springer (1975)。
  3. Kato, *Perturbation Theory for Linear Operators*, Grundlehren 132, Springer（1966；2nd ed. 1976）——解析族单重特征值的解析性定理。
  4. Hensley：连分数转移算子/大偏商维数（题名、刊名、卷页、年、DOI）。
  5. Mauldin–Urbański, *Graph Directed Markov Systems*, Cambridge Tracts in Math. 148, CUP (2003)。
  6. Mayer, *On the thermodynamic formalism for the Gauss map*, Ergodic Theory Dynam. Systems 11 (1991)。
  7. 若上述某条检索不到：写「负搜索未找到」，并写明检索词与覆盖范围；**不得**写成「不存在」。
- **路径（产出）**：`verification/T6_citation_pack_20261124.md`。
- **目标**：T6 证明的引文底座；明确哪些可引、哪些只能写 unverified，缺口 (a)(b) 的引文状态可被主会话直接采信。
- **验收**：≥5 条；每条有 URL；字段来源标注（P·DOI / P·卷页 / R 二手 / 未核到）；原文摘录照录；负搜索写明范围；不评价本论文。

## E15｜工程卫生预检（只读，不执行）

- **任务**：为 P2 卫生三项产出决策材料，**不执行任何删除或 git 写操作**。
- **方法**：
  1. `Python/` 盘点：`Get-ChildItem Python -Recurse -File | Measure-Object Length -Sum` 给字节数与文件数；列顶层条目（名称、类型）；`git grep -n "Python/"` 看是否有已跟踪文件引用（只读）。
  2. `slice_index` 新旧关系：对照 `split/README.md` 与 `split/slice_index_20261124.csv`，起草一行注释草稿（新文件，**不插入**既有文件）。
  3. 未跟踪文件分组：`git status --porcelain=v1` 过滤 `??`，按主题分 4–5 组（规划/总览、扫描数据、T6、拆分产物、任务书/台账、其他），给每组文件数与清单（可用通配模式）。
  4. 输出建议的 commit 分组表（组名、文件数、涉及路径），**不执行 commit**。
- **路径（产出）**：`verification/hygiene_precheck_20261124.md`。
- **目标**：PI 决定 `Python/` 处置与 commit 分组的依据。
- **验收**：`Python/` 字节数与文件数实测；`git grep` 命中数（0 或清单）；commit 分组表含文件数；无删除、无 git 写。

## E16｜KMS 补齐（需联网）

- **任务**：补齐 E9 剩余的 Stratmann 合著期刊版 2–3 条，线索 arXiv 1006.5693。
- **方法**：检索 arXiv 1006.5693 的期刊版（作者、题名、刊名、卷页、年、DOI）；再找 2 条 2010–2026 年 KMS 相关期刊论文；逐条给 URL + 1–2 句英文原文摘录（相变/临界结论）+ 字段来源标注；打不开写「未核到」；负搜索写明检索词与范围。
- **路径（产出）**：`verification/kms_comparison_materials_addendum_20261124.md`。
- **目标**：P2B 对照专节的原始素材补页。
- **验收**：2–3 条，每条 URL + 字段来源标注 + 英文摘录；不评价本论文。

---

## 主会话保留（关键/困难，不由 flash 做）

- T6 极点分解引理的完整纸面证明（六步骨架 → 定理，缺口 a/b/c 逐个闭）。
- 桥接引理：CLU Thm 2.3 ↔ 内核 `dimH_cfAlphabetSet_finset_eq_poincareAbscissa` 的相容性陈述与证明。
- Lean 陈述 `C_S_pole_decomposition`（务实路径：一条新白名单公理）与 Layer A 证明。
- E13 产出的审校（节归属、占位符、审计子集声明、`prereq-2B`/`sec-num` 两处待决）。
- 逐条验收：读文件、抽查命令输出；不合格打回并写明差异。

## 回报格式

- 每条一段 ≤100 字：做了什么、产出路径、异常/偏离。
- 不得粘贴大段文件内容到回答；证据写进产出文件。
- 某条无法执行（工具缺失/额度不足）时，写明停在哪一步、已落盘哪些文件，不得虚构完成。
