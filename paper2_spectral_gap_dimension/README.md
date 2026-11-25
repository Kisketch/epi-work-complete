# 论文二目录导航（`paper2_spectral_gap_dimension/`）

> 本目录归档论文二《Complete spectrum discretization, exact Hausdorff gauges, and dimension phase transitions for Diophantine approximation along the convergent denominators of $e$》当前完整合稿、两篇独立衍生定理论文（**Paper 2D** 与 **Paper 2E**）、独立研究日志与指南（[`00_research_log_and_guide/`](00_research_log_and_guide/SPINOFF_AND_TRIAL_LOG.md)）、历史冻结版本，以及面向投稿拆分的四轨（2A / 2B / 2C / S）源切片工程。遵循 [`AGENTS.md`](../AGENTS.md) 诚实基线：**本论文不解决 $e+\pi$ 的无理性问题。**

## 一、主文定稿文件（`2026-11-25` Round 2 同步重编）

| 文件 | 说明 | 实测规格 |
| :--- | :--- | :--- |
| [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension.tex) | 论文二完整主稿 TeX，与 [`split/src_sections/slice_index.csv`](split/src_sections/slice_index.csv) 的 11 个切片拼接**逐字节一致** | `293,395` 字节、`4,568` 行、`86` 个唯一 `\label`、`28/28` `\bibitem` 全引用 |
| [`paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension.pdf) | 洁净 `pdflatex` 重编最新 PDF（同步接入 `ResidueCertStrictOpen` 消去 R1、`PerronFrobenius` 消去 R3，以及 2D/2E 指引与 `356` 文件 / `1,093` 声明全量 Lean 审计映射） | **66 页** |
| [`paper2_spectral_gap_dimension.log`](paper2_spectral_gap_dimension.log) | 最新 `pdflatex` 完整编译日志 | EXIT 0、0 `Undefined`、0 `Overfull \hbox` |
| [`spinoff_critical_and_supercritical_exact_20261125/`](spinoff_critical_and_supercritical_exact_20261125/README.md) | **Paper 2D**：临界标度 7 缺陷全修复、无条件超临界精确主导常数与稀疏字母表尾相变（附 `GeneralAlphabetFloor` [15] & `SupercriticalConstant` [6] Lean 4 模块） | **18 页**、0 错 / 0 Undefined / 0 Overfull |
| [`spinoff_full_convergent_and_even_hurwitz_20261125/`](spinoff_full_convergent_and_even_hurwitz_20261125/README.md) | **Paper 2E**：$e$ 全正则收敛列完整谱论、任意 Hurwitz 拟周期 $(-1)^{p-1}$ 符号律、无 Brouwer PF 消去（附 `FullConvergentSpectrum` [40] & `PerronFrobenius` [13] Lean 4 模块） | **8 页**、0 错 / 0 Undefined / 0 Overfull |
| [`00_research_log_and_guide/`](00_research_log_and_guide/SPINOFF_AND_TRIAL_LOG.md) | 物理分离的衍生演进/对抗纠偏日志 [`SPINOFF_AND_TRIAL_LOG.md`](00_research_log_and_guide/SPINOFF_AND_TRIAL_LOG.md) 与总研究指南 [`MASTER_GUIDE_SKILL.md`](00_research_log_and_guide/MASTER_GUIDE_SKILL.md) | 与主文/Lean 源码完全隔离 |

## 二、2026-11-23 至 2026-11-25 补丁脚本（按时间演化留存）

* [`patch_residues_N512_20261123.py`](patch_residues_N512_20261123.py)：将 `tab:residues-general` 与上界从 $N=256$ 更新为 $N=512$（$359/512 \to 179/256$），补充 `rem:residue-kernel`。
* [`patch_stale_N512_20261123.py`](patch_stale_N512_20261123.py)：清理 $N=256$ 改稿遗留表述并同步拆分源切片。
* [`patch_blr_remarks_20261123.py`](patch_blr_remarks_20261123.py) / [`patch_blr_remarks_fix_20261123.py`](patch_blr_remarks_fix_20261123.py)：新增与校准 Bugeaud–Liao–Rams (BLR) 对比注记 `rem:poly-BLR` / `rem:growing-BLR`。
* [`patch_fourth_term_remark_20261124.py`](patch_fourth_term_remark_20261124.py)：新增启发式四阶项注记 `rem:fourth-term` 与 `tab:fourth-term`（明确标为猜想与非严格数值佐证），并记录第二次 Colab 独立复建审计。
* [`patch_evidence_citations_20261125.py`](patch_evidence_citations_20261125.py)：增补 `Hensley1996`（含勘误）、`JP2018`、`CLN2026`、`CLUW2024`、`Brown2026`、`TTWW2026`、`BW2025` 并规范 DOI。
* [`patch_novelty_wording_20261125.py`](patch_novelty_wording_20261125.py) / [`patch_blr_baker_fix_20261125.py`](patch_blr_baker_fix_20261125.py) / [`patch_unify_20261125.py`](patch_unify_20261125.py)：按投稿前新颖性核查改写 `sec:prior` 与诚实边界并增补 `DFSU`/`MU96`/`Good41`/`HU02`/`Hensley92`/`DLMF`，修正 `rem:poly-BLR`/`rem:growing-BLR` Baker 措辞，并完成 **28/28 文献全并集**、DOI 无 `\allowbreak` 清洗与 L283 `m^{-1-\varepsilon}` 笔误修正。
* [`patch_round2_20261125.py`](patch_round2_20261125.py)：同步 Round 2 Lean 内核消除 R1（`ResidueCertStrictOpen` 22）与 R3（`PerronFrobenius` 13），接入 Paper 2D/2E 与全库 356 文件 / 1,093 条声明统计并重建 11 切片与 `frontmatter-2C`/`sec-finstate`。

## 三、拆分三轨一补工程（[`split/`](split/README.md)）与 `v3` 临界标度实验归档（[`drafts_v3_critical_scaling/`](drafts_v3_critical_scaling/README.md)）

* **权威总览与记录**：[`split/README.md`](split/README.md)、[`split/BUILD_TRIAL_LOG.md`](split/BUILD_TRIAL_LOG.md)、[`split/src_sections/SLICE_LOG.md`](split/src_sections/SLICE_LOG.md)、[`split/derive_2A_pub.py`](split/derive_2A_pub.py)。
* **源文件共享切片**：[`split/src_sections/`](split/src_sections/)（核心 11 片登记于 [`slice_index.csv`](split/src_sections/slice_index.csv)，另有 `preamble.tex`、`frontmatter.tex`、`intro-shared.tex`、`refs.tex`、2A 投稿呈现版 `*-2Apub.tex` 与 `refs-2Apub.tex` 及三轨派生引言/前提切片）。
* **四个独立编译目录**（再生 PDF 由 `.gitignore` 忽略，编译日志入库留痕）：
  * **2A 核心规范与三分法（期刊呈现版 `*-2Apub`）**：[`split/2A_core_gauge_trichotomy/paper2A_draft.tex`](split/2A_core_gauge_trichotomy/paper2A_draft.tex)（21 页，0 未定义引用，0 Overfull）
  * **2B 一般递推理论**：[`split/2B_general_theory/paper2B_draft.tex`](split/2B_general_theory/paper2B_draft.tex)（16 页，0 未定义引用，0 Overfull）
  * **2C 窗口、残差与有限状态**：[`split/2C_windows_residues_finstate/paper2C_draft.tex`](split/2C_windows_residues_finstate/paper2C_draft.tex)（26 页，含 §7.5 `thm:multi-residue-asymptotic`，0 未定义引用，0 Overfull）
  * **S 补充材料（Supplement）**：[`split/S_supplement/paperS_draft.tex`](split/S_supplement/paperS_draft.tex)（8 页，0 未定义文献引文；说明见 [`split/S_supplement/MANIFEST.md`](split/S_supplement/MANIFEST.md)）
* **T6 临界标度 `v3` 与两主稿实验存档**：[`drafts_v3_critical_scaling/README.md`](drafts_v3_critical_scaling/README.md)（独立归档 `sec-critical-scaling.tex`、`paper2_spectral_gap_dimension_v3_20261124.pdf` 70 页、`paper2A_critical_scaling_draft_20261124.pdf` 31 页与 `paper2B_unified_draft_20261124.pdf` 35 页，不替代主稿 11 切片）。

## 四、历史冻结版本（[`historical_versions/`](historical_versions/)）

保留全部里程碑快照以便对照回溯：`paper2_old.tex/.pdf`、`paper2_20261118.tex/.pdf`、`paper2_integrated_v20261122_ed61a92.tex`、`paper2_integrated_v20261123_1e91028.tex/.pdf`、`paper2_integrated_v20261123_7ece3b9.tex`（`256,402` 字节 LF），以及 `numerics/` 与 `paper2_submission_snapshot.zip`。

## 五、常用复现与校验命令

```powershell
# 1. 结构、标签、引文、切片逐字节一致性与完整内容校验
python ..\verification\verify_paper2_merge.py

# 2. 拆分轨引用与文献核查
python split\undef_ref_audit.py

# 3. 洁净重编主论文（三遍）
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
```
