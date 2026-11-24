# 论文二目录导航（`paper2_spectral_gap_dimension/`）

> 本目录归档论文二《Complete spectrum discretization, exact Hausdorff gauges, and dimension phase transitions for Diophantine approximation along the convergent denominators of $e$》当前完整合稿、历史冻结版本，以及面向投稿拆分的四轨（2A / 2B / 2C / S）源切片工程。遵循 [`AGENTS.md`](../AGENTS.md) 诚实基线：**本论文不解决 $e+\pi$ 的无理性问题。**

## 一、主文定稿文件（`2026-11-23` 最新重编）

| 文件 | 说明 | 实测规格 |
| :--- | :--- | :--- |
| [`paper2_spectral_gap_dimension.tex`](paper2_spectral_gap_dimension.tex) | 论文二完整主稿 TeX，与 [`split/src_sections/slice_index.csv`](split/src_sections/slice_index.csv) 的 11 个切片拼接**逐字节一致** | `279,145` 字节、`4,403` 行、`84` 个唯一 `\label`、`15/15` `\bibitem` 全引用 |
| [`paper2_spectral_gap_dimension.pdf`](paper2_spectral_gap_dimension.pdf) | 洁净 `pdflatex` 三遍重编最新 PDF（含新增 §7.5 `thm:multi-residue-asymptotic` 与 `tab:multi-residue-asymptotic`） | **63 页**、`894,432` 字节 |
| [`paper2_spectral_gap_dimension.log`](paper2_spectral_gap_dimension.log) | 最新 `pdflatex` 完整编译日志 | EXIT 0、0 `Undefined`、0 `Overfull \hbox` |
| [`paper2_build_tectonic_20261123.log`](paper2_build_tectonic_20261123.log) | `7ece3b9` 阶段 `tectonic` 编译历史留痕（保留备查） | 对应 59 页历史节点 |

## 二、2026-11-23 补丁脚本（按时间演化留存）

* [`patch_residues_N512_20261123.py`](patch_residues_N512_20261123.py)：将 `tab:residues-general` 与上界从 $N=256$ 更新为 $N=512$（$359/512 \to 179/256$），补充 `rem:residue-kernel`。
* [`patch_stale_N512_20261123.py`](patch_stale_N512_20261123.py)：清理 $N=256$ 改稿遗留表述并同步拆分源切片。
* [`patch_blr_remarks_20261123.py`](patch_blr_remarks_20261123.py) / [`patch_blr_remarks_fix_20261123.py`](patch_blr_remarks_fix_20261123.py)：新增与校准 Bugeaud–Liao–Rams (BLR) 对比注记 `rem:poly-BLR` / `rem:growing-BLR`。

## 三、拆分三轨一补工程（[`split/`](split/README.md)）

* **权威总览与记录**：[`split/README.md`](split/README.md)、[`split/BUILD_TRIAL_LOG.md`](split/BUILD_TRIAL_LOG.md)、[`split/src_sections/SLICE_LOG.md`](split/src_sections/SLICE_LOG.md)。
* **源文件共享切片**：[`split/src_sections/`](split/src_sections/)（核心 11 片登记于 [`slice_index.csv`](split/src_sections/slice_index.csv)，另有 `preamble.tex`、`frontmatter.tex`、`intro-shared.tex`、`refs.tex` 及三轨派生引言/前提切片）。
* **四个独立编译目录**（再生 PDF 由 `.gitignore` 忽略，编译日志入库留痕）：
  * **2A 核心规范与三分法**：[`split/2A_core_gauge_trichotomy/paper2A_draft.tex`](split/2A_core_gauge_trichotomy/paper2A_draft.tex)（24 页，0 未定义引用）
  * **2B 一般递推理论**：[`split/2B_general_theory/paper2B_draft.tex`](split/2B_general_theory/paper2B_draft.tex)（15 页，0 未定义引用）
  * **2C 窗口、残差与有限状态**：[`split/2C_windows_residues_finstate/paper2C_draft.tex`](split/2C_windows_residues_finstate/paper2C_draft.tex)（24 页，含 §7.5 `thm:multi-residue-asymptotic`，0 未定义引用）
  * **S 补充材料（Supplement）**：[`split/S_supplement/paperS_draft.tex`](split/S_supplement/paperS_draft.tex)（说明见 [`split/S_supplement/MANIFEST.md`](split/S_supplement/MANIFEST.md)）

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
