# 论文二扩展实验稿：`T6` 临界标度与两主稿草案（`drafts_v3_critical_scaling/`）

> **定位声明**：本目录完整归档 `2026-11-24/25` 于本地开展的 **T6 临界标度定理化**（`sec-critical-scaling.tex`）及 `v3` / 两主稿试装配实验线，与主仓标准 11 切片真源（[`../split/src_sections/slice_index.csv`](../split/src_sections/slice_index.csv)）及 [`../paper2_spectral_gap_dimension.tex`](../paper2_spectral_gap_dimension.tex) 隔离存放，**不替代标准主稿与 `split/` 三轨**。

## 一、数学结论与形式化诚实边界

1. **论文正文层面的已证结果**（见 [`sec-critical-scaling.tex`](sec-critical-scaling.tex)，其中部分论证依赖仓库转移算子准则 `thm:residues-general`(ii)）：
   - `lem:pole`：在 Banach 空间 $A(\{|z-1|<1\})$ 上，由 Perron–Frobenius + Kato 解析摄动证得 $C_S(p)=\kappa(S)/(p-2s_0(S))+O(1)$；
   - `lem:resolvent-uniform`、`lem:master`：建立均匀双侧预解展开与主方程（下界侧以有限子字母表 $K=\lceil e^{m^3}\rceil$ 闭环）；
   - `thm:critical-scaling`、`cor:critical-exp`：联合标度极限 $m^{1/2}(\dimH F_{m,S,B}-1/2)\to\Phi(x)/2$（$\Phi(x)=(-x+\sqrt{x^2+4d\kappa})/2$），给出临界指数 $1/2$ 与振幅 $\sqrt{d\kappa}/2$，无对数修正。
2. **未证明 / 启发式 / 已证伪部分**：
   - **未证（启发式猜想）**：超临界主导常数 $\frac{d\kappa(S)}{2(2s_0(S)-1)}m^{-2s_0(S)}$（`prop:supercritical-constant` / `rem:supercritical-status`）、临界线 $s_0(S)=1/2$ 整数集合存在性及 $\kappa(S)$ 连续性；
   - **已证伪**：固定 $\eta\neq0$ 形式的旧猜想 C2（`rem:naive-C2-false`，复算脚本 [`../../verification/verify_c2_discrepancy_20261124.py`](../../verification/verify_c2_discrepancy_20261124.py)）；
   - **Lean 4 状态**：T6 分析层未入 Lean 内核；配套草稿接口 [`Paper2C.lean`](../../verification/lean_drafts/paper_interfaces_20261124/Paper2C.lean) 对 `lem:pole` 显式声明了 1 条项目公理 `C_S_pole_decomposition`（隔离在 `verification/lean_drafts/`，未并入 `epi_formal/`）。

## 二、归档文件索引

- 集成稿 v3 与补丁：[`paper2_spectral_gap_dimension_v3_20261124.tex`](paper2_spectral_gap_dimension_v3_20261124.tex) / [`.pdf`](paper2_spectral_gap_dimension_v3_20261124.pdf) / [`.log`](paper2_spectral_gap_dimension_v3_20261124.log)、[`sec-critical-scaling.tex`](sec-critical-scaling.tex)、[`refs-addendum-20261124.tex`](refs-addendum-20261124.tex)、[`BUILD_LOG_20261124.md`](BUILD_LOG_20261124.md)、[`patch_t6_integration_20261124.py`](patch_t6_integration_20261124.py)、[`patch_e17_upgrade_20261125.py`](patch_e17_upgrade_20261125.py)、[`patch_abstract_scope_20261124.py`](patch_abstract_scope_20261124.py)。
- 两主稿试装配草案：[`paper2A_critical_scaling_draft_20261124.tex`](paper2A_critical_scaling_draft_20261124.tex) / [`.pdf`](paper2A_critical_scaling_draft_20261124.pdf)（2C+T6, 31 页）、[`paper2B_unified_draft_20261124.tex`](paper2B_unified_draft_20261124.tex) / [`.pdf`](paper2B_unified_draft_20261124.pdf)（2A+2B, 35 页）、[`refs-2C-v3-20261124.tex`](refs-2C-v3-20261124.tex)、`frontmatter-*-v2/v3*.tex`、[`frontmatter_v2_report_20261124.md`](frontmatter_v2_report_20261124.md)、[`slice_index_20261124.csv`](slice_index_20261124.csv)、[`slice_concat_check_20261124.md`](slice_concat_check_20261124.md)。
