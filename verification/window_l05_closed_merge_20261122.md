# L05 Frostman 组装闭合 + 真实父依赖尺度 + CF 停止规则树实现合入记录（2026-11-22）

## 一句总判断

L05 Frostman 逐窗组装（`Hwin` discharge）、`hCbig` 与小窗级联、论文真实尺度 $H_j=\lfloor Q_j\sqrt{j}\rfloor$ 与父依赖尺度 $R(j,u)=H_{j+1}/u$ 实例化、`thm:no-short-dim` 实指数维数组装，以及 `thm:windows` 的**具体连分数停止规则柱树实现**（`WindowCFRealize.cfWindowsTree`）全部闭合并通过 Lean 4 内核验证：**5 个新模块共 78 条新声明，全部仅依赖 Lean 基础三公理（`propext`, `Classical.choice`, `Quot.sound`），`sorryAx = 0`；全量审计 724 对 724 双向全唯一**；同时完成树路线与测度路线双非空真见证（`nonvacuous_factorial_tree_dimH`、`nonvacuous_factorial_measure_dimH`）并修复 Paper 2 `rem:windows-lean` 全部 Overfull `\hbox` 溢出（0 error、0 undefined reference、0 Overfull `\hbox`）。

## 新增与修复模块（5 个，78 条声明）

1. **`epi_formal/EpiFormal/WindowTreePrune.lean`**（18 条）：
   - `cantorSet` / `isCompact_cantorSet` / `exists_mem_cantorSet_of_mem_atoms` / `cantorSet_nonempty`（Cantor 闭区间套交非空）。
   - `exists_ancestor_desc` / `atoms_card_le_sum_meet_desc`（`Hcount` 双计数核心）。
   - `pruneTree` 系列（任意非均匀下界树剪枝为精确均匀分支子树，保持 `cantorSet T' j0 ⊆ cantorSet T j0`）。

2. **`epi_formal/EpiFormal/WindowAsympThresh.lean`**（8 条）：
   - `general_overlap_const` / `stopped_overlap_const`、`log_pred_fact_ge`、`asymp_thresh_exists_rpow` / `asymp_thresh_exists`、`coprime_branching_quad`、`coprimeS_branching_rpow`、`hCbig_of_ge_scale`。

3. **`epi_formal/EpiFormal/WindowFrostmanDischarge.lean`**（10 条）：
   - `frostman_of_uniform_tree`、`frostman_of_stopped_tree_rpow`、`dimH_ge_of_stopped_tree_rpow`。
   - **修复父依赖尺度接口**：`dimH_ge_one_of_coprime_tree` 与 `dimH_ge_gamma_of_coprimeS_tree` 改为接收父依赖尺度 `R : ℕ → (ℝ × ℝ) → ℝ`，避免因 `copCount R` 对平移矩形不单调而导致论文真实树无法满足固定 `Rpaper j` 的接口错配。
   - **修复局部质量分布接口**：`mass_distrib_of_local_diam_bound` 改为一般 Frostman 不等式 `μ K ≤ ENNReal.ofReal C * μH[s] K`（不再要求 `ofReal C ≤ μ K`，从而可直接与概率测度的 `mu_window_cascade_full` 组合），新增 `dimH_ge_of_local_diam_bound` 与 `dimH_ge_of_mu_window_cascade`。
   - `mu_singleton_zero_of_support` / `mu_window_cascade_full`（基于真实支撑条件 `μ (cantorSet T j0)ᶜ = 0`）。

4. **`epi_formal/EpiFormal/WindowPaperScale.lean`**（16 条）：
   - `Hpaper` 尺度性质（`Hpaper_pos`, `Hpaper_eq`, `Rpaper_ge_three_mul`, `Rpaper_ge_ten_pow_six`, `Hpaper_ge_three_pow`, `Hpaper_inv_sq_tendsto`, `Hpaper_le_fact`, `Hpaper_log_le`）。
   - 论文真实尺度主定理：
     - `dimH_ge_one_windows_paper_scale`（使用论文 L2430/L2446 真实下界 `(2/5) * Rpaper j ≤ R j u`，自动推出 `(6/5) j ≤ R j u` 与 `10^6 ≤ R j u`）；
     - `dimH_ge_half_prescribed_paper_scale`（`b = 1`，`1/2 ≤ dimH`）；
     - `exists_j0_no_short`、`dimH_ge_gamma_no_short_paper_scale`（从 `Hpaper` 与 `NoShortDim.gamma_pos` 实际 discharge 论文 L2771 的 `c_R = 6/(5 φ²)` 与 `10^6 ≤ R j u`）及 `dimH_ge_one_of_gamma_family`。
   - **双分支非空真机器见证**：`cantorSet_factTree_eq_Icc`、`nonvacuous_factorial_tree_dimH`（树分支）、`nonvacuous_factorial_measure_dimH`（以 `volume.restrict (Icc 0 1)` 零外加前提实例化 `dimH_ge_of_mu_window_cascade`）。

5. **`epi_formal/EpiFormal/WindowCFRealize.lean`**（26 条）：
   - 欧几里得连分数展开 `euclidCF`（`euclidCF_pos_digits`, `euclidCF_col0`, `euclidCF_last_ge_two`）与奇偶翻转孪生 `flipLast` / `chooseParityCF`（`flipLast_col0`, `chooseParityCF_props`）。
   - Möbius 柱区间几何 `mobius` / `cylPair`（`mobius_sub`, `mobius_mul`, `cylPair_len`, `cylPair_len_bounds`, `mobius_mem_cylPair`, `cylPair_nest`, `cylPair_disj_sibling`, `cylPair_disj_of_incomparable`）。
   - 具体停止规则柱树 `cfWindowsTree ε`（`j0CF = 10^6`，`initWord_inv`, `parentScale_ge`, `childWord_transition`, `childWord_incomparable`, `cfWordAtoms_inv_and_incomp`, `cylPair_injOn_atoms`），无树接口假设直接证得：
     `WindowCFRealize.dimH_ge_one_cfWindowsTree : (1 : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet (cfWindowsTree ε) (10 ^ 6))`。

## 仍留纸面的诚实边界

- 将极限点 `x ∈ cantorSet (cfWindowsTree ε) j0CF` 与 mathlib 正则连分数展开的收敛分母序列 `q_n(x)` / 停止指标 `k(j)(x)` 逐点等同的桥梁尚未在 Lean 内形式化。
- `thm:no-short-dim` 的前置 1 块 CF 柱树实现与 `thm:windows` 给定计数构造（`b = 1`）的 CF 柱树实现尚未在 Lean 内构造（其 Frostman 维数组装与真实尺度 `H_j` 已在 `WindowPaperScale.lean` 机检）。
- `thm:residues` 的 Bowen 压力泛函 / 转移算子组装、`thm:short-ae` 的具体遍历系统实例化、`B ≥ 7` 与 `$e+\pi$` 本体均未推进（与之前一致）。

## 复现与验证证据

- `lake build EpiFormal`：EXIT 0（9160 jobs）。
- `lake env lean Audit.lean`：`verification/audit_l05_closed_20261122.log`（EXIT 0）。
- `verification/check_audit_reconcile.py`：
  - `Audit.lean` `#print axioms` = **724**（全唯一）；
  - 日志声明总计 = **724**（与 `Audit.lean` 严格一一对应）；
  - `sorryAx` = **0**；
  - 经典白名单公理（`e_transcendental`, `pi_transcendental`, `mu_e_eq_two`）= **23** 条（全在 Paper 1 侧）；其余 **701** 条（含全部 78 条新增声明）仅依赖 Lean 基础三公理。
- Paper 2：`paper2_spectral_gap_dimension.tex` 更新 `rem:windows-lean` 及文末形式化声明；`pdflatex` 两轮编译 EXIT 0（47 页，716795 bytes，0 error，0 undefined reference，0 Overfull `\hbox`）。
