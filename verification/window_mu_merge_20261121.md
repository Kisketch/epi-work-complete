# E5 合入记录：WindowMuImplication（2026-11-21）

## 一句总判断

`WindowMuImplication.lean`（3 定理：`mu_biUnion_le`、`mu_window_le`、`exp_ratio_bound`）已合入主树，全量审计 **602 条（599+3），`sorryAx = 0`**，3 条全仅依赖 Lean 基础三公理。

## 定理

- `WindowMu.mu_biUnion_le`：有限并次可加（`measure_union_le` 归纳，无需可测假设）。
- `WindowMu.mu_window_le`：窗内质量 ≤ N·m0（`measure_mono` + 次可加 + `sum_le_sum` + `nsmul_eq_mul` + `mul_le_mul_of_nonneg_right`）。
- `WindowMu.exp_ratio_bound`：O(h^s) 代数核心，m0/h^s ≤ C·exp(-(b-2s)j·log j + Oj + sK)（需 `0 ≤ s` 显式假设）。

## 调试留痕（5 处）

1. `ℝ≥0∞` 记号须 `open scoped ENNReal`（"expected token" 即缺作用域）。
2. `Real.rpow_def_of_pos` 给出 `exp (log h * s)`（log 在前）→ 先 `mul_comm` 转向再与 RHS 会合。
3. `Real.log_inv h` 直接可用（无需 `ne_of_gt` 桥）。
4. `Finset.card_nsmul` 不存在 → `Finset.sum_const` + `nsmul_eq_mul`。
5. `mul_le_mul_right'` 已改名 → `mul_le_mul_of_nonneg_right _ bot_le`；删未用假设 `hm0`（零告警纪律）。

## 接线（三处）

- `EpiFormal.lean` / `Audit.lean` 各 +1 import；Audit +3 prints。
- 单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_mu_wired_20261121.log` EXIT 0，602 条。
- 单文件四轮验证日志：`window_mu_verify[_2|_3].log`（终轮零 issue）。

## 下一步

Hinter 实例化组装：`mu_window_le`（测度侧）+ `meet_card_of_diam_le`（计数侧）+ `coprime_count_ge`（输入）→ discharge `frostman_of_count_thresh`，得 windows 质量分布下界（L02/L05 收尾）。
