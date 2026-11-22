# LogFact 合入记录：WindowLogFact（2026-11-21）

## 一句总判断

`WindowLogFact.lean`（2 定理：`log_factorial_ge`、`log_factorial_le`）已合入主树，全量审计 **620 条（618+2），`sorryAx = 0`**，2 条全仅依赖 Lean 基础三公理。

## 定理

- `log_factorial_ge`：`n * log n - n ≤ log (n!)`（mathlib `Real.le_sum_log_nat` + `sum_log_eq_log_factorial` 桥；常数 1，用 Stirling）。
- `log_factorial_le`：`log (n!) ≤ n * log n`（`Real.sum_log_le'` 在 `x = n` 处取值，需 `1 ≤ N`）。

## 关键发现（mathlib 现货）

- 2026 版 mathlib 已有 Tao 的解析数论新增（`Analysis/SpecialFunctions/Log/Sum.lean`）：`sum_log_eq_log_factorial`、`sum_log_add_one_eq_log_factorial`、`sum_log_le`/`le_sum_log`、`le_sum_log_nat`（Stirling 下界）。
- 备选路线（exp 级数单项界）未用：`expSeries_div_hasSum_exp` + `Real.exp_eq_exp_ℝ` 链已确认存在，但 Stirling 现货更直接。
- `Finset.prod_le_pow_card`、`Finset.prod_range_add_one_eq_factorial` 实名确认（上界路线备用，未用）。

## 调试留痕（2 处）

1. `!` 后缀表示法在 `(N ! : ℝ)` 位置解析失败（"expected no space before or term"）→ 改 `Nat.factorial N` 全名。
2. 初版写坏一行（`#AverageMenuBar...` 混入）→ 立即修复。

## 接线 / 验证

- 两入口各 +1 import；Audit +2 prints；单文件两轮验证（终轮 EXIT 0 零 issue）；单目标构建 EXIT 0（9047 jobs）；全量审计 `audit_logfact_wired_20261121.log` EXIT 0，620 条。
- `#print` 双定理均为 `[propext, Classical.choice, Quot.sound]`。

## 下一步

阈值 discharge：`log M_j ≥ b(j log j - j)`（level_count + log_fact_ge）+ 对数比较（`log H_j = j log j + O(j)` e-side 接口）+ `h^s` 桥 ⇒ F3 阈值数值化。
