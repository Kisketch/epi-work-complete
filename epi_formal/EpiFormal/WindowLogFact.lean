import Mathlib

/-!
# 对数阶乘界（阈值 O(j) 项的显式常数）

为质量分布阈值 discharge 提供 Stirling 阶乘界，两-sided，常数 1 不可改进方向：

- `log_factorial_ge`：`n * log n - n ≤ log (n!)`（经 `Real.le_sum_log_nat`，mathlib 内 Stirling）。
- `log_factorial_le`：`log (n!) ≤ n * log n`（经 `Real.sum_log_le'` 在 `x = n` 处取值）。

桥引理（mathlib 现货）：
- `Real.sum_log_eq_log_factorial`：`∑ n ∈ Ioc 0 N, log n = log N !`。
- `Real.sum_log_add_one_eq_log_factorial`：range 版本（备用）。
-/

namespace WindowLogFact

open Finset Real

/-- Stirling 下界：`n * log n - n ≤ log (n!)`（mathlib `le_sum_log_nat` + 求和↔阶乘桥）。 -/
theorem log_factorial_ge (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (Nat.factorial N : ℝ) := by
  have h := Real.le_sum_log_nat N
  rwa [Real.sum_log_eq_log_factorial] at h

/-- 平凡上界：`log (n!) ≤ n * log n`（`n ≥ 1`；`sum_log_le'` 在 `x = n` 处取值）。 -/
theorem log_factorial_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log (Nat.factorial N : ℝ) ≤ (N : ℝ) * Real.log N := by
  have hx : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h := Real.sum_log_le' (x := (N : ℝ)) hx
  rw [Nat.floor_natCast] at h
  rwa [Real.sum_log_eq_log_factorial] at h

#print axioms WindowLogFact.log_factorial_ge
#print axioms WindowLogFact.log_factorial_le

end WindowLogFact
