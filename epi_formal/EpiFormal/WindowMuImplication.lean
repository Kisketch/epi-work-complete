import Mathlib

/-!
# 窗质量蕴含（paper2 §7 Frostman 组装原文 L2536–2559 的形式化）

- `mu_biUnion_le`：有限并的次可加性（`measure_union_le` 归纳）。
- `mu_window_le`：窗口交 N 个原子、每原子质量 ≤ m0 ⇒ 窗内质量 ≤ N·m0。
- `exp_ratio_bound`：m0 ≤ C·exp(-bj·log j + Oj)、log(h⁻¹) ≤ 2j·log j + K ⇒
  m0/h^s ≤ C·exp(-(b-2s)j·log j + Oj + sK)（O(h^s) 代数核心）。
- 质量分布原理（μ(U) ≤ C·diam^s ⇒ dimH ≥ s）由 `CylinderFrostman`
  的 `frostman_of_count_thresh` 承载；本文件提供其 windows 实例的测度侧输入。
-/

namespace WindowMu

open MeasureTheory Finset Real
open scoped ENNReal

variable {ι : Type*} {μ : Measure ℝ}

/-- 有限并次可加（对任意集成立，归纳自 `measure_union_le`）。 -/
theorem mu_biUnion_le (A : ι → Set ℝ) (G : Finset ι) :
    μ (⋃ i ∈ G, A i) ≤ ∑ i ∈ G, μ (A i) := by
  classical
  induction G using Finset.induction with
  | empty => simp
  | @insert a G ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact le_trans (measure_union_le _ _) (add_le_add le_rfl ih)

/-- 窗内质量：交窗原子指标集基数 ≤ N、每原子质量 ≤ m0。 -/
theorem mu_window_le (A : ι → Set ℝ) (G : Finset ι) (U : Set ℝ)
    (N : ℕ) (m0 : ℝ) (hcard : G.card ≤ N)
    (hcover : U ⊆ ⋃ i ∈ G, A i)
    (hbound : ∀ i ∈ G, μ (A i) ≤ ENNReal.ofReal m0) :
    μ U ≤ (N : ℝ≥0∞) * ENNReal.ofReal m0 := by
  classical
  calc μ U ≤ μ (⋃ i ∈ G, A i) := measure_mono hcover
    _ ≤ ∑ i ∈ G, μ (A i) := mu_biUnion_le A G
    _ ≤ ∑ _i ∈ G, ENNReal.ofReal m0 := Finset.sum_le_sum hbound
    _ = (G.card : ℝ≥0∞) * ENNReal.ofReal m0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal m0 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.cast_le.mpr hcard) bot_le

/-- O(h^s) 代数核心：m0/h^s 的指数上界（s < b/2 时指数 -(b-2s)j log j 主导）。 -/
theorem exp_ratio_bound (m0 C b s j Oj K h : ℝ)
    (hC : 0 < C) (hh : 0 < h) (hs : 0 ≤ s)
    (hexp : m0 ≤ C * Real.exp (-b * j * Real.log j + Oj))
    (hlog : Real.log h⁻¹ ≤ 2 * j * Real.log j + K) :
    m0 / h ^ s ≤ C * Real.exp (-(b - 2 * s) * j * Real.log j + Oj + s * K) := by
  have e1 : Real.log h⁻¹ = -Real.log h := Real.log_inv h
  have hrw : m0 / h ^ s = m0 * Real.exp (s * Real.log h⁻¹) := by
    rw [Real.rpow_def_of_pos hh s, div_eq_mul_inv, mul_comm (Real.log h) s, e1,
      show s * -Real.log h = -(s * Real.log h) by ring, Real.exp_neg]
  rw [hrw]
  have h1 : Real.exp (s * Real.log h⁻¹)
      ≤ Real.exp (s * (2 * j * Real.log j + K)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog hs)
  calc m0 * Real.exp (s * Real.log h⁻¹)
      ≤ (C * Real.exp (-b * j * Real.log j + Oj)) * Real.exp (s * (2 * j * Real.log j + K)) :=
        mul_le_mul hexp h1 (Real.exp_pos _).le (mul_nonneg hC.le (Real.exp_pos _).le)
    _ = C * Real.exp (-(b - 2 * s) * j * Real.log j + Oj + s * K) := by
        have e : (-b * j * Real.log j + Oj) + s * (2 * j * Real.log j + K)
            = -(b - 2 * s) * j * Real.log j + Oj + s * K := by ring
        rw [mul_assoc, ← Real.exp_add, e]

#print axioms WindowMu.mu_biUnion_le
#print axioms WindowMu.mu_window_le
#print axioms WindowMu.exp_ratio_bound

end WindowMu
