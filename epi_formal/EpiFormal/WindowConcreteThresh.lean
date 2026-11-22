import EpiFormal.WindowRealize

/-!
# F3g：stopped 层阈值的具体数值实例

`stopped_window_realize` 的数值阈值 `hnum` 在一组具体参数
（`R = 10^6`、`H = 100`、`s = 1`、`Mpar = 1`、`C = 1/500`、
`d0 = 4/(25·100²)`、`L = 9/(16·100²)`、`diam U = 1`）下由 `norm_num`
直接验证。

剩余接口（`hK` realize 计数、`hsplit` 均分、`hcov` 覆盖、
`hbound` 逐原子质量）属于用方的柱族构造，由具体应用 discharge。
-/

namespace WindowConcrete

open scoped ENNReal

variable {μ : MeasureTheory.Measure ℝ}

theorem stopped_window_unit
    {m0 : ℝ} {_d0 _L : ℝ}
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hden : ∀ I ∈ P, ∃ q₀ q₁ : ℝ, 4 * (100 : ℝ) / 3 ≤ q₀ ∧ q₀ ≤ 5 * (100 : ℝ) / 2 ∧
      4 * (100 : ℝ) / 3 ≤ q₁ ∧ q₁ ≤ 5 * (100 : ℝ) / 2 ∧ I.2 - I.1 = 1 / (q₀ * q₁))
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hK : ((WindowMobiusCount.copCount (10 ^ 6 : ℝ) : ℕ) : ℝ) ≤ (P.card : ℝ))
    (hsplit : m0 ≤ 1 / (P.card : ℝ))
    (hm0 : 0 ≤ m0)
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hdiam : Metric.diam U = 1)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0) :
    μ U ≤ ENNReal.ofReal ((1 / 500 : ℝ) * Metric.diam U ^ (1 : ℝ)) := by
  have hR : (10 ^ 6 : ℝ) ≤ (10 ^ 6 : ℝ) := le_rfl
  have hH : (0 : ℝ) < (100 : ℝ) := by norm_num
  have hnum : ((2 * Metric.diam U + 3 * (9 / (16 * (100 : ℝ) ^ 2))) /
      (4 / (25 * (100 : ℝ) ^ 2)) + 2) * ((1 : ℝ) * 10000 / (10 ^ 6 : ℝ) ^ 2)
      ≤ (1 / 500 : ℝ) * Metric.diam U ^ (1 : ℝ) := by
    rw [hdiam]
    norm_num
  refine WindowRealize.stopped_window_realize (10 ^ 6 : ℝ) (100 : ℝ) hR hH ?_ ?_
    hm0 ?_ rfl rfl P htriv hden hdisj hK hsplit U hbddU hcov hbound hnum
  · norm_num
  · norm_num
  · norm_num

#print axioms WindowConcrete.stopped_window_unit

end WindowConcrete
