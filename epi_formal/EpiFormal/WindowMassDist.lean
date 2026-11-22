import Mathlib

/-!
# 直接质量分布原理（windows 用：无公共 M，逐集定标）

Frostman 通用骨架（`CylinderFrostman` 的 S1/S8 tsum 部分）+ Hinter 形状不适配
非均匀树，故此处直接形式化质量分布原理：逐集测度上界
`μ V ≤ C * diam V ^ s` 蕴含 `μ K ≤ ofReal C * μH[s] K`。
后续 windows 实例化只需 discharge 逐集上界（逐集选层），无需公共 M 与纤维一致性。
-/

namespace WindowMass

open MeasureTheory ENNReal

open scoped BigOperators ENNReal

/-- 逐点桥：`ofReal (C * diam^s) ≤ ofReal C * ediam^s`（`⊤` 情形单独处理）。 -/
theorem ofReal_diam_le_mul_ediam_rpow {C s : ℝ} {V : Set ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) :
    ENNReal.ofReal (C * (Metric.diam V) ^ s)
      ≤ ENNReal.ofReal C * Metric.ediam V ^ s := by
  rcases eq_or_ne (Metric.ediam V) ⊤ with htop | htop
  · have hd0 : Metric.diam V = 0 := by
      unfold Metric.diam
      rw [htop, ENNReal.toReal_top]
    rw [hd0, Real.zero_rpow (ne_of_gt hs), mul_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have he : Metric.ediam V = ENNReal.ofReal (Metric.diam V) :=
      (ENNReal.ofReal_toReal htop).symm
    rw [he, ENNReal.ofReal_rpow_of_nonneg Metric.diam_nonneg (le_of_lt hs),
      ← ENNReal.ofReal_mul hC]

/-- 直接质量分布原理：逐集 `μ V ≤ C * diam V ^ s` 蕴含
`μ K ≤ ofReal C * μH[s] K`（对一切可数覆盖取下确界再取上确界）。 -/
theorem mass_distrib_of_diam_bound {μ : Measure ℝ} {K : Set ℝ} {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s)
    (hK : ENNReal.ofReal C ≤ μ K)
    (h : ∀ V : Set ℝ, μ V ≤ ENNReal.ofReal (C * (Metric.diam V) ^ s)) :
    1 ≤ MeasureTheory.Measure.hausdorffMeasure s K := by
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (1 : ℝ≥0∞) one_pos)
  apply le_iInf; intro t; apply le_iInf; intro hcov; apply le_iInf; intro _
  -- 逐覆盖：1 ≤ Σ' ediam^s
  have hsub : μ K ≤ ∑' n, μ (t n) := by
    have hle : μ.toOuterMeasure (⋃ n, t n) ≤ ∑' n, μ.toOuterMeasure (t n) :=
      MeasureTheory.measure_iUnion_le t
    have hle2 : μ (⋃ n, t n) ≤ ∑' n, μ (t n) := by
      simpa [MeasureTheory.Measure.toOuterMeasure_apply] using hle
    exact le_trans (measure_mono hcov) hle2
  have hterm : ∀ n, μ (t n)
      ≤ ENNReal.ofReal C * Metric.ediam (t n) ^ s := by
    intro n
    exact le_trans (h (t n)) (ofReal_diam_le_mul_ediam_rpow (le_of_lt hC) hs)
  have hCS : ENNReal.ofReal C
      ≤ ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s := by
    refine le_trans hK (le_trans hsub ?_)
    calc ∑' n, μ (t n)
        ≤ ∑' n, (ENNReal.ofReal C * Metric.ediam (t n) ^ s) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s :=
          ENNReal.tsum_mul_left
  -- 消去 ofReal C（≠ 0，≠ ⊤），得逐覆盖下界
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hCt : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : (1 : ℝ≥0∞) ≤ ∑' n, Metric.ediam (t n) ^ s := by
    have h4 := mul_le_mul_of_nonneg_left hCS (show (0 : ℝ≥0∞) ≤ (ENNReal.ofReal C)⁻¹ by positivity)
    have h3 : ((ENNReal.ofReal C)⁻¹ * ENNReal.ofReal C) * ∑' n, Metric.ediam (t n) ^ s
        = (ENNReal.ofReal C)⁻¹ * (ENNReal.ofReal C * ∑' n, Metric.ediam (t n) ^ s) := by
      rw [mul_assoc]
    rw [← h3, ENNReal.inv_mul_cancel hC0 hCt, one_mul] at h4
    exact h4
  -- guarded sup 与裸项逐点相等（空集情形用 ediam_empty + zero_rpow + bot_eq_zero）
  have hguard : ∀ n, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s)
      = Metric.ediam (t n) ^ s := by
    intro n
    by_cases h : (t n).Nonempty
    · simp only [h]
      exact iSup_const
    · have hempty : t n = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hempty, Metric.ediam_empty]
      have hz : ((0 : ℝ≥0∞) ^ s) = 0 := by
        rw [← ENNReal.ofReal_zero,
          ENNReal.ofReal_rpow_of_nonneg le_rfl hs.le,
          Real.zero_rpow (ne_of_gt hs), ENNReal.ofReal_zero]
      apply le_antisymm
      · apply iSup_le; intro _; exact le_rfl
      · rw [hz]; exact bot_le
  simpa only [hguard] using h2

#print axioms WindowMass.ofReal_diam_le_mul_ediam_rpow
#print axioms WindowMass.mass_distrib_of_diam_bound

end WindowMass
