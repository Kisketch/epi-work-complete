import Mathlib

/-!
# 大窗区阈值（L02a，paper2 §7 windows 固定层上界的大窗部分）

对满足 `dmin ≤ diam U ≤ 1` 的窗，以显式常数
`C(s) = ((2+3L)/d0+2)*m0/dmin^s` discharge F3e 数值阈值。
`diam < dmin` 的小窗区需原子内质量级联细分（接口留用方）。
-/

open Real

namespace WindowLargeThresh

/-- 大窗区数值阈值：`((2D+3L)/d0+2)*m0 ≤ C*diam^s`，其中
    `C = ((2+3L)/d0+2)*m0/dmin^s`。 -/
theorem large_window_thresh {d0 L m0 C s dmin : ℝ} {D : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0)
    (hlo : dmin ≤ D) (hhi : D ≤ 1) (hdmin : 0 < dmin)
    (hs : 0 ≤ s)
    (hC : C = ((2 + 3 * L) / d0 + 2) * m0 / dmin ^ s) :
    ((2 * D + 3 * L) / d0 + 2) * m0 ≤ C * D ^ s := by
  have hDnn : 0 ≤ D := le_trans (le_of_lt hdmin) hlo
  have hdiv : (2 * D + 3 * L) / d0 ≤ (2 + 3 * L) / d0 := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hd0)
    linarith [hhi]
  have h1 : (2 * D + 3 * L) / d0 + 2 ≤ (2 + 3 * L) / d0 + 2 :=
    add_le_add_left hdiv 2
  have h2 : ((2 * D + 3 * L) / d0 + 2) * m0 ≤ ((2 + 3 * L) / d0 + 2) * m0 :=
    mul_le_mul_of_nonneg_right h1 hm0
  have h3 : ((2 + 3 * L) / d0 + 2) * m0 = C * dmin ^ s := by
    rw [hC]
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hdmin s))]
  have hCnn : (0:ℝ) ≤ C := by
    rw [hC]
    apply div_nonneg _ (le_of_lt (Real.rpow_pos_of_pos hdmin s))
    apply mul_nonneg _ hm0
    have hpos : (0:ℝ) ≤ (2 + 3 * L) / d0 + 2 := by
      apply add_nonneg _ (by norm_num)
      apply div_nonneg _ (le_of_lt hd0)
      linarith [hL]
    linarith [hpos]
  have h4 : C * dmin ^ s ≤ C * D ^ s :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hdmin) hlo hs) hCnn
  linarith [h2, h3, h4]

#print axioms WindowLargeThresh.large_window_thresh

end WindowLargeThresh
