import EpiFormal.WindowMuThresh
import EpiFormal.WindowLargeThresh

/-!
# L02b：大窗逐窗质量上界（F3e + L02a 组装）

`dmin ≤ diam U ≤ 1` 的窗：以 L02a 显式常数 discharge F3e 的数值阈值，
得 F1 逐集上界形状。`dmin` 以下的小窗区需级联细分（接口留用方）。
-/

namespace WindowLargeWindow

open scoped ENNReal

variable {μ : MeasureTheory.Measure ℝ}

theorem mu_large_window
    (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R)
    {d0 L m0 C s Mpar dmin : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0) (hMpar : 0 ≤ Mpar)
    (hdmin : 0 < dmin) (hs : 0 ≤ s)
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (K : ℕ) (hK : ((WindowMobiusCount.copCount R : ℕ) : ℝ) ≤ (K : ℝ))
    (hsplit : m0 ≤ Mpar / (K : ℝ))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hdiam_lo : dmin ≤ Metric.diam U) (hdiam_hi : Metric.diam U ≤ 1)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0)
    (hC : C = ((2 + 3 * L) / d0 + 2) * (Mpar * 10000 / R ^ 2) / dmin ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  have hsplit_nn : 0 ≤ Mpar * 10000 / R ^ 2 :=
    div_nonneg (mul_nonneg hMpar (by norm_num)) (by positivity)
  have hnum := WindowLargeThresh.large_window_thresh
    (m0 := Mpar * 10000 / R ^ 2) hd0 hL hsplit_nn
    hdiam_lo hdiam_hi hdmin hs hC
  exact WindowMuThreshLevel.mu_window_thresh_num R hR hd0 hL hm0 hMpar
    P htriv hlen_lo hlen_hi hdisj K hK hsplit U hbddU hcov hbound hnum

#print axioms WindowLargeWindow.mu_large_window
