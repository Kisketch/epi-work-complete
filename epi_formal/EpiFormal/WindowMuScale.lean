import EpiFormal.WindowMuLevel

/-!
# F3c：stopped 层数值阈值（diam 双侧夹 ⇒ 纯数值条件）

`mu_le_at_level` 的逐窗阈值 `((2*diam+3L)/d0+2)*m0 ≤ C*diam^s`
含窗直径 diam U。用三明治双侧夹 `dmin ≤ diam U ≤ dmax`
把阈值归约为**纯数值条件**（`hnum`，在用方以具体 R/H/s 数值 discharge）：

  `((2*dmax+3L)/d0+2)*m0 ≤ C*dmin^s`。

`stopped_window_bound` 把归约与 `mu_le_at_level` 组装，
给出可直接喂给 F1 主定理的逐窗上界。
-/

open Set Finset Real Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace WindowMuScale

variable {μ : MeasureTheory.Measure ℝ}

/-- 数值阈值归约：diam 双侧夹 ⇒ 逐窗阈值。 -/
theorem stopped_thresh_of_scale {d0 L m0 C s dmin dmax : ℝ}
    (hd0 : 0 < d0) (_hL : 0 ≤ L) (hm0 : 0 ≤ m0) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hdmin : 0 ≤ dmin)
    (hnum : ((2 * dmax + 3 * L) / d0 + 2) * m0 ≤ C * dmin ^ s)
    (U : Set ℝ) (hdlo : dmin ≤ Metric.diam U) (hdhi : Metric.diam U ≤ dmax) :
    ((2 * Metric.diam U + 3 * L) / d0 + 2) * m0 ≤ C * Metric.diam U ^ s := by
  have hle : (2 * Metric.diam U + 3 * L) / d0 ≤ (2 * dmax + 3 * L) / d0 :=
    div_le_div_of_nonneg_right (by linarith [hdhi]) (le_of_lt hd0)
  have h1 : ((2 * Metric.diam U + 3 * L) / d0 + 2) * m0
      ≤ ((2 * dmax + 3 * L) / d0 + 2) * m0 := by
    have h2 : (2 * Metric.diam U + 3 * L) / d0 + 2
        ≤ (2 * dmax + 3 * L) / d0 + 2 := by linarith [hle]
    exact mul_le_mul_of_nonneg_right h2 hm0
  have h2 : C * dmin ^ s ≤ C * Metric.diam U ^ s := by
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow hdmin hdlo hs
  exact le_trans h1 (le_trans hnum h2)

/-- stopped 层逐窗上界（F1 逐集上界形状，可直接实例化主定理）。 -/
theorem stopped_window_bound {d0 L m0 C s dmin dmax : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hdmin : 0 ≤ dmin)
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hnum : ((2 * dmax + 3 * L) / d0 + 2) * m0 ≤ C * dmin ^ s)
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0)
    (hdlo : dmin ≤ Metric.diam U) (hdhi : Metric.diam U ≤ dmax) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) :=
  WindowMuLevel.mu_le_at_level hd0 hL hm0 P htriv hlen_lo hlen_hi hdisj U hbddU
    hcov hbound (stopped_thresh_of_scale hd0 hL hm0 hs hC hdmin hnum U hdlo hdhi)

#print axioms WindowMuScale.stopped_thresh_of_scale
#print axioms WindowMuScale.stopped_window_bound

end WindowMuScale
