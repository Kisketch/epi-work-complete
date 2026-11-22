import EpiFormal.WindowMuLevel
import EpiFormal.WindowSplitMass
import EpiFormal.WindowMobiusCount

/-!
# F3e：stopped 层阈值数值化（用方实例化接口）

`uniform_split_mass_bound`（每原子质量 `m0 ≤ Mpar*10000/R²`）+
`mu_le_at_level`（固定层上界）⇒ stopped 层逐窗质量上界。

显式纸面接口（用方 discharge）：
- `hK`：被计数的互素对实现为互不相同的子柱数下界（realize 桥）；
- `hsplit`：等条件概率均分（每原子质量 `≤ Mpar/K`）；
- `hnum`：以具体 `R/H/s/C/d0/L` 数值验证的阈值不等式；
- 原子族几何（`htriv/hlen_lo/hlen_hi/hdisj`）、覆盖（`hcov`）、逐原子质量（`hbound`）。
-/

namespace WindowMuThreshLevel

open WindowMobiusCount WindowSplitMass WindowMuLevel

variable {μ : MeasureTheory.Measure ℝ}

/-- stopped 层逐窗质量上界：分裂质量界 + 固定层上界组装。 -/
theorem mu_window_thresh_num
    (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R)
    {d0 L m0 C s Mpar : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0) (hMpar : 0 ≤ Mpar)
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (K : ℕ) (hK : ((copCount R : ℕ) : ℝ) ≤ (K : ℝ))
    (hsplit : m0 ≤ Mpar / (K : ℝ))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0)
    (hnum : ((2 * Metric.diam U + 3 * L) / d0 + 2) * (Mpar * 10000 / R ^ 2)
      ≤ C * Metric.diam U ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  have hm0' : m0 ≤ Mpar * 10000 / R ^ 2 :=
    uniform_split_mass_bound R hR K hK Mpar m0 hMpar hsplit
  have hfac : 0 ≤ (2 * Metric.diam U + 3 * L) / d0 + 2 := by
    have hD : 0 ≤ Metric.diam U := Metric.diam_nonneg
    have h1 : (0 : ℝ) ≤ (2 * Metric.diam U + 3 * L) / d0 :=
      div_nonneg (by linarith [hD, hL]) (le_of_lt hd0)
    linarith
  have hthresh : ((2 * Metric.diam U + 3 * L) / d0 + 2) * m0
      ≤ C * Metric.diam U ^ s := by
    have hstep : ((2 * Metric.diam U + 3 * L) / d0 + 2) * m0
        ≤ ((2 * Metric.diam U + 3 * L) / d0 + 2) * (Mpar * 10000 / R ^ 2) :=
      mul_le_mul_of_nonneg_left hm0' hfac
    exact le_trans hstep hnum
  exact mu_le_at_level hd0 hL hm0 P htriv hlen_lo hlen_hi hdisj U hbddU hcov
    hbound hthresh

#print axioms WindowMuThreshLevel.mu_window_thresh_num

end WindowMuThreshLevel
