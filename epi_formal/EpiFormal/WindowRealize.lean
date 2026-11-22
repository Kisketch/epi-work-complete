import EpiFormal.WindowMuThresh
import EpiFormal.WindowOverlap
import EpiFormal.WindowMobiusCount

/-
F3f：stopped 层用方实例化（realize 桥）。

把 F3e（`WindowMuThreshLevel.mu_window_thresh_num`）的原子几何假设
`hlen_lo/hi` 归约为停止规则接口 `hden`（每 stopped 原子有分母对
`q₀,q₁ ∈ [4H/3, 5H/2]` 使长度 `= 1/(q₀*q₁)`），经已验证的
`CoverCount.child_len_bounds` 真实 discharge。

剩余纸面接口（用方 / 论文侧）：
- `hden`：停止规则（每原子分母对落在 stopped 区间）；
- `hdisj`：不同 stopped 柱内部不交；
- `hK`：realize 单射（互素对 → 互异 stopped 柱），即
  `copCount R ≤ card P`；
- `hsplit`：均匀分裂（每原子质量 `≤ Mpar/card P`）；
- `hcov`：窗被 stopped 原子覆盖；
- `hbound`：逐原子质量界；
- `hnum`：以具体 `R/H/s/C` 数值验证的阈值不等式。
-/

namespace WindowRealize

variable {μ : MeasureTheory.Measure ℝ}

/-- stopped 层逐窗质量上界（realize 实例化版）。 -/
theorem stopped_window_realize
    (R H : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (hH : 0 < H)
    {d0 L m0 C s Mpar : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0) (hMpar : 0 ≤ Mpar)
    (hd0eq : d0 = 4 / (25 * H ^ 2)) (hLeq : L = 9 / (16 * H ^ 2))
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hden : ∀ I ∈ P, ∃ q₀ q₁ : ℝ, 4 * H / 3 ≤ q₀ ∧ q₀ ≤ 5 * H / 2 ∧
      4 * H / 3 ≤ q₁ ∧ q₁ ≤ 5 * H / 2 ∧ I.2 - I.1 = 1 / (q₀ * q₁))
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hK : ((WindowMobiusCount.copCount R : ℕ) : ℝ) ≤ (P.card : ℝ))
    (hsplit : m0 ≤ Mpar / (P.card : ℝ))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0)
    (hnum : ((2 * Metric.diam U + 3 * L) / d0 + 2) * (Mpar * 10000 / R ^ 2)
      ≤ C * Metric.diam U ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  have hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1 := by
    intro I hI
    obtain ⟨q₀, q₁, hlo0, hhi0, hlo1, hhi1, hlen⟩ := hden I hI
    rw [hlen, hd0eq]
    exact (CoverCount.child_len_bounds hH hlo0 hhi0 hlo1 hhi1).1
  have hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L := by
    intro I hI
    obtain ⟨q₀, q₁, hlo0, hhi0, hlo1, hhi1, hlen⟩ := hden I hI
    rw [hlen, hLeq]
    exact (CoverCount.child_len_bounds hH hlo0 hhi0 hlo1 hhi1).2
  exact WindowMuThreshLevel.mu_window_thresh_num R hR hd0 hL hm0 hMpar P
    htriv hlen_lo hlen_hi hdisj P.card hK hsplit U hbddU hcov hbound hnum

end WindowRealize

#print axioms WindowRealize.stopped_window_realize
