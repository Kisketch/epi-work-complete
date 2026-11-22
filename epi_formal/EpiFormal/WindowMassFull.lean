import EpiFormal.WindowMuLevel

open Topology
open scoped ENNReal

/-!
# L02 逐窗质量上界（三分支组装，T12 形状）

`mu_window_le_full`：对任意有界窗 `U`，
- `diam U = 0`：`U` 至多单点集，质量为零（`hpt`）；
- `0 < diam U ≤ 1/(H j0)^2`：F3b 选层组装（`mu_le_of_sandwich`）；
- `diam U > 1/(H j0)^2`：全测度上界 + 大常数阈值（`hCbig`）。
-/

namespace WindowMassFull

variable {μ : MeasureTheory.Measure ℝ}

theorem mu_window_le_full
    {H : ℕ → ℝ} {j0 : ℕ}
    (hH : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (d0 L : ℕ → ℝ) (m0 : ℕ → ℝ) (C s : ℝ)
    (P : ℕ → Finset (ℝ × ℝ))
    (hd0j : ∀ j, 0 < d0 j) (hLj : ∀ j, 0 ≤ L j) (hm0j : ∀ j, 0 ≤ m0 j)
    (htriv : ∀ j, ∀ I ∈ P j, I.1 < I.2)
    (hlen_lo : ∀ j, ∀ I ∈ P j, d0 j ≤ I.2 - I.1)
    (hlen_hi : ∀ j, ∀ I ∈ P j, I.2 - I.1 ≤ L j)
    (hdisj : ∀ j, ∀ I ∈ P j, ∀ J ∈ P j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hcov : ∀ j, ∀ x ∈ U, ∃ I ∈ P j, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ j, ∀ I ∈ P j, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m0 j))
    (hthresh : ∀ j, j0 ≤ j → ∀ h', h' ∈ Set.Icc (1 / (H (j + 1)) ^ 2) (1 / (H j) ^ 2) →
      ((2 * h' + 3 * L j) / d0 j + 2) * m0 j ≤ C * h' ^ s)
    (hpt : ∀ x : ℝ, μ {x} = 0)
    (hprob : ∀ V : Set ℝ, μ V ≤ 1)
    (hCbig : ∀ D : ℝ, 1 / (H j0) ^ 2 < D → (1 : ℝ) ≤ C * D ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := U)) with h0 | hpos
  · have hU0 : μ U = 0 := by
      classical
      by_cases hU : ∃ x, x ∈ U
      · obtain ⟨x, hx⟩ := hU
        have hsub : U ⊆ {x} := by
          intro y hy
          rw [Set.mem_singleton_iff]
          have hle : dist y x ≤ Metric.diam U :=
            Metric.dist_le_diam_of_mem hbddU hy hx
          rw [← h0] at hle
          exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)
        exact le_antisymm
          (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq (hpt x))) zero_le
      · have hempty : U = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hU ⟨x, hx⟩)
        rw [hempty]
        simp
    rw [hU0]
    exact zero_le
  · rcases le_total (Metric.diam U) (1 / (H j0) ^ 2) with hle | hge
    · exact WindowMuLevel.mu_le_of_sandwich hH d0 L m0 C s P hd0j hLj hm0j
        htriv hlen_lo hlen_hi hdisj U hbddU hpos hle hcov hbound hthresh
    · rcases eq_or_lt_of_le hge with heq | hgt
      · exact WindowMuLevel.mu_le_of_sandwich hH d0 L m0 C s P hd0j hLj hm0j
          htriv hlen_lo hlen_hi hdisj U hbddU hpos heq.symm.le hcov hbound hthresh
      · have h1 : μ U ≤ 1 := hprob U
        have h2 : (1 : ℝ) ≤ C * Metric.diam U ^ s := hCbig _ hgt
        have e1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal h2
        exact le_trans h1 e1

#print axioms WindowMassFull.mu_window_le_full

end WindowMassFull
