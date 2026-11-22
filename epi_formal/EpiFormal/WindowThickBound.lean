import Mathlib
import EpiFormal.WindowMuLevel
import EpiFormal.WindowStoppedTree
import EpiFormal.WindowSandwich

open MeasureTheory Set Filter Finset ENNReal Metric
open scoped NNReal BigOperators Topology MeasureTheory

namespace WindowThickBound

variable {μ : MeasureTheory.Measure ℝ}

/-- 逐窗上界（正直径情形）：三明治选层 + 固定层交数/质量/阈值。
    `diam = 0` 的情形由终文件另行处理（单点质量论证），此处要求 `0 < diam U`。 -/
theorem mu_thickened_le
    {T : StoppedTree.TreeData} {m : ℕ → ℝ} {H : ℕ → ℝ} {j0 : ℕ} {C s : ℝ}
    {d0 L : ℕ → ℝ}
    (hH : Filter.Tendsto (fun j => 1 / (H j) ^ 2) Filter.atTop (nhds 0))
    (hd0j : ∀ j, 0 < d0 j) (hLj : ∀ j, 0 ≤ L j) (hm0j : ∀ j, 0 ≤ m j)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen_lo : ∀ j ≥ j0, ∀ I ∈ T.atoms j, d0 j ≤ I.2 - I.1)
    (hlen_hi : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.2 - I.1 ≤ L j)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hthresh : ∀ n ≥ j0, ∀ h', h' ∈ Set.Icc (1 / (H (n + 1)) ^ 2) (1 / (H n) ^ 2) →
      ((2 * h' + 3 * L n) / d0 n + 2) * m n ≤ C * h' ^ s)
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hdpos : 0 < Metric.diam U) (hdle : Metric.diam U ≤ 1 / (H j0) ^ 2)
    (hcov : ∀ n ≥ j0, ∀ x ∈ U, ∃ I ∈ T.atoms n, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ n ≥ j0, ∀ I ∈ T.atoms n, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m n)) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  obtain ⟨n, hn0, hlo, hhi⟩ :=
    WindowSandwich.sandwich_of_tendsto H hH j0 hdpos hdle
  have hbound_n : ∀ I ∈ T.atoms n, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m n) :=
    fun I hI => hbound n hn0 I hI
  have hcov_n : ∀ x ∈ U, ∃ I ∈ T.atoms n, x ∈ Set.Icc I.1 I.2 :=
    fun x hx => hcov n hn0 x hx
  exact WindowMuLevel.mu_le_at_level (hd0j n) (hLj n) (hm0j n)
    (T.atoms n) (htriv n hn0) (hlen_lo n hn0) (hlen_hi n hn0) (hdisj n hn0)
    U hbddU hcov_n hbound_n
    (hthresh n hn0 (Metric.diam U) ⟨hlo, hhi⟩)

#print axioms WindowThickBound.mu_thickened_le

end WindowThickBound
