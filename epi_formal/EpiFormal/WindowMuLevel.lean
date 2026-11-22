import EpiFormal.WindowCoverCount
import EpiFormal.WindowMuImplication
import EpiFormal.WindowSandwich
import Mathlib

/-!
# F3b：选层 + 交数 + 质量的三明治组装

`mu_le_at_level`：固定层数据（原子对族 + 分离/长度/不交 + 覆盖 + 逐原子质量
+ 以 diam U 为参数的数值阈值）⇒ `μ U ≤ ofReal (C * diam U ^ s)`。
`mu_le_of_sandwich`：三明治选层定 j，再调固定层上界；阈值以区间成员为接口，
由具体数值（R/H/s）在用方 discharge。
e-specific 几何（柱族全覆盖、逐原子质量、数值阈值）全部留接口。
-/

open Set Finset Real Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace WindowMuLevel

variable {μ : MeasureTheory.Measure ℝ}

open Classical in
/-- 交窗子族的交数上界（E4a 引理在过滤子族上的实例化）。 -/
theorem filter_meet_card {d0 L D : ℝ} (hd0 : 0 < d0) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U) (hdiamU : Metric.diam U ≤ D) :
    ((P.filter (fun (I : ℝ × ℝ) => (Set.Icc I.1 I.2 ∩ U).Nonempty)).card : ℝ) ≤
      (2 * D + 3 * L) / d0 + 2 := by
  classical
  set G := P.filter (fun (I : ℝ × ℝ) => (Set.Icc I.1 I.2 ∩ U).Nonempty) with hG
  have hsub : G ⊆ P := Finset.filter_subset _ _
  have hmeet : ∀ I ∈ G, ∃ x ∈ U, I.1 ≤ x ∧ x ≤ I.2 := by
    intro I hI
    obtain ⟨x, hxI, hxU⟩ := (Finset.mem_filter.mp hI).2
    exact ⟨x, hxU, (Set.mem_Icc.mp hxI).1, (Set.mem_Icc.mp hxI).2⟩
  exact CoverCount.meet_card_of_diam_le hd0 hL hD G
    (fun I hI => htriv I (hsub hI)) (fun I hI => hlen_lo I (hsub hI))
    (fun I hI => hlen_hi I (hsub hI))
    (fun I hI J hJ hne => hdisj I (hsub hI) J (hsub hJ) hne)
    U hbddU hdiamU hmeet

/-- 固定层上界：交数 + 质量 + 数值阈值（以 diam U 为参数）⇒ μU ≤ C·diam^s。 -/
theorem mu_le_at_level {d0 L m0 C s : ℝ}
    (hd0 : 0 < d0) (hL : 0 ≤ L) (hm0 : 0 ≤ m0)
    (P : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ P, I.1 < I.2)
    (hlen_lo : ∀ I ∈ P, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ P, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ P, ∀ J ∈ P, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hcov : ∀ x ∈ U, ∃ I ∈ P, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ I ∈ P, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal m0)
    (hthresh : ((2 * Metric.diam U + 3 * L) / d0 + 2) * m0 ≤ C * Metric.diam U ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  classical
  set G := P.filter (fun (I : ℝ × ℝ) => (Set.Icc I.1 I.2 ∩ U).Nonempty) with hG
  have hcover : U ⊆ ⋃ i ∈ G, Set.Icc i.1 i.2 := by
    intro x hxU
    obtain ⟨I, hIP, hxI⟩ := hcov x hxU
    have hmeet : (Set.Icc I.1 I.2 ∩ U).Nonempty := ⟨x, hxI, hxU⟩
    have hIG : I ∈ G := Finset.mem_filter.mpr ⟨hIP, hmeet⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr hIG) hxI
  have hmass : μ U ≤ (G.card : ℝ≥0∞) * ENNReal.ofReal m0 :=
    WindowMu.mu_window_le _ G U G.card m0 le_rfl hcover
      (fun i hiI => hbound i (Finset.mem_of_subset (Finset.filter_subset _ _) hiI))
  have hcard : ((G.card : ℕ) : ℝ)
      ≤ (2 * Metric.diam U + 3 * L) / d0 + 2 :=
    filter_meet_card hd0 hL Metric.diam_nonneg P
      htriv hlen_lo hlen_hi hdisj U hbddU le_rfl
  have hle : (G.card : ℝ≥0∞) * ENNReal.ofReal m0 ≤
      ENNReal.ofReal (C * Metric.diam U ^ s) := by
    have e1 : (G.card : ℝ≥0∞) * ENNReal.ofReal m0
        = ENNReal.ofReal ((G.card : ℝ) * m0) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [e1]
    apply ENNReal.ofReal_le_ofReal
    exact le_trans (mul_le_mul_of_nonneg_right hcard hm0) hthresh
  exact le_trans hmass hle

/-- 三明治选层版：先 sandwich 定层，再调固定层上界。 -/
theorem mu_le_of_sandwich {H : ℕ → ℝ} {j0 : ℕ}
    (hH : Tendsto (fun j => 1 / (H j) ^ 2) atTop (nhds 0))
    (d0 L : ℕ → ℝ) (m0 : ℕ → ℝ) (C s : ℝ)
    (P : ℕ → Finset (ℝ × ℝ))
    (hd0j : ∀ j, 0 < d0 j) (hLj : ∀ j, 0 ≤ L j) (hm0j : ∀ j, 0 ≤ m0 j)
    (htriv : ∀ j, ∀ I ∈ P j, I.1 < I.2)
    (hlen_lo : ∀ j, ∀ I ∈ P j, d0 j ≤ I.2 - I.1)
    (hlen_hi : ∀ j, ∀ I ∈ P j, I.2 - I.1 ≤ L j)
    (hdisj : ∀ j, ∀ I ∈ P j, ∀ J ∈ P j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (U : Set ℝ) (hbddU : Bornology.IsBounded U)
    (hdpos : 0 < Metric.diam U) (hdle : Metric.diam U ≤ 1 / (H j0) ^ 2)
    (hcov : ∀ j, ∀ x ∈ U, ∃ I ∈ P j, x ∈ Set.Icc I.1 I.2)
    (hbound : ∀ j, ∀ I ∈ P j, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m0 j))
    (hthresh : ∀ j, j0 ≤ j → ∀ h', h' ∈ Set.Icc (1 / (H (j + 1)) ^ 2) (1 / (H j) ^ 2) →
      ((2 * h' + 3 * L j) / d0 j + 2) * m0 j ≤ C * h' ^ s) :
    μ U ≤ ENNReal.ofReal (C * Metric.diam U ^ s) := by
  classical
  obtain ⟨j, hj0, hlo, hhi⟩ :=
    WindowSandwich.sandwich_of_tendsto H hH j0 hdpos hdle
  exact mu_le_at_level (hd0j j) (hLj j) (hm0j j)
    (P j) (htriv j) (hlen_lo j) (hlen_hi j) (hdisj j)
    U hbddU (fun x hx => hcov j x hx) (fun I hI => hbound j I hI)
    (hthresh j hj0 (Metric.diam U) ⟨hlo, hhi⟩)

#print axioms WindowMuLevel.filter_meet_card
#print axioms WindowMuLevel.mu_le_at_level
#print axioms WindowMuLevel.mu_le_of_sandwich

end WindowMuLevel
