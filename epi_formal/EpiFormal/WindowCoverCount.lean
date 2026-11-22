import Mathlib

/-!
# Covering-count lemma for disjoint interval families (paper2 §7, Frostman input).

Generic combinatorial heart of the `Hinter` discharge: a finite family of
pairwise-interior-disjoint nontrivial closed intervals, each of length at
least `d0 > 0` and at most `L`, meeting a window `[Vl, Vr]` of diameter
`δ`, has at most `(δ + L) / d0 + 2` members.

Proof idea: left endpoints of distinct members are `d0`-separated
(disjoint interiors + length `≥ d0`), so `⌊left / d0⌋` is injective;
meeting the window pins `left ∈ [Vl - L, Vr]`, and the integer range has
at most `(δ + L) / d0 + 2` points.
-/

namespace CoverCount

open Finset Set

/-- Left endpoints of distinct members are `d0`-separated: the intervals
are ordered one way or the other. -/
theorem left_separated
    {I J : ℝ × ℝ} (hI : I.1 < I.2) (hJ : J.1 < J.2)
    (hdisj : Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2)) :
    I.2 ≤ J.1 ∨ J.2 ≤ I.1 := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have hmax1 : max I.1 J.1 < I.2 := by
    rw [max_lt_iff]; exact ⟨hI, h1⟩
  have hmax2 : max I.1 J.1 < J.2 := by
    rw [max_lt_iff]; exact ⟨h2, hJ⟩
  have hmem : (Set.Ioo I.1 I.2 ∩ Set.Ioo J.1 J.2).Nonempty := by
    have hlt : max I.1 J.1 < min I.2 J.2 :=
      lt_min hmax1 hmax2
    obtain ⟨x, hx1, hx2⟩ := Set.nonempty_Ioo.mpr hlt
    exact ⟨x,
      ⟨lt_of_le_of_lt (le_max_left _ _) hx1,
       lt_of_lt_of_le hx2 (min_le_left _ _)⟩,
      ⟨lt_of_le_of_lt (le_max_right _ _) hx1,
       lt_of_lt_of_le hx2 (min_le_right _ _)⟩⟩
  rw [Set.disjoint_iff_inter_eq_empty] at hdisj
  exact hmem.ne_empty hdisj

/-- `d0`-separated reals have strictly ordered scaled floors. -/
theorem floor_lt_of_separated {d0 a b : ℝ} (hd0 : 0 < d0)
    (hsep : d0 ≤ b - a) : ⌊a / d0⌋ < ⌊b / d0⌋ := by
  have h1 : (⌊a / d0⌋ : ℤ) + 1 ≤ ⌊b / d0⌋ := by
    rw [Int.le_floor]
    push_cast
    have h4 : (1 : ℝ) ≤ (b - a) / d0 :=
      (le_div_iff₀ hd0).mpr (by linarith [hsep])
    have h5 : (b - a) / d0 = b / d0 - a / d0 := sub_div _ _ _
    have hfl : ((⌊a / d0⌋ : ℤ) : ℝ) ≤ a / d0 := Int.floor_le _
    linarith
  omega

/-- Meeting family card bound: at most `(δ + L) / d0 + 2` members.
Needs `Vl ≤ Vr` (nonempty window) and `0 ≤ L`, else the bound can fail
for far-apart empty windows. -/
theorem meet_card_le {d0 L Vl Vr : ℝ} (hd0 : 0 < d0)
    (hwin : Vl ≤ Vr) (hL : 0 ≤ L)
    (F : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ F, I.1 < I.2)
    (hlen_lo : ∀ I ∈ F, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ F, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hmeet : ∀ I ∈ F, I.1 ≤ Vr ∧ Vl ≤ I.2) :
    ((F.card : ℕ) : ℝ) ≤ (Vr - Vl + L) / d0 + 2 := by
  classical
  -- The scaled-floor map is injective on the family.
  set φ : (ℝ × ℝ) → ℤ := fun I => ⌊I.1 / d0⌋ with hφ
  have hinj : Set.InjOn φ (↑F : Set (ℝ × ℝ)) := by
    intro I hI J hJ heq
    rw [Finset.mem_coe] at hI hJ
    by_contra hne
    have hsep : d0 ≤ J.1 - I.1 ∨ d0 ≤ I.1 - J.1 := by
      rcases left_separated (htriv I hI) (htriv J hJ) (hdisj I hI J hJ hne) with h | h
      · left
        have h1 := hlen_lo I hI
        linarith
      · right
        have h1 := hlen_lo J hJ
        linarith
    rcases hsep with hsep | hsep
    · have hlt : ⌊I.1 / d0⌋ < ⌊J.1 / d0⌋ :=
        floor_lt_of_separated hd0 hsep
      have heq' : ⌊I.1 / d0⌋ = ⌊J.1 / d0⌋ := heq
      omega
    · have hlt : ⌊J.1 / d0⌋ < ⌊I.1 / d0⌋ :=
        floor_lt_of_separated hd0 hsep
      have heq' : ⌊J.1 / d0⌋ = ⌊I.1 / d0⌋ := heq.symm
      omega
  -- Image lands in an explicit integer interval.
  have hmem_lo : ∀ I ∈ F, ⌊(Vl - L) / d0⌋ ≤ φ I := by
    intro I hI
    have hlo : Vl - L ≤ I.1 := by
      have h1 := (hmeet I hI).2
      have h2 := hlen_hi I hI
      linarith
    have h1 : ((⌊(Vl - L) / d0⌋ : ℤ) : ℝ) ≤ (Vl - L) / d0 :=
      Int.floor_le _
    have h2 : (Vl - L) / d0 ≤ I.1 / d0 := by
      gcongr
    have h3 : I.1 / d0 < ((φ I : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h4 : ((⌊(Vl - L) / d0⌋ : ℤ) : ℝ) < ((φ I : ℤ) : ℝ) + 1 := by
      linarith
    have h5 : ⌊(Vl - L) / d0⌋ < φ I + 1 := by
      exact_mod_cast h4
    omega
  have hmem_hi : ∀ I ∈ F, φ I ≤ ⌊Vr / d0⌋ := by
    intro I hI
    have hup : I.1 ≤ Vr := (hmeet I hI).1
    have h1 : ((φ I : ℤ) : ℝ) ≤ I.1 / d0 := Int.floor_le _
    have h2 : I.1 / d0 ≤ Vr / d0 := by
      gcongr
    have h3 : ((φ I : ℤ) : ℝ) ≤ Vr / d0 := le_trans h1 h2
    exact (Int.le_floor).mpr h3
  have hsub : F.image φ ⊆ Finset.Icc ⌊(Vl - L) / d0⌋ ⌊Vr / d0⌋ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨I, hI, rfl⟩ := hn
    rw [Finset.mem_Icc]
    exact ⟨hmem_lo I hI, hmem_hi I hI⟩
  have hle : (F.image φ).card ≤ (⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋).toNat := by
    have h := Finset.card_le_card hsub
    rwa [Int.card_Icc] at h
  have hXnn : 0 ≤ ⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋ := by
    have hle2 : ⌊(Vl - L) / d0⌋ ≤ ⌊Vr / d0⌋ := by
      have h1 : ((⌊(Vl - L) / d0⌋ : ℤ) : ℝ) ≤ (Vl - L) / d0 :=
        Int.floor_le _
      have h2 : (Vl - L) / d0 ≤ Vr / d0 := by
        gcongr
        linarith [hwin, hL]
      have h3 : Vr / d0 < ((⌊Vr / d0⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have h4 : ((⌊(Vl - L) / d0⌋ : ℤ) : ℝ) < ((⌊Vr / d0⌋ : ℤ) : ℝ) + 1 := by
        linarith
      have h5 : ⌊(Vl - L) / d0⌋ < ⌊Vr / d0⌋ + 1 := by
        exact_mod_cast h4
      omega
    omega
  have hcard : F.card = (F.image φ).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hfin : ((F.card : ℕ) : ℝ) ≤
      ((((⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋).toNat : ℕ)) : ℝ) := by
    rw [hcard]
    exact_mod_cast hle
  have hfin2 : (((⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋ : ℤ)) : ℝ) ≤
      (Vr - Vl + L) / d0 + 2 := by
    have hhi : ((⌊Vr / d0⌋ : ℤ) : ℝ) ≤ Vr / d0 := Int.floor_le _
    have hlo : (Vl - L) / d0 - 1 < ((⌊(Vl - L) / d0⌋ : ℤ) : ℝ) := by
      have h := Int.lt_floor_add_one ((Vl - L) / d0)
      linarith
    have hdiv : Vr / d0 - (Vl - L) / d0 = (Vr - Vl + L) / d0 := by
      rw [sub_div]
      ring
    push_cast
    linarith [hhi, hlo, hdiv]
  calc ((F.card : ℕ) : ℝ)
      ≤ ((((⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋).toNat : ℕ)) : ℝ) := hfin
    _ = (((⌊Vr / d0⌋ + 1 - ⌊(Vl - L) / d0⌋ : ℤ)) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hXnn]
    _ ≤ (Vr - Vl + L) / d0 + 2 := hfin2

/-- Diameter version of `meet_card_le`: atoms meeting a bounded set `V`
of diameter `≤ D` are controlled by the expanded window
`[x₀-D-L, x₀+D+L]`. Needs `0 ≤ D` and `IsBounded V`. -/
theorem meet_card_of_diam_le {d0 L D : ℝ} (hd0 : 0 < d0) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (F : Finset (ℝ × ℝ))
    (htriv : ∀ I ∈ F, I.1 < I.2)
    (hlen_lo : ∀ I ∈ F, d0 ≤ I.2 - I.1)
    (hlen_hi : ∀ I ∈ F, I.2 - I.1 ≤ L)
    (hdisj : ∀ I ∈ F, ∀ J ∈ F, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (V : Set ℝ) (hbdd : Bornology.IsBounded V) (hdiam : Metric.diam V ≤ D)
    (hmeet : ∀ I ∈ F, ∃ x ∈ V, I.1 ≤ x ∧ x ≤ I.2) :
    ((F.card : ℕ) : ℝ) ≤ (2 * D + 3 * L) / d0 + 2 := by
  rcases Finset.eq_empty_or_nonempty F with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    have h1 : (0 : ℝ) ≤ (2 * D + 3 * L) / d0 := by
      apply div_nonneg _ (le_of_lt hd0)
      linarith [hD, hL]
    linarith
  · obtain ⟨I0, hI0⟩ := hne
    obtain ⟨x0, hx0, _, _⟩ := hmeet I0 hI0
    set Vl := x0 - D - L with hVl
    set Vr := x0 + D + L with hVr
    have hwin : Vl ≤ Vr := by simp only [hVl, hVr]; linarith [hD, hL]
    have hsub : ∀ I ∈ F, I.1 ≤ Vr ∧ Vl ≤ I.2 := by
      intro I hI
      obtain ⟨x, hx, h1x, h2x⟩ := hmeet I hI
      have hDx : dist x x0 ≤ D :=
        le_trans (Metric.dist_le_diam_of_mem hbdd hx hx0) hdiam
      rw [Real.dist_eq] at hDx
      have habs := abs_le.mp hDx
      constructor <;> simp only [hVr, hVl] <;> linarith [habs.1, habs.2, h1x, h2x, hL]
    have h := meet_card_le hd0 hwin hL F htriv hlen_lo hlen_hi hdisj hsub
    have hrw : Vr - Vl + L = 2 * D + 3 * L := by simp only [hVr, hVl]; ring
    rwa [hrw] at h

end CoverCount

#print axioms CoverCount.left_separated
#print axioms CoverCount.floor_lt_of_separated
#print axioms CoverCount.meet_card_le
#print axioms CoverCount.meet_card_of_diam_le
