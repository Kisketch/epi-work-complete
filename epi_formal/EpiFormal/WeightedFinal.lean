import Mathlib
import EpiFormal.WeightedUpper
import EpiFormal.DimHFinite

open Real Filter Topology Set Polynomial Finset MeasureTheory intervalIntegral DimHCore WeightedFiber WeightedDimH SpectralGap WeightedUpper
open scoped Interval ENNReal NNReal

namespace WeightedFinal

noncomputable section

/-- 周期性：apprSeqα α (x+m) j = apprSeqα α x j。 -/
lemma apprSeqα_add_intCast (α : ℝ) (x : ℝ) (m : ℤ) (j : ℕ) :
    apprSeqα α (x + m) j = apprSeqα α x j := by
  unfold apprSeqα
  have hcast : (Qsel j : ℝ) * (x + m) = (Qsel j : ℝ) * x + (Qsel j * m : ℤ) := by push_cast; ring
  rw [hcast, DimHFinite.distToNearestInt_add_intCast]

lemma apprExponentα_add_intCast (α : ℝ) (x : ℝ) (m : ℤ) :
    apprExponentα α (x + m) = apprExponentα α x := by
  unfold apprExponentα
  congr 1; funext j
  unfold apprSeqαE
  rw [apprSeqα_add_intCast]

/-- 水平集 ⊆  wtailSet 的可数并（J≥1）。 -/
lemma levelSetα_subset_iUnion (α c t : ℝ) (hα0 : 0 ≤ α) (hc0 : 0 ≤ c) (hct : c < t) :
    levelSetα α (ENNReal.ofReal c) ⊆
      ⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ), (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1 := by
  intro x hx
  have hxlim : apprExponentα α x ≤ ENNReal.ofReal c := hx
  have hctE : ENNReal.ofReal c < ENNReal.ofReal t :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc0 hct)).mpr hct
  have hlt : apprExponentα α x < ENNReal.ofReal t := lt_of_le_of_lt hxlim hctE
  have hev : ∀ᶠ j : ℕ in atTop, apprSeqαE α x j < ENNReal.ofReal t :=
    eventually_lt_of_limsup_lt hlt
  have ht0 : 0 < t := lt_of_le_of_lt hc0 hct
  have hev' : ∀ᶠ j : ℕ in atTop, apprSeqα α x j ≤ t := by
    filter_upwards [hev] with j hj
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff ht0).mp hj)
  obtain ⟨J0, hJ0⟩ := Filter.eventually_atTop.mp hev'
  set J := max 1 J0 with hJdef
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJ : ∀ j, J ≤ j → apprSeqα α x j ≤ t := fun j hj => hJ0 j (le_trans (le_max_right _ _) hj)
  set m := ⌊x⌋ with hmdef
  set y := x - (m : ℝ) with hydef
  have hy0 : 0 ≤ y := by have := Int.floor_le x; linarith
  have hy1 : y ≤ 1 := by have := Int.lt_floor_add_one x; linarith
  have hym : x = y + (m : ℝ) := by linarith
  have htail : ∀ j, J ≤ j → apprSeqα α y j ≤ t := by
    intro j hj
    have := hJ j hj
    rw [hym, apprSeqα_add_intCast] at this
    exact this
  have hytail : y ∈ wtailSet t α J := ⟨hy0, hy1, htail⟩
  refine Set.mem_iUnion.mpr ⟨⟨J, hJ1⟩, ?_⟩
  refine Set.mem_iUnion.mpr ⟨m, ?_⟩
  exact ⟨y, hytail, by linarith⟩

/-- **加权相变上界**：dimH{Λ_α≤c} ≤ 1−α（0≤α≤1，c 有限）。 -/
theorem dimH_levelSetα_le (α c : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    dimH (levelSetα α (ENNReal.ofReal c)) ≤ ENNReal.ofReal (1 - α) := by
  set c' := max c 0 with hc'def
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hmono0 : levelSetα α (ENNReal.ofReal c) ⊆ levelSetα α (ENNReal.ofReal c') := by
    intro x hx
    exact le_trans hx (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set t := c' + 1 with htdef
  have hct : c' < t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hsub := Set.Subset.trans hmono0 (levelSetα_subset_iUnion α c' t hα0 hc'0 hct)
  have hdim : dimH (⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ),
      (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) ≤ ENNReal.ofReal (1 - α) := by
    have h1 : ∀ J : {J : ℕ // 1 ≤ J},
        dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) ≤ ENNReal.ofReal (1 - α) := by
      intro J
      have hJ : 1 ≤ J.1 := J.2
      have h2 : ∀ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) ≤ ENNReal.ofReal (1 - α) := by
        intro m
        have hlip : LipschitzWith 1 (fun y : ℝ => y + (m : ℝ)) := by
          apply LipschitzWith.of_dist_le_mul
          intro y₁ y₂
          simp only [dist_eq_norm, NNReal.coe_one, one_mul]
          have hshift : (y₁ + (m : ℝ)) - (y₂ + (m : ℝ)) = y₁ - y₂ := by ring
          rw [hshift]
        have := hlip.dimH_image_le (wtailSet t α J.1)
        exact le_trans this (dimH_wtailSet_le t α ht0 hα0 hα1 J.1 hJ)
      have h3 : dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) ≤
          ⨆ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) := by
        rw [dimH_iUnion]
      have h4 : (⨆ m : ℤ, dimH ((fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1)) ≤ ENNReal.ofReal (1 - α) := by
        apply iSup_le; intro m; exact h2 m
      exact le_trans h3 h4
    have h6 : dimH (⋃ (J : {J : ℕ // 1 ≤ J}) (m : ℤ),
        (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) ≤
        ⨆ J : {J : ℕ // 1 ≤ J}, dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1) := by
      rw [dimH_iUnion]
    have h7 : (⨆ J : {J : ℕ // 1 ≤ J}, dimH (⋃ m : ℤ, (fun y : ℝ => y + (m : ℝ)) '' wtailSet t α J.1)) ≤
        ENNReal.ofReal (1 - α) := by
      apply iSup_le; intro J; exact h1 J
    exact le_trans h6 h7
  exact le_trans (dimH_mono hsub) hdim

end

end WeightedFinal

#print axioms WeightedFinal.dimH_levelSetα_le
