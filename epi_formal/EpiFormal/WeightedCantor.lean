import Mathlib
import EpiFormal.WeightedDimHCore
import EpiFormal.WeightedLower

open Real Filter Topology Set Polynomial Finset DimHCore WeightedFiber WeightedDimH WeightedLower

namespace WeightedCantor

noncomputable section

/-- **同级分离**：不同中心的加权区间不交（需 2·wrad < 1/Q_j）。
    这是 Frostman 质量分布论证的必需几何零件。注意：分支条件是区间相交
    （|c_j−c_{j+1}|≤r_j+r_{j+1}），并非嵌套；上界覆盖论证不需嵌套。 -/
lemma winterv_disjoint (t α : ℝ) (ht : 0 ≤ t) (j k₁ k₂ : ℕ) (hj : 1 ≤ j)
    (hne : k₁ ≠ k₂) (hsmall : 2 * wrad t α j < 1 / (Qsel j : ℝ)) :
    Disjoint (winterv t α j k₁) (winterv t α j k₂) := by
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  set c₁ := (k₁ : ℝ) / (Qsel j : ℝ) with hc1def
  set c₂ := (k₂ : ℝ) / (Qsel j : ℝ) with hc2def
  set r := wrad t α j with hrdef
  have hgap : 1 / (Qsel j : ℝ) ≤ |c₁ - c₂| := by
    have hdiff : c₁ - c₂ = ((k₁ : ℝ) - (k₂ : ℝ)) / (Qsel j : ℝ) := by
      simp only [hc1def, hc2def]; ring
    rw [hdiff, abs_div, abs_of_pos hQj]
    have hnum : 1 ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
      have hneZ : (k₁ : ℤ) ≠ (k₂ : ℤ) := by exact_mod_cast hne
      have h1 : 1 ≤ |(k₁ : ℤ) - (k₂ : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hneZ)
      exact_mod_cast h1
    have hone : 1 / (Qsel j : ℝ) * (Qsel j : ℝ) = 1 := by field_simp
    have hgoal : 1 / (Qsel j : ℝ) * (Qsel j : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
      rw [hone]; exact hnum
    exact (le_div_iff₀ hQj).mpr hgoal
  rw [Set.disjoint_iff]
  intro x hx
  rw [Set.mem_inter_iff] at hx
  have hxI1 : x ∈ winterv t α j k₁ := hx.1
  have hxI2 : x ∈ winterv t α j k₂ := hx.2
  have hx1' : x ∈ Icc (c₁ - r) (c₁ + r) := hxI1
  have hx2' : x ∈ Icc (c₂ - r) (c₂ + r) := hxI2
  rw [Set.mem_Icc] at hx1' hx2'
  have hdist : |c₁ - c₂| ≤ 2 * r := by
    have hup : c₁ - c₂ ≤ 2 * r := by linarith [hx1'.1, hx2'.2]
    have hlo : c₂ - c₁ ≤ 2 * r := by linarith [hx2'.1, hx1'.2]
    exact abs_sub_le_iff.mpr ⟨hup, hlo⟩
  have hsmall' : 2 * r < 1 / (Qsel j : ℝ) := hsmall
  linarith [hgap, hdist, hsmall']

end

end WeightedCantor

#print axioms WeightedCantor.winterv_disjoint
