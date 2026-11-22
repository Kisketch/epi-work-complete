import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import EpiFormal.AdjacentWitness

namespace EpiCertificate

theorem farey_bounds :
    (16687677659 : ℝ) / 2847787561 < Real.exp 1 + Real.pi ∧
    Real.exp 1 + Real.pi < (4617039282 : ℝ) / 787907539 := by
  have h := abs_le.mp Real.exp_one_near_20
  constructor
  · linarith [h.1, Real.pi_gt_d20]
  · linarith [h.2, Real.pi_lt_d20]

theorem denominator_bound (a b : ℤ) (hb : 0 < b)
    (heq : (b : ℝ) * (Real.exp 1 + Real.pi) = (a : ℝ)) :
    3635695100 ≤ b := by
  obtain ⟨hl, hu⟩ := farey_bounds
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h₁ := mul_lt_mul_of_pos_left hl hb'
  have h₂ := mul_lt_mul_of_pos_left hu hb'
  rw [heq] at h₁ h₂
  have l : (16687677659 : ℝ) * b < 2847787561 * a := by linarith
  have u : (787907539 : ℝ) * a < 4617039282 * b := by linarith
  have li : 16687677659 * b < 2847787561 * a := by exact_mod_cast l
  have ui : 787907539 * a < 4617039282 * b := by exact_mod_cast u
  have lx := Int.add_one_le_iff.mpr li
  have ux := Int.add_one_le_iff.mpr ui
  linarith only [mul_le_mul_of_nonneg_left lx (by decide : (0:ℤ) ≤ 787907539),
    mul_le_mul_of_nonneg_left ux (by decide : (0:ℤ) ≤ 2847787561)]

#print axioms farey_bounds
#print axioms denominator_bound
/-- A uniform separation, including nonreduced input fractions. -/
theorem uniform_gap (a b : ℤ) (hb : 0 < b) (hmax : b < 3635695100) :
    (1:ℝ)/5000000000 < |(b:ℝ) * (Real.exp 1 + Real.pi) - a| := by
  let x := Real.exp 1 + Real.pi
  let L := (2847787561:ℝ)*x-16687677659
  let U := (4617039282:ℝ)-787907539*x
  have he := abs_le.mp Real.exp_one_near_20
  have hl : (1:ℝ)/5000000000 < L := by
    dsimp [L,x]; linarith [he.1, Real.pi_gt_d20]
  have hu : (1:ℝ)/5000000000 < U := by
    dsimp [U,x]; linarith [he.2, Real.pi_lt_d20]
  let m := 4617039282*b - 787907539*a
  let n := 2847787561*a - 16687677659*b
  have hden : b = 2847787561*m + 787907539*n := by dsimp [m,n]; ring
  have ident : (b:ℝ)*x-a = (m:ℝ)*L - (n:ℝ)*U := by
    dsimp [m,n,L,U]; push_cast; ring
  change (1:ℝ)/5000000000 < |(b:ℝ)*x-a|
  rw [ident,lt_abs]
  have hcases : (1 ≤ m ∧ n ≤ 0) ∨ (m ≤ 0 ∧ 1 ≤ n) := by omega
  rcases hcases with ⟨hm,hn⟩ | ⟨hm,hn⟩
  · left
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (n:ℝ) ≤ 0 := by exact_mod_cast hn
    nlinarith only [hl, mul_nonneg (sub_nonneg.mpr hm') (by linarith : 0 ≤ L),
      mul_nonpos_of_nonpos_of_nonneg hn' (by linarith : 0 ≤ U)]
  · right
    have hm' : (m:ℝ) ≤ 0 := by exact_mod_cast hm
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hu, mul_nonneg (sub_nonneg.mpr hn') (by linarith : 0 ≤ U),
      mul_nonpos_of_nonpos_of_nonneg hm' (by linarith : 0 ≤ L)]

#print axioms uniform_gap
theorem no_adjacent_match (B j : ℕ) (hB : 0 < B) (hb : B < 3635695100) (hj : 8 ≤ j) :
    AdjacentWitness.Tsel B j ≠ -(B : ℤ) * AdjacentWitness.Csel j := by
  intro hm
  have H := AdjacentWitness.quantitative_bound_succ hm
  have G := uniform_gap (round ((B:ℝ)*(Real.exp 1+Real.pi))) (B:ℤ)
    (by exact_mod_cast hB) (by exact_mod_cast hb)
  push_cast at G
  have hq : (10622799089:ℝ) ≤ (Qsel (j+1):ℝ) := by
    have h₉ : Qsel 9 = 10622799089 := by decide
    have h := Qsel_strictMono.monotoneOn (show 9 ∈ Set.Ici (1:ℕ) by decide)
      (show j+1 ∈ Set.Ici (1:ℕ) by change 1 ≤ j+1; omega) (by omega : 9 ≤ j+1)
    rw [h₉] at h
    exact_mod_cast h
  have hd := abs_deltaSel_lt (j+1) (by omega)
  have hj' : (1:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ j+1)
  have hmul : (10622799089:ℝ) ≤ 2*((j+1:ℕ):ℝ)*(Qsel (j+1):ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hj') (by linarith : 0 ≤ (Qsel (j+1):ℝ)) ]
  have hd' : |deltaSel (j+1)| ≤ 1/10622799089 := by
    exact hd.le.trans (one_div_le_one_div_of_le (by norm_num) hmul)
  have hB' : (B:ℝ) ≤ 3635695100 := by exact_mod_cast hb.le
  have hp := mul_le_mul hB' hd' (abs_nonneg _) (by norm_num)
  have HH := (le_div_iff₀ (by linarith : 0 < (Qsel (j+1):ℝ))).mp H
  change (1:ℝ)/5000000000 < distToNearestInt ((B:ℝ)*(Real.exp 1+Real.pi)) at G
  nlinarith [mul_le_mul_of_nonneg_left hq (le_trans (by norm_num : (0:ℝ) ≤ 1/5000000000) G.le)]

#print axioms no_adjacent_match
end EpiCertificate


