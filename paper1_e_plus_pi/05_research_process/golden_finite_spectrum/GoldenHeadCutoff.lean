import Mathlib

/-! Uniform real inequalities for the first mismatch at a large continued-fraction head. -/

namespace GoldenHeadCutoff

theorem fixed_side_ratio {head tail z q theta : ℝ}
    (hh : 8 ≤ head) (ht : head ≤ tail) (ht' : tail ≤ head + 1)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hq : q ≤ head / 2) (hθ : theta ≤ 1) :
    1 / 6 ≤ |tail - (q + theta)| / (tail + z) := by
  have hd : 0 < tail + z := by linarith
  rw [le_div_iff₀ hd]
  have hnum : head / 4 ≤ |tail - (q + theta)| :=
    (show head / 4 ≤ tail - (q + theta) by linarith).trans (le_abs_self _)
  linarith

theorem moving_side_ratio {head tail z q thetaConj : ℝ}
    (hh : 8 ≤ head) (ht : head ≤ tail) (ht' : tail ≤ head + 1)
    (hz : 0 ≤ z) (hz' : z ≤ 1) (hq : head / 2 ≤ q) (hθ : -2 ≤ thetaConj) :
    1 / 6 ≤ |q + thetaConj + z| / (tail + z) := by
  have hd : 0 < tail + z := by linarith
  rw [le_div_iff₀ hd]
  have hnum : head / 4 ≤ |q + thetaConj + z| :=
    (show head / 4 ≤ q + thetaConj + z by linarith).trans (le_abs_self _)
  linarith

theorem mismatch_gap {head q : ℤ} {tail theta delta : ℝ}
    (hq : q ≠ head) (hlo : (head : ℝ) + delta ≤ tail)
    (hhi : tail ≤ (head : ℝ) + 1 - delta)
    (hθlo : 0 ≤ theta) (hθhi : theta ≤ 1) :
    delta ≤ |tail - ((q : ℝ) + theta)| := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · have hq' : (q : ℝ) + 1 ≤ head := by exact_mod_cast (show q + 1 ≤ head by omega)
    exact (show delta ≤ tail - ((q : ℝ) + theta) by linarith).trans (le_abs_self _)
  · have hq' : (head : ℝ) + 1 ≤ q := by exact_mod_cast (show head + 1 ≤ q by omega)
    exact (show delta ≤ -(tail - ((q : ℝ) + theta)) by linarith).trans (neg_le_abs _)

end GoldenHeadCutoff

#print axioms GoldenHeadCutoff.fixed_side_ratio
#print axioms GoldenHeadCutoff.moving_side_ratio
#print axioms GoldenHeadCutoff.mismatch_gap
