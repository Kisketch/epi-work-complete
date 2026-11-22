import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SharpWindow

/-- Exact optimization behind the cubic-root transition. -/
theorem cubicGap (c v : ℝ) :
    4*c^3/27 - v*(c-v)^2 = (v-c/3)^2*(4*c/3-v) := by ring

/-- The maximum on the physical interval is unique. -/
theorem strictPeak {c v : ℝ} (hc : 0 < c) (hv : v ≤ c)
    (hne : v ≠ c/3) : v*(c-v)^2 < 4*c^3/27 := by
  have h₁ : 0 < (v-c/3)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have h₂ : 0 < 4*c/3-v := by linarith
  have h₃ := mul_pos h₁ h₂
  linarith [cubicGap c v]

/-- The floor count for one residue class has a location-independent error. -/
theorem residueCountScaledError (l u r q : ℤ) (hq : 0 < q) :
    -q < q*((u-r)/q-(l-r)/q)-(u-l) ∧
    q*((u-r)/q-(l-r)/q)-(u-l) < q := by
  have hl := Int.emod_add_mul_ediv (l-r) q
  have hu := Int.emod_add_mul_ediv (u-r) q
  have h₁ := Int.emod_nonneg (l-r) (ne_of_gt hq)
  have h₂ := Int.emod_nonneg (u-r) (ne_of_gt hq)
  have h₃ := Int.emod_lt_of_pos (l-r) hq
  have h₄ := Int.emod_lt_of_pos (u-r) hq
  have h : q*((u-r)/q-(l-r)/q)-(u-l) = (l-r)%q-(u-r)%q := by
    linarith
  rw [h]
  constructor <;> linarith

end SharpWindow

#print axioms SharpWindow.cubicGap
#print axioms SharpWindow.strictPeak
#print axioms SharpWindow.residueCountScaledError



