import EpiFormal.CylinderOrder

namespace Cylinder

open Matrix Finset

/-- Consecutive children are one unit apart in cross form. -/
theorem consec_cross (w : List ℕ) (k : ℕ) :
    (cfProd (w ++ [k + 1])) 0 0 * (cfProd (w ++ [k])) 1 0
      - (cfProd (w ++ [k + 1])) 1 0 * (cfProd (w ++ [k])) 0 0
      = (cfProd w).det := by
  have h := sibling_cross w (k + 1) k
  have e : ((k + 1 : ℕ) : ℤ) - (k : ℤ) = 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [e, one_mul] at h
  linarith [h]

/-- The cross difference of consecutive children has absolute value one. -/
theorem consec_cross_abs (w : List ℕ) (k : ℕ) :
    |(cfProd (w ++ [k + 1])) 0 0 * (cfProd (w ++ [k])) 1 0
      - (cfProd (w ++ [k + 1])) 1 0 * (cfProd (w ++ [k])) 0 0| = 1 := by
  rw [consec_cross, cfProd_det]
  rw [abs_pow, abs_neg, abs_one, one_pow]

/-- Child denominators are at least one. -/
theorem childDen_ge_one (w : List ℕ) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (cfProd (w ++ [k])) 1 0 := by
  have h := childDen_pos w k hk
  omega

#print axioms consec_cross
#print axioms consec_cross_abs
#print axioms childDen_ge_one

end Cylinder