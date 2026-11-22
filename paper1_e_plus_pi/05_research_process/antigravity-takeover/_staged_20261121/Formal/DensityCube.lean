import Mathlib.Data.Int.ModEq
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DensityCube

/-- A chosen prime-ideal residue makes the trace norm numerator divisible. -/
theorem squareResidueWitness (q m r D : ℤ)
    (hm : q ∣ m-r) (hr : q ∣ r*r-D) : q ∣ m*m-D := by
  obtain ⟨k,hk⟩ := hm
  obtain ⟨j,hj⟩ := hr
  refine ⟨k*(m+r)+j,?_⟩
  calc
    m*m-D = (m-r)*(m+r)+(r*r-D) := by ring
    _ = _ := by rw [hk,hj]; ring

/-- A shared rational trace imposes the common parity at an odd multiplier. -/
theorem oddMultiplier (k u v : ℤ) (hk : k ≡ 1 [ZMOD 2])
    (h : k*u ≡ v [ZMOD 2]) : u ≡ v [ZMOD 2] := by
  have h' := hk.mul_right u
  rw [one_mul] at h'
  exact h'.symm.trans h

/-- The two polynomial losses in the discrepancy argument balance at 1/3. -/
theorem cubicExponent (a : ℝ) :
    a < 1-2*a ↔ a < 1/3 := by
  constructor <;> intro h <;> linarith

/-- The amplitude enters in opposite powers on the two sides. -/
theorem amplitudeBalance (a b c : ℝ) (hc : 0 < c) :
    a*c < b/c^2 ↔ a*c^3 < b := by
  rw [lt_div_iff₀ (pow_pos hc 2)]
  rw [show a*c*c^2 = a*c^3 by ring]

end DensityCube

#print axioms DensityCube.squareResidueWitness
#print axioms DensityCube.oddMultiplier
#print axioms DensityCube.cubicExponent
#print axioms DensityCube.amplitudeBalance

