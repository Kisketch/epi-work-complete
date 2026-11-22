import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace OrbitAndFlow

theorem primeNorm_unitFactor (a c : ℤ) (h : Nat.Prime (a*c).natAbs) :
    a.natAbs = 1 ∨ c.natAbs = 1 := by
  rw [Int.natAbs_mul] at h
  rcases Nat.prime_mul_iff.mp h with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

def pathSlack {V : Type} (F : V → ℝ) (v : V) : List (V × ℝ) → ℝ
  | [] => 0
  | (u,w) :: tail => F v - w - F u + pathSlack F u tail

def pathWeight {V : Type} : List (V × ℝ) → ℝ
  | [] => 0
  | (_,w) :: tail => w + pathWeight tail

def pathEnd {V : Type} (v : V) : List (V × ℝ) → V
  | [] => v
  | (u,_) :: tail => pathEnd u tail

theorem pathSlack_telescopes {V : Type} (F : V → ℝ) (v : V)
    (path : List (V × ℝ)) :
    pathSlack F v path = F v - F (pathEnd v path) - pathWeight path := by
  induction path generalizing v with
  | nil => simp [pathSlack, pathEnd, pathWeight]
  | cons edge tail ih =>
    rcases edge with ⟨u,w⟩
    simp only [pathSlack, pathEnd, pathWeight, ih]
    ring

end OrbitAndFlow

#print axioms OrbitAndFlow.primeNorm_unitFactor
#print axioms OrbitAndFlow.pathSlack_telescopes
