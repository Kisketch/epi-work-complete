import Mathlib

/-!
# Cylinder infrastructure, phase A: continuant matrices (paper2 §7, L09/L10 prerequisite; L02/L12/L13 later).

A finite continued-fraction word `w = [a₁, …, aᵣ]` (each `aᵢ : ℕ`) acts by
`M(aᵢ) = !![aᵢ, 1; 1, 0]`; the product gives convergents numerators/denominators.
All results here are elementary algebra over `ℤ` (no analysis, no whitelist axioms).

Paper anchor: tex L2421–2425 (cylinder geometry needs `u = qᵣ`, `v = qᵣ₋₁`);
L2471–2485 (continuant identity `t = m*u' + n*v'`); L2790–2794 (two regular
expansions of `m/n`, lengths `s` and `s+1`).
-/

open Matrix Finset

namespace Cylinder

/-- Single-letter matrix. -/
def cfMat (a : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(a : ℤ), 1; 1, 0]

/-- Product over a word (left-to-right application order). -/
def cfProd : List ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | a :: w => cfMat a * cfProd w

/-- Determinant of a single letter. -/
theorem cfMat_det (a : ℕ) : (cfMat a).det = -1 := by
  unfold cfMat; rw [det_fin_two]; simp

/-- Determinant of a product: `(-1)^length`. -/
theorem cfProd_det (w : List ℕ) : (cfProd w).det = (-1 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [cfProd]
  | cons a w ih =>
    simp only [cfProd, List.length_cons, pow_succ]
    rw [det_mul, cfMat_det, ih]; ring

/-- Convergents pair `(p, q)` by recursion: `(0,1)` then `(a*p+q, p)`. -/
def convPair : List ℕ → ℤ × ℤ
  | [] => (0, 1)
  | a :: w => ((a : ℤ) * (convPair w).1 + (convPair w).2, (convPair w).1)

/-- Numerator / denominator projections. -/
def convNum (w : List ℕ) : ℤ := (convPair w).1
def convDen (w : List ℕ) : ℤ := (convPair w).2

/-- Unfold once. -/
theorem convPair_cons (a : ℕ) (w : List ℕ) :
    convPair (a :: w) = ((a : ℤ) * (convPair w).1 + (convPair w).2, (convPair w).1) := by
  rfl

/-- Both components nonneg (joint induction). -/
theorem convPair_nonneg (w : List ℕ) : 0 ≤ (convPair w).1 ∧ 0 ≤ (convPair w).2 := by
  induction w with
  | nil => constructor <;> norm_num [convPair]
  | cons a w ih =>
    obtain ⟨hp, hq⟩ := ih
    rw [convPair_cons]
    constructor
    · simp only
      have : (0 : ℤ) ≤ (a : ℤ) * (convPair w).1 := mul_nonneg (Int.natCast_nonneg a) hp
      linarith
    · simp only; exact hp

/-- Denominator nonneg. -/
theorem convDen_nonneg (w : List ℕ) : 0 ≤ convDen w := (convPair_nonneg w).2

/-- Numerator nonneg. -/
theorem convNum_nonneg (w : List ℕ) : 0 ≤ convNum w := (convPair_nonneg w).1

/-- Denominator of a cons is the numerator of the tail. -/
theorem convDen_cons (a : ℕ) (w : List ℕ) : convDen (a :: w) = convNum w := by
  unfold convDen convNum; rw [convPair_cons]

/-- Numerator recurrence. -/
theorem convNum_cons (a : ℕ) (w : List ℕ) :
    convNum (a :: w) = (a : ℤ) * convNum w + convDen w := by
  unfold convNum convDen; rw [convPair_cons]

#print axioms cfMat_det
#print axioms cfProd_det
#print axioms convPair_cons
#print axioms convPair_nonneg
#print axioms convDen_nonneg
#print axioms convNum_nonneg
#print axioms convDen_cons
#print axioms convNum_cons
