import EpiFormal.Cylinder

namespace Cylinder

open Matrix Finset

/-- Splitting a snoc into a product on the right. -/
theorem cfProd_append_single (w : List ℕ) (k : ℕ) :
    cfProd (w ++ [k]) = cfProd w * cfMat k := by
  induction w with
  | nil => simp [cfProd]
  | cons a w ih =>
    show cfProd (a :: (w ++ [k])) = cfProd (a :: w) * cfMat k
    rw [cfProd, cfProd, ih, Matrix.mul_assoc]

/-- The second column of the product matrix is the convergent pair. -/
theorem col1_convPair (w : List ℕ) :
    ((cfProd w) 0 1, (cfProd w) 1 1) = convPair w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [cfProd, convPair_cons]
    have e00 : (cfMat a * cfProd w) 0 1
        = (a : ℤ) * (cfProd w) 0 1 + (cfProd w) 1 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [cfMat]
    have e11 : (cfMat a * cfProd w) 1 1 = (cfProd w) 0 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp [cfMat]
    rw [e00, e11]
    have h0 : (cfProd w) 0 1 = (convPair w).1 := congrArg Prod.fst ih
    have h1 : (cfProd w) 1 1 = (convPair w).2 := congrArg Prod.snd ih
    rw [h0, h1]

/-- Sibling cross-difference identity (mediant separation core).
    For children `w ++ [k₁]`, `w ++ [k₂]`, writing `P k`, `Q k` for the
    numerator / denominator entries of the first column, we get
    `P k₁ * Q k₂ - P k₂ * Q k₁ = (k₁ - k₂) * det`. -/
theorem sibling_cross (w : List ℕ) (k₁ k₂ : ℕ) :
    (cfProd (w ++ [k₁])) 0 0 * (cfProd (w ++ [k₂])) 1 0
      - (cfProd (w ++ [k₂])) 0 0 * (cfProd (w ++ [k₁])) 1 0
      = ((k₁ : ℤ) - (k₂ : ℤ)) * (cfProd w).det := by
  rw [cfProd_append_single, cfProd_append_single]
  have e00 : ∀ k : ℕ, (cfProd w * cfMat k) 0 0
      = (cfProd w) 0 0 * (k : ℤ) + (cfProd w) 0 1 := by
    intro k
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat]
  have e10 : ∀ k : ℕ, (cfProd w * cfMat k) 1 0
      = (cfProd w) 1 0 * (k : ℤ) + (cfProd w) 1 1 := by
    intro k
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfMat]
  rw [e00 k₁, e00 k₂, e10 k₁, e10 k₂, Matrix.det_fin_two]
  ring

#print axioms cfProd_append_single
#print axioms col1_convPair
#print axioms sibling_cross
