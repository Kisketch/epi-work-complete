import EpiFormal.CylinderMediant

namespace Cylinder

open Matrix Finset

/-- All entries of a convergent product matrix are nonneg. -/
theorem cfProd_nonneg (w : List ℕ) (i j : Fin 2) : 0 ≤ (cfProd w) i j := by
  induction w generalizing i j with
  | nil =>
    show (0 : ℤ) ≤ (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
    rcases eq_or_ne i j with rfl | hne
    · rw [Matrix.one_apply_eq]; norm_num
    · rw [Matrix.one_apply_ne hne]
  | cons a w ih =>
    rw [cfProd, Matrix.mul_apply, Fin.sum_univ_two]
    have hM : ∀ p q : Fin 2, 0 ≤ (cfMat a) p q := by
      intro p q
      fin_cases p <;> fin_cases q <;> simp [cfMat]
    have t0 : 0 ≤ (cfMat a) i 0 * (cfProd w) 0 j :=
      mul_nonneg (hM i 0) (ih 0 j)
    have t1 : 0 ≤ (cfMat a) i 1 * (cfProd w) 1 j :=
      mul_nonneg (hM i 1) (ih 1 j)
    linarith

/-- The determinant is nonzero. -/
theorem cfProd_det_ne_zero (w : List ℕ) : (cfProd w).det ≠ 0 := by
  rw [cfProd_det]
  exact pow_ne_zero _ (by norm_num)

/-- Child denominators are positive for positive partial quotients. -/
theorem childDen_pos (w : List ℕ) (k : ℕ) (hk : 1 ≤ k) :
    0 < (cfProd (w ++ [k])) 1 0 := by
  rw [cfProd_append_single, Matrix.mul_apply, Fin.sum_univ_two]
  simp [cfMat]
  set x : ℤ := (cfProd w) 1 0 with hx
  set y : ℤ := (cfProd w) 1 1 with hy
  have hx0 : 0 ≤ x := cfProd_nonneg w 1 0
  have hy0 : 0 ≤ y := cfProd_nonneg w 1 1
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  by_contra h
  push Not at h
  have hle : (k : ℤ) * x + y ≤ 0 := by linarith
  have hge : 0 ≤ (k : ℤ) * x + y := by
    have := mul_nonneg (le_of_lt hk0) hx0
    linarith
  have heq : (k : ℤ) * x + y = 0 := le_antisymm hle hge
  have hx_eq : x = 0 := by
    have hkx : (k : ℤ) * x = 0 := by
      have h1 : (k : ℤ) * x ≤ 0 := by linarith
      have h2 : 0 ≤ (k : ℤ) * x := mul_nonneg (le_of_lt hk0) hx0
      linarith
    rcases mul_eq_zero.mp hkx with hkz | hxz
    · exfalso; exact (ne_of_gt hk0) hkz
    · exact hxz
  have hkx0 : (k : ℤ) * x = 0 := by rw [hx_eq, mul_zero]
  have hy_eq : y = 0 := by linarith
  have hdet : (cfProd w).det = 0 := by
    rw [Matrix.det_fin_two]
    have e00 : (cfProd w) 0 0 * (cfProd w) 1 1 = (cfProd w) 0 0 * y := by rw [hy]
    have e01 : (cfProd w) 0 1 * (cfProd w) 1 0 = (cfProd w) 0 1 * x := by rw [hx]
    rw [e00, e01, hx_eq, hy_eq]
    ring
  exact cfProd_det_ne_zero w hdet

/-- Distinct partial quotients give distinct child fractions
    (cross-multiplied form, no division needed). -/
theorem sibling_strict (w : List ℕ) (k₁ k₂ : ℕ) (h : k₁ ≠ k₂) :
    (cfProd (w ++ [k₁])) 0 0 * (cfProd (w ++ [k₂])) 1 0
      ≠ (cfProd (w ++ [k₂])) 0 0 * (cfProd (w ++ [k₁])) 1 0 := by
  have hcross := sibling_cross w k₁ k₂
  have hk : ((k₁ : ℤ) - (k₂ : ℤ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact fun heq => h (Nat.cast_injective heq)
  have hd : (cfProd w).det ≠ 0 := cfProd_det_ne_zero w
  have hne : ((k₁ : ℤ) - (k₂ : ℤ)) * (cfProd w).det ≠ 0 :=
    mul_ne_zero hk hd
  rw [← hcross] at hne
  exact sub_ne_zero.mp hne

#print axioms cfProd_nonneg
#print axioms cfProd_det_ne_zero
#print axioms childDen_pos
#print axioms sibling_strict
