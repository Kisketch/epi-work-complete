import EpiFormal.CylinderDiameter

namespace Cylinder

open Matrix

/-- Difference of two fractions with unit cross determinant.

The hypothesis uses `a * d - c * b` order to match `consec_cross` syntactically. -/
theorem frac_abs_sub_of_unit_cross (a b c d : ℤ) (hc : 0 < c) (hd : 0 < d)
    (hdet : a * d - c * b = 1 ∨ a * d - c * b = -1) :
    |(a : ℝ) / (c : ℝ) - (b : ℝ) / (d : ℝ)| = 1 / ((c : ℝ) * (d : ℝ)) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hsub : (a : ℝ) / (c : ℝ) - (b : ℝ) / (d : ℝ)
      = ((a : ℝ) * (d : ℝ) - (c : ℝ) * (b : ℝ)) / ((c : ℝ) * (d : ℝ)) := by
    field_simp
  have hnum : |(a : ℝ) * (d : ℝ) - (c : ℝ) * (b : ℝ)| = 1 := by
    have e : ((a * d - c * b : ℤ) : ℝ) = (a : ℝ) * (d : ℝ) - (c : ℝ) * (b : ℝ) := by
      norm_cast
    cases hdet with
    | inl h => rw [← e, h, Int.cast_one, abs_one]
    | inr h => rw [← e, h, Int.cast_neg, Int.cast_one, abs_neg, abs_one]
  rw [hsub, abs_div, hnum]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ))]

/-- Diameter of the ordered closed interval between two reals. -/
theorem diam_Icc_min_max (x y : ℝ) :
    Metric.diam (Set.Icc (min x y) (max x y)) = |x - y| := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h, Real.diam_Icc h, ← abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [min_eq_right h, max_eq_left h, Real.diam_Icc h, ← abs_sub_comm,
      abs_of_nonpos (sub_nonpos.mpr h), neg_sub]

/-- The convergent fraction of a matrix: upper-left over lower-left entry. -/
noncomputable def cylFrac (M : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (M 0 0 : ℝ) / (M 1 0 : ℝ)

/-- The denominator of a matrix as a real. -/
noncomputable def cylDen (M : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := (M 1 0 : ℝ)

/-- Word-level cylinder diameter: consecutive children span `1 / (q * q')`. -/
theorem child_cyl_diam (w : List ℕ) (k : ℕ) (hk : 1 ≤ k) :
    Metric.diam (Set.Icc
      (min (cylFrac (cfProd (w ++ [k + 1]))) (cylFrac (cfProd (w ++ [k]))))
      (max (cylFrac (cfProd (w ++ [k + 1]))) (cylFrac (cfProd (w ++ [k])))))
      = 1 / (cylDen (cfProd (w ++ [k + 1])) * cylDen (cfProd (w ++ [k]))) := by
  have hq1 : 0 < (cfProd (w ++ [k + 1])) 1 0 :=
    childDen_pos w (k + 1) (Nat.le_add_left 1 k)
  have hq0 : 0 < (cfProd (w ++ [k])) 1 0 := childDen_pos w k hk
  have hdet : (cfProd (w ++ [k + 1])) 0 0 * (cfProd (w ++ [k])) 1 0
      - (cfProd (w ++ [k + 1])) 1 0 * (cfProd (w ++ [k])) 0 0 = 1
      ∨ (cfProd (w ++ [k + 1])) 0 0 * (cfProd (w ++ [k])) 1 0
      - (cfProd (w ++ [k + 1])) 1 0 * (cfProd (w ++ [k])) 0 0 = -1 := by
    have hcc := consec_cross w k
    have hD := cfProd_det w
    rw [hD] at hcc
    have hpm := neg_one_pow_eq_or ℤ w.length
    cases hpm with
    | inl h1 => left; rw [hcc, h1]
    | inr h1 => right; rw [hcc, h1]
  rw [diam_Icc_min_max]
  simp only [cylFrac, cylDen]
  exact frac_abs_sub_of_unit_cross
    ((cfProd (w ++ [k + 1])) 0 0) ((cfProd (w ++ [k])) 0 0)
    ((cfProd (w ++ [k + 1])) 1 0) ((cfProd (w ++ [k])) 1 0) hq1 hq0 hdet

#print axioms frac_abs_sub_of_unit_cross
#print axioms diam_Icc_min_max
#print axioms child_cyl_diam

end Cylinder
