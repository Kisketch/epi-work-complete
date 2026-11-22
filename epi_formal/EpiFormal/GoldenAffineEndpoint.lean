import Mathlib

/-- A bounded scaled distance to a rational endpoint bounds the leading
coefficient when the conjugate separation has bounded discriminant. -/
theorem rational_endpoint_cutoff
    (a x y r D M S : ℝ) (ha : 0 < a) (hM : 0 ≤ M)
    (hsep : a * |x - y| ≤ S) (hclose : a * |r - x| ≤ M)
    (hnorm : 1 ≤ D ^ 2 * a * |r - x| * |r - y|) :
    a ≤ D ^ 2 * M * (M + S) := by
  have htriangle : |r - y| ≤ |r - x| + |x - y| := by
    rw [show r - y = (r - x) + (x - y) by ring]
    exact abs_add_le (r - x) (x - y)
  have hy : a * |r - y| ≤ M + S := by
    calc
      a * |r - y| ≤ a * (|r - x| + |x - y|) :=
        mul_le_mul_of_nonneg_left htriangle ha.le
      _ ≤ M + S := by rw [mul_add]; linarith
  calc
    a ≤ D ^ 2 * (a * |r - x|) * (a * |r - y|) := by
      have h := mul_le_mul_of_nonneg_left hnorm ha.le
      nlinarith only [h]
    _ ≤ D ^ 2 * M * (M + S) := by
      gcongr

#print axioms rational_endpoint_cutoff
