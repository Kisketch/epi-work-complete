import Mathlib

/-!
# Log comparison + Frostman ratio bound (paper §7, blueprint S3–S5)

- `log_inv_le_two_log` (S3): `h ≥ H^{-2}` ⇒ `log h⁻¹ ≤ 2 log H`.
- `frostman_ratio_bound` (S5 core): overlap mass + exp-form mass + log
  comparison ⇒ `μU ≤ K0·M0·exp(-(b-2s)·jlogj + E1 + E2) · h^s`.
  The hypothesis `s < b/2` (i.e. `0 < b - 2*s`) is exactly what makes the
  residual exponent decay; it is NOT assumed here (stated with plain `0 < s`),
  so the decay role is visible in the exponent.

`H_j` growth (`log H_j = j log j + O(j)`) and the `E2 ≥ 0` error bound are
use-site interfaces (short-ae `H_j` line); see blueprint §4.
-/

namespace WindowLogThresh

open Real

/-- S3: from `H^{-2} ≤ h`, `log h⁻¹ ≤ 2 log H`. -/
theorem log_inv_le_two_log (h H : ℝ) (hh : 0 < h) (hH : 0 < H)
    (hle : ((H ^ 2)⁻¹ : ℝ) ≤ h) :
    Real.log h⁻¹ ≤ 2 * Real.log H := by
  have h1 : h⁻¹ ≤ ((H ^ 2)⁻¹ : ℝ)⁻¹ := by
    have hpos : (0 : ℝ) < ((H ^ 2)⁻¹ : ℝ) := by positivity
    exact (inv_le_inv₀ hh hpos).mpr hle
  have h2 : (((H ^ 2)⁻¹ : ℝ)⁻¹ : ℝ) = H ^ 2 := inv_inv _
  have h3 : Real.log h⁻¹ ≤ Real.log (H ^ 2 : ℝ) := by
    apply Real.log_le_log (inv_pos.mpr hh)
    rw [← h2]; exact h1
  rw [Real.log_pow] at h3
  push_cast at h3
  linarith

/-- S5 core ratio bound. `E2 ≥ 0` is the totalised log-error (use site). -/
theorem frostman_ratio_bound
    (muU mU h s b jlogj E1 E2 K0 M0 : ℝ)
    (_hs : 0 < s) (hh : 0 < h)
    (hmass : muU ≤ K0 * mU)
    (hK0 : 0 ≤ K0) (hM0 : 0 ≤ M0)
    (hexp : mU ≤ M0 * Real.exp (-(b * jlogj) + E1))
    (hlog : -(2 * s * jlogj) - E2 ≤ s * Real.log h)
    (_hE2 : 0 ≤ E2)
    : muU ≤ K0 * M0 * Real.exp (-((b - 2 * s) * jlogj) + E1 + E2) * h ^ s := by
  have hM0nn : (0 : ℝ) ≤ K0 * M0 := mul_nonneg hK0 hM0
  have e1 : muU ≤ K0 * M0 * Real.exp (-(b * jlogj) + E1) := by
    have h2a : K0 * mU ≤ K0 * (M0 * Real.exp (-(b * jlogj) + E1)) :=
      mul_le_mul_of_nonneg_left hexp hK0
    have h2 : K0 * mU ≤ K0 * M0 * Real.exp (-(b * jlogj) + E1) := by
      rwa [← mul_assoc] at h2a
    exact le_trans hmass h2
  have e2 : Real.exp (-(b * jlogj) + E1)
      ≤ Real.exp (-((b - 2 * s) * jlogj) + E1 + E2) * h ^ s := by
    have hrw : h ^ s = Real.exp (Real.log h * s) := Real.rpow_def_of_pos hh s
    rw [hrw, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlog' : -(2 * s * jlogj) - E2 ≤ Real.log h * s := by
      have : s * Real.log h = Real.log h * s := mul_comm _ _
      linarith [hlog]
    linarith [hlog']
  have e3 : K0 * M0 * Real.exp (-(b * jlogj) + E1)
      ≤ (K0 * M0 * Real.exp (-((b - 2 * s) * jlogj) + E1 + E2)) * h ^ s := by
    rw [mul_assoc (K0 * M0)]
    exact mul_le_mul_of_nonneg_left e2 hM0nn
  exact le_trans e1 e3

#print axioms WindowLogThresh.log_inv_le_two_log
#print axioms WindowLogThresh.frostman_ratio_bound

end WindowLogThresh
