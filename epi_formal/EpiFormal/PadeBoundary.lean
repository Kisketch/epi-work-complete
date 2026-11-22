import Mathlib
import EpiFormal.PadeODE
import EpiFormal.PadeDeriv

open Real Polynomial Finset MeasureTheory intervalIntegral

noncomputable section

/-- I_n = ∫₀¹ e^t p_n(t) dt。 -/
def padeI (n : ℕ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp t * (padéP n).eval t

/-- p_n 在 0 处求值为 0（n≥1）。 -/
lemma padéP_eval_zero (n : ℕ) (hn : 1 ≤ n) : (padéP n).eval 0 = 0 := by
  unfold padéP
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  have h : (0:ℝ) ^ n = 0 := zero_pow (by omega)
  simp [h]

/-- p_n 在 1 处求值为 0（n≥1）。 -/
lemma padéP_eval_one (n : ℕ) (hn : 1 ≤ n) : (padéP n).eval 1 = 0 := by
  unfold padéP
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  have hn0 : n ≠ 0 := by omega
  simp [hn0]

/-- p_n' 在 0 处为 0（n≥2）。 -/
lemma padéP_deriv_eval_zero (n : ℕ) (hn : 2 ≤ n) :
    (derivative (padéP n)).eval 0 = 0 := by
  rw [padéP_first_deriv]
  simp only [eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one]
  have h1 : n - 1 ≥ 1 := by omega
  have h : (0:ℝ) ^ (n - 1) = 0 := zero_pow (by omega)
  simp [h]

/-- p_n' 在 1 处为 0（n≥2）。 -/
lemma padéP_deriv_eval_one (n : ℕ) (hn : 2 ≤ n) :
    (derivative (padéP n)).eval 1 = 0 := by
  rw [padéP_first_deriv]
  simp only [eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one]
  have hn1 : n - 1 ≠ 0 := by omega
  simp [hn1]

end

#print axioms padéP_eval_zero
#print axioms padéP_eval_one
#print axioms padéP_deriv_eval_zero
#print axioms padéP_deriv_eval_one
