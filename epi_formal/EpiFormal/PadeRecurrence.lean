import Mathlib
import EpiFormal.PadeODE
import EpiFormal.PadeDeriv
import EpiFormal.PadeBoundary

open Real Polynomial Finset MeasureTheory intervalIntegral Set
open scoped Interval

noncomputable section

/-- 被积函数 e^t·(多项式求值) 连续。 -/
lemma cont_exp_mul_eval (p : ℝ[X]) :
    Continuous (fun t : ℝ => Real.exp t * p.eval t) :=
  Real.continuous_exp.mul p.continuous_aeval

/-- 一次分部积分（边界项为零时）：∫e^t p' = −∫e^t p，
    前提 p(0)=p(1)=0。 -/
lemma ibp_zero (p : ℝ[X]) (h0 : p.eval 0 = 0) (h1 : p.eval 1 = 0) :
    ∫ t in (0:ℝ)..1, Real.exp t * (derivative p).eval t =
      -∫ t in (0:ℝ)..1, Real.exp t * p.eval t := by
  have hcont_e : ContinuousOn Real.exp [[(0:ℝ), 1]] :=
    Real.continuous_exp.continuousOn
  have hcont_p : ContinuousOn (fun t => p.eval t) [[(0:ℝ), 1]] :=
    p.continuous_aeval.continuousOn
  have hde : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt Real.exp (Real.exp x) x := fun x _ => Real.hasDerivAt_exp x
  have hdp : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun t => p.eval t) ((derivative p).eval x) x :=
    fun x _ => p.hasDerivAt_aeval x
  have hie : IntervalIntegrable Real.exp volume (0:ℝ) 1 :=
    Real.continuous_exp.intervalIntegrable _ _
  have hip : IntervalIntegrable (fun t => (derivative p).eval t) volume (0:ℝ) 1 :=
    (derivative p).continuous_aeval.intervalIntegrable _ _
  have h := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := Real.exp) (v := fun t => p.eval t) (u' := Real.exp)
    (v' := fun t => (derivative p).eval t) hcont_e hcont_p hde hdp hie hip
  -- h : ∫ exp * p' = exp 1 * p(1) - exp 0 * p(0) - ∫ exp * p
  rw [h0, h1] at h
  simp only [mul_zero, sub_zero, zero_sub] at h
  linarith [h]

/-- 两次分部积分：∫e^t p_n = ∫e^t p_n''（n≥2，四个边界值皆零）。 -/
lemma padeI_eq_second (n : ℕ) (hn : 2 ≤ n) :
    ∫ t in (0:ℝ)..1, Real.exp t * (padéP n).eval t =
      ∫ t in (0:ℝ)..1, Real.exp t * (derivative^[2] (padéP n)).eval t := by
  have h1 : 1 ≤ n := by omega
  have h1' : 1 ≤ n - 1 := by omega
  -- 第一次：p_n 边界零 ⇒ ∫e^t p_n' = −∫e^t p_n
  have step1 := ibp_zero (padéP n) (padéP_eval_zero n h1) (padéP_eval_one n h1)
  -- 第二次：p_n' 边界零 ⇒ ∫e^t p_n'' = −∫e^t p_n'
  have step2 := ibp_zero (derivative (padéP n))
    (padéP_deriv_eval_zero n hn) (padéP_deriv_eval_one n hn)
  have hiter : derivative^[2] (padéP n) = derivative (derivative (padéP n)) := by
    simp [Function.iterate_succ_apply']
  rw [hiter]
  linarith [step1, step2]

/-- **积分递推**：I_n = n(n−1) I_{n−2} − 2n(2n−1) I_{n−1}（n≥2）。 -/
lemma padeI_recurrence (n : ℕ) (hn : 2 ≤ n) :
    ∫ t in (0:ℝ)..1, Real.exp t * (padéP n).eval t =
      (n * (n - 1) : ℕ) * (∫ t in (0:ℝ)..1, Real.exp t * (padéP (n-2)).eval t) -
        (2 * n * (2 * n - 1) : ℕ) * (∫ t in (0:ℝ)..1, Real.exp t * (padéP (n-1)).eval t) := by
  rw [padeI_eq_second n hn, padéP_second_deriv n hn]
  -- 被积函数按 eval 展开为线性组合
  have hpoint : ∀ t : ℝ,
      Real.exp t * (C ((n * (n - 1) : ℕ) : ℝ) * padéP (n - 2) -
        C ((2 * n * (2 * n - 1) : ℕ) : ℝ) * padéP (n - 1)).eval t =
      (n * (n - 1) : ℕ) * (Real.exp t * (padéP (n-2)).eval t) -
        (2 * n * (2 * n - 1) : ℕ) * (Real.exp t * (padéP (n-1)).eval t) := by
    intro t
    simp only [eval_sub, eval_mul, eval_C]
    push_cast
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  · exact ((cont_exp_mul_eval (padéP (n-2))).const_mul _).intervalIntegrable _ _
  · exact ((cont_exp_mul_eval (padéP (n-1))).const_mul _).intervalIntegrable _ _

end

#print axioms ibp_zero
#print axioms padeI_eq_second
#print axioms padeI_recurrence
