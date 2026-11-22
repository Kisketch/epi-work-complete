import Mathlib
import EpiFormal.PadeODE

open Real Filter Topology Set Polynomial MeasureTheory intervalIntegral

namespace PadeIntegral

noncomputable section

/-- F(t) = e^t · R_n(t)（作为 ℝ → ℝ 函数）。 -/
def padeF (n : ℕ) (t : ℝ) : ℝ := Real.exp t * (padéR n).eval t

/-- F 在每点可导，导数 = e^t · p_n(t)（用 ODE：R_n + R_n' = p_n）。 -/
lemma padeF_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (padeF n) (Real.exp t * (padéP n).eval t) t := by
  -- F = exp · (R_n.eval)，乘积求导
  have hexp : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  have hR : HasDerivAt (fun t => (padéR n).eval t) ((derivative (padéR n)).eval t) t :=
    (padéR n).hasDerivAt_aeval t
  have hmul := hexp.mul hR
  -- hmul : HasDerivAt F (exp t * R_n.eval t + exp t * (R_n').eval t) t
  have hderiv : Real.exp t * (padéR n).eval t + Real.exp t * (derivative (padéR n)).eval t =
      Real.exp t * (padéP n).eval t := by
    have hode := padéR_ode n
    have heval := congrArg (fun p => p.eval t) hode
    simp only [eval_add] at heval
    -- heval : R_n.eval t + (R_n').eval t = p_n.eval t
    have h : Real.exp t * (padéR n).eval t + Real.exp t * (derivative (padéR n)).eval t =
        Real.exp t * ((padéR n).eval t + (derivative (padéR n)).eval t) := by ring
    rw [h, heval]
  convert hmul using 1
  · funext t; rfl
  · exact hderiv.symm

/-- 积分表示：∫₀¹ e^t p_n(t) dt = e·R_n(1) − R_n(0)。 -/
lemma pade_integral_repr (n : ℕ) :
    ∫ t in (0 : ℝ)..1, Real.exp t * (padéP n).eval t =
      Real.exp 1 * (padéR n).eval 1 - (padéR n).eval 0 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (padeF n) (Real.exp t * (padéP n).eval t) t := by
    intro t _
    exact padeF_hasDerivAt n t
  have hcont : Continuous (fun t : ℝ => Real.exp t * (padéP n).eval t) := by
    apply Continuous.mul Real.continuous_exp
    exact (padéP n).continuous_aeval
  have hinteg : IntervalIntegrable (fun t => Real.exp t * (padéP n).eval t) volume 0 1 :=
    hcont.intervalIntegrable _ _
  have hint := integral_eq_sub_of_hasDerivAt hderiv hinteg
  simp only [padeF, Real.exp_zero, one_mul] at hint
  exact hint

end

end PadeIntegral

#print axioms PadeIntegral.padeF_hasDerivAt
#print axioms PadeIntegral.pade_integral_repr
