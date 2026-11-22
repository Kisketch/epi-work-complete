import Mathlib
import EpiFormal.PadeODE
import EpiFormal.PadeDeriv
import EpiFormal.PadeBoundary
import EpiFormal.PadeRecurrence
import EpiFormal.PadeIntegral
import EpiFormal.DeltaReduction
import EpiFormal.DimHCore

open Real Polynomial Finset MeasureTheory intervalIntegral Set
open scoped Interval ENNReal

namespace DeltaSign

noncomputable section

/-- I_n = ∫₀¹ e^t t^n(1−t)^n dt。 -/
def I (n : ℕ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp t * (padéP n).eval t

/-- E_n = (−1)^n · n! · δ_n。 -/
def E (n : ℕ) : ℝ := (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * deltaSel n

/-! ## 初值 -/

lemma I_zero : I 0 = Real.exp 1 - 1 := by
  unfold I padéP
  simp only [pow_zero, mul_one, eval_one]
  simp [intervalIntegral.integral_const_mul]

lemma E_zero : E 0 = Real.exp 1 - 1 := by
  unfold E deltaSel
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, Qsel_zero, Psel_zero]
  push_cast
  ring

lemma I_one : I 1 = 3 - Real.exp 1 := by
  have h := PadeIntegral.pade_integral_repr 1
  unfold I
  rw [h]
  -- R_1 = Σ_{k≤2}(−1)^k D^k p_1；p_1 = X(1−X)
  have hR0 : (padéR 1).eval 0 = -3 := by
    unfold padéR padéP
    norm_num [Finset.sum_range_succ, Function.iterate_succ_apply']
    <;> simp [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X]
    <;> ring
  have hR1 : (padéR 1).eval 1 = -1 := by
    unfold padéR padéP
    norm_num [Finset.sum_range_succ, Function.iterate_succ_apply']
    <;> simp [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X]
    <;> ring
  rw [hR0, hR1]
  ring

lemma E_one : E 1 = 3 - Real.exp 1 := by
  unfold E deltaSel
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, Qsel_one, Psel_one]
  push_cast
  ring

/-! ## E 的递推（由 deltaSel_rec 纯代数推出） -/

lemma E_recurrence (n : ℕ) (hn : 2 ≤ n) :
    E n = (n : ℝ) * ((n - 1 : ℕ) * E (n - 2) - (4 * n - 2 : ℝ) * E (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : (m + 2 - 1 : ℕ) = m + 1 := by omega
  have h2 : (m + 2 - 2 : ℕ) = m := by omega
  -- δ 递推：δ_{m+2} = (4(m+1)+2) δ_{m+1} + δ_m
  have hd := DeltaReduction.deltaSel_rec (m + 1) (by omega)
  have h3 : (m + 1 - 1 : ℕ) = m := by omega
  have h4 : (m + 1 + 1 : ℕ) = m + 2 := by omega
  rw [h3, h4] at hd
  -- 阶乘关系
  have hf1 : (Nat.factorial (m + 1) : ℝ) = (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf2 : (Nat.factorial (m + 2) : ℝ) =
      (m + 2 : ℝ) * (m + 1 : ℝ) * (Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  -- 符号关系
  have hs1 : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by rw [pow_succ]; ring
  have hs2 : (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ m := by
    rw [pow_succ, pow_succ]; ring
  unfold E
  simp only [h1, h2]
  rw [hf1, hf2, hs1, hs2, hd]
  push_cast
  ring

/-! ## I 的递推（已验证 padeI_recurrence 的包装） -/

lemma I_recurrence (n : ℕ) (hn : 2 ≤ n) :
    I n = (n : ℝ) * ((n - 1 : ℕ) * I (n - 2) - (4 * n - 2 : ℝ) * I (n - 1)) := by
  have h := padeI_recurrence n hn
  unfold I
  rw [h]
  have hc1 : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    push_cast; ring
  have hc2 : ((2 * n * (2 * n - 1) : ℕ) : ℝ) = (n : ℝ) * (4 * n - 2 : ℝ) := by
    have h2n : (2 * n - 1 : ℕ) = 2 * n - 1 := rfl
    cases n with
    | zero => omega
    | succ k =>
        simp only [Nat.mul_succ, Nat.add_sub_cancel]
        push_cast
        ring
  rw [hc1, hc2]
  ring

/-! ## 归纳：E_n = I_n -/

theorem E_eq_I (n : ℕ) : E n = I n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · rw [E_zero, I_zero]
    · rw [E_one, I_one]
    · have hn : 2 ≤ m + 2 := by omega
      have h1 : m + 2 - 2 = m := by omega
      have h2 : m + 2 - 1 = m + 1 := by omega
      rw [E_recurrence (m + 2) hn, I_recurrence (m + 2) hn, h1, h2]
      rw [ih m (by omega), ih (m + 1) (by omega)]

/-! ## I_n > 0（被积函数在 (0,1) 恒正） -/

theorem I_pos (n : ℕ) : 0 < I n := by
  -- 被积函数在 (0,1) 严格正：e^t>0, t^n>0, (1−t)^n>0
  have hpos_on : ∀ t ∈ Ioo (0:ℝ) 1,
      0 < Real.exp t * (padéP n).eval t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have h1t : 0 < 1 - t := by linarith
    apply mul_pos (Real.exp_pos t)
    unfold padéP
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    exact mul_pos (pow_pos ht0 n) (pow_pos h1t n)
  have hcont : Continuous (fun t : ℝ => Real.exp t * (padéP n).eval t) :=
    cont_exp_mul_eval (padéP n)
  have hnn : ∀ t ∈ Ioc (0:ℝ) 1, 0 ≤ Real.exp t * (padéP n).eval t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    apply mul_nonneg (le_of_lt (Real.exp_pos t))
    unfold padéP
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    exact mul_nonneg (pow_nonneg (le_of_lt ht0) n) (pow_nonneg (by linarith) n)
  -- 用严格正性 + 连续性：取中点 1/2 处正，故积分正
  have hmid : (1/2 : ℝ) ∈ Ioo (0:ℝ) 1 := by norm_num
  have hm := hpos_on (1/2) hmid
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp t * (padéP n).eval t)
      volume (0:ℝ) 1 := hcont.intervalIntegrable _ _
  unfold I
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae']
  · refine ⟨by norm_num, ?_⟩
    -- support ∩ Ioc 0 1 ⊇ Ioo 0 1，测度 1 > 0
    have hsub : Ioo (0:ℝ) 1 ⊆ Function.support
        (fun t : ℝ => Real.exp t * (padéP n).eval t) ∩ Ioc (0:ℝ) 1 := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht.1
      have ht1 : t < 1 := ht.2
      exact ⟨ne_of_gt (hpos_on t ⟨ht0, ht1⟩), ⟨ht0, le_of_lt ht1⟩⟩
    have hmeas : volume (Ioo (0:ℝ) 1) = 1 := by simp
    have hle : volume (Ioo (0:ℝ) 1) ≤ volume
        (Function.support (fun t : ℝ => Real.exp t * (padéP n).eval t) ∩ Ioc (0:ℝ) 1) :=
      measure_mono hsub
    rw [hmeas] at hle
    exact lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1) hle
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact hnn t ht
  · exact hint

/-! ## 结论：δ 符号交替 -/

theorem deltaSignAlternation_proved : DeltaReduction.deltaSignAlternation := by
  intro j hj
  have hEI := E_eq_I j
  have hpos := I_pos j
  unfold E at hEI
  rw [← hEI] at hpos
  -- hpos : 0 < (−1)^j · j! · δ_j，j! > 0
  have hfact : 0 < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hrearr : (-1 : ℝ) ^ j * (Nat.factorial j : ℝ) * deltaSel j =
      (Nat.factorial j : ℝ) * ((-1 : ℝ) ^ j * deltaSel j) := by ring
  rw [hrearr] at hpos
  have hdiv : 0 < (Nat.factorial j : ℝ) * ((-1 : ℝ) ^ j * deltaSel j) /
      (Nat.factorial j : ℝ) := div_pos hpos hfact
  rwa [mul_div_cancel_left₀ _ (ne_of_gt hfact)] at hdiv

/-! ## 两条原公理，现证为定理（OBL-5 终点） -/

/-- **原公理 1，现为定理**：δ_j → 0。 -/
theorem deltaSel_tendsto_zero_proved :
    Filter.Tendsto deltaSel Filter.atTop (nhds 0) :=
  DeltaReduction.deltaSel_tendsto_zero_of_sign deltaSignAlternation_proved

/-- **原公理 2，现为定理**：|δ_j| < 1/(2j·Q_j)（j≥1）。 -/
theorem abs_deltaSel_lt_proved (j : ℕ) (hj : 1 ≤ j) :
    |deltaSel j| < 1 / (2 * (j : ℝ) * (Qsel j : ℝ)) :=
  DeltaReduction.abs_deltaSel_lt_of_sign deltaSignAlternation_proved j hj

end

end DeltaSign

#print axioms DeltaSign.E_eq_I
#print axioms DeltaSign.I_pos
#print axioms DeltaSign.deltaSignAlternation_proved
#print axioms DeltaSign.deltaSel_tendsto_zero_proved
#print axioms DeltaSign.abs_deltaSel_lt_proved
