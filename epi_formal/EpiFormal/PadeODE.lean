import Mathlib

open Polynomial Finset

noncomputable section

def padéP (n : ℕ) : ℝ[X] := X ^ n * (1 - X) ^ n

def padéR (n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (2 * n + 1), C ((-1 : ℝ) ^ k) * (derivative^[k] (padéP n))

/-- 反望远镜和：Σ_{k<m}(g k − g(k+1)) = g 0 − g m。 -/
lemma sum_telescope {G : Type*} [AddCommGroup G] (g : ℕ → G) (m : ℕ) :
    ∑ k ∈ range m, (g k - g (k + 1)) = g 0 - g m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih]
      abel

/-- 通用 telescoping：A_m + B_m = p + (−1)^m D^{m+1}p（反望远镜，无和式归纳）。 -/
lemma tele_general (p : ℝ[X]) (m : ℕ) :
    (∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k] p)) +
      (∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p)) =
      p + C ((-1 : ℝ) ^ m) * (derivative^[m + 1] p) := by
  have hmerge :
      (∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k] p)) +
        (∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p)) =
      ∑ k ∈ range (m + 1),
        (C ((-1 : ℝ) ^ k) * (derivative^[k] p) +
          C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p)) := by
    rw [← sum_add_distrib]
  rw [hmerge]
  -- 被加项 = g k − g(k+1)，g k = C((−1)^k) D^k p
  have hg : ∀ k ∈ range (m + 1),
      C ((-1 : ℝ) ^ k) * (derivative^[k] p) +
        C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p) =
      (fun k => C ((-1 : ℝ) ^ k) * (derivative^[k] p)) k -
        (fun k => C ((-1 : ℝ) ^ k) * (derivative^[k] p)) (k + 1) := by
    intro k _
    change C ((-1 : ℝ) ^ k) * (derivative^[k] p) +
        C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p) =
      C ((-1 : ℝ) ^ k) * (derivative^[k] p) -
        C ((-1 : ℝ) ^ (k + 1)) * (derivative^[k + 1] p)
    have hpow : (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) := by rw [pow_succ]; ring
    rw [hpow, C_neg]
    ring
  rw [sum_congr rfl hg]
  simp only [sum_telescope, pow_zero, Function.iterate_zero, C_1, one_mul, id_eq]
  -- 目标：p − C((−1)^(m+1)) D^{m+1}p = p + C((−1)^m) D^{m+1}p
  have hpow : (-1 : ℝ) ^ (m + 1) = -((-1 : ℝ) ^ m) := by rw [pow_succ]; ring
  rw [hpow, C_neg]
  simp only [neg_smul, one_smul, neg_neg, smul_eq_mul, neg_mul, one_mul]
  abel

/-- natDegree p_n ≤ 2n。 -/
lemma natDegree_padéP (n : ℕ) : (padéP n).natDegree ≤ 2 * n := by
  unfold padéP
  have hX : (X ^ n : ℝ[X]).natDegree = n := natDegree_X_pow n
  have h1 : (1 - X : ℝ[X]).natDegree = 1 := by
    have hneg : (1 - X : ℝ[X]) = -(X - C 1) := by simp only [C_1]; ring
    rw [hneg, natDegree_neg, natDegree_X_sub_C]
  have hpow : ((1 - X : ℝ[X]) ^ n).natDegree = n := by
    rw [natDegree_pow, h1, mul_one]
  have hne1 : (X ^ n : ℝ[X]) ≠ 0 := pow_ne_zero n X_ne_zero
  have hne2 : ((1 - X : ℝ[X]) ^ n) ≠ 0 := by
    have h1ne : (1 - X : ℝ[X]) ≠ 0 := by
      intro h
      have := congrArg (fun p => p.natDegree) h
      simp [h1] at this
    exact pow_ne_zero n h1ne
  rw [natDegree_mul hne1 hne2, hX, hpow]
  omega

/-- D^{2n+1} p_n = 0。 -/
lemma iter_deriv_padéP (n : ℕ) : derivative^[2 * n + 1] (padéP n) = 0 := by
  apply iterate_derivative_eq_zero
  have := natDegree_padéP n
  omega

/-- derivative 与迭代和交换：derivative A_m = B_m。 -/
lemma deriv_A (p : ℝ[X]) (m : ℕ) :
    derivative (∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k] p)) =
      ∑ k ∈ range (m + 1), C ((-1 : ℝ) ^ k) * (derivative^[k + 1] p) := by
  simp only [map_sum, derivative_C_mul, Function.iterate_succ_apply']

/-- 主 ODE：R_n + R_n' = p_n。 -/
lemma padéR_ode (n : ℕ) : padéR n + derivative (padéR n) = padéP n := by
  unfold padéR
  rw [deriv_A]
  have h := tele_general (padéP n) (2 * n)
  have hlast : C ((-1 : ℝ) ^ (2 * n)) * (derivative^[2 * n + 1] (padéP n)) = 0 := by
    rw [iter_deriv_padéP, mul_zero]
  rw [hlast, add_zero] at h
  exact h

end

#print axioms sum_telescope
#print axioms tele_general
#print axioms natDegree_padéP
#print axioms iter_deriv_padéP
#print axioms deriv_A
#print axioms padéR_ode
