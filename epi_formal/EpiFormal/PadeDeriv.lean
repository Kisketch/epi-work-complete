import Mathlib
import EpiFormal.PadeODE

open Polynomial Finset

noncomputable section

/-- 裸形式一阶导数（不带 padéP 包装，便于语法重写）：
    derivative (X^k (1−X)^k) = k·X^{k−1}(1−X)^{k−1}(1−2X)。 -/
lemma deriv_prod (k : ℕ) :
    derivative (X ^ k * (1 - X) ^ k : ℝ[X]) =
      C (k : ℝ) * (X ^ (k - 1) * (1 - X) ^ (k - 1)) * (1 - 2 * X) := by
  rcases k with _ | k
  · simp
  · change derivative (X ^ (k + 1) * (1 - X) ^ (k + 1) : ℝ[X]) =
      C ((k + 1 : ℕ) : ℝ) * (X ^ k * (1 - X) ^ k) * (1 - 2 * X)
    rw [derivative_mul, derivative_pow_succ, derivative_pow_succ]
    simp only [derivative_X, derivative_one, derivative_sub, mul_one]
    push_cast
    ring

/-- derivative (1 − 2X) = −2。 -/
lemma deriv_one_sub_two_X : derivative (1 - 2 * X : ℝ[X]) = -2 := by
  simp [derivative_sub, derivative_mul, derivative_X]

/-- p_n' = n·t^{n−1}(1−t)^{n−1}(1−2t)。 -/
lemma padéP_first_deriv (n : ℕ) :
    derivative (padéP n) =
      C (n : ℝ) * (X ^ (n - 1) * (1 - X) ^ (n - 1)) * (1 - 2 * X) :=
  deriv_prod n

/-- p_n'' = n(n−1) p_{n−2} − 2n(2n−1) p_{n−1}（对一切 n，n<2 时两边皆 0 由截断减法保证）。 -/
lemma padéP_second_deriv (n : ℕ) (hn : 2 ≤ n) :
    derivative^[2] (padéP n) =
      C ((n * (n - 1) : ℕ) : ℝ) * padéP (n - 2) -
        C ((2 * n * (2 * n - 1) : ℕ) : ℝ) * padéP (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : (m + 2 - 1 : ℕ) = m + 1 := by omega
  have h2 : (m + 2 - 2 : ℕ) = m := by omega
  have h3 : (m + 1 - 1 : ℕ) = m := by omega
  have h4 : (2 * (m + 2) - 1 : ℕ) = 2 * m + 3 := by omega
  simp only [h1, h2, h4, Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  unfold padéP
  rw [deriv_prod (m + 2), h1]
  -- 重结合，使 C 常数在最外层
  rw [mul_assoc, derivative_C_mul, derivative_mul]
  rw [deriv_prod (m + 1), deriv_one_sub_two_X, h3]
  -- 把所有幂展开成共同因子 X^m, (1−X)^m
  simp only [pow_succ]
  -- 逐点求值降到 ℝ：C a 求值即 a，ring 在实数域可完整处理
  apply Polynomial.funext
  intro t
  simp [eval_sub, eval_add, eval_mul, eval_pow]
  push_cast
  ring

end

#print axioms deriv_prod
#print axioms padéP_first_deriv
#print axioms padéP_second_deriv
