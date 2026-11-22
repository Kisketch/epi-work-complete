import Mathlib

/-!
# 命题 C：尾项级数的精确递推 tₙ₊₁ = (n+1)tₙ − 1（M4，已证）

tₙ = Σ_{k>n} n!/k!。可和性由 ∑ 1/k! 可和（Real.summable_pow_div_factorial 1）
经常数倍与余有限同余得到；递推由 (n+1)·n! = (n+1)! 与拆分 k=n+1 项（值为 1）得到。
-/

open Real Filter

/-- 尾项 tₙ = Σ_{k>n} n!/k!（以 tsum 定义，k≤n 项补零）。 -/
noncomputable def tail (n : ℕ) : ℝ :=
  ∑' k : ℕ, if n < k then (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ) else 0

/-- 常数版可和性：Σ_{k>n} c/k! 可和（c 为任意实常数）。 -/
lemma summable_tail_const (c : ℝ) (n : ℕ) :
    Summable (fun k : ℕ => if n < k then c / (Nat.factorial k : ℝ) else 0) := by
  have hbase : Summable (fun k : ℕ => c / (Nat.factorial k : ℝ)) := by
    have := (Real.summable_pow_div_factorial 1).mul_left c
    convert this using 1 with k
    simp only [one_pow, mul_one]
    ring
  have heq : ∀ᶠ k in atTop, (if n < k then c / (Nat.factorial k : ℝ) else 0)
      = c / (Nat.factorial k : ℝ) := by
    filter_upwards [eventually_gt_atTop n] with k hk
    exact if_pos hk
  exact (summable_congr_atTop heq).mpr hbase

/-- 可和性（前置引理）。 -/
lemma tail_summable (n : ℕ) :
    Summable (fun k : ℕ => if n < k then (Nat.factorial n : ℝ) / (Nat.factorial k : ℝ) else 0) :=
  summable_tail_const (Nat.factorial n : ℝ) n

/-- 命题 C：tₙ₊₁ = (n+1)·tₙ − 1。 -/
theorem tail_recurrence (n : ℕ) : tail (n + 1) = (n + 1 : ℝ) * tail n - 1 := by
  -- (n+1)·tₙ = Σ_{k>n} (n+1)!/k!
  have hmul : (n + 1 : ℝ) * tail n =
      ∑' k : ℕ, if n < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0 := by
    simp only [tail]
    rw [← Summable.tsum_mul_left (n + 1 : ℝ) (tail_summable n)]
    apply tsum_congr
    intro k
    by_cases h : n < k
    · simp only [h, ite_true]
      have hfac : (Nat.factorial (n + 1) : ℝ) = (n + 1 : ℝ) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac]
      field_simp
    · simp only [h, ite_false, mul_zero]
  -- 拆分 k=n+1 项：Σ_{k>n} (n+1)!/k! = 1 + Σ_{k>n+1} (n+1)!/k! = 1 + tₙ₊₁
  have hsplit : (∑' k : ℕ, if n < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0)
      = 1 + tail (n + 1) := by
    have hpoint : (fun k : ℕ => if n < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0)
        = (fun k : ℕ => if k = n + 1 then (1 : ℝ) else 0)
          + (fun k : ℕ => if n + 1 < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0) := by
      funext k
      by_cases h1 : k = n + 1
      · subst h1
        have hlt : n < n + 1 := Nat.lt_succ_self n
        have hgt : ¬ n + 1 < n + 1 := by omega
        simp only [hlt, hgt, ite_true, ite_false, Pi.add_apply, add_zero]
        exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      · by_cases h2 : n + 1 < k
        · have hn : n < k := by omega
          simp only [h1, h2, hn, ite_true, ite_false, Pi.add_apply, zero_add]
        · have hn : ¬ n < k := by omega
          simp only [h1, h2, hn, ite_false, Pi.add_apply, zero_add, add_zero]
    rw [hpoint]
    have hs1 : Summable (fun k : ℕ => if k = n + 1 then (1 : ℝ) else 0) := by
      apply summable_of_ne_finset_zero (s := {n + 1})
      intro k hk
      simp only [Finset.mem_singleton] at hk
      exact if_neg hk
    have hs2 : Summable (fun k : ℕ => if n + 1 < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0) :=
      summable_tail_const (Nat.factorial (n + 1) : ℝ) (n + 1)
    show (∑' k : ℕ, ((if k = n + 1 then (1 : ℝ) else 0)
        + (if n + 1 < k then (Nat.factorial (n + 1) : ℝ) / (Nat.factorial k : ℝ) else 0)))
        = 1 + tail (n + 1)
    rw [hs1.tsum_add hs2]
    have hone : (∑' k : ℕ, if k = n + 1 then (1 : ℝ) else 0) = 1 := by
      rw [tsum_ite_eq]
    rw [hone]
    rfl
  linarith [hmul, hsplit]
