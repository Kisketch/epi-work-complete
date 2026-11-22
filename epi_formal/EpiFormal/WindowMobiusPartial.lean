import Mathlib
import EpiFormal.WindowMobiusCount

/-!
# Partial Möbius sums feeding the window count (paper2 §7, `thm:windows`)

This file isolates the elementary real-analytic input used by
`EpiFormal.WindowMobiusCount` (`coprime_count_ge`): the partial sums of
`μ(d)/d²` over `1 ≤ d ≤ D` are bounded below by `359/900`, uniformly in `D ≥ 1`.

* `moebius_first_five`: `∑_{d=1}^{5} μ(d)/d² = 1 - 1/4 - 1/9 - 1/25 = 539/900`.
* `moebius_tail_le`: `|∑_{d=6}^{D} μ(d)/d²| ≤ 1/5`, from termwise
  `|μ d| ≤ 1` and the harmonic square tail `∑_{d≥6} 1/d² ≤ 1/5`
  (`WindowMobiusCount.moebius_tail_sq`).
* `moebius_partial`: `∑_{d=1}^{D} μ(d)/d² ≥ 539/900 - 1/5 = 359/900` for `D ≥ 1`
  (the hypothesis `1 ≤ D` is necessary: at `D = 0` the sum is `0`).

Reference: paper2 §7, `thm:windows`.
-/

open ArithmeticFunction Finset Real
open scoped BigOperators

namespace WindowMobiusCount

/-- The first five Möbius terms sum to `539/900`. -/
theorem moebius_first_five :
    (∑ d ∈ Finset.Icc 1 5, (moebius d : ℝ) / (d : ℝ) ^ 2) = 539 / 900 := by
  have hset : Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  have h1 : (moebius 1 : ℝ) = 1 := by
    rw [moebius_apply_one]
    norm_num
  have h2 : (moebius 2 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 2)]
    norm_num
  have h3 : (moebius 3 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 3)]
    norm_num
  have h4 : (moebius 4 : ℝ) = 0 := by
    have h := moebius_apply_prime_pow (p := 2) (k := 2) (by norm_num) (by norm_num)
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num,
      ite_eq_right (by norm_num : ¬(2 : ℕ) = 1)] at h
    exact_mod_cast h
  have h5 : (moebius 5 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 5)]
    norm_num
  rw [hset]
  rw [Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4, 5} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4, 5} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4, 5} : Finset ℕ)),
    Finset.sum_insert (by decide : (4 : ℕ) ∉ ({5} : Finset ℕ)),
    Finset.sum_singleton]
  rw [h1, h2, h3, h4, h5]
  norm_num

/-- The Möbius tail over `[6, D]` is bounded by `1/5` in absolute value. -/
theorem moebius_tail_le (D : ℕ) :
    |∑ d ∈ Finset.Icc 6 D, (moebius d : ℝ) / (d : ℝ) ^ 2| ≤ 1 / 5 := by
  refine le_trans (Finset.abs_sum_le_sum_abs (fun d => (moebius d : ℝ) / (d : ℝ) ^ 2)
    (Finset.Icc 6 D)) ?_
  have hterm : ∀ d ∈ Finset.Icc 6 D,
      |(moebius d : ℝ) / (d : ℝ) ^ 2| ≤ 1 / (d : ℝ) ^ 2 := by
    intro d hd
    have hd6 : 6 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      have hd0 : (0 : ℕ) < d := by omega
      exact_mod_cast hd0
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos hdpos 2
    have hμ : |(moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast abs_moebius_le_one (n := d)
    rw [abs_div, abs_of_pos hd2]
    exact div_le_div_of_nonneg_right hμ (le_of_lt hd2)
  exact le_trans (Finset.sum_le_sum hterm) (moebius_tail_sq D)

/-- Partial sums of `μ(d)/d²` are at least `359/900` for every `D ≥ 1`. -/
theorem moebius_partial (D : ℕ) (hD1 : 1 ≤ D) :
    359 / 900 ≤ ∑ d ∈ Finset.Icc 1 D, (moebius d : ℝ) / (d : ℝ) ^ 2 := by
  have h1 : (moebius 1 : ℝ) = 1 := by
    rw [moebius_apply_one]
    norm_num
  have h2 : (moebius 2 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 2)]
    norm_num
  have h3 : (moebius 3 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 3)]
    norm_num
  have h4 : (moebius 4 : ℝ) = 0 := by
    have h := moebius_apply_prime_pow (p := 2) (k := 2) (by norm_num) (by norm_num)
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num,
      ite_eq_right (by norm_num : ¬(2 : ℕ) = 1)] at h
    exact_mod_cast h
  have h5 : (moebius 5 : ℝ) = -1 := by
    rw [moebius_apply_prime (by norm_num : Nat.Prime 5)]
    norm_num
  by_cases hD : D ≤ 5
  · interval_cases D
    · rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) by decide, Finset.sum_singleton, h1]
      norm_num
    · rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
        Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)),
        Finset.sum_singleton, h1, h2]
      norm_num
    · rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide,
        Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)),
        Finset.sum_singleton, h1, h2, h3]
      norm_num
    · rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide,
        Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
        Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)),
        Finset.sum_singleton, h1, h2, h3, h4]
      norm_num
    · rw [moebius_first_five]
      norm_num
  · push Not at hD
    obtain ⟨k, rfl⟩ : ∃ k, D = 5 + k := ⟨D - 5, by omega⟩
    have hdisj : Disjoint (Finset.Icc 1 5) (Finset.Icc 6 (5 + k)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_Icc] at hd1 hd2
      omega
    have hunion : Finset.Icc 1 (5 + k) = Finset.Icc 1 5 ∪ Finset.Icc 6 (5 + k) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hunion, Finset.sum_union hdisj]
    have hfirst := moebius_first_five
    have htail := moebius_tail_le (5 + k)
    have hlow : -(1 / 5 : ℝ) ≤
        ∑ d ∈ Finset.Icc 6 (5 + k), (moebius d : ℝ) / (d : ℝ) ^ 2 := by
      have habs := (abs_le.mp htail).1
      linarith
    linarith

end WindowMobiusCount

#print axioms WindowMobiusCount.moebius_first_five
#print axioms WindowMobiusCount.moebius_tail_le
#print axioms WindowMobiusCount.moebius_partial
