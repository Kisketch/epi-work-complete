import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ResearchAdvance

/-- Two nonnegative error budgets give a strict small-integer bound. -/
theorem integerBudget_zero (b u v : ℝ) (z : ℤ)
    (hbound : |(z : ℝ)| < b * (u + v)) (hbudget : b * (u + v) ≤ 1) :
    z = 0 := by
  have hh : |(z : ℝ)| < 1 := lt_of_lt_of_le hbound hbudget
  rw [abs_lt] at hh
  have hl : (-1 : ℤ) < z := by exact_mod_cast hh.1
  have hr : z < (1 : ℤ) := by exact_mod_cast hh.2
  omega

/-- At a strip endpoint the exact budget holds without a strict margin in the strip. -/
theorem stripBudget (b j t : ℝ) (hb : 0 < b) (hj : 0 < j)
    (ht₁ : 2 * b ≤ t) (ht₂ : b * t ≤ j) :
    b * (t / (2 * j) + 1 / t) ≤ 1 := by
  have ht : 0 < t := by linarith
  have hleft : b * t / (2 * j) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * j by positivity)).2
    linarith
  have hright : b / t ≤ 1 / 2 := by
    apply (div_le_iff₀ ht).2
    linarith
  calc
    b * (t / (2 * j) + 1 / t) = b * t / (2 * j) + b / t := by ring
    _ ≤ 1 := by linarith

/-- Integer deficits are isolated inside an open unit neighborhood. -/
theorem digitGap (a k : ℤ) (u ε : ℝ) (hε : ε < 1)
    (happrox : |u - (a : ℝ)| + |u - (k : ℝ)| ≤ ε) : a = k := by
  have hplus : (a : ℝ) - (k : ℝ) ≤ |u - (a : ℝ)| + |u - (k : ℝ)| := by
    linarith [neg_abs_le (u - (a : ℝ)), le_abs_self (u - (k : ℝ))]
  have hminus : -(|u - (a : ℝ)| + |u - (k : ℝ)|) ≤ (a : ℝ) - (k : ℝ) := by
    linarith [le_abs_self (u - (a : ℝ)), neg_abs_le (u - (k : ℝ))]
  have hlow : (-1 : ℤ) < a - k :=
    by exact_mod_cast (show (-1 : ℝ) < (a : ℝ) - (k : ℝ) by linarith)
  have hhigh : a - k < (1 : ℤ) :=
    by exact_mod_cast (show (a : ℝ) - (k : ℝ) < (1 : ℝ) by linarith)
  omega

/-- The two congruence obstructions for the discriminant-60 example. -/
theorem normSevenExcluded (u v : ℤ) :
    u ^ 2 - 15 * v ^ 2 ≠ 7 ∧ u ^ 2 - 15 * v ^ 2 ≠ -7 := by
  constructor
  · intro h
    have h' := congrArg (fun t : ℤ => t % 5) h
    change (u ^ 2 - 15 * v ^ 2) % 5 = 7 % 5 at h'
    simp only [pow_two] at h'
    rw [Int.sub_emod, Int.mul_emod u u 5, Int.mul_emod 15 (v * v) 5] at h'
    have hlo : 0 ≤ u % 5 := Int.emod_nonneg _ (by norm_num)
    have hhi : u % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases u % 5 <;> norm_num at h'
  · intro h
    have h' := congrArg (fun t : ℤ => t % 3) h
    change (u ^ 2 - 15 * v ^ 2) % 3 = (-7) % 3 at h'
    simp only [pow_two] at h'
    rw [Int.sub_emod, Int.mul_emod u u 3, Int.mul_emod 15 (v * v) 3] at h'
    have hlo : 0 ≤ u % 3 := Int.emod_nonneg _ (by norm_num)
    have hhi : u % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases u % 3 <;> norm_num at h'

def stripWeight (d c : ℤ) : List Bool → ℤ
  | [] => 0
  | bit :: rest => d * (if bit then 1 else 0) - c + stripWeight d c rest

def markedCount : List Bool → ℤ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + markedCount rest

/-- Cumulative strip displacement is the scaled frequency discrepancy. -/
theorem stripWeight_eq (d c : ℤ) (word : List Bool) :
    stripWeight d c word = d * markedCount word - c * (word.length : ℤ) := by
  induction word with
  | nil => simp [stripWeight, markedCount]
  | cons bit tail ih =>
    simp only [stripWeight, markedCount, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

end ResearchAdvance

#print axioms ResearchAdvance.integerBudget_zero
#print axioms ResearchAdvance.stripBudget
#print axioms ResearchAdvance.digitGap
#print axioms ResearchAdvance.stripWeight_eq
#print axioms ResearchAdvance.normSevenExcluded
