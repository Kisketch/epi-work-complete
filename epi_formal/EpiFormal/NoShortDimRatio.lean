import Mathlib
import EpiFormal.Classification

open Real Finset
open scoped BigOperators

namespace NoShortDim

/-!
# Ratio bounds for the paper's Q-sequence and H-sequence (paper2 §7, no-short-dim phase 1).

Paper anchors: `Qsel_rec'` (Classification.lean:59-60), `Qsel_pos` (:68),
`Qsel_double` (:101), base values `Qsel_zero/one/two` (EulerConvergents.lean:63-67).
Target: design doc L01 (Q-ratio + H-ratio bounds) and L05 (`γ > 0`).

Conventions: `Qsel j : ℤ` is the root sequence; all divisions are real.
`H j = ⌊Q_j √j⌋₊`. Constants are explicit but not optimal
(H upper uses `20·j`, same order as the paper's `O(j)`).
-/

/-- `Qsel (j-1) ≤ Qsel j` for `j ≥ 1` (from doubling + base values). -/
theorem Qpred_le (j : ℕ) (hj : 1 ≤ j) : Qsel (j - 1) ≤ Qsel j := by
  rcases j with (_ | k)
  · omega
  · simp only [Nat.add_sub_cancel]
    rcases k with (_ | k')
    · simp [Qsel_zero, Qsel_one]
    · have hd := Classification.Qsel_double (k' + 1) (by omega : 1 ≤ k' + 1)
      have hpos : 0 < Qsel (k' + 1) := Classification.Qsel_pos _
      omega

/-- Cast helper: the three-index recurrence over ℝ. -/
theorem Qsel_rec_real (j : ℕ) (hj : 1 ≤ j) :
    ((Qsel (j + 1) : ℤ) : ℝ) =
      (4 * (j : ℝ) + 2) * ((Qsel j : ℤ) : ℝ) + ((Qsel (j - 1) : ℤ) : ℝ) := by
  have h := Classification.Qsel_rec' j hj
  have hc := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at hc ⊢
  linarith [hc]

/-- Nonnegativity of cast Q-values. -/
theorem Qsel_cast_nonneg (j : ℕ) : (0 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := by
  have h : 0 < Qsel j := Classification.Qsel_pos j
  have h' : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by exact_mod_cast h
  linarith [h']

/-- Q-ratio lower bound: `4j+2 ≤ Q_{j+1}/Q_j` for `j ≥ 1`. -/
theorem Q_ratio_lo (j : ℕ) (hj : 1 ≤ j) :
    (4 * (j : ℝ) + 2) ≤ ((Qsel (j + 1) : ℤ) : ℝ) / ((Qsel j : ℤ) : ℝ) := by
  have hQj : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by
    have h2 : 0 < Qsel j := Classification.Qsel_pos j
    have h3 : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by exact_mod_cast h2
    exact h3
  rw [le_div_iff₀ hQj]
  have hrec := Qsel_rec_real j hj
  have hnn := Qsel_cast_nonneg (j - 1)
  nlinarith [hrec, hnn, hQj]

/-- Q-ratio upper bound: `Q_{j+1}/Q_j ≤ 4j+3` for `j ≥ 1`. -/
theorem Q_ratio_hi (j : ℕ) (hj : 1 ≤ j) :
    ((Qsel (j + 1) : ℤ) : ℝ) / ((Qsel j : ℤ) : ℝ) ≤ (4 * (j : ℝ) + 3) := by
  have hQj : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by
    have h2 : 0 < Qsel j := Classification.Qsel_pos j
    have h3 : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by exact_mod_cast h2
    exact h3
  rw [div_le_iff₀ hQj]
  have hrec := Qsel_rec_real j hj
  have hle : Qsel (j - 1) ≤ Qsel j := Qpred_le j hj
  have hleR : ((Qsel (j - 1) : ℤ) : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := by
    exact_mod_cast hle
  nlinarith [hrec, hleR, hQj]

/-- The paper's `H_j = ⌊Q_j √j⌋`. -/
noncomputable def H (j : ℕ) : ℕ :=
  ⌊((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ)⌋₊

/-- `Q_j √j ≥ 1` for `j ≥ 1`. -/
theorem Qsqrt_ge_one (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) := by
  have hQ : (1 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := by
    have h : 0 < Qsel j := Classification.Qsel_pos j
    have h1 : 1 ≤ Qsel j := h
    exact_mod_cast h1
  have hsq : (1 : ℝ) ≤ Real.sqrt (j : ℝ) := by
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (j : ℝ) := Real.sqrt_le_sqrt hjR
  have hnn : (0 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := Qsel_cast_nonneg j
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) :=
        mul_le_mul hQ hsq (by norm_num) hnn

/-- `H_j ≥ 1` for `j ≥ 1`. -/
theorem H_ge_one (j : ℕ) (hj : 1 ≤ j) : 1 ≤ H j := by
  unfold H
  have h := Qsqrt_ge_one j hj
  have h1 : ((1 : ℕ) : ℝ) ≤ ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) := by
    simpa using h
  exact Nat.le_floor h1

/-- `√j ≤ √(j+1)`. -/
theorem sqrt_mono_succ (j : ℕ) :
    Real.sqrt (j : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) := by
  apply Real.sqrt_le_sqrt
  have hle : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
  simpa using hle

/-- H-ratio lower bound: `3j ≤ H_{j+1}/H_j` for `j ≥ 1`. -/
theorem H_ratio_lo (j : ℕ) (hj : 1 ≤ j) :
    (3 : ℝ) * (j : ℝ) ≤ ((H (j + 1) : ℕ) : ℝ) / ((H j : ℕ) : ℝ) := by
  have hHj : (0 : ℝ) < ((H j : ℕ) : ℝ) := by
    have h := H_ge_one j hj
    have h' : 0 < H j := by omega
    exact_mod_cast h'
  rw [le_div_iff₀ hHj]
  have hnn_sqrt : (0 : ℝ) ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  have hnn_sqrt1 : (0 : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
    Real.sqrt_nonneg _
  have hQnn : (0 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := Qsel_cast_nonneg j
  have hHle : ((H j : ℕ) : ℝ) ≤
      ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) := by
    unfold H
    exact Nat.floor_le (mul_nonneg hQnn hnn_sqrt)
  have hrec := Qsel_rec_real j hj
  have hQjp1 : (4 * (j : ℝ) + 2) * ((Qsel j : ℤ) : ℝ) ≤
      ((Qsel (j + 1) : ℤ) : ℝ) := by
    have hnnm : (0 : ℝ) ≤ ((Qsel (j - 1) : ℤ) : ℝ) :=
      Qsel_cast_nonneg (j - 1)
    linarith [hrec, hnnm]
  have hHlo : (4 * (j : ℝ) + 2) * ((Qsel j : ℤ) : ℝ) *
        Real.sqrt ((j + 1 : ℕ) : ℝ) - 1 ≤ ((H (j + 1) : ℕ) : ℝ) := by
    have hA : (4 * (j : ℝ) + 2) * ((Qsel j : ℤ) : ℝ) *
          Real.sqrt ((j + 1 : ℕ) : ℝ) ≤
        ((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hQjp1 hnn_sqrt1
    have hB : ((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) - 1 ≤
        ((H (j + 1) : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one
        (((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ))
      unfold H
      have hcast : ((((⌊((Qsel (j + 1) : ℤ) : ℝ) *
          Real.sqrt ((j + 1 : ℕ) : ℝ)⌋₊ : ℕ))) : ℝ) =
          (((⌊((Qsel (j + 1) : ℤ) : ℝ) *
            Real.sqrt ((j + 1 : ℕ) : ℝ)⌋₊ : ℕ)) : ℝ) := rfl
      linarith [h]
    linarith [hA, hB]
  have hsqrt_mono := sqrt_mono_succ j
  have hQjj := Qsqrt_ge_one j hj
  have hmid : (3 : ℝ) * (j : ℝ) * (((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ)) ≤
      (4 * (j : ℝ) + 2) * ((Qsel j : ℤ) : ℝ) *
        Real.sqrt ((j + 1 : ℕ) : ℝ) - 1 := by
    have e1 : ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) ≤
        ((Qsel j : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsqrt_mono hQnn
    nlinarith [e1, hQjj, hQnn, hnn_sqrt]
  have h3j : (3 : ℝ) * (j : ℝ) * ((H j : ℕ) : ℝ) ≤
      (3 : ℝ) * (j : ℝ) * (((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ)) := by
    have hj0 : (0 : ℝ) ≤ 3 * (j : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hHle hj0
  linarith [h3j, hmid, hHlo]

/-- Helper: `Q_j √j ≥ 2` for `j ≥ 2`. -/
theorem Qsqrt_ge_two (j : ℕ) (hj : 2 ≤ j) :
    (2 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) := by
  have hj1 : 1 ≤ j - 1 := by omega
  have hd := Classification.Qsel_double (j - 1) hj1
  have hjm : j - 1 + 1 = j := by omega
  rw [hjm] at hd
  have h2 : (2 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := by
    have h1 : (1 : ℤ) ≤ Qsel (j - 1) := Classification.Qsel_pos _
    have h2z : (2 : ℤ) ≤ Qsel j := by omega
    exact_mod_cast h2z
  have hsq : (1 : ℝ) ≤ Real.sqrt (j : ℝ) := by
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by
      have hle : 1 ≤ j := by omega
      exact_mod_cast hle
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt (j : ℝ) := Real.sqrt_le_sqrt hjR
  nlinarith [h2, hsq]

/-- `√(j+1) ≤ 2√j` for `j ≥ 1`. -/
theorem sqrt_succ_le (j : ℕ) (hj : 1 ≤ j) :
    Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
  have hle : ((j + 1 : ℕ) : ℝ) ≤ (2 * Real.sqrt (j : ℝ)) ^ 2 := by
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hsq2 : (Real.sqrt (j : ℝ)) ^ 2 = (j : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hj
    nlinarith [hsq2, hj1]
  have hnn : (0 : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by positivity
  have h := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hnn] at h

/-- H-ratio upper bound: `H_{j+1}/H_j ≤ 20·j` for `j ≥ 3`. -/
theorem H_ratio_hi (j : ℕ) (hj : 3 ≤ j) :
    ((H (j + 1) : ℕ) : ℝ) / ((H j : ℕ) : ℝ) ≤ (20 : ℝ) * (j : ℝ) := by
  have hHj : (0 : ℝ) < ((H j : ℕ) : ℝ) := by
    have h := H_ge_one j (by omega : 1 ≤ j)
    have h' : 0 < H j := by omega
    exact_mod_cast h'
  rw [div_le_iff₀ hHj]
  have hQnn : (0 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) := Qsel_cast_nonneg j
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  have hQjj2 : (2 : ℝ) ≤ ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) :=
    Qsqrt_ge_two j (by omega : 2 ≤ j)
  have hHle : ((H (j + 1) : ℕ) : ℝ) ≤
      ((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) := by
    unfold H
    exact Nat.floor_le (mul_nonneg
      (Qsel_cast_nonneg (j + 1)) (Real.sqrt_nonneg _))
  have hQhi : ((Qsel (j + 1) : ℤ) : ℝ) ≤
      (4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ) := by
    have h := Q_ratio_hi j (by omega : 1 ≤ j)
    have hQj : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by
      have hh : 0 < Qsel j := Classification.Qsel_pos j
      have h3 : (0 : ℝ) < ((Qsel j : ℤ) : ℝ) := by exact_mod_cast hh
      exact h3
    have h2 := (div_le_iff₀ hQj).mp h
    linarith [h2]
  have hsq2 := sqrt_succ_le j (by omega : 1 ≤ j)
  have hHlo : ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) / 2 ≤
      ((H j : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one
      (((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ))
    unfold H
    linarith [h, hQjj2]
  have hstep1 : ((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) ≤
      (4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ) * (2 * Real.sqrt (j : ℝ)) := by
    have hnn1 : (0 : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
      Real.sqrt_nonneg _
    calc ((Qsel (j + 1) : ℤ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ)
          ≤ ((4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ)) *
            Real.sqrt ((j + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hQhi hnn1
        _ ≤ ((4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ)) * (2 * Real.sqrt (j : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hsq2 _
            have hpos : (0 : ℝ) ≤ (4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ) := by
              have hj0 : (0 : ℝ) ≤ 4 * (j : ℝ) + 3 := by positivity
              exact mul_nonneg hj0 hQnn
            exact hpos
  have hstep2 : (4 * (j : ℝ) + 3) * ((Qsel j : ℤ) : ℝ) * (2 * Real.sqrt (j : ℝ)) ≤
      (20 : ℝ) * (j : ℝ) * ((H j : ℕ) : ℝ) := by
    have e1 : ((Qsel j : ℤ) : ℝ) * Real.sqrt (j : ℝ) ≤ 2 * ((H j : ℕ) : ℝ) := by
      linarith [hHlo]
    have hj3 : (3 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hj
    nlinarith [e1, hQnn, hsqnn, hj3]
  linarith [hHle, hstep1, hstep2]

/-- `γ = 1 - η·log φ > 0` from `η < 1/log φ`. -/
theorem gamma_pos (η : ℝ) (_hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) :
    0 < 1 - η * Real.log Real.goldenRatio := by
  have hlog : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  have h : η * Real.log Real.goldenRatio < 1 := by
    have h' := (lt_div_iff₀ hlog).mp hη1
    linarith [h']
  linarith [h]

#print axioms Q_ratio_lo
#print axioms Q_ratio_hi
#print axioms Qsqrt_ge_one
#print axioms H_ge_one
#print axioms H_ratio_lo
#print axioms Qsqrt_ge_two
#print axioms H_ratio_hi
#print axioms gamma_pos
