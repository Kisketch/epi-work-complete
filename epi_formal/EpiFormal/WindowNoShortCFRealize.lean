import EpiFormal.NoShortDimCount
import EpiFormal.WindowCFBridge

/-!
# Continued-fraction stopping-rule realization for `thm:no-short-dim` (`WindowNoShortCFRealize`)

Constructs the concrete prelude-of-ones stopped-cylinder tree `cfNoShortTree ε η`
at the paper's actual scale `H_j = ⌊Q_j √j⌋` (`WindowPaperScale.Hpaper`), discharging EVERY
hypothesis of `WindowPaperScale.dimH_ge_gamma_no_short_paper_scale` and
`WindowPaperScale.dimH_ge_one_of_gamma_family` unconditionally, and closing the pointwise
regular continued-fraction identification via `WindowCFBridge.stopped_word_tree_cf_bridge`:

1. **Fibonacci prelude matrix bounds**:
   - `cfProd_replicate_one`: first column of `cfProd (List.replicate ℓ 1)` is `(F_{ℓ+1}, F_ℓ)`.
   - `fib_le_goldenRatio_pow`: `Nat.fib (n + 1) ≤ φ ^ n`.
   - `prelude_den_bounds`: appending `ℓ = ⌈η log j⌉` ones multiplies the denominator by at most
     `φ ^ (ℓ + 1) ≤ φ ^ 2 * j ^ (η log φ)` while keeping `0 < v' < u'`.
2. **Concrete CF tree `cfNoShortTree ε η` (`j0 = j0NoShort η`)**:
   - Maintains `StageInv ε j w` using `NoShortDim.boxS` (`[0.34 R, 0.35 R] × [0.12 R, 0.13 R]`)
     and `NoShortDim.copCountS`.
   - `dimH_ge_gamma_cfNoShortTree`: unconditional
     `ENNReal.ofReal (1 - η * log φ) ≤ dimH (cantorSet (cfNoShortTree ε η) (j0NoShort η))`.
3. **End-to-end pointwise regular CF theorems (`thm:no-short-dim`)**:
   - `mem_cantorSet_cfNoShortTree_cf`: every `x ∈ cantorSet (cfNoShortTree ε η) (j0NoShort η)`
     is irrational in `(0, 1)` with `((cfStopIdx x j) % 2 == 1) = ε j` and
     `η * log j ≤ cfStopIdx x (j + 1) - cfStopIdx x j` for all `j ≥ j0NoShort η`.
   - `dimH_ge_gamma_noShortSet`: `ENNReal.ofReal (1 - η * log φ) ≤ dimH (noShortSet ε η)`.
   - `dimH_ge_one_divWindowSet`: `(1 : ℝ≥0∞) ≤ dimH (divWindowSet ε)` for prescribed parity
     and `r_j(x) → ∞`.

Only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowNoShortCFRealize

open Matrix Set Filter Finset ENNReal Metric Real Cylinder WindowCFRealize WindowCFBridge
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Fibonacci prelude matrix & golden-ratio growth bounds -/

theorem posDigits_replicate_one (ℓ : ℕ) : PosDigits (List.replicate ℓ 1) := by
  intro a ha
  rw [List.mem_replicate] at ha
  omega

/-- First column of `cfProd (List.replicate ℓ 1)` is `(F_{ℓ+1}, F_ℓ)`. -/
theorem cfProd_replicate_one (ℓ : ℕ) :
    (cfProd (List.replicate ℓ 1)) 0 0 = (Nat.fib (ℓ + 1) : ℤ) ∧
    (cfProd (List.replicate ℓ 1)) 1 0 = (Nat.fib ℓ : ℤ) := by
  induction ℓ with
  | zero => simp [cfProd, Nat.fib]
  | succ ℓ ih =>
    rw [List.replicate_succ, cfProd, Matrix.mul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [cfMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_one, one_mul, zero_mul, add_zero]
    rw [ih.1, ih.2]
    refine ⟨?_, rfl⟩
    rw [Nat.fib_add_two]
    push_cast
    ring

/-- Elementary bound `Nat.fib (n + 1) ≤ φ ^ n` for all `n : ℕ`. -/
theorem fib_le_goldenRatio_pow (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) ≤ Real.goldenRatio ^ n := by
  have hφsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := by
    unfold Real.goldenRatio
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [Nat.fib]
    | 1 => simpa [Nat.fib] using hφ1
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      have hfib : (Nat.fib (m + 3) : ℝ) = (Nat.fib (m + 1) : ℝ) + (Nat.fib (m + 2) : ℝ) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have hpow : Real.goldenRatio ^ (m + 2) =
          Real.goldenRatio ^ m + Real.goldenRatio ^ (m + 1) := by
        have : Real.goldenRatio ^ (m + 2) = Real.goldenRatio ^ m * Real.goldenRatio ^ 2 := by
          rw [pow_add]
        rw [this, hφsq, pow_succ]
        ring
      linarith

/-- Appending `ℓ` ones to a word with `0 < v < u` yields `u' = F_{ℓ+1} u + F_ℓ v ≤ φ^{ℓ+1} u`
    and preserves `0 < v' < u'`. -/
theorem prelude_den_bounds {w : List ℕ} (ℓ : ℕ)
    (hu_pos : 0 < (cfProd (0 :: w)) 1 0)
    (hv_pos : 0 < (cfProd (0 :: w)) 1 1)
    (hv_lt : (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0) :
    let w' := w ++ List.replicate ℓ 1
    (cfProd (0 :: w)) 1 0 ≤ (cfProd (0 :: w')) 1 0 ∧
    ((cfProd (0 :: w')) 1 0 : ℝ) ≤
      Real.goldenRatio ^ (ℓ + 1) * ((cfProd (0 :: w)) 1 0 : ℝ) ∧
    0 < (cfProd (0 :: w')) 1 1 ∧
    (cfProd (0 :: w')) 1 1 < (cfProd (0 :: w')) 1 0 := by
  intro w'
  have hcons : (0 :: w') = (0 :: w) ++ List.replicate ℓ 1 := rfl
  have hu'_eq : (cfProd (0 :: w')) 1 0 =
      (cfProd (0 :: w)) 1 0 * (Nat.fib (ℓ + 1) : ℤ) +
      (cfProd (0 :: w)) 1 1 * (Nat.fib ℓ : ℤ) := by
    rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two,
      (cfProd_replicate_one ℓ).1, (cfProd_replicate_one ℓ).2]
  have hfib1 : (1 : ℤ) ≤ (Nat.fib (ℓ + 1) : ℤ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos ℓ)
  have hfib0 : (0 : ℤ) ≤ (Nat.fib ℓ : ℤ) := by exact_mod_cast Nat.zero_le _
  have hu_le : (cfProd (0 :: w)) 1 0 ≤ (cfProd (0 :: w')) 1 0 := by
    rw [hu'_eq]; nlinarith
  have hu'_le_fib : (cfProd (0 :: w')) 1 0 ≤ (Nat.fib (ℓ + 2) : ℤ) * (cfProd (0 :: w)) 1 0 := by
    rw [hu'_eq, Nat.fib_add_two]
    push_cast
    nlinarith
  have hu'_le_phi : ((cfProd (0 :: w')) 1 0 : ℝ) ≤
      Real.goldenRatio ^ (ℓ + 1) * ((cfProd (0 :: w)) 1 0 : ℝ) := by
    have h1 : ((cfProd (0 :: w')) 1 0 : ℝ) ≤
        (Nat.fib (ℓ + 2) : ℝ) * ((cfProd (0 :: w)) 1 0 : ℝ) := by exact_mod_cast hu'_le_fib
    have h2 : (Nat.fib (ℓ + 2) : ℝ) ≤ Real.goldenRatio ^ (ℓ + 1) := fib_le_goldenRatio_pow (ℓ + 1)
    have huR : (0 : ℝ) ≤ ((cfProd (0 :: w)) 1 0 : ℝ) := by exact_mod_cast le_of_lt hu_pos
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 huR)
  have hpen : 0 < (cfProd (0 :: w')) 1 1 ∧ (cfProd (0 :: w')) 1 1 < (cfProd (0 :: w')) 1 0 := by
    cases ℓ with
    | zero => simpa [w'] using ⟨hv_pos, hv_lt⟩
    | succ m =>
      exact append_penult_bounds hu_pos hv_pos (posDigits_replicate_one (m + 1)) (by simp)
  exact ⟨hu_le, hu'_le_phi, hpen.1, hpen.2⟩

/-! ### Part 2: Generalized stage-`j0` initializer & prelude-of-ones CF tree -/

/-- Initial stopped word at any stage `j0 ≥ 6` matching parity `ε j0`. -/
noncomputable def initWordAt (ε : ℕ → Bool) (j0 : ℕ) : List ℕ :=
  let d : ℕ := Nat.floor (WindowPaperScale.Hpaper j0 / 2)
  if ε j0 then [d, 4] else [d - 1, 1, 4]

theorem initWordAt_inv (ε : ℕ → Bool) {j0 : ℕ} (hj0 : 6 ≤ j0) :
    StageInv ε j0 (initWordAt ε j0) := by
  have hH_big : (100 : ℝ) ≤ WindowPaperScale.Hpaper j0 := by
    have h3 := WindowPaperScale.Hpaper_ge_three_pow (j := j0) (by omega)
    have hpow : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ (j0 - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h243 : (100 : ℝ) ≤ (3 : ℝ) ^ 5 := by norm_num
    linarith
  set H0 : ℝ := WindowPaperScale.Hpaper j0
  set d : ℕ := Nat.floor (H0 / 2)
  have hd_le : (d : ℝ) ≤ H0 / 2 := Nat.floor_le (by linarith)
  have hd_gt : H0 / 2 - 1 < (d : ℝ) := by
    have := Nat.lt_floor_add_one (H0 / 2); linarith
  have hd_ge : 49 ≤ d := by
    have : (49 : ℝ) ≤ (d : ℝ) := by linarith
    exact_mod_cast this
  have hdZ : (49 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd_ge
  unfold initWordAt
  change StageInv ε j0 (if ε j0 then [d, 4] else [d - 1, 1, 4])
  split_ifs with hε
  · have hM : cfProd (0 :: [d, 4]) = !![(4 : ℤ), 1; 4 * (d : ℤ) + 1, (d : ℤ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [cfProd, cfMat, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
    refine ⟨?_, by simp, by simp [hε], ?_, ?_, ?_, ?_⟩
    · simp only [PosDigits, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl) <;> omega
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp
  · have hM : cfProd (0 :: [d - 1, 1, 4]) = !![(5 : ℤ), 1; 5 * (d : ℤ) - 1, (d : ℤ)] := by
      have hd1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [cfProd, cfMat, Matrix.mul_apply, Fin.sum_univ_two, hd1]; try ring)
    refine ⟨?_, by simp, by simp [hε], ?_, ?_, ?_, ?_⟩
    · simp only [PosDigits, List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith
    · rw [hM]; simp; linarith

/-- Explicit starting stage `j0NoShort η ≥ 6` for `thm:no-short-dim`. -/
noncomputable def j0NoShort (η : ℝ) : ℕ :=
  let γ : ℝ := 1 - η * Real.log Real.goldenRatio
  let cR : ℝ := 6 / (5 * Real.goldenRatio ^ 2)
  max 6 (Nat.ceil (((10 ^ 6 : ℝ) / cR) ^ (1 / γ)) + 1)

theorem j0NoShort_ge_six (η : ℝ) : 6 ≤ j0NoShort η := le_max_left _ _

theorem j0NoShort_scale {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / Real.log Real.goldenRatio) :
    (10 ^ 6 : ℝ) ≤
      (6 / (5 * Real.goldenRatio ^ 2)) *
        (j0NoShort η : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by
  set γ : ℝ := 1 - η * Real.log Real.goldenRatio
  have hγpos : 0 < γ := NoShortDim.gamma_pos η hη0 hη1
  have hφpos : 0 < Real.goldenRatio := lt_trans zero_lt_one Real.one_lt_goldenRatio
  set cR : ℝ := 6 / (5 * Real.goldenRatio ^ 2)
  have hcRpos : 0 < cR := by positivity
  set M : ℝ := ((10 ^ 6 : ℝ) / cR) ^ (1 / γ)
  have hjM : M ≤ (j0NoShort η : ℝ) := by
    have h1 : Nat.ceil M ≤ j0NoShort η := le_trans (Nat.le_succ _) (le_max_right _ _)
    have h2 : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have h3 : (Nat.ceil M : ℝ) ≤ (j0NoShort η : ℝ) := by exact_mod_cast h1
    linarith
  have hMnn : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  have hrpow : M ^ γ ≤ (j0NoShort η : ℝ) ^ γ := Real.rpow_le_rpow hMnn hjM (le_of_lt hγpos)
  have hMγ : M ^ γ = (10 ^ 6 : ℝ) / cR := by
    dsimp only [M]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hγpos), Real.rpow_one]
  rw [hMγ] at hrpow
  have hmul := mul_le_mul_of_nonneg_left hrpow (le_of_lt hcRpos)
  rwa [mul_div_cancel₀ _ (ne_of_gt hcRpos)] at hmul

/-- Prelude length `ℓ_j = ⌈η log j⌉` of ones at stage `j`. -/
noncomputable def preludeLen (η : ℝ) (j : ℕ) : ℕ :=
  Nat.ceil (η * Real.log (j : ℝ))

/-- Word after appending the prelude of `preludeLen η j` ones. -/
noncomputable def preludeWord (η : ℝ) (j : ℕ) (w : List ℕ) : List ℕ :=
  w ++ List.replicate (preludeLen η j) 1

/-- Remaining parent-dependent scale `R'(j, w) = Hpaper (j + 1) / u'` (Paper 2 L2770). -/
noncomputable def noShortScale (η : ℝ) (j : ℕ) (w : List ℕ) : ℝ :=
  WindowPaperScale.Hpaper (j + 1) / ((cfProd (0 :: preludeWord η j w)) 1 0 : ℝ)

/-- Child word from parent `w`, prelude of ones, coprime pair `(m, n) ∈ boxS`, and `[4]`. -/
noncomputable def makeNoShortChild (ε : ℕ → Bool) (η : ℝ) (j : ℕ) (w : List ℕ)
    (p : ℕ × ℕ) : List ℕ :=
  let w' := preludeWord η j w
  w' ++ chooseParityCF p.1 p.2 (targetTailParity ε j w') ++ [4]

/-- Finite set of stopped child words of `w` at stage `j → j + 1`. -/
noncomputable def noShortWordChild (ε : ℕ → Bool) (η : ℝ) (j : ℕ) (w : List ℕ) : Finset (List ℕ) :=
  let R := noShortScale η j w
  ((NoShortDim.boxS R).filter (fun p => Nat.gcd p.1 p.2 = 1)).image (makeNoShortChild ε η j w)

/-- Stage-`j` stopped words for `thm:no-short-dim`. -/
noncomputable def noShortWordAtomsAux (ε : ℕ → Bool) (η : ℝ) : ℕ → Finset (List ℕ)
  | 0 => {initWordAt ε (j0NoShort η)}
  | d + 1 => (noShortWordAtomsAux ε η d).biUnion (noShortWordChild ε η (j0NoShort η + d))

noncomputable def noShortWordAtoms (ε : ℕ → Bool) (η : ℝ) (j : ℕ) : Finset (List ℕ) :=
  if j0NoShort η ≤ j then noShortWordAtomsAux ε η (j - j0NoShort η) else ∅

theorem noShortWordAtoms_base (ε : ℕ → Bool) (η : ℝ) :
    noShortWordAtoms ε η (j0NoShort η) = {initWordAt ε (j0NoShort η)} := by
  simp [noShortWordAtoms, noShortWordAtomsAux]

theorem noShortWordAtoms_succ (ε : ℕ → Bool) (η : ℝ) {j : ℕ} (hj : j0NoShort η ≤ j) :
    noShortWordAtoms ε η (j + 1) =
      (noShortWordAtoms ε η j).biUnion (noShortWordChild ε η j) := by
  have hj1 : j0NoShort η ≤ j + 1 := by omega
  have hsub : j + 1 - j0NoShort η = (j - j0NoShort η) + 1 := by omega
  have hadd : j0NoShort η + (j - j0NoShort η) = j := by omega
  simp only [noShortWordAtoms, hj, hj1, ↓reduceIte, hsub, noShortWordAtomsAux, hadd]

/-- Paper 2 L2771 scale lower bound:
    `noShortScale η j w ≥ (2 / (5 φ²)) * Rpaper j * j^(-η log φ)`. -/
theorem noShortScale_ge {ε : ℕ → Bool} {η : ℝ} (hη0 : 0 < η) {j : ℕ} (hj : 6 ≤ j)
    {w : List ℕ} (hw : StageInv ε j w) :
    (2 / (5 * Real.goldenRatio ^ 2)) * WindowPaperScale.Rpaper j *
      (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤ noShortScale η j w := by
  have hHj := WindowPaperScale.Hpaper_pos j
  have hHj1 := WindowPaperScale.Hpaper_pos (j + 1)
  have hφpos : 0 < Real.goldenRatio := lt_trans zero_lt_one Real.one_lt_goldenRatio
  have hφ1 : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
  have hu_posR : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by linarith [hw.2.2.2.1]
  have hu_posZ : 0 < (cfProd (0 :: w)) 1 0 := by exact_mod_cast hu_posR
  have hv_posZ : 0 < (cfProd (0 :: w)) 1 1 := hw.2.2.2.2.2.1
  have hv_ltZ : (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0 := by
    linarith [hw.2.2.2.2.2.1, hw.2.2.2.2.2.2]
  obtain ⟨hu_le, hu'_phi, _, _⟩ := prelude_den_bounds (preludeLen η j) hu_posZ hv_posZ hv_ltZ
  have hu'_posR : (0 : ℝ) < ((cfProd (0 :: preludeWord η j w)) 1 0 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hu_posZ hu_le
  have hlogj_nn : 0 ≤ η * Real.log (j : ℝ) := mul_nonneg (le_of_lt hη0) (Real.log_nonneg hj1)
  have hceil_lt : (preludeLen η j : ℝ) < η * Real.log (j : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlogj_nn
  have hphi_bound : Real.goldenRatio ^ (preludeLen η j + 1) ≤
      Real.goldenRatio ^ 2 * (j : ℝ) ^ (η * Real.log Real.goldenRatio) := by
    have hpow_eq : Real.goldenRatio ^ (preludeLen η j + 1) =
        Real.goldenRatio ^ ((preludeLen η j + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    rw [hpow_eq]
    have hexp_le : ((preludeLen η j + 1 : ℕ) : ℝ) ≤ 2 + η * Real.log (j : ℝ) := by
      push_cast; linarith
    have hr1 : Real.goldenRatio ^ ((preludeLen η j + 1 : ℕ) : ℝ) ≤
        Real.goldenRatio ^ (2 + η * Real.log (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hφ1 hexp_le
    have hr2 : Real.goldenRatio ^ (2 + η * Real.log (j : ℝ)) =
        Real.goldenRatio ^ 2 * (j : ℝ) ^ (η * Real.log Real.goldenRatio) := by
      rw [Real.rpow_add hφpos, Real.rpow_two, Real.rpow_def_of_pos hφpos,
        Real.rpow_def_of_pos hjpos]
      congr 1; congr 1; ring
    linarith
  have hu'_ub : ((cfProd (0 :: preludeWord η j w)) 1 0 : ℝ) ≤
      Real.goldenRatio ^ 2 * (j : ℝ) ^ (η * Real.log Real.goldenRatio) *
        ((5 / 2 : ℝ) * WindowPaperScale.Hpaper j) := by
    have h1 : Real.goldenRatio ^ (preludeLen η j + 1) * ((cfProd (0 :: w)) 1 0 : ℝ) ≤
        (Real.goldenRatio ^ 2 * (j : ℝ) ^ (η * Real.log Real.goldenRatio)) *
          ((5 / 2 : ℝ) * WindowPaperScale.Hpaper j) :=
      mul_le_mul hphi_bound hw.2.2.2.2.1 (le_of_lt hu_posR) (by positivity)
    exact le_trans hu'_phi h1
  unfold noShortScale WindowPaperScale.Rpaper
  have hdiv := div_le_div_of_nonneg_left (le_of_lt hHj1) hu'_posR hu'_ub
  have hrneg : (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) =
      ((j : ℝ) ^ (η * Real.log Real.goldenRatio))⁻¹ := Real.rpow_neg (le_of_lt hjpos) _
  have hrpos : 0 < (j : ℝ) ^ (η * Real.log Real.goldenRatio) := Real.rpow_pos_of_pos hjpos _
  have heq : WindowPaperScale.Hpaper (j + 1) /
      (Real.goldenRatio ^ 2 * (j : ℝ) ^ (η * Real.log Real.goldenRatio) *
        (5 / 2 * WindowPaperScale.Hpaper j)) =
      2 / (5 * Real.goldenRatio ^ 2) *
        (WindowPaperScale.Hpaper (j + 1) / WindowPaperScale.Hpaper j) *
        (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by
    rw [hrneg]
    have h1 : Real.goldenRatio ^ 2 ≠ 0 := by positivity
    have h2 : (j : ℝ) ^ (η * Real.log Real.goldenRatio) ≠ 0 := ne_of_gt hrpos
    have h3 : WindowPaperScale.Hpaper j ≠ 0 := ne_of_gt hHj
    field_simp
  linarith

/-- For `j ≥ j0NoShort η`, `noShortScale η j w ≥ 10^6`. -/
theorem noShortScale_ge_ten_pow_six {ε : ℕ → Bool} {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) {j : ℕ} (hj : j0NoShort η ≤ j)
    {w : List ℕ} (hw : StageInv ε j w) :
    (10 ^ 6 : ℝ) ≤ noShortScale η j w := by
  have hj6 : 6 ≤ j := le_trans (j0NoShort_ge_six η) hj
  have hipos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hφpos : 0 < Real.goldenRatio := lt_trans zero_lt_one Real.one_lt_goldenRatio
  have hγpos : 0 < 1 - η * Real.log Real.goldenRatio := NoShortDim.gamma_pos η hη0 hη1
  have hlo := noShortScale_ge hη0 hj6 hw
  have hrat := WindowPaperScale.Rpaper_ge_three_mul (by omega : 1 ≤ j)
  have hcoeff : 0 ≤ (2 / (5 * Real.goldenRatio ^ 2)) *
      (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by positivity
  have hmul : (2 / (5 * Real.goldenRatio ^ 2)) * (3 * (j : ℝ)) *
      (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤ noShortScale η j w := by
    have h2 := mul_le_mul_of_nonneg_right hrat hcoeff
    linarith
  have hrp : (j : ℝ) * (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) =
      (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by
    calc (j : ℝ) * (j : ℝ) ^ (-(η * Real.log Real.goldenRatio))
        = (j : ℝ) ^ (1 : ℝ) * (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by rw [Real.rpow_one]
      _ = (j : ℝ) ^ (1 + -(η * Real.log Real.goldenRatio)) := (Real.rpow_add hipos _ _).symm
      _ = (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by rw [sub_eq_add_neg]
  have hstep : (6 / (5 * Real.goldenRatio ^ 2)) * (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) ≤
      noShortScale η j w := by
    have heq : (6 / (5 * Real.goldenRatio ^ 2)) * (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) =
        (2 / (5 * Real.goldenRatio ^ 2)) * (3 * (j : ℝ)) *
        (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by rw [← hrp]; ring
    linarith
  have hmono : (j0NoShort η : ℝ) ^ (1 - η * Real.log Real.goldenRatio) ≤
      (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hj) (le_of_lt hγpos)
  have hscale := j0NoShort_scale hη0 hη1
  have hcR : 0 < 6 / (5 * Real.goldenRatio ^ 2) := by positivity
  have hmul2 := mul_le_mul_of_nonneg_left hmono (le_of_lt hcR)
  exact le_trans hscale (le_trans hmul2 hstep)

/-- Helper: every `(m, n) ∈ NoShortDim.boxS R` for `R ≥ 10^6` satisfies `1 ≤ n < m`. -/
private theorem boxS_lt {R : ℝ} (hR : (10 ^ 6 : ℝ) ≤ R) {p : ℕ × ℕ}
    (hp : p ∈ NoShortDim.boxS R) : 1 ≤ p.2 ∧ p.2 < p.1 := by
  have hn1 := (NoShortDim.boxS_mem_pos R p hp).2
  obtain ⟨hm, hn⟩ := (NoShortDim.boxS_mem_iff R p).mp hp
  simp only [Finset.mem_Icc] at hm hn
  have h1 : ((NoShortDim.MloS R : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hm.1
  have h2 : 0.34 * R < ((Nat.floor (0.34 * R) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : (p.2 : ℝ) ≤ ((NoShortDim.NhiS R : ℕ) : ℝ) := by exact_mod_cast hn.2
  have h4 : ((Nat.floor (0.13 * R) : ℕ) : ℝ) ≤ 0.13 * R := Nat.floor_le (by linarith)
  simp only [NoShortDim.MloS, NoShortDim.NhiS, Nat.cast_add, Nat.cast_one] at h1 h3
  exact ⟨hn1, by exact_mod_cast (by linarith : (p.2 : ℝ) < (p.1 : ℝ))⟩

/-- Core transition step for `thm:no-short-dim` (Paper 2 L2779–L2816). -/
theorem noShortChild_transition {ε : ℕ → Bool} {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) {j : ℕ} (hj : j0NoShort η ≤ j)
    {w : List ℕ} (hw : StageInv ε j w) {p : ℕ × ℕ}
    (hp_box : p ∈ NoShortDim.boxS (noShortScale η j w)) (hgcd : Nat.gcd p.1 p.2 = 1) :
    let w' := preludeWord η j w
    let tail := chooseParityCF p.1 p.2 (targetTailParity ε j w')
    ((cfProd (0 :: (w' ++ tail))) 1 0 : ℝ) < (1 / 2 : ℝ) * WindowPaperScale.Hpaper (j + 1) ∧
    StageInv ε (j + 1) (makeNoShortChild ε η j w p) := by
  set w' := preludeWord η j w
  set R : ℝ := noShortScale η j w
  set T : ℝ := WindowPaperScale.Hpaper (j + 1)
  have hTpos : 0 < T := WindowPaperScale.Hpaper_pos (j + 1)
  have hR_lo : (10 ^ 6 : ℝ) ≤ R := noShortScale_ge_ten_pow_six hη0 hη1 hj hw
  obtain ⟨hm_mem, hn_mem⟩ := (NoShortDim.boxS_mem_iff R p).mp hp_box
  simp only [Finset.mem_Icc] at hm_mem hn_mem
  have hm_gt : 0.34 * R < (p.1 : ℝ) := by
    have h1 : ((NoShortDim.MloS R : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hm_mem.1
    have h2 : 0.34 * R < ((Nat.floor (0.34 * R) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [NoShortDim.MloS, Nat.cast_add, Nat.cast_one] at h1
    linarith
  have hm_le : (p.1 : ℝ) ≤ 0.35 * R := by
    have h1 : (p.1 : ℝ) ≤ ((NoShortDim.MhiS R : ℕ) : ℝ) := by exact_mod_cast hm_mem.2
    have h2 : ((Nat.floor (0.35 * R) : ℕ) : ℝ) ≤ 0.35 * R := Nat.floor_le (by linarith)
    simp only [NoShortDim.MhiS] at h1
    linarith
  have hn_gt : 0.12 * R < (p.2 : ℝ) := by
    have h1 : ((NoShortDim.NloS R : ℕ) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hn_mem.1
    have h2 : 0.12 * R < ((Nat.floor (0.12 * R) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    simp only [NoShortDim.NloS, Nat.cast_add, Nat.cast_one] at h1
    linarith
  have hn_le : (p.2 : ℝ) ≤ 0.13 * R := by
    have h1 : (p.2 : ℝ) ≤ ((NoShortDim.NhiS R : ℕ) : ℝ) := by exact_mod_cast hn_mem.2
    have h2 : ((Nat.floor (0.13 * R) : ℕ) : ℝ) ≤ 0.13 * R := Nat.floor_le (by linarith)
    simp only [NoShortDim.NhiS] at h1
    linarith
  obtain ⟨hn1, hnm⟩ := boxS_lt hR_lo hp_box
  set tail := chooseParityCF p.1 p.2 (targetTailParity ε j w')
  obtain ⟨htail_pos, htail_ne, hcol0, hcol1, htail_par⟩ :=
    chooseParityCF_props hn1 hnm hgcd (targetTailParity ε j w')
  have hu_posR : (0 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by
    have := WindowPaperScale.Hpaper_pos j; linarith [hw.2.2.2.1]
  have hu_posZ : 0 < (cfProd (0 :: w)) 1 0 := by exact_mod_cast hu_posR
  have hv_posZ : 0 < (cfProd (0 :: w)) 1 1 := hw.2.2.2.2.2.1
  have hv_ltZ : (cfProd (0 :: w)) 1 1 < (cfProd (0 :: w)) 1 0 := by
    linarith [hw.2.2.2.2.2.1, hw.2.2.2.2.2.2]
  obtain ⟨hu_le, _, hv'_posZ, hv'_ltZ⟩ := prelude_den_bounds (preludeLen η j) hu_posZ hv_posZ hv_ltZ
  set u' : ℤ := (cfProd (0 :: w')) 1 0
  set v' : ℤ := (cfProd (0 :: w')) 1 1
  have hu'_posZ : 0 < u' := lt_of_lt_of_le hu_posZ hu_le
  have hu'_posR : (0 : ℝ) < (u' : ℝ) := by exact_mod_cast hu'_posZ
  have hv'_posR : (0 : ℝ) < (v' : ℝ) := by exact_mod_cast hv'_posZ
  have hv'_ltR : (v' : ℝ) < (u' : ℝ) := by exact_mod_cast hv'_ltZ
  have hRu' : R * (u' : ℝ) = T := div_mul_cancel₀ T (ne_of_gt hu'_posR)
  set t : ℤ := (cfProd (0 :: (w' ++ tail))) 1 0
  set t' : ℤ := (cfProd (0 :: (w' ++ tail))) 1 1
  have ht_eq : (t : ℝ) = (p.1 : ℝ) * (u' : ℝ) + (p.2 : ℝ) * (v' : ℝ) := by
    have hcons : (0 :: (w' ++ tail)) = (0 :: w') ++ tail := rfl
    have hZ : t = u' * (cfProd tail) 0 0 + v' * (cfProd tail) 1 0 := by
      dsimp only [t, u', v']
      rw [hcons, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hZ, hcol0, hcol1]
    push_cast; ring
  have ht_lo : (1 / 3 : ℝ) * T < (t : ℝ) := by nlinarith
  have ht_hi : (t : ℝ) < (1 / 2 : ℝ) * T := by nlinarith
  obtain ⟨ht'_pos, ht'_lt⟩ := append_penult_bounds hu'_posZ hv'_posZ htail_pos htail_ne
  have ht'_posR : (0 : ℝ) < (t' : ℝ) := by exact_mod_cast ht'_pos
  have ht'_ltR : (t' : ℝ) < (t : ℝ) := by exact_mod_cast ht'_lt
  have hcons4 : (0 :: makeNoShortChild ε η j w p) = (0 :: (w' ++ tail)) ++ [4] := by
    simp [makeNoShortChild, w', tail]
  have hu_new : (cfProd (0 :: makeNoShortChild ε η j w p)) 1 0 = 4 * t + t' := by
    rw [hcons4, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, t, t']; ring
  have hv_new : (cfProd (0 :: makeNoShortChild ε η j w p)) 1 1 = t := by
    rw [hcons4, cfProd_append, Matrix.mul_apply, Fin.sum_univ_two]
    simp [cfProd, cfMat, t]
  have hw'_pos : PosDigits w' := posDigits_append.mpr ⟨hw.1, posDigits_replicate_one _⟩
  refine ⟨ht_hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold makeNoShortChild
    exact posDigits_append.mpr ⟨posDigits_append.mpr ⟨hw'_pos, htail_pos⟩,
      posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
  · unfold makeNoShortChild
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil 4 [])
  · unfold makeNoShortChild
    have hlen : (w' ++ tail ++ [4]).length - 1 = w'.length + tail.length := by simp
    rw [hlen]
    have hpar_eq : ((w'.length + tail.length) % 2 == 1) =
        xor (w'.length % 2 == 1) (tail.length % 2 == 1) := by
      have : (w'.length + tail.length) % 2 = (w'.length % 2 + tail.length % 2) % 2 :=
        Nat.add_mod _ _ _
      rw [this]
      rcases Nat.mod_two_eq_zero_or_one w'.length with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one tail.length with h2 | h2 <;>
        simp [h1, h2]
    rw [hpar_eq, htail_par, targetTailParity]
    cases (w'.length % 2 == 1) <;> cases (ε (j + 1)) <;> rfl
  · rw [hu_new]; push_cast; linarith
  · rw [hu_new]; push_cast; linarith
  · rw [hv_new]; exact lt_trans ht'_pos ht'_lt
  · rw [hu_new, hv_new]; linarith [ht'_pos]

/-- Distinct coprime pairs in `NoShortDim.boxS (noShortScale η j w)` produce
    prefix-incomparable child words. -/
theorem noShortChild_incomparable {ε : ℕ → Bool} {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) {j : ℕ} (hj : j0NoShort η ≤ j)
    {w : List ℕ} (hw : StageInv ε j w) {p₁ p₂ : ℕ × ℕ}
    (hp₁ : p₁ ∈ NoShortDim.boxS (noShortScale η j w)) (hg₁ : Nat.gcd p₁.1 p₁.2 = 1)
    (hp₂ : p₂ ∈ NoShortDim.boxS (noShortScale η j w)) (hg₂ : Nat.gcd p₂.1 p₂.2 = 1)
    (hne : p₁ ≠ p₂) :
    ¬ (makeNoShortChild ε η j w p₁ <+: makeNoShortChild ε η j w p₂) := by
  intro hpref
  set w' := preludeWord η j w
  obtain ⟨_, hinv₁⟩ := noShortChild_transition hη0 hη1 hj hw hp₁ hg₁
  obtain ⟨ht₂_hi, _⟩ := noShortChild_transition hη0 hη1 hj hw hp₂ hg₂
  set t₁ := chooseParityCF p₁.1 p₁.2 (targetTailParity ε j w')
  set t₂ := chooseParityCF p₂.1 p₂.2 (targetTailParity ε j w')
  have hTpos := WindowPaperScale.Hpaper_pos (j + 1)
  have hR_lo : (10 ^ 6 : ℝ) ≤ noShortScale η j w := noShortScale_ge_ten_pow_six hη0 hη1 hj hw
  have h1_ge : (4 / 3 : ℝ) * WindowPaperScale.Hpaper (j + 1) ≤
      ((cfProd (0 :: makeNoShortChild ε η j w p₁)) 1 0 : ℝ) := hinv₁.2.2.2.1
  by_cases heq : makeNoShortChild ε η j w p₁ = makeNoShortChild ε η j w p₂
  · unfold makeNoShortChild at heq
    have h1 := List.append_inj_left' heq rfl
    have ht_eq : t₁ = t₂ := List.append_cancel_left h1
    obtain ⟨hn1, hlt1⟩ := boxS_lt hR_lo hp₁
    obtain ⟨hn2, hlt2⟩ := boxS_lt hR_lo hp₂
    have hc1 := chooseParityCF_props hn1 hlt1 hg₁ (targetTailParity ε j w')
    have hc2 := chooseParityCF_props hn2 hlt2 hg₂ (targetTailParity ε j w')
    dsimp only [t₁, t₂] at ht_eq
    have hm_eq : (p₁.1 : ℤ) = (p₂.1 : ℤ) := by rw [← hc1.2.2.1, ← hc2.2.2.1, ht_eq]
    have hn_eq : (p₁.2 : ℤ) = (p₂.2 : ℤ) := by rw [← hc1.2.2.2.1, ← hc2.2.2.2.1, ht_eq]
    exact hne (Prod.ext (by exact_mod_cast hm_eq) (by exact_mod_cast hn_eq))
  · obtain ⟨suf, hsuf⟩ := hpref
    have hsuf_ne : suf ≠ [] := by intro h; apply heq; simpa [h] using hsuf
    have hpre_t2 : makeNoShortChild ε η j w p₁ <+: w' ++ t₂ := by
      rcases List.eq_nil_or_concat suf with rfl | ⟨init, last, hlast⟩
      · exact absurd rfl hsuf_ne
      · rw [hlast, List.concat_eq_append, ← List.append_assoc] at hsuf
        have hsuf' : (makeNoShortChild ε η j w p₁ ++ init) ++ [last] = (w' ++ t₂) ++ [4] := hsuf
        exact ⟨init, List.append_inj_left' hsuf' rfl⟩
    obtain ⟨suf', hsuf'⟩ := hpre_t2
    have hsuf'_pos : PosDigits suf' := by
      obtain ⟨hn2, hlt2⟩ := boxS_lt hR_lo hp₂
      have hpos_wt2 : PosDigits (w' ++ t₂) := posDigits_append.mpr
        ⟨posDigits_append.mpr ⟨hw.1, posDigits_replicate_one _⟩,
          (chooseParityCF_props hn2 hlt2 hg₂ (targetTailParity ε j w')).1⟩
      rw [← hsuf'] at hpos_wt2
      exact (posDigits_append.mp hpos_wt2).2
    have hmono : (cfProd (0 :: makeNoShortChild ε η j w p₁)) 1 0 ≤
        (cfProd (0 :: (w' ++ t₂))) 1 0 := by
      rw [← hsuf']
      exact den_mono_prefix hsuf'_pos
    have hmonoR : ((cfProd (0 :: makeNoShortChild ε η j w p₁)) 1 0 : ℝ) ≤
        ((cfProd (0 :: (w' ++ t₂))) 1 0 : ℝ) := by exact_mod_cast hmono
    linarith

/-- Every word in `noShortWordAtoms ε η j` satisfies `StageInv ε j` and distinct words at
    stage `j` are prefix-incomparable. -/
theorem noShortWordAtoms_inv_and_incomp (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) :
    ∀ j ≥ j0NoShort η,
      (∀ w ∈ noShortWordAtoms ε η j, StageInv ε j w) ∧
      (∀ w₁ ∈ noShortWordAtoms ε η j, ∀ w₂ ∈ noShortWordAtoms ε η j,
        w₁ ≠ w₂ → ¬ (w₁ <+: w₂)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    rw [noShortWordAtoms_base]
    refine ⟨fun w hw => ?_, fun w₁ h1 w₂ h2 hne => ?_⟩
    · rw [Finset.mem_singleton.mp hw]; exact initWordAt_inv ε (j0NoShort_ge_six η)
    · rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2] at hne
      exact absurd rfl hne
  | succ j hj ih =>
    obtain ⟨ih_inv, ih_inc⟩ := ih
    rw [noShortWordAtoms_succ ε η hj]
    constructor
    · intro c hc
      obtain ⟨w, hw, hcw⟩ := Finset.mem_biUnion.mp hc
      simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hcw
      obtain ⟨p, ⟨hp_box, hgcd⟩, rfl⟩ := hcw
      exact (noShortChild_transition hη0 hη1 hj (ih_inv w hw) hp_box hgcd).2
    · intro c₁ hc₁ c₂ hc₂ hne hpref
      obtain ⟨w₁, hw₁, hcw₁⟩ := Finset.mem_biUnion.mp hc₁
      obtain ⟨w₂, hw₂, hcw₂⟩ := Finset.mem_biUnion.mp hc₂
      simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hcw₁ hcw₂
      obtain ⟨p₁, ⟨hp₁, hg₁⟩, rfl⟩ := hcw₁
      obtain ⟨p₂, ⟨hp₂, hg₂⟩, rfl⟩ := hcw₂
      by_cases hw_eq : w₁ = w₂
      · subst hw_eq
        have hp_ne : p₁ ≠ p₂ := fun h => hne (by subst h; rfl)
        exact noShortChild_incomparable hη0 hη1 hj (ih_inv w₁ hw₁) hp₁ hg₁ hp₂ hg₂ hp_ne hpref
      · have hw1_pre : w₁ <+: makeNoShortChild ε η j w₁ p₁ := by
          unfold makeNoShortChild preludeWord
          simp only [List.append_assoc]
          exact List.prefix_append w₁ _
        have hw2_pre : w₂ <+: makeNoShortChild ε η j w₂ p₂ := by
          unfold makeNoShortChild preludeWord
          simp only [List.append_assoc]
          exact List.prefix_append w₂ _
        have hw1_in_c2 : w₁ <+: makeNoShortChild ε η j w₂ p₂ := List.IsPrefix.trans hw1_pre hpref
        rcases List.prefix_or_prefix_of_prefix hw1_in_c2 hw2_pre with h12 | h21
        · exact ih_inc w₁ hw₁ w₂ hw₂ hw_eq h12
        · exact ih_inc w₂ hw₂ w₁ hw₁ (Ne.symm hw_eq) h21

/-- `cylPair` is injective on `noShortWordAtoms ε η j`. -/
theorem cylPair_injOn_noShortAtoms (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) {j : ℕ} (hj : j0NoShort η ≤ j) :
    Set.InjOn cylPair ↑(noShortWordAtoms ε η j) := by
  obtain ⟨hinv, hinc⟩ := noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj
  intro w₁ hw₁ w₂ hw₂ heq
  by_contra hne
  have h1 := Finset.mem_coe.mp hw₁
  have h2 := Finset.mem_coe.mp hw₂
  have hdisj := cylPair_disj_of_incomparable (hinv w₁ h1).1 (hinv w₂ h2).1
    (hinc w₁ h1 w₂ h2 hne) (hinc w₂ h2 w₁ h1 (Ne.symm hne))
  rw [heq] at hdisj
  have hlen := cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) (hinv w₂ h2).1 (hinv w₂ h2).2.1
    (hinv w₂ h2).2.2.2.1 (hinv w₂ h2).2.2.2.2.1
    (by exact_mod_cast le_of_lt (hinv w₂ h2).2.2.2.2.2.1)
    (by exact_mod_cast (by linarith [(hinv w₂ h2).2.2.2.2.2.1, (hinv w₂ h2).2.2.2.2.2.2] :
      (cfProd (0 :: w₂)) 1 1 ≤ (cfProd (0 :: w₂)) 1 0))
  have hlt : (cylPair w₂).1 < (cylPair w₂).2 := by
    have : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith [hlen.1]
  have hmid : ((cylPair w₂).1 + (cylPair w₂).2) / 2 ∈
      Set.Ioo (cylPair w₂).1 (cylPair w₂).2 := ⟨by linarith, by linarith⟩
  exact Set.disjoint_left.mp hdisj hmid hmid

open Classical in
/-- Concrete `StoppedTree.TreeData` for Paper 2's `thm:no-short-dim` prelude-of-ones CF tree. -/
noncomputable def cfNoShortTree (ε : ℕ → Bool) (η : ℝ) : StoppedTree.TreeData where
  atoms := fun j => (noShortWordAtoms ε η j).image cylPair
  child := fun j I =>
    if h : ∃ w ∈ noShortWordAtoms ε η j, cylPair w = I then
      (noShortWordChild ε η j (Classical.choose h)).image cylPair
    else ∅

/-- Unconditional Hausdorff dimension lower bound for `cfNoShortTree ε η`:
    discharges all hypotheses of `WindowPaperScale.dimH_ge_gamma_no_short_paper_scale`. -/
theorem dimH_ge_gamma_cfNoShortTree (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) :
    ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) ≤
      dimH (WindowTreePrune.cantorSet (cfNoShortTree ε η) (j0NoShort η)) := by
  classical
  let j0 := j0NoShort η
  have hj06 : 6 ≤ j0 := j0NoShort_ge_six η
  let R : ℕ → (ℝ × ℝ) → ℝ := fun j I =>
    if h : ∃ w ∈ noShortWordAtoms ε η j, cylPair w = I then
      noShortScale η j (Classical.choose h)
    else (2 / (5 * Real.goldenRatio ^ 2)) * WindowPaperScale.Rpaper j *
      (j : ℝ) ^ (-(η * Real.log Real.goldenRatio))
  have hchoose_eq : ∀ j ≥ j0, ∀ w ∈ noShortWordAtoms ε η j,
      ∀ h : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w,
        Classical.choose h = w := by
    intro j hj w hw h
    obtain ⟨hw', heq⟩ := Classical.choose_spec h
    exact cylPair_injOn_noShortAtoms ε hη0 hη1 hj
      (Finset.mem_coe.mpr hw') (Finset.mem_coe.mpr hw) heq
  have hR_lo : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j,
      (2 / (5 * Real.goldenRatio ^ 2)) * WindowPaperScale.Rpaper j *
        (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤ R j I := by
    intro j hj I hI
    simp only [cfNoShortTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [R, hex, ↓reduceDIte, hchoose_eq j hj w hw hex]
    exact noShortScale_ge hη0 (le_trans hj06 hj)
      ((noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw)
  have hne0 : ((cfNoShortTree ε η).atoms j0).Nonempty := by
    refine ⟨cylPair (initWordAt ε j0), ?_⟩
    simp [cfNoShortTree, j0, noShortWordAtoms_base]
  have hlen : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j,
      (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 ≤ I.2 - I.1 ∧
      I.2 - I.1 ≤ (9 / 16 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
    intro j hj I hI
    simp only [cfNoShortTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hinv := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
    exact cylPair_len_bounds (WindowPaperScale.Hpaper_pos j) hinv.1 hinv.2.1
      hinv.2.2.2.1 hinv.2.2.2.2.1
      (by exact_mod_cast le_of_lt hinv.2.2.2.2.2.1)
      (by exact_mod_cast (by linarith [hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2] :
        (cfProd (0 :: w)) 1 1 ≤ (cfProd (0 :: w)) 1 0))
  have htriv : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j, I.1 < I.2 := by
    intro j hj I hI
    have h1 := (hlen j hj I hI).1
    have hpos : (0 : ℝ) < (2 / 25 : ℝ) / (WindowPaperScale.Hpaper j) ^ 2 := by
      have := WindowPaperScale.Hpaper_pos j; positivity
    linarith
  have hdisj : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j, ∀ J ∈ (cfNoShortTree ε η).atoms j,
      I ≠ J → Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) := by
    intro j hj I hI J hJ hne
    simp only [cfNoShortTree, Finset.mem_image] at hI hJ
    obtain ⟨w₁, hw₁, rfl⟩ := hI
    obtain ⟨w₂, hw₂, rfl⟩ := hJ
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    obtain ⟨hinv, hinc⟩ := noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj
    exact cylPair_disj_of_incomparable (hinv w₁ hw₁).1 (hinv w₂ hw₂).1
      (hinc w₁ hw₁ w₂ hw₂ hw_ne) (hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne))
  have hchild_mem : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j,
      (cfNoShortTree ε η).child j I ⊆ (cfNoShortTree ε η).atoms (j + 1) := by
    intro j hj I hI c hc
    simp only [cfNoShortTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfNoShortTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image] at hc ⊢
    obtain ⟨cw, hcw, rfl⟩ := hc
    refine ⟨cw, ?_, rfl⟩
    rw [noShortWordAtoms_succ ε η hj]
    exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩
  have hchild_cop : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j,
      NoShortDim.copCountS (R j I) ≤ ((cfNoShortTree ε η).child j I).card := by
    intro j hj I hI
    simp only [cfNoShortTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    have hinv := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
    simp only [R, cfNoShortTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex]
    have hsub_atoms : noShortWordChild ε η j w ⊆ noShortWordAtoms ε η (j + 1) := by
      intro c hc
      rw [noShortWordAtoms_succ ε η hj]
      exact Finset.mem_biUnion.mpr ⟨w, hw, hc⟩
    have hinj_cyl : Set.InjOn cylPair ↑(noShortWordChild ε η j w) :=
      (cylPair_injOn_noShortAtoms ε hη0 hη1 (by omega : j0 ≤ j + 1)).mono
        (Finset.coe_subset.mpr hsub_atoms)
    rw [Finset.card_image_of_injOn hinj_cyl]
    unfold noShortWordChild NoShortDim.copCountS
    have hinj_word : Set.InjOn (makeNoShortChild ε η j w)
        ↑((NoShortDim.boxS (noShortScale η j w)).filter (fun p => Nat.gcd p.1 p.2 = 1)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      by_contra hne
      simp only [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
      exact noShortChild_incomparable hη0 hη1 hj hinv hp₁.1 hp₁.2 hp₂.1 hp₂.2 hne (by rw [heq])
    rw [Finset.card_image_of_injOn hinj_word]
  have hdisj_child : ∀ j ≥ j0, ∀ I₁ ∈ (cfNoShortTree ε η).atoms j,
      ∀ I₂ ∈ (cfNoShortTree ε η).atoms j, I₁ ≠ I₂ →
      Disjoint ((cfNoShortTree ε η).child j I₁) ((cfNoShortTree ε η).child j I₂) := by
    intro j hj I₁ hI₁ I₂ hI₂ hne
    simp only [cfNoShortTree, Finset.mem_image] at hI₁ hI₂
    obtain ⟨w₁, hw₁, rfl⟩ := hI₁
    obtain ⟨w₂, hw₂, rfl⟩ := hI₂
    have hw_ne : w₁ ≠ w₂ := fun h => hne (by subst h; rfl)
    have hex₁ : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w₁ := ⟨w₁, hw₁, rfl⟩
    have hex₂ : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w₂ := ⟨w₂, hw₂, rfl⟩
    simp only [cfNoShortTree, hex₁, hex₂, ↓reduceDIte,
      hchoose_eq j hj w₁ hw₁ hex₁, hchoose_eq j hj w₂ hw₂ hex₂]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    simp only [Finset.mem_image] at hc₁ hc₂
    obtain ⟨c₁, hc₁', rfl⟩ := hc₁
    obtain ⟨c₂, hc₂', heq⟩ := hc₂
    have hc₁_atoms : c₁ ∈ noShortWordAtoms ε η (j + 1) := by
      rw [noShortWordAtoms_succ ε η hj]; exact Finset.mem_biUnion.mpr ⟨w₁, hw₁, hc₁'⟩
    have hc₂_atoms : c₂ ∈ noShortWordAtoms ε η (j + 1) := by
      rw [noShortWordAtoms_succ ε η hj]; exact Finset.mem_biUnion.mpr ⟨w₂, hw₂, hc₂'⟩
    have hc_eq : c₁ = c₂ :=
      cylPair_injOn_noShortAtoms ε hη0 hη1 (by omega : j0 ≤ j + 1)
        (Finset.mem_coe.mpr hc₁_atoms) (Finset.mem_coe.mpr hc₂_atoms) heq.symm
    subst hc_eq
    simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hc₁' hc₂'
    obtain ⟨p₁, _, hp₁_eq⟩ := hc₁'
    obtain ⟨p₂, _, hp₂_eq⟩ := hc₂'
    have hpre₁ : w₁ <+: c₁ := by
      rw [← hp₁_eq]; unfold makeNoShortChild preludeWord
      simp only [List.append_assoc]; exact List.prefix_append w₁ _
    have hpre₂ : w₂ <+: c₁ := by
      rw [← hp₂_eq]; unfold makeNoShortChild preludeWord
      simp only [List.append_assoc]; exact List.prefix_append w₂ _
    have hinc := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).2
    rcases List.prefix_or_prefix_of_prefix hpre₁ hpre₂ with h12 | h21
    · exact hinc w₁ hw₁ w₂ hw₂ hw_ne h12
    · exact hinc w₂ hw₂ w₁ hw₁ (Ne.symm hw_ne) h21
  have hnest : ∀ j ≥ j0, ∀ I ∈ (cfNoShortTree ε η).atoms j,
      ∀ C ∈ (cfNoShortTree ε η).child j I, Set.Icc C.1 C.2 ⊆ Set.Icc I.1 I.2 := by
    intro j hj I hI C hC
    simp only [cfNoShortTree, Finset.mem_image] at hI
    obtain ⟨w, hw, rfl⟩ := hI
    have hex : ∃ w' ∈ noShortWordAtoms ε η j, cylPair w' = cylPair w := ⟨w, hw, rfl⟩
    simp only [cfNoShortTree, hex, ↓reduceDIte, hchoose_eq j hj w hw hex, Finset.mem_image] at hC
    obtain ⟨cw, hcw, rfl⟩ := hC
    have hinv_w := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
    have hinv_cw := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 (j + 1) (by omega)).1 cw
      (by rw [noShortWordAtoms_succ ε η hj]; exact Finset.mem_biUnion.mpr ⟨w, hw, hcw⟩)
    simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hcw
    obtain ⟨p, _, rfl⟩ := hcw
    unfold makeNoShortChild preludeWord at hinv_cw ⊢
    simp only [List.append_assoc] at hinv_cw ⊢
    exact cylPair_nest hinv_w.1 hinv_w.2.1 (posDigits_append.mp hinv_cw.1).2
  exact WindowPaperScale.dimH_ge_gamma_no_short_paper_scale
    (T := cfNoShortTree ε η) (j0 := j0) (by omega) hη0 hη1 (j0NoShort_scale hη0 hη1)
    hR_lo hne0 htriv hlen hdisj hchild_mem hchild_cop hdisj_child hnest

/-! ### Part 3: Pointwise regular CF bridge & end-to-end `thm:no-short-dim` -/

/-- Target set of `thm:no-short-dim` for fixed `0 < η < 1 / log φ`:
    irrationals `x ∈ (0, 1)` with eventual parity `ε j` and `r_j(x) ≥ η log j`. -/
def noShortSet (ε : ℕ → Bool) (η : ℝ) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧ ∃ J0 : ℕ, ∀ j ≥ J0,
      ((cfStopIdx x j) % 2 == 1) = ε j ∧
      η * Real.log (j : ℝ) ≤ ((cfStopIdx x (j + 1) - cfStopIdx x j : ℕ) : ℝ)}

/-- Target set of `thm:no-short-dim` with divergent window counts `r_j(x) → ∞`
    and prescribed eventual parity `ε j`. -/
def divWindowSet (ε : ℕ → Bool) : Set ℝ :=
  {x ∈ Set.Ioo (0 : ℝ) 1 |
    Irrational x ∧
    (∃ J0 : ℕ, ∀ j ≥ J0, ((cfStopIdx x j) % 2 == 1) = ε j) ∧
    Filter.Tendsto (fun j => cfStopIdx x (j + 1) - cfStopIdx x j) Filter.atTop Filter.atTop}

/-- Pointwise regular CF bridge for `cfNoShortTree ε η`:
    every `x ∈ cantorSet (cfNoShortTree ε η) (j0NoShort η)` is irrational in `(0, 1)` with
    `((cfStopIdx x j) % 2 == 1) = ε j` and `η * log j ≤ r_j(x)` for all `j ≥ j0NoShort η`. -/
theorem mem_cantorSet_cfNoShortTree_cf (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) {x : ℝ}
    (hx : x ∈ WindowTreePrune.cantorSet (cfNoShortTree ε η) (j0NoShort η)) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧
    Irrational x ∧
    ∀ j ≥ j0NoShort η,
      ((cfStopIdx x j) % 2 == 1) = ε j ∧
      η * Real.log (j : ℝ) ≤ ((cfStopIdx x (j + 1) - cfStopIdx x j : ℕ) : ℝ) := by
  have hbridge := stopped_word_tree_cf_bridge
    (wordAtoms := noShortWordAtoms ε η) (wordChild := noShortWordChild ε η)
    (T := cfNoShortTree ε η) (j0 := j0NoShort η) (by have := j0NoShort_ge_six η; omega)
    (fun _ _ => rfl)
    (fun j hj => noShortWordAtoms_succ ε η hj)
    (fun j hj w hw =>
      let h := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
      ⟨h.1, h.2.1⟩)
    (fun j hj => (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).2)
    (fun j hj w hw => by
      have h := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
      have hHpos := WindowPaperScale.Hpaper_pos j
      have hv_lt : (4 : ℝ) * ((cfProd (0 :: w)) 1 1 : ℝ) < ((cfProd (0 :: w)) 1 0 : ℝ) := by
        exact_mod_cast h.2.2.2.2.2.2
      exact ⟨by linarith [h.2.2.2.2.1], by linarith [h.2.2.2.1]⟩)
    (fun j hj w hw c hc => by
      simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hc
      obtain ⟨p, ⟨hp_box, hgcd⟩, rfl⟩ := hc
      have hinv := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 w hw
      have hR_lo := noShortScale_ge_ten_pow_six hη0 hη1 hj hinv
      obtain ⟨hn1, hnm⟩ := boxS_lt hR_lo hp_box
      obtain ⟨ht_pos, ht_ne, _, _, _⟩ :=
        chooseParityCF_props hn1 hnm hgcd (targetTailParity ε j (preludeWord η j w))
      let tail := chooseParityCF p.1 p.2 (targetTailParity ε j (preludeWord η j w))
      refine ⟨List.replicate (preludeLen η j) 1 ++ tail ++ [4], ?_, ?_, Or.inl ?_⟩
      · simp [makeNoShortChild, preludeWord, tail, List.append_assoc]
      · exact posDigits_append.mpr
          ⟨posDigits_append.mpr ⟨posDigits_replicate_one _, ht_pos⟩,
            posDigits_cons.mpr ⟨by omega, posDigits_nil⟩⟩
      · have hlen1 : 1 ≤ tail.length := List.length_pos_of_ne_nil ht_ne
        simp; omega)
    hx
  obtain ⟨hunit, hirr, w, hw_mem, hw_child, _, _, hstop⟩ := hbridge
  refine ⟨hunit, hirr, ?_⟩
  intro j hj
  have hst := (hstop j hj).2
  have hst1 := (hstop (j + 1) (by omega)).2
  have hinv_j := (noShortWordAtoms_inv_and_incomp ε hη0 hη1 j hj).1 (w j) (hw_mem j hj)
  have hpar : ((cfStopIdx x j) % 2 == 1) = ε j := by rw [hst]; exact hinv_j.2.2.1
  have hch := hw_child j hj
  simp only [noShortWordChild, Finset.mem_image, Finset.mem_filter] at hch
  obtain ⟨p, _, hp_eq⟩ := hch
  have hlen_j : 1 ≤ (w j).length := List.length_pos_of_ne_nil hinv_j.2.1
  have hlen_diff : preludeLen η j ≤ (w (j + 1)).length - 1 - ((w j).length - 1) := by
    rw [← hp_eq]
    unfold makeNoShortChild preludeWord
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hr_ge : η * Real.log (j : ℝ) ≤ ((cfStopIdx x (j + 1) - cfStopIdx x j : ℕ) : ℝ) := by
    rw [hst, hst1]
    have h1 : η * Real.log (j : ℝ) ≤ (preludeLen η j : ℝ) := Nat.le_ceil _
    have h2 : (preludeLen η j : ℝ) ≤ (((w (j + 1)).length - 1 - ((w j).length - 1) : ℕ) : ℝ) := by
      exact_mod_cast hlen_diff
    linarith
  exact ⟨hpar, hr_ge⟩

theorem cantorSet_cfNoShortTree_subset_noShortSet (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) :
    WindowTreePrune.cantorSet (cfNoShortTree ε η) (j0NoShort η) ⊆ noShortSet ε η := by
  intro x hx
  obtain ⟨hunit, hirr, hall⟩ := mem_cantorSet_cfNoShortTree_cf ε hη0 hη1 hx
  exact ⟨hunit, hirr, j0NoShort η, hall⟩

/-- End-to-end unconditional `thm:no-short-dim` (fixed `η` branch):
    `ENNReal.ofReal (1 - η * log φ) ≤ dimH (noShortSet ε η)`. -/
theorem dimH_ge_gamma_noShortSet (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / Real.log Real.goldenRatio) :
    ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) ≤ dimH (noShortSet ε η) :=
  le_trans (dimH_ge_gamma_cfNoShortTree ε hη0 hη1)
    (dimH_mono (cantorSet_cfNoShortTree_subset_noShortSet ε hη0 hη1))

theorem noShortSet_subset_divWindowSet (ε : ℕ → Bool) {η : ℝ} (hη0 : 0 < η) :
    noShortSet ε η ⊆ divWindowSet ε := by
  intro x ⟨hunit, hirr, J0, hJ0⟩
  refine ⟨hunit, hirr, ⟨J0, fun j hj => (hJ0 j hj).1⟩, ?_⟩
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨max J0 (Nat.ceil (Real.exp ((b : ℝ) / η)) + 1), ?_⟩
  intro j hj
  have hj0 : J0 ≤ j := le_trans (le_max_left _ _) hj
  have hj_exp : Real.exp ((b : ℝ) / η) < (j : ℝ) := by
    have h1 : Nat.ceil (Real.exp ((b : ℝ) / η)) + 1 ≤ j := le_trans (le_max_right _ _) hj
    have h2 : Real.exp ((b : ℝ) / η) ≤ (Nat.ceil (Real.exp ((b : ℝ) / η)) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (Real.exp ((b : ℝ) / η)) : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hlog : (b : ℝ) / η < Real.log (j : ℝ) := by
    rw [← Real.log_exp ((b : ℝ) / η)]
    exact Real.log_lt_log (Real.exp_pos _) hj_exp
  have hmul : (b : ℝ) < η * Real.log (j : ℝ) := by
    have := mul_lt_mul_of_pos_left hlog hη0
    rwa [mul_div_cancel₀ _ (ne_of_gt hη0)] at this
  have hle := (hJ0 j hj0).2
  have hltR : (b : ℝ) < ((cfStopIdx x (j + 1) - cfStopIdx x j : ℕ) : ℝ) := lt_of_lt_of_le hmul hle
  exact le_of_lt (by exact_mod_cast hltR)

/-- End-to-end unconditional `thm:no-short-dim` (full-dimension divergent-window branch):
    `(1 : ℝ≥0∞) ≤ dimH (divWindowSet ε)` via `η ↓ 0`. -/
theorem dimH_ge_one_divWindowSet (ε : ℕ → Bool) :
    (1 : ℝ≥0∞) ≤ dimH (divWindowSet ε) :=
  WindowPaperScale.dimH_ge_one_of_gamma_family fun _η hη0 hη1 =>
    le_trans (dimH_ge_gamma_noShortSet ε hη0 hη1)
      (dimH_mono (noShortSet_subset_divWindowSet ε hη0))

/-- Exact dimension `dimH (divWindowSet ε) = 1` for `thm:no-short-dim`. -/
theorem dimH_divWindowSet_eq_one (ε : ℕ → Bool) :
    dimH (divWindowSet ε) = 1 :=
  le_antisymm (dimH_le_one_of_subset_Ioo_unit fun _ hx => hx.1)
    (dimH_ge_one_divWindowSet ε)

#print axioms WindowNoShortCFRealize.cfProd_replicate_one
#print axioms WindowNoShortCFRealize.fib_le_goldenRatio_pow
#print axioms WindowNoShortCFRealize.prelude_den_bounds
#print axioms WindowNoShortCFRealize.initWordAt_inv
#print axioms WindowNoShortCFRealize.j0NoShort_scale
#print axioms WindowNoShortCFRealize.noShortScale_ge
#print axioms WindowNoShortCFRealize.noShortScale_ge_ten_pow_six
#print axioms WindowNoShortCFRealize.noShortChild_transition
#print axioms WindowNoShortCFRealize.noShortChild_incomparable
#print axioms WindowNoShortCFRealize.noShortWordAtoms_inv_and_incomp
#print axioms WindowNoShortCFRealize.cylPair_injOn_noShortAtoms
#print axioms WindowNoShortCFRealize.dimH_ge_gamma_cfNoShortTree
#print axioms WindowNoShortCFRealize.mem_cantorSet_cfNoShortTree_cf
#print axioms WindowNoShortCFRealize.cantorSet_cfNoShortTree_subset_noShortSet
#print axioms WindowNoShortCFRealize.dimH_ge_gamma_noShortSet
#print axioms WindowNoShortCFRealize.noShortSet_subset_divWindowSet
#print axioms WindowNoShortCFRealize.dimH_ge_one_divWindowSet
#print axioms WindowNoShortCFRealize.dimH_divWindowSet_eq_one

end WindowNoShortCFRealize
