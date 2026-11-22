import EpiFormal.WindowMassProd
import EpiFormal.WindowLogFact
import EpiFormal.WindowLogThresh
import EpiFormal.WindowMainBound
import EpiFormal.NoShortDimCount

/-!
# Asymptotic threshold discharge for windows & no-short-dim Frostman assembly

Connects the verified arithmetic pieces:
- `WindowMassProd.mass_le_prod` / `prod_Ico_self_eq_fact_div` / `mass_le_fact_bound`,
- `WindowLogFact.log_factorial_ge` (Stirling lower bound),
- `WindowLogThresh.log_inv_le_two_log` and `WindowLogThresh.frostman_ratio_bound`,
- `WindowMobiusCount.coprime_count_ge` (`R²/10000`) and
  `NoShortDim.coprimeS_count_ge` (`R²/100000`),

to prove:
1. `general_overlap_const` & `stopped_overlap_const`: scale-free overlap constant
   `(2 + 3 * L_c) / d0_c + 2` (specializing to `1603 / 64` for `(4/25, 9/16)` and
   `2953 / 64` for the paper's `(2/25, 9/16)`).
2. `log_pred_fact_ge`: `j log j - log j - j ≤ log ((j - 1)!)` for `j ≥ 2`.
3. `asymp_thresh_exists_rpow` & `asymp_thresh_exists`: for any real `b : ℝ`
   (covering `b = 2`, `b = 1`, and `b = 2γ` in `thm:no-short-dim`), `0 < s < b / 2`,
   branching `B i ≥ c * i^b`, and `log (H (j + 1)) ≤ j log j + C_H * j`, there exists
   `J1 ≥ j0` such that `K0 / ∏_{i ∈ [j0, j)} B i ≤ h'^s` for all `j ≥ J1` and
   `h' ≥ 1 / (H (j + 1))^2`.
4. `coprime_branching_quad` & `coprimeS_branching_rpow`: instantiate branching bounds
   from the verified Möbius rectangle counts.
5. `hCbig_of_ge_scale`: discharges the large-window constant interface `hCbig`
   for `WindowMassFull.mu_window_le_full`.

Only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowAsympThresh

open Real Finset

/-- General scale-free overlap constant for cylinders with lengths in
    `[d0_c / H², L_c / H²]` and window width `h' ≤ 1 / H²`. -/
theorem general_overlap_const {H h' d0_c L_c : ℝ}
    (hH : 0 < H) (hd0 : 0 < d0_c) (hh' : h' ≤ 1 / H ^ 2) :
    (2 * h' + 3 * (L_c / H ^ 2)) / (d0_c / H ^ 2) + 2 ≤ (2 + 3 * L_c) / d0_c + 2 := by
  have hd0pos : (0 : ℝ) < d0_c / H ^ 2 := by positivity
  have hnum : 2 * h' + 3 * (L_c / H ^ 2) ≤ 2 * (1 / H ^ 2) + 3 * (L_c / H ^ 2) := by
    linarith
  have hdiv : (2 * h' + 3 * (L_c / H ^ 2)) / (d0_c / H ^ 2) ≤
      (2 * (1 / H ^ 2) + 3 * (L_c / H ^ 2)) / (d0_c / H ^ 2) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hd0pos)
  have heq : (2 * (1 / H ^ 2) + 3 * (L_c / H ^ 2)) / (d0_c / H ^ 2) =
      (2 + 3 * L_c) / d0_c := by
    have hHne : H ≠ 0 := ne_of_gt hH
    have hd0ne : d0_c ≠ 0 := ne_of_gt hd0
    field_simp
  linarith

/-- Scale-free overlap constant for stopped cylinders of lengths in
    `[4/(25 H²), 9/(16 H²)]` and window width `h' ≤ 1/H²`. -/
theorem stopped_overlap_const {H h' : ℝ} (hH : 0 < H) (hh' : h' ≤ 1 / H ^ 2) :
    (2 * h' + 3 * (9 / (16 * H ^ 2))) / (4 / (25 * H ^ 2)) + 2 ≤ 1603 / 64 := by
  have h := general_overlap_const (d0_c := 4 / 25) (L_c := 9 / 16) hH (by norm_num) hh'
  have hrw1 : (9 / 16 : ℝ) / H ^ 2 = 9 / (16 * H ^ 2) := by ring
  have hrw2 : (4 / 25 : ℝ) / H ^ 2 = 4 / (25 * H ^ 2) := by ring
  have hrw3 : (2 + 3 * (9 / 16 : ℝ)) / (4 / 25) + 2 = 1603 / 64 := by norm_num
  rw [hrw1, hrw2, hrw3] at h
  exact h

/-- Shifted Stirling lower bound: `j log j - log j - j ≤ log ((j - 1)!)` for `j ≥ 2`. -/
theorem log_pred_fact_ge {j : ℕ} (hj : 2 ≤ j) :
    (j : ℝ) * Real.log (j : ℝ) - Real.log (j : ℝ) - (j : ℝ) ≤
      Real.log (Nat.factorial (j - 1) : ℝ) := by
  have hbase := WindowLogFact.log_factorial_ge (j - 1)
  have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  rw [hcast] at hbase
  have hj1pos : (0 : ℝ) < (j : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have hratio : Real.log ((j : ℝ) / ((j : ℝ) - 1)) ≤ (j : ℝ) / ((j : ℝ) - 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hjpos hj1pos)
  have hlogdiv : Real.log ((j : ℝ) / ((j : ℝ) - 1)) =
      Real.log (j : ℝ) - Real.log ((j : ℝ) - 1) :=
    Real.log_div (ne_of_gt hjpos) (ne_of_gt hj1pos)
  have hsub1 : (j : ℝ) / ((j : ℝ) - 1) - 1 = 1 / ((j : ℝ) - 1) := by
    field_simp
    ring
  rw [hlogdiv, hsub1] at hratio
  have hmul : ((j : ℝ) - 1) * (Real.log (j : ℝ) - Real.log ((j : ℝ) - 1)) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hratio (le_of_lt hj1pos)
    have h2 : ((j : ℝ) - 1) * (1 / ((j : ℝ) - 1)) = 1 := by
      field_simp
    linarith
  linarith

/-- Real-exponent asymptotic Frostman threshold discharge for `0 < s < b / 2`:
    covers integer `b ∈ {1, 2}` (`thm:windows`) and real `b = 2γ` (`thm:no-short-dim`). -/
theorem asymp_thresh_exists_rpow
    (j0 : ℕ) (hj0 : 1 ≤ j0)
    (b c s K0 C_H : ℝ) (hc : 0 < c) (hs0 : 0 < s) (hsb : s < b / 2) (hK0 : 0 < K0)
    (B H : ℕ → ℝ)
    (hBpos : ∀ i, 0 < B i)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ B i)
    (hHpos : ∀ j, 0 < H j)
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ)) :
    ∃ J1 : ℕ, j0 ≤ J1 ∧
      ∀ j ≥ J1, ∀ h' : ℝ, 1 / (H (j + 1)) ^ 2 ≤ h' →
        K0 / (∏ i ∈ Finset.Ico j0 j, B i) ≤ h' ^ s := by
  have hbpos : 0 < b := by linarith
  let D0 : ℝ := b * Real.log (Nat.factorial (j0 - 1) : ℝ)
  let A1 : ℝ := 2 * b + |Real.log c|
  let A : ℝ := A1 + 2 * s * max C_H 0 + |D0| + |Real.log K0|
  have hδ : 0 < b - 2 * s := by linarith
  let J1 : ℕ := max (max j0 2) (Nat.ceil (Real.exp (A / (b - 2 * s))) + 1)
  refine ⟨J1, le_trans (le_max_left j0 2) (le_max_left _ _), ?_⟩
  intro j hj h' hh'
  have hj_j0 : j0 ≤ j := le_trans (le_trans (le_max_left j0 2) (le_max_left _ _)) hj
  have hj2 : 2 ≤ j := le_trans (le_trans (le_max_right j0 2) (le_max_left _ _)) hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    linarith
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
    linarith
  have hh'pos : 0 < h' := lt_of_lt_of_le (by have := hHpos (j + 1); positivity) hh'
  -- Step 1: Unroll product and bound below by c^(j-j0) * ((j-1)! / (j0-1)!)^b.
  let m : ℕ → ℝ := fun k => 1 / (∏ i ∈ Finset.Ico j0 k, B i)
  have hm0 : m j0 = 1 := by simp [m]
  have hmrec : ∀ k ≥ j0, m (k + 1) = m k / B k := by
    intro k hk
    simp only [m, Finset.prod_Ico_succ_top hk B, div_div]
  have hprod_unroll := WindowMassProd.mass_le_prod m B j0 hBpos hmrec j hj_j0
  rw [hm0] at hprod_unroll
  set Fnum : ℝ := ((Nat.factorial (j - 1) : ℕ) : ℝ)
  set Fden : ℝ := ((Nat.factorial (j0 - 1) : ℕ) : ℝ)
  have hFnum : 0 < Fnum := Nat.cast_pos.mpr (Nat.factorial_pos (j - 1))
  have hFden : 0 < Fden := Nat.cast_pos.mpr (Nat.factorial_pos (j0 - 1))
  set P : ℝ := c ^ (j - j0) * (Fnum / Fden) ^ b
  have hPpos : 0 < P :=
    mul_pos (pow_pos hc _) (Real.rpow_pos_of_pos (div_pos hFnum hFden) b)
  have hP_le : P ≤ ∏ i ∈ Finset.Ico j0 j, B i := by
    have h1 : ∏ i ∈ Finset.Ico j0 j, (c * (i : ℝ) ^ b) ≤
        ∏ i ∈ Finset.Ico j0 j, B i := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg i) b)
      · intro i hi
        exact hbranch i (Finset.mem_Ico.mp hi).1
    have h2 : ∏ i ∈ Finset.Ico j0 j, (c * (i : ℝ) ^ b) = P := by
      have hrp : ∏ i ∈ Finset.Ico j0 j, (i : ℝ) ^ b =
          (∏ i ∈ Finset.Ico j0 j, (i : ℝ)) ^ b :=
        Real.finsetProd_rpow (Finset.Ico j0 j) (fun i => (i : ℝ))
          (fun i _ => Nat.cast_nonneg i) b
      rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, hrp,
        WindowMassProd.prod_Ico_self_eq_fact_div j0 hj0 j hj_j0]
    exact h2 ▸ h1
  have hmj : m j ≤ 1 / P :=
    le_trans hprod_unroll (div_le_div_of_nonneg_left zero_le_one hPpos hP_le)
  -- Step 2: Convert factorial bound to exponential form.
  have hlogP : Real.log P =
      ((j - j0 : ℕ) : ℝ) * Real.log c + b * (Real.log Fnum - Real.log Fden) := by
    simp only [P]
    rw [Real.log_mul (ne_of_gt (pow_pos hc _))
          (ne_of_gt (Real.rpow_pos_of_pos (div_pos hFnum hFden) b)),
      Real.log_pow, Real.log_rpow (div_pos hFnum hFden),
      Real.log_div (ne_of_gt hFnum) (ne_of_gt hFden)]
  have hsub_cast : ((j - j0 : ℕ) : ℝ) = (j : ℝ) - (j0 : ℝ) := Nat.cast_sub hj_j0
  have hjj0_nn : (0 : ℝ) ≤ (j : ℝ) - (j0 : ℝ) := by
    have : (j0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj_j0
    linarith
  have hlogc_term : -(((j - j0 : ℕ) : ℝ) * Real.log c) ≤ |Real.log c| * (j : ℝ) := by
    rw [hsub_cast]
    have h1 : -Real.log c ≤ |Real.log c| := neg_le_abs (Real.log c)
    have h2 : ((j : ℝ) - (j0 : ℝ)) * (-Real.log c) ≤ ((j : ℝ) - (j0 : ℝ)) * |Real.log c| :=
      mul_le_mul_of_nonneg_left h1 hjj0_nn
    have h3 : ((j : ℝ) - (j0 : ℝ)) * |Real.log c| ≤ (j : ℝ) * |Real.log c| := by
      have hj0nn : (0 : ℝ) ≤ (j0 : ℝ) := Nat.cast_nonneg j0
      nlinarith [abs_nonneg (Real.log c)]
    linarith
  have hlogj_le : Real.log (j : ℝ) ≤ (j : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hjpos]
  have hfact_ge : (j : ℝ) * Real.log (j : ℝ) - 2 * (j : ℝ) ≤ Real.log Fnum := by
    have h1 := log_pred_fact_ge hj2
    linarith [h1, hlogj_le]
  have hneg_logP :
      -Real.log P ≤ -(b * ((j : ℝ) * Real.log (j : ℝ))) + (A1 * (j : ℝ) + D0) := by
    rw [hlogP]
    have hbf : b * ((j : ℝ) * Real.log (j : ℝ) - 2 * (j : ℝ)) ≤ b * Real.log Fnum :=
      mul_le_mul_of_nonneg_left hfact_ge (le_of_lt hbpos)
    simp only [A1, D0, Fden]
    linarith [hlogc_term, hbf]
  have hexp_mj :
      m j ≤ 1 * Real.exp (-(b * ((j : ℝ) * Real.log (j : ℝ))) + (A1 * (j : ℝ) + D0)) := by
    have h1 : 1 / P = Real.exp (-Real.log P) := by
      rw [Real.exp_neg, Real.exp_log hPpos, one_div]
    rw [one_mul]
    calc m j ≤ 1 / P := hmj
      _ = Real.exp (-Real.log P) := h1
      _ ≤ Real.exp (-(b * ((j : ℝ) * Real.log (j : ℝ))) + (A1 * (j : ℝ) + D0)) :=
          Real.exp_le_exp.mpr hneg_logP
  -- Step 3: Log comparison via WindowLogThresh.log_inv_le_two_log.
  have hloginv : Real.log h'⁻¹ ≤ 2 * Real.log (H (j + 1)) :=
    WindowLogThresh.log_inv_le_two_log h' (H (j + 1)) hh'pos (hHpos (j + 1))
      (by simpa [one_div] using hh')
  have hlogH : Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + max C_H 0 * (j : ℝ) := by
    have h1 := hHlog j hj_j0
    have h2 : C_H * (j : ℝ) ≤ max C_H 0 * (j : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left C_H 0) (le_of_lt hjpos)
    linarith
  have hlog_h' :
      -(2 * s * ((j : ℝ) * Real.log (j : ℝ))) - (2 * s * max C_H 0 * (j : ℝ)) ≤
        s * Real.log h' := by
    have hneg : -Real.log h' ≤ 2 * ((j : ℝ) * Real.log (j : ℝ) + max C_H 0 * (j : ℝ)) := by
      rw [← Real.log_inv]
      linarith [hloginv, hlogH]
    have hmul := mul_le_mul_of_nonneg_left hneg (le_of_lt hs0)
    linarith
  have hE2nn : 0 ≤ 2 * s * max C_H 0 * (j : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hs0)) (le_max_right C_H 0))
      (le_of_lt hjpos)
  -- Step 4: Combine via WindowLogThresh.frostman_ratio_bound.
  have hratio := WindowLogThresh.frostman_ratio_bound
    (K0 * m j) (m j) h' s b ((j : ℝ) * Real.log (j : ℝ))
    (A1 * (j : ℝ) + D0) (2 * s * max C_H 0 * (j : ℝ)) K0 1
    hs0 hh'pos le_rfl (le_of_lt hK0) (by norm_num) hexp_mj hlog_h' hE2nn
  -- Step 5: Show the prefactor is ≤ 1 for j ≥ J1.
  have hceil : Real.exp (A / (b - 2 * s)) ≤ (j : ℝ) := by
    have hj_ge : Nat.ceil (Real.exp (A / (b - 2 * s))) ≤ j :=
      le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hj)
    have h1 : Real.exp (A / (b - 2 * s)) ≤
        (Nat.ceil (Real.exp (A / (b - 2 * s))) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (A / (b - 2 * s))) : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast hj_ge
    linarith
  have hlogj_ge : A / (b - 2 * s) ≤ Real.log (j : ℝ) := by
    have h1 := Real.log_le_log (Real.exp_pos _) hceil
    rwa [Real.log_exp] at h1
  have hδlogj : A ≤ (b - 2 * s) * Real.log (j : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hlogj_ge (le_of_lt hδ)
    rwa [mul_div_cancel₀ _ (ne_of_gt hδ)] at h1
  have hAj : A * (j : ℝ) ≤ (b - 2 * s) * ((j : ℝ) * Real.log (j : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right hδlogj (le_of_lt hjpos)
    linarith
  have hconst_le :
      Real.log K0 + (A1 * (j : ℝ) + D0) + 2 * s * max C_H 0 * (j : ℝ) ≤ A * (j : ℝ) := by
    have hD0 : D0 ≤ |D0| * (j : ℝ) := by
      have h1 : D0 ≤ |D0| := le_abs_self D0
      nlinarith [abs_nonneg D0, hj1]
    have hK0' : Real.log K0 ≤ |Real.log K0| * (j : ℝ) := by
      have h1 : Real.log K0 ≤ |Real.log K0| := le_abs_self (Real.log K0)
      nlinarith [abs_nonneg (Real.log K0), hj1]
    simp only [A]
    linarith
  have hpref : K0 * 1 *
      Real.exp (-((b - 2 * s) * ((j : ℝ) * Real.log (j : ℝ))) +
        (A1 * (j : ℝ) + D0) + 2 * s * max C_H 0 * (j : ℝ)) ≤ 1 := by
    rw [mul_one, ← Real.exp_log hK0, ← Real.exp_add]
    have hexp_le : Real.log K0 +
        (-((b - 2 * s) * ((j : ℝ) * Real.log (j : ℝ))) +
          (A1 * (j : ℝ) + D0) + 2 * s * max C_H 0 * (j : ℝ)) ≤ 0 := by
      linarith [hAj, hconst_le]
    calc Real.exp (Real.log K0 +
          (-((b - 2 * s) * ((j : ℝ) * Real.log (j : ℝ))) +
            (A1 * (j : ℝ) + D0) + 2 * s * max C_H 0 * (j : ℝ)))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr hexp_le
      _ = 1 := Real.exp_zero
  have hK0m : K0 * m j = K0 / (∏ i ∈ Finset.Ico j0 j, B i) := by
    simp only [m, mul_one_div]
  rw [← hK0m]
  calc K0 * m j
      ≤ K0 * 1 *
          Real.exp (-((b - 2 * s) * ((j : ℝ) * Real.log (j : ℝ))) +
            (A1 * (j : ℝ) + D0) + 2 * s * max C_H 0 * (j : ℝ)) * h' ^ s := hratio
    _ ≤ 1 * h' ^ s :=
        mul_le_mul_of_nonneg_right hpref (le_of_lt (Real.rpow_pos_of_pos hh'pos s))
    _ = h' ^ s := one_mul _

/-- Natural-exponent wrapper of `asymp_thresh_exists_rpow`. -/
theorem asymp_thresh_exists
    (j0 b : ℕ) (hj0 : 1 ≤ j0)
    (c s K0 C_H : ℝ) (hc : 0 < c) (hs0 : 0 < s) (hsb : s < (b : ℝ) / 2) (hK0 : 0 < K0)
    (B H : ℕ → ℝ)
    (hBpos : ∀ i, 0 < B i)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ^ b ≤ B i)
    (hHpos : ∀ j, 0 < H j)
    (hHlog : ∀ j ≥ j0,
      Real.log (H (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ)) :
    ∃ J1 : ℕ, j0 ≤ J1 ∧
      ∀ j ≥ J1, ∀ h' : ℝ, 1 / (H (j + 1)) ^ 2 ≤ h' →
        K0 / (∏ i ∈ Finset.Ico j0 j, B i) ≤ h' ^ s :=
  asymp_thresh_exists_rpow j0 hj0 (b : ℝ) c s K0 C_H hc hs0 hsb hK0 B H hBpos
    (fun i hi => by simpa [Real.rpow_natCast] using hbranch i hi) hHpos hHlog

/-- Quadratic branching bound from the verified Möbius coprime count
    (`WindowMobiusCount.coprime_count_ge`). -/
theorem coprime_branching_quad
    (R : ℕ → ℝ) (j0 : ℕ) (c_R : ℝ) (hcR : 0 < c_R)
    (hR106 : ∀ i ≥ j0, (10 ^ 6 : ℝ) ≤ R i)
    (hRlin : ∀ i ≥ j0, c_R * (i : ℝ) ≤ R i) :
    ∀ i ≥ j0, (c_R ^ 2 / 10000) * (i : ℝ) ^ 2 ≤
      ((WindowMobiusCount.copCount (R i) : ℕ) : ℝ) := by
  intro i hi
  have hge := WindowMobiusCount.coprime_count_ge (R i) (hR106 i hi)
  have hlin := hRlin i hi
  have hnn : 0 ≤ c_R * (i : ℝ) := mul_nonneg (le_of_lt hcR) (Nat.cast_nonneg i)
  have hsq : (c_R * (i : ℝ)) ^ 2 ≤ (R i) ^ 2 := by nlinarith
  have hdiv : (c_R * (i : ℝ)) ^ 2 / 10000 ≤ (R i) ^ 2 / 10000 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  have hrw : (c_R ^ 2 / 10000) * (i : ℝ) ^ 2 = (c_R * (i : ℝ)) ^ 2 / 10000 := by ring
  linarith

/-- Real-exponent branching bound for `thm:no-short-dim` from the verified
    short-rectangle Möbius coprime count (`NoShortDim.coprimeS_count_ge`). -/
theorem coprimeS_branching_rpow
    (R : ℕ → ℝ) (j0 : ℕ) (c_R γ : ℝ) (hcR : 0 < c_R)
    (hR106 : ∀ i ≥ j0, (10 ^ 6 : ℝ) ≤ R i)
    (hRpow : ∀ i ≥ j0, c_R * (i : ℝ) ^ γ ≤ R i) :
    ∀ i ≥ j0, (c_R ^ 2 / 100000) * (i : ℝ) ^ (2 * γ) ≤
      ((NoShortDim.copCountS (R i) : ℕ) : ℝ) := by
  intro i hi
  have hge := NoShortDim.coprimeS_count_ge (R i) (hR106 i hi)
  have hlin := hRpow i hi
  have hnn : 0 ≤ c_R * (i : ℝ) ^ γ :=
    mul_nonneg (le_of_lt hcR) (Real.rpow_nonneg (Nat.cast_nonneg i) γ)
  have hsq : (c_R * (i : ℝ) ^ γ) ^ 2 ≤ (R i) ^ 2 := by nlinarith
  have hpow2 : ((i : ℝ) ^ γ) ^ 2 = (i : ℝ) ^ (2 * γ) := by
    rw [← Real.rpow_natCast ((i : ℝ) ^ γ) 2, ← Real.rpow_mul (Nat.cast_nonneg i)]
    congr 1
    ring
  have hrw : (c_R ^ 2 / 100000) * (i : ℝ) ^ (2 * γ) = (c_R * (i : ℝ) ^ γ) ^ 2 / 100000 := by
    rw [mul_pow, hpow2]; ring
  have hdiv : (c_R * (i : ℝ) ^ γ) ^ 2 / 100000 ≤ (R i) ^ 2 / 100000 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  linarith

/-- Discharges `hCbig` for `WindowMassFull.mu_window_le_full`:
    any constant `C ≥ (H0 ^ 2) ^ s` gives `1 ≤ C * D ^ s` for all `D > 1 / H0 ^ 2`. -/
theorem hCbig_of_ge_scale {H0 C s : ℝ} (hH0 : 0 < H0) (hs : 0 ≤ s)
    (hC : (H0 ^ 2) ^ s ≤ C) :
    ∀ D : ℝ, 1 / H0 ^ 2 < D → (1 : ℝ) ≤ C * D ^ s := by
  intro D hD
  have hH2pos : 0 < H0 ^ 2 := sq_pos_of_pos hH0
  have hinv_pos : 0 < 1 / H0 ^ 2 := div_pos one_pos hH2pos
  have hDpos : 0 < D := lt_trans hinv_pos hD
  have hrpow : (1 / H0 ^ 2) ^ s ≤ D ^ s :=
    Real.rpow_le_rpow (le_of_lt hinv_pos) (le_of_lt hD) hs
  have hprod1 : (H0 ^ 2) ^ s * (1 / H0 ^ 2) ^ s = 1 := by
    rw [← Real.mul_rpow (le_of_lt hH2pos) (le_of_lt hinv_pos),
      mul_one_div_cancel (ne_of_gt hH2pos), Real.one_rpow]
  have hCnn : 0 ≤ (H0 ^ 2) ^ s := le_of_lt (Real.rpow_pos_of_pos hH2pos s)
  calc (1 : ℝ) = (H0 ^ 2) ^ s * (1 / H0 ^ 2) ^ s := hprod1.symm
    _ ≤ (H0 ^ 2) ^ s * D ^ s := mul_le_mul_of_nonneg_left hrpow hCnn
    _ ≤ C * D ^ s := mul_le_mul_of_nonneg_right hC (le_of_lt (Real.rpow_pos_of_pos hDpos s))

#print axioms WindowAsympThresh.general_overlap_const
#print axioms WindowAsympThresh.stopped_overlap_const
#print axioms WindowAsympThresh.log_pred_fact_ge
#print axioms WindowAsympThresh.asymp_thresh_exists_rpow
#print axioms WindowAsympThresh.asymp_thresh_exists
#print axioms WindowAsympThresh.coprime_branching_quad
#print axioms WindowAsympThresh.coprimeS_branching_rpow
#print axioms WindowAsympThresh.hCbig_of_ge_scale

end WindowAsympThresh
