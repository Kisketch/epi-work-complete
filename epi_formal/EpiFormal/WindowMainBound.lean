import Mathlib
import EpiFormal.WindowMobiusCount
import EpiFormal.WindowMobiusPartial
import EpiFormal.WindowWindowBounds

open ArithmeticFunction Finset Real
open scoped BigOperators

namespace WindowMobiusCount

/-!
# Main window count lower bound (paper2 §7, `thm:windows` assembly).

Assembles `coprime_count_eq` (exact identity), `moebius_partial` (359/900),
and the window bounds (`Acount`/`Bcount` within ±1 of `W/d`) into

  `copCount R ≥ R² / 10000` for `R ≥ 10^6`.

Error control: `|A·B − W₁W₂/d²| ≤ (W1/d + W2/d) + 1 ≤ 0.042·R/d + 1`,
summed with the harmonic bound; the `log` tail is closed by
`e³ > 10`, i.e. `log 10 < 3`, i.e. `log(10⁶) < 18`.
-/

/-- `e³ > 10`, via `e > 2.7`. -/
theorem exp_three_gt_ten : (10 : ℝ) < (Real.exp 1) ^ 3 := by
  have e27 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hS : (0 : ℝ) < (Real.exp 1) ^ 2 + 2.7 * (Real.exp 1) + 2.7 ^ 2 := by
    have e0 := Real.exp_pos 1
    have c0 : (0 : ℝ) < 2.7 := by norm_num
    have h1 := mul_pos e0 c0
    nlinarith [sq_nonneg (Real.exp 1), h1]
  have hprod : (0 : ℝ) < (Real.exp 1 - 2.7) *
      ((Real.exp 1) ^ 2 + 2.7 * (Real.exp 1) + 2.7 ^ 2) :=
    mul_pos (sub_pos.mpr e27) hS
  have hexpand : (Real.exp 1 - 2.7) *
      ((Real.exp 1) ^ 2 + 2.7 * (Real.exp 1) + 2.7 ^ 2) =
      (Real.exp 1) ^ 3 - 2.7 ^ 3 := by ring
  have hcube : (2.7 : ℝ) ^ 3 = 19.683 := by norm_num
  linarith [hprod, hexpand, hcube]

/-- `log 10 < 3`, from `10 < e³`. -/
theorem log_ten_lt_three : Real.log 10 < 3 := by
  have e3eq : (Real.exp 1) ^ 3 = Real.exp 3 := by
    rw [pow_three, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hexp3 : (10 : ℝ) < Real.exp 3 := by
    rw [← e3eq]
    exact exp_three_gt_ten
  exact (Real.log_lt_iff_lt_exp (show (0 : ℝ) < 10 by norm_num)).mpr hexp3

/-- `log(10⁶) < 18`. -/
theorem log106_lt : Real.log ((10 : ℝ) ^ 6) < 18 := by
  rw [Real.log_pow]
  have h6 : (((6 : ℕ)) : ℝ) * Real.log 10 < (((6 : ℕ)) : ℝ) * 3 :=
    mul_lt_mul_of_pos_left log_ten_lt_three (by norm_num)
  norm_num at h6 ⊢
  linarith [h6]

/-- Log of the window top, via `log(x/10⁶) ≤ x/10⁶ − 1`. -/
theorem logMhi_le (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) :
    Real.log ((Mhi R : ℕ) : ℝ) ≤ ((Mhi R : ℕ) : ℝ) / 10 ^ 6 + 17 := by
  have hR0 : (0 : ℝ) ≤ R := by linarith [hR]
  have hMhi1 : 1 ≤ Mhi R :=
    le_trans (Mlo_ge_one R) (box_nonempty R (by linarith : (100 : ℝ) ≤ R)).1
  have hMhipos : (0 : ℝ) < ((Mhi R : ℕ) : ℝ) := by
    have hN : 0 < Mhi R := by omega
    exact_mod_cast hN
  have h106ne : ((10 : ℝ) ^ 6) ≠ 0 := by norm_num
  have hdiv : Real.log (((Mhi R : ℕ) : ℝ) / 10 ^ 6) =
      Real.log ((Mhi R : ℕ) : ℝ) - Real.log ((10 : ℝ) ^ 6) :=
    Real.log_div (ne_of_gt hMhipos) h106ne
  have hle : Real.log (((Mhi R : ℕ) : ℝ) / 10 ^ 6) ≤ ((Mhi R : ℕ) : ℝ) / 10 ^ 6 - 1 :=
    Real.log_le_sub_one_of_pos
      (div_pos hMhipos (by norm_num : (0 : ℝ) < 10 ^ 6))
  calc Real.log ((Mhi R : ℕ) : ℝ)
      = Real.log (((Mhi R : ℕ) : ℝ) / 10 ^ 6) + Real.log ((10 : ℝ) ^ 6) := by
        rw [hdiv]; ring
    _ ≤ (((Mhi R : ℕ) : ℝ) / 10 ^ 6 - 1) + 18 :=
        add_le_add hle log106_lt.le
    _ = ((Mhi R : ℕ) : ℝ) / 10 ^ 6 + 17 := by ring

/-- Per-`d` transfer-operator error. -/
theorem err_bound (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) (d : ℕ) (hd : 1 ≤ d) :
    |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| ≤
      (0.042 * R) * (1 / (d : ℝ)) + 1 := by
  have hR0 : (0 : ℝ) ≤ R := by linarith [hR]
  have hdN : 0 < d := by omega
  have hdrpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdN
  have hW1nn : 0 ≤ W1 R := by
    have h := W1_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.019 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hW2nn : 0 ≤ W2 R := by
    have h := W2_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.019 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hAnn : (0 : ℝ) ≤ (Acount R d : ℝ) := Nat.cast_nonneg _
  have hBnn : (0 : ℝ) ≤ (Bcount R d : ℝ) := Nat.cast_nonneg _
  have ha_nn : (0 : ℝ) ≤ W1 R / (d : ℝ) := div_nonneg hW1nn (le_of_lt hdrpos)
  have hb_nn : (0 : ℝ) ≤ W2 R / (d : ℝ) := div_nonneg hW2nn (le_of_lt hdrpos)
  have hA1 : |(Acount R d : ℝ) - W1 R / (d : ℝ)| ≤ 1 := by
    have hlo := Acount_lo R hR d hd
    have hhi := Acount_hi R hR d hd
    exact abs_le.mpr ⟨by linarith [hlo], by linarith [hhi]⟩
  have hB1 : |(Bcount R d : ℝ) - W2 R / (d : ℝ)| ≤ 1 := by
    have hlo := Bcount_lo R hR d hd
    have hhi := Bcount_hi R hR d hd
    exact abs_le.mpr ⟨by linarith [hlo], by linarith [hhi]⟩
  have hBub : (Bcount R d : ℝ) ≤ W2 R / (d : ℝ) + 1 := by
    linarith [Bcount_hi R hR d hd]
  have ha : W1 R / (d : ℝ) ≤ 0.021 * R / (d : ℝ) :=
    div_le_div_of_nonneg_right (W1_hi R hR) (le_of_lt hdrpos)
  have hb : W2 R / (d : ℝ) ≤ 0.021 * R / (d : ℝ) :=
    div_le_div_of_nonneg_right (W2_hi R hR) (le_of_lt hdrpos)
  have hadd : (0.021 * R) / (d : ℝ) + (0.021 * R) / (d : ℝ) =
      (0.042 * R) / (d : ℝ) := by
    rw [← add_div]
    congr 1
    ring
  have hmul0 : (0.042 * R) * (1 / (d : ℝ)) = (0.042 * R) / (d : ℝ) := by ring
  have e2 : (W1 R / (d : ℝ)) * (W2 R / (d : ℝ)) =
      (W1 R * W2 R) / (d : ℝ) ^ 2 := by
    rw [div_mul_div_comm, pow_two]
  have htri : |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| ≤
      1 * (Bcount R d : ℝ) + (W1 R / (d : ℝ)) * 1 := by
    have e12 : ((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ) +
        (W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ)) =
        ((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R / (d : ℝ)) * (W2 R / (d : ℝ)) := by
      ring
    calc |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2|
          = |(((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ) +
            (W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ)))| := by
            rw [← e2, ← e12]
        _ ≤ |((Acount R d : ℝ) - W1 R / (d : ℝ))| * |(Bcount R d : ℝ)| +
            |(W1 R / (d : ℝ))| * |((Bcount R d : ℝ) - W2 R / (d : ℝ))| := by
          have eX : |((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ)| =
              |((Acount R d : ℝ) - W1 R / (d : ℝ))| * |(Bcount R d : ℝ)| := abs_mul _ _
          have eY : |(W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ))| =
              |(W1 R / (d : ℝ))| * |((Bcount R d : ℝ) - W2 R / (d : ℝ))| := abs_mul _ _
          have hX1 := neg_abs_le (((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ))
          have hY1 := neg_abs_le ((W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ)))
          have hX2 := le_abs_self (((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ))
          have hY2 := le_abs_self ((W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ)))
          have hT : |(((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ) +
              (W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ)))| ≤
              |((Acount R d : ℝ) - W1 R / (d : ℝ)) * (Bcount R d : ℝ)| +
              |(W1 R / (d : ℝ)) * ((Bcount R d : ℝ) - W2 R / (d : ℝ))| :=
            abs_le.mpr ⟨by linarith [hX1, hY1], by linarith [hX2, hY2]⟩
          linarith [hT, eX, eY]
        _ = |((Acount R d : ℝ) - W1 R / (d : ℝ))| * (Bcount R d : ℝ) +
            (W1 R / (d : ℝ)) * |((Bcount R d : ℝ) - W2 R / (d : ℝ))| := by
            rw [abs_of_nonneg hBnn, abs_of_nonneg ha_nn]
        _ ≤ 1 * (Bcount R d : ℝ) + (W1 R / (d : ℝ)) * 1 := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hA1 hBnn
            · exact mul_le_mul_of_nonneg_left hB1 ha_nn
  have hfin : 1 * (Bcount R d : ℝ) + (W1 R / (d : ℝ)) * 1 ≤
      (0.042 * R) * (1 / (d : ℝ)) + 1 := by
    have h1 : (Bcount R d : ℝ) + W1 R / (d : ℝ) ≤
        (0.021 * R) / (d : ℝ) + (0.021 * R) / (d : ℝ) + 1 := by
      linarith [hBub, ha]
    linarith [h1, hadd, hmul0]
  linarith [htri, hfin]

/-- The window count is at least `R²/10000`. -/
theorem coprime_count_ge (R : ℝ) (hR : (10 ^ 6 : ℝ) ≤ R) :
    R ^ 2 / 10000 ≤ ((copCount R : ℕ) : ℝ) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith [hR]
  have hMhi1 : 1 ≤ Mhi R :=
    le_trans (Mlo_ge_one R) (box_nonempty R (by linarith : (100 : ℝ) ≤ R)).1
  have hMhi_ub : ((Mhi R : ℕ) : ℝ) ≤ 0.36 * R :=
    Nat.floor_le (mul_nonneg (by norm_num) hR0)
  have hW1nn : 0 ≤ W1 R := by
    have h := W1_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.019 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hW2nn : 0 ≤ W2 R := by
    have h := W2_lo R hR
    have hR0' : (0 : ℝ) ≤ 0.019 * R := mul_nonneg (by norm_num) hR0
    linarith [h]
  have hS : (359 / 900 : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2 :=
    moebius_partial (Mhi R) hMhi1
  have hcast : ((copCount R : ℝ)) = ∑ d ∈ Finset.Icc 1 (Mhi R),
      (moebius d : ℝ) * (((Acount R d : ℝ)) * ((Bcount R d : ℝ))) := by
    exact_mod_cast coprime_count_eq R
  have hS2 : (W1 R * W2 R) *
      (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 (Mhi R),
        (moebius d : ℝ) * ((W1 R * W2 R) / (d : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hdiff : ((copCount R : ℝ)) -
      (W1 R * W2 R) * (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) =
      ∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) *
        (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2) := by
    rw [hcast, hS2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hsum1 : ∑ _d ∈ Finset.Icc 1 (Mhi R), (1 : ℝ) = ((Mhi R : ℕ) : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hHerr : |(∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) *
      (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2))| ≤
      (0.042 * R) * (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) + ((Mhi R : ℕ) : ℝ) := by
    have h1 : |∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) *
        (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2)| ≤
        ∑ d ∈ Finset.Icc 1 (Mhi R),
          |(moebius d : ℝ) *
            (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∀ d ∈ Finset.Icc 1 (Mhi R),
        |(moebius d : ℝ) *
          (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2)| ≤
        (0.042 * R) * (1 / (d : ℝ)) + 1 := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hmu : |(moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast abs_moebius_le_one (n := d)
      have herr := err_bound R hR d hd1
      have e1 : |(moebius d : ℝ) *
          (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2)| =
          |(moebius d : ℝ)| *
            |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| :=
        abs_mul _ _
      have e2 : |(moebius d : ℝ)| *
          |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| ≤
          1 * ((0.042 * R) * (1 / (d : ℝ)) + 1) := by
        have g1 : |(moebius d : ℝ)| *
            |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| ≤
            1 * |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        have g2 : (1 : ℝ) *
            |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| ≤
            1 * ((0.042 * R) * (1 / (d : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left herr zero_le_one
        linarith [g1, g2, e1]
      calc |(moebius d : ℝ) *
            (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2)|
          = |(moebius d : ℝ)| *
            |((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2| := abs_mul _ _
        _ ≤ 1 * ((0.042 * R) * (1 / (d : ℝ)) + 1) := e2
        _ = (0.042 * R) * (1 / (d : ℝ)) + 1 := by ring
    have h3 := Finset.sum_le_sum h2
    have h4 : (∑ d ∈ Finset.Icc 1 (Mhi R), ((0.042 * R) * (1 / (d : ℝ)) + 1)) =
        (0.042 * R) * (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) + ((Mhi R : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum1]
    linarith [h1, h3, h4]
  have hH : (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) ≤
      ((Mhi R : ℕ) : ℝ) / 10 ^ 6 + 18 := by
    have hbase := harmonic_le (Mhi R) hMhi1
    have hlog := logMhi_le R hR
    have hMhi6 : ((Mhi R : ℕ) : ℝ) / 10 ^ 6 ≤ (0.36 * R) / 10 ^ 6 :=
      div_le_div_of_nonneg_right hMhi_ub (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
    linarith [hbase, hlog, hMhi6]
  have hW12 : (0.019 * R) ^ 2 ≤ (W1 R) * (W2 R) := by
    have h1 : (0.019 * R) * (0.019 * R) ≤ (W1 R) * (W2 R) := by
      have e1 : (0.019 * R) * (0.019 * R) ≤ (W1 R) * (0.019 * R) :=
        mul_le_mul_of_nonneg_right (W1_lo R hR) (by positivity)
      have e2 : (W1 R) * (0.019 * R) ≤ (W1 R) * (W2 R) :=
        mul_le_mul_of_nonneg_left (W2_lo R hR) hW1nn
      linarith [e1, e2]
    have e3 : (0.019 * R) ^ 2 = (0.019 * R) * (0.019 * R) := by ring
    linarith [h1, e3]
  have hM2 : (0.019 * R) ^ 2 * (359 / 900 : ℝ) ≤
      (W1 R * W2 R) * (359 / 900 : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    linarith [hW12]
  have hM3 : (W1 R * W2 R) * (359 / 900 : ℝ) ≤
      (W1 R * W2 R) * (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left hS _
    apply mul_nonneg hW1nn hW2nn
  have hEfin : (0.042 * R) *
      (((0.36 * R) / 10 ^ 6 + 18)) + ((Mhi R : ℕ) : ℝ) ≤
      1.116 * R + 0.0000000152 * R ^ 2 := by
    have e1 : (0.042 * R) * (((0.36 * R) / 10 ^ 6 + 18)) =
        0.042 * R * ((0.36 * R) / 10 ^ 6) + 0.042 * R * 18 := by ring
    have e2 : (0.042 * R) * ((0.36 * R) / 10 ^ 6) ≤ 0.0000000152 * R ^ 2 := by
      have e2a : (0.042 * R) * ((0.36 * R) / 10 ^ 6) =
          (0.042 * 0.36 / 10 ^ 6) * (R * R) := by ring
      have e2b : (0.042 * 0.36 / 10 ^ 6 : ℝ) ≤ 0.0000000152 := by norm_num
      have e2c : (0.042 * 0.36 / 10 ^ 6) * (R * R) ≤
          0.0000000152 * (R * R) :=
        mul_le_mul_of_nonneg_right e2b (mul_nonneg hR0 hR0)
      have e2d : (0.0000000152 : ℝ) * (R * R) = 0.0000000152 * R ^ 2 := by ring
      linarith [e2a, e2c, e2d]
    have e3 : (0.042 * R) * 18 = 0.756 * R := by ring
    have hM : ((Mhi R : ℕ) : ℝ) ≤ 0.36 * R := hMhi_ub
    linarith [e1, e2, hM, e3]
  have hfin : R ^ 2 / 10000 ≤
      (0.019 * R) ^ 2 * (359 / 900 : ℝ) - (1.116 * R + 0.0000000152 * R ^ 2) := by
    have hbig : (30000 : ℝ) ≤ R := by linarith [hR]
    have hRnn : (0 : ℝ) ≤ R := by linarith [hR]
    have hC : (0.0000439 : ℝ) ≤
        (0.019) ^ 2 * (359 / 900) - 1 / 10000 - 0.0000000152 := by norm_num
    have hP : (0 : ℝ) ≤ (R - 30000) * R :=
      mul_nonneg (by linarith [hbig]) hRnn
    nlinarith [hbig, hRnn, hC, hP, sq_nonneg R]
  have hErrNeg : -((0.042 * R) *
      ((∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ))) + ((Mhi R : ℕ) : ℝ)) ≤
      ((copCount R : ℝ)) - (W1 R * W2 R) *
        (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) := by
    have h1 := neg_le_neg hHerr
    have h2 := neg_abs_le (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) *
      (((Acount R d : ℝ) * (Bcount R d : ℝ)) - (W1 R * W2 R) / (d : ℝ) ^ 2))
    linarith [h1, h2, hdiff]
  have hStep1 : (0.019 * R) ^ 2 * (359 / 900 : ℝ) - ((0.042 * R) *
      ((0.36 * R) / 10 ^ 6 + 18) + ((Mhi R : ℕ) : ℝ)) ≤ ((copCount R : ℝ)) := by
    have eA : (0.019 * R) ^ 2 * (359 / 900 : ℝ) ≤
        (W1 R * W2 R) * (359 / 900 : ℝ) := hM2
    have eB : (W1 R * W2 R) * (359 / 900 : ℝ) ≤
        (W1 R * W2 R) *
          (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) := hM3
    have eC : (W1 R * W2 R) *
        (∑ d ∈ Finset.Icc 1 (Mhi R), (moebius d : ℝ) / (d : ℝ) ^ 2) -
        ((0.042 * R) * ((0.36 * R) / 10 ^ 6 + 18) + ((Mhi R : ℕ) : ℝ)) ≤
        ((copCount R : ℝ)) := by
      have hE1 : (0.042 * R) * (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) ≤
          (0.042 * R) * ((0.36 * R) / 10 ^ 6 + 18) := by
        apply mul_le_mul_of_nonneg_left _ _
        · have hH0 : (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) ≤
              ((Mhi R : ℕ) : ℝ) / 10 ^ 6 + 18 := by
            have hb := harmonic_le (Mhi R) hMhi1
            have hl := logMhi_le R hR
            linarith [hb, hl]
          have hM0 : ((Mhi R : ℕ) : ℝ) / 10 ^ 6 ≤ (0.36 * R) / 10 ^ 6 :=
            div_le_div_of_nonneg_right hMhi_ub (by norm_num : (0 : ℝ) ≤ 10 ^ 6)
          linarith [hH0, hM0]
        · have hR0' : (0 : ℝ) ≤ 0.042 * R :=
            mul_nonneg (by norm_num) hR0
          linarith [hR0']
      have hE2 : (0.042 * R) * (∑ d ∈ Finset.Icc 1 (Mhi R), 1 / (d : ℝ)) +
          ((Mhi R : ℕ) : ℝ) ≤
          (0.042 * R) * ((0.36 * R) / 10 ^ 6 + 18) + ((Mhi R : ℕ) : ℝ) := by
        linarith [hE1]
      linarith [hErrNeg, hE2, hdiff]
    linarith [eA, eB, eC]
  have hStep2 : (0.019 * R) ^ 2 * (359 / 900 : ℝ) - (1.116 * R + 0.0000000152 * R ^ 2) ≤
      (0.019 * R) ^ 2 * (359 / 900 : ℝ) -
        ((0.042 * R) * ((0.36 * R) / 10 ^ 6 + 18) + ((Mhi R : ℕ) : ℝ)) := by
    linarith [hEfin]
  linarith [hStep1, hStep2, hfin]

#print axioms WindowMobiusCount.exp_three_gt_ten
#print axioms WindowMobiusCount.log_ten_lt_three
#print axioms WindowMobiusCount.log106_lt
#print axioms WindowMobiusCount.logMhi_le
#print axioms WindowMobiusCount.err_bound
#print axioms WindowMobiusCount.coprime_count_ge

end WindowMobiusCount
