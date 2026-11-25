import EpiFormal.EulerConvergents

/-!
# Unconditional Core-Axiom Proof of `irrMeasure (Real.exp 1) = 2`

Eliminates the classical `mu_e_eq_two` assumption in `EpiFormal/Measure.lean` by proving
`mu_e_eq_two_proved : irrMeasure (Real.exp 1) = 2` strictly on Lean's three base axioms
(`propext`, `Classical.choice`, `Quot.sound`), using the Hermite-Padé selected convergents
`Psel j / Qsel j` already formalized in `EpiFormal/EulerConvergents.lean`.

## Proof outline
1. **Lower bound (`2 ≤ irrMeasure (Real.exp 1)`)**:
   For every `j ≥ 1`, `abs_deltaSel_lt` yields
   `|e - Psel j / Qsel j| = |deltaSel j| / Qsel j < 1 / (2j · Qsel j^2) < Qsel j^(-2)`.
   Strict monotonicity of `Qsel` on `Ici 1` gives infinitely many approximation pairs at `ν = 2`.
2. **Upper bound (`irrMeasure (Real.exp 1) ≤ 2`)**:
   - From `abs_sum_eq_two` (`Q_j |δ_{j+1}| + Q_{j+1} |δ_j| = 2`) and `Q_{j+2} ≥ 4 Q_j`, we
     obtain the lower bound `|δ_j| ≥ 1 / Q_{j+1}` for every `j ≥ 1`.
   - For any `(p, q) ∈ ℤ × ℕ` with `q > 0`, pick `j ≥ 1` with `Q_j ≤ 4q < Q_{j+1}`.
     * If `P_j q ≠ p Q_j`, then `1 ≤ |P_j q - p Q_j| ≤ Q_j |q e - p| + q |δ_j|` with
       `q |δ_j| ≤ 2q / Q_{j+1} < 1/2`, giving `|e - p/q| > 1 / (8 q^2)`.
     * If `P_j q = p Q_j`, then `p/q = P_j/Q_j`, so
       `|e - p/q| = |δ_j| / Q_j ≥ 1 / (Q_j Q_{j+1}) ≥ 1 / (16 (4j + 3) q^2)`.
     (We also prove `Psel_Qsel_coprime : Int.gcd (Psel j) (Qsel j) = 1` from `sel_determinant`
     and `Qsel_odd`.)
   - Since `2^(j-1) ≤ Q_j ≤ 4q`, for any `ν = 2 + ε > 2` the factor `16 (4j + 3)` is
     asymptotically dominated by `q^ε`, so `apprPairs (Real.exp 1) ν` has bounded denominators
     and is therefore finite.
-/

open Filter Topology Real Set

namespace MuEEqTwo

/-- Coprimality of the selected Euler convergents: `gcd(P_j, Q_j) = 1` for all `j ≥ 1`.
    Follows from `P_j Q_{j+1} - P_{j+1} Q_j = ±2` and `Odd (Qsel j)`. -/
lemma Psel_Qsel_coprime (j : ℕ) (hj : 1 ≤ j) : Int.gcd (Psel j) (Qsel j) = 1 := by
  set d : ℕ := Int.gcd (Psel j) (Qsel j) with hd_def
  have hdP : (d : ℤ) ∣ Psel j := Int.gcd_dvd_left (Psel j) (Qsel j)
  have hdQ : (d : ℤ) ∣ Qsel j := Int.gcd_dvd_right (Psel j) (Qsel j)
  have hd_det : (d : ℤ) ∣ Psel j * Qsel (j + 1) - Psel (j + 1) * Qsel j :=
    dvd_sub (dvd_mul_of_dvd_left hdP _) (dvd_mul_of_dvd_right hdQ _)
  rw [sel_determinant j hj] at hd_det
  have hd_nat : d ∣ (2 * (-1 : ℤ) ^ (j + 1)).natAbs := Int.natCast_dvd.mp hd_det
  have habs2 : (2 * (-1 : ℤ) ^ (j + 1)).natAbs = 2 := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    simp
  rw [habs2] at hd_nat
  have hd_le2 : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd_nat
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_nat (by norm_num)
  have hd_ne2 : d ≠ 2 := by
    intro h2
    rw [h2] at hdQ
    obtain ⟨m, hm⟩ := hdQ
    obtain ⟨k, hk⟩ := Qsel_odd j hj
    omega
  omega

/-- Exponential lower growth of selected denominators: `2^(j-1) ≤ Qsel j` for `j ≥ 1`. -/
lemma two_pow_le_Qsel (j : ℕ) (hj : 1 ≤ j) : (2 : ℤ) ^ (j - 1) ≤ Qsel j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  clear hj
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hstep := Qsel_double_all k
    rw [pow_succ']
    linarith

/-- One-step upper growth of selected denominators: `Qsel (j + 1) ≤ (4j + 3) Qsel j` (`j ≥ 1`). -/
lemma Qsel_succ_le (j : ℕ) (hj : 1 ≤ j) :
    Qsel (j + 1) ≤ (4 * (j : ℤ) + 3) * Qsel j := by
  have hrec := Qsel_rec1 j hj
  have hprev : Qsel (j - 1) ≤ Qsel j := by
    by_cases h1 : j = 1
    · subst h1; simp
    · have hlt := Qsel_lt_succ (j - 1) (by omega)
      rw [show j - 1 + 1 = j by omega] at hlt
      exact hlt.le
  linarith

/-- Exact lower bound on `|deltaSel j|`: `1 / Q_{j+1} ≤ |deltaSel j|` for `j ≥ 1`. -/
lemma inv_Qsel_succ_le_abs_deltaSel (j : ℕ) (hj : 1 ≤ j) :
    1 / (Qsel (j + 1) : ℝ) ≤ |deltaSel j| := by
  have hsum := abs_sum_eq_two j hj
  have hnext := abs_deltaSel_le_two_div (j + 1) (by omega)
  have hQ_pos : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQ1_pos : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hQ2_pos : (0 : ℝ) < (Qsel (j + 2) : ℝ) := by exact_mod_cast Qsel_pos (j + 2) (by omega)
  have hdbl1 : 2 * Qsel j ≤ Qsel (j + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact Qsel_double_all k
  have hdbl2 : 2 * Qsel (j + 1) ≤ Qsel (j + 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact Qsel_double_all (k + 1)
  have h4Q : 4 * (Qsel j : ℝ) ≤ (Qsel (j + 2) : ℝ) := by
    have : 4 * Qsel j ≤ Qsel (j + 2) := by linarith
    exact_mod_cast this
  have hterm_le : (Qsel j : ℝ) * |deltaSel (j + 1)| ≤ 1 / 2 := by
    have h1 : (Qsel j : ℝ) * |deltaSel (j + 1)| ≤ (Qsel j : ℝ) * (2 / (Qsel (j + 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hnext hQ_pos.le
    have h2 : (Qsel j : ℝ) * (2 / (Qsel (j + 2) : ℝ)) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hQ2_pos]
      linarith
    exact h1.trans h2
  rw [div_le_iff₀ hQ1_pos]
  linarith

/-- Every integer `X ≥ 1` lies in a unique bracket `Qsel j ≤ X < Qsel (j + 1)` with `j ≥ 1`. -/
lemma exists_Qsel_bracket (X : ℤ) (hX : 1 ≤ X) :
    ∃ j : ℕ, 1 ≤ j ∧ Qsel j ≤ X ∧ X < Qsel (j + 1) := by
  have aux : ∀ n : ℕ, 1 ≤ n → Qsel 1 ≤ X → X < Qsel n →
      ∃ j : ℕ, 1 ≤ j ∧ Qsel j ≤ X ∧ X < Qsel (j + 1) := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro _ h1 hlt
      by_cases hn0 : n = 0
      · subst hn0; simp at h1 hlt; omega
      · by_cases hlt_n : X < Qsel n
        · exact ih (by omega) h1 hlt_n
        · exact ⟨n, by omega, not_lt.mp hlt_n, hlt⟩
  have hbig : X < Qsel (X.toNat + 2) := by
    have hge : ((X.toNat + 1 : ℕ) + 1 : ℤ) ≤ Qsel ((X.toNat + 1) + 1) := Qsel_ge_index (X.toNat + 1)
    have hXeq : (X.toNat : ℤ) = X := Int.toNat_of_nonneg (by omega)
    rw [show (X.toNat + 1) + 1 = X.toNat + 2 by omega] at hge
    omega
  exact aux (X.toNat + 2) (by omega) (by simpa using hX) hbig

/-- **Unified Diophantine lower bound for `e`**: for every rational `p / q` (`q > 0`),
    there exists `j ≥ 1` with `Qsel j ≤ 4q` and `|e - p/q| ≥ 1 / (16 (4j + 3) q^2)`. -/
lemma abs_exp_sub_rat_ge (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ j : ℕ, 1 ≤ j ∧ Qsel j ≤ 4 * (q : ℤ) ∧
      1 / (16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2) ≤ |Real.exp 1 - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨j, hj1, hQle, hQlt⟩ := exists_Qsel_bracket (4 * (q : ℤ)) (by omega)
  refine ⟨j, hj1, hQle, ?_⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQR : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj1
  have hQ1R : (0 : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hQleR : (Qsel j : ℝ) ≤ 4 * (q : ℝ) := by exact_mod_cast hQle
  have hQltR : 4 * (q : ℝ) < (Qsel (j + 1) : ℝ) := by exact_mod_cast hQlt
  by_cases hdet : Psel j * (q : ℤ) = p * Qsel j
  · have hdetR : (Psel j : ℝ) * (q : ℝ) = (p : ℝ) * (Qsel j : ℝ) := by exact_mod_cast hdet
    have hrat_eq : (p : ℝ) / (q : ℝ) = (Psel j : ℝ) / (Qsel j : ℝ) := by
      field_simp [hqR.ne', hQR.ne']
      linarith
    have hdiff_eq : |Real.exp 1 - (p : ℝ) / (q : ℝ)| = |deltaSel j| / (Qsel j : ℝ) := by
      have h1 : Real.exp 1 - (p : ℝ) / (q : ℝ) = deltaSel j / (Qsel j : ℝ) := by
        rw [hrat_eq]
        unfold deltaSel
        field_simp [hQR.ne']
      rw [h1, abs_div, abs_of_pos hQR]
    have hlb := inv_Qsel_succ_le_abs_deltaSel j hj1
    have hstep1 : 1 / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ)) ≤ |Real.exp 1 - (p : ℝ) / (q : ℝ)| := by
      rw [hdiff_eq]
      calc 1 / ((Qsel j : ℝ) * (Qsel (j + 1) : ℝ))
          = (1 / (Qsel (j + 1) : ℝ)) / (Qsel j : ℝ) := by rw [div_div, mul_comm]
        _ ≤ |deltaSel j| / (Qsel j : ℝ) := div_le_div_of_nonneg_right hlb hQR.le
    have hQ1_le : (Qsel (j + 1) : ℝ) ≤ (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := by
      exact_mod_cast Qsel_succ_le j hj1
    have hprod_le : (Qsel j : ℝ) * (Qsel (j + 1) : ℝ) ≤ 16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2 := by
      have hsq : (Qsel j : ℝ) ^ 2 ≤ 16 * (q : ℝ) ^ 2 := by nlinarith
      calc (Qsel j : ℝ) * (Qsel (j + 1) : ℝ)
          ≤ (Qsel j : ℝ) * ((4 * (j : ℝ) + 3) * (Qsel j : ℝ)) :=
            mul_le_mul_of_nonneg_left hQ1_le hQR.le
        _ = (4 * (j : ℝ) + 3) * (Qsel j : ℝ) ^ 2 := by ring
        _ ≤ (4 * (j : ℝ) + 3) * (16 * (q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = 16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2 := by ring
    exact (one_div_le_one_div_of_le (mul_pos hQR hQ1R) hprod_le).trans hstep1
  · have hne : Psel j * (q : ℤ) - p * Qsel j ≠ 0 := sub_ne_zero.mpr hdet
    have honeZ : (1 : ℤ) ≤ |Psel j * (q : ℤ) - p * Qsel j| := Int.one_le_abs hne
    have honeR : (1 : ℝ) ≤ |(Psel j : ℝ) * (q : ℝ) - (p : ℝ) * (Qsel j : ℝ)| := by
      exact_mod_cast honeZ
    have hid : (Psel j : ℝ) * (q : ℝ) - (p : ℝ) * (Qsel j : ℝ) =
        (Qsel j : ℝ) * ((q : ℝ) * Real.exp 1 - (p : ℝ)) - (q : ℝ) * deltaSel j := by
      unfold deltaSel; ring
    have htri : (1 : ℝ) ≤
        (Qsel j : ℝ) * |(q : ℝ) * Real.exp 1 - (p : ℝ)| + (q : ℝ) * |deltaSel j| := by
      rw [hid] at honeR
      calc (1 : ℝ) ≤ |(Qsel j : ℝ) * ((q : ℝ) * Real.exp 1 - (p : ℝ)) - (q : ℝ) * deltaSel j| :=
            honeR
        _ ≤ |(Qsel j : ℝ) * ((q : ℝ) * Real.exp 1 - (p : ℝ))| + |(q : ℝ) * deltaSel j| :=
            abs_sub _ _
        _ = (Qsel j : ℝ) * |(q : ℝ) * Real.exp 1 - (p : ℝ)| + (q : ℝ) * |deltaSel j| := by
            rw [abs_mul, abs_mul, abs_of_pos hQR, abs_of_pos hqR]
    have hqdelta : (q : ℝ) * |deltaSel j| < 1 / 2 := by
      have h1 : (q : ℝ) * |deltaSel j| ≤ (q : ℝ) * (2 / (Qsel (j + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left (abs_deltaSel_le_two_div j hj1) hqR.le
      have h2 : (q : ℝ) * (2 / (Qsel (j + 1) : ℝ)) < 1 / 2 := by
        rw [mul_div_assoc', div_lt_iff₀ hQ1R]
        linarith
      exact lt_of_le_of_lt h1 h2
    have hqe_eq : |(q : ℝ) * Real.exp 1 - (p : ℝ)| =
        (q : ℝ) * |Real.exp 1 - (p : ℝ) / (q : ℝ)| := by
      have h1 : (q : ℝ) * Real.exp 1 - (p : ℝ) = (q : ℝ) * (Real.exp 1 - (p : ℝ) / (q : ℝ)) := by
        field_simp [hqR.ne']
      rw [h1, abs_mul, abs_of_pos hqR]
    have hhalf_lt : (1 / 2 : ℝ) < 4 * (q : ℝ) ^ 2 * |Real.exp 1 - (p : ℝ) / (q : ℝ)| := by
      have h1 : (1 / 2 : ℝ) < (Qsel j : ℝ) * ((q : ℝ) * |Real.exp 1 - (p : ℝ) / (q : ℝ)|) := by
        rw [← hqe_eq]; linarith
      have h2 : (Qsel j : ℝ) * ((q : ℝ) * |Real.exp 1 - (p : ℝ) / (q : ℝ)|) ≤
          (4 * (q : ℝ)) * ((q : ℝ) * |Real.exp 1 - (p : ℝ) / (q : ℝ)|) :=
        mul_le_mul_of_nonneg_right hQleR (mul_nonneg hqR.le (abs_nonneg _))
      nlinarith
    have h8 : 1 / (8 * (q : ℝ) ^ 2) < |Real.exp 1 - (p : ℝ) / (q : ℝ)| := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 8 * (q : ℝ) ^ 2)]
      linarith
    have hcmp : 1 / (16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2) ≤ 1 / (8 * (q : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hq2 : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    exact hcmp.trans h8.le

/-- Asymptotic domination of linear growth by `(2^ε)^(j - 1)`. -/
lemma exists_poly_le_two_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      16 * (4 * (j : ℝ) + 3) * (4 : ℝ) ^ ε ≤ ((2 : ℝ) ^ ε) ^ (j - 1) := by
  set r : ℝ := (2 : ℝ) ^ ε with hr_def
  have hr1 : 1 < r := Real.one_lt_rpow one_lt_two hε
  have hr0 : 0 < r := by linarith
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / r ^ j) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hr1
  have h2 : Tendsto (fun j : ℕ => (1 : ℝ) / r ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hr1)
  have hcomb : Tendsto
      (fun j : ℕ => (64 * (4 : ℝ) ^ ε * r) * ((j : ℝ) / r ^ j) +
        (48 * (4 : ℝ) ^ ε * r) * ((1 : ℝ) / r ^ j))
      atTop (𝓝 0) := by
    have := (h1.const_mul (64 * (4 : ℝ) ^ ε * r)).add (h2.const_mul (48 * (4 : ℝ) ^ ε * r))
    simpa only [mul_zero, add_zero] using this
  have hev := (hcomb.eventually (gt_mem_nhds one_pos)).and (eventually_ge_atTop 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨J₀, hJ₀⟩ := hev
  refine ⟨J₀, fun j hj => ?_⟩
  obtain ⟨hlt, hj1⟩ := hJ₀ j hj
  have hrj_pos : 0 < r ^ j := pow_pos hr0 j
  have hrew : (64 * (4 : ℝ) ^ ε * r) * ((j : ℝ) / r ^ j) +
      (48 * (4 : ℝ) ^ ε * r) * ((1 : ℝ) / r ^ j) =
      (16 * (4 * (j : ℝ) + 3) * (4 : ℝ) ^ ε * r) / r ^ j := by
    ring
  rw [hrew, div_lt_one hrj_pos] at hlt
  have hpow : r ^ j = r ^ (j - 1) * r := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
  rw [hpow] at hlt
  exact (mul_lt_mul_iff_left₀ hr0).mp hlt |>.le

/-- Lower bound: `2 ≤ irrMeasure (Real.exp 1)`. -/
theorem two_le_mu_e : (2 : ENNReal) ≤ irrMeasure (Real.exp 1) := by
  have hmem : (2 : NNReal) ∈ apprSet (Real.exp 1) := by
    change (apprPairs (Real.exp 1) ((2 : NNReal) : ℝ)).Infinite
    let f : ℕ → ℤ × ℕ := fun j => (Psel j, (Qsel j).toNat)
    have hsub : f '' Set.Ici 1 ⊆ apprPairs (Real.exp 1) ((2 : NNReal) : ℝ) := by
      rintro _ ⟨j, hj, rfl⟩
      have hj1 : 1 ≤ j := hj
      have hQpos : 0 < Qsel j := Qsel_pos j hj1
      have hq_nat : 0 < (Qsel j).toNat := Int.pos_iff_toNat_pos.mp hQpos
      have hq_cast : ((Qsel j).toNat : ℝ) = (Qsel j : ℝ) := by
        have h : ((Qsel j).toNat : ℤ) = Qsel j := Int.toNat_of_nonneg hQpos.le
        exact_mod_cast h
      refine ⟨hq_nat, ?_⟩
      rw [hq_cast]
      have hQR : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast hQpos
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
      have hdiff : |Real.exp 1 - (Psel j : ℝ) / (Qsel j : ℝ)| = |deltaSel j| / (Qsel j : ℝ) := by
        have h1 : Real.exp 1 - (Psel j : ℝ) / (Qsel j : ℝ) = deltaSel j / (Qsel j : ℝ) := by
          unfold deltaSel
          field_simp [hQR.ne']
        rw [h1, abs_div, abs_of_pos hQR]
      rw [hdiff]
      have hlt := abs_deltaSel_lt j hj1
      have hstep : |deltaSel j| / (Qsel j : ℝ) < 1 / (2 * (j : ℝ) * (Qsel j : ℝ) ^ 2) := by
        calc |deltaSel j| / (Qsel j : ℝ)
            < (1 / (2 * (j : ℝ) * (Qsel j : ℝ))) / (Qsel j : ℝ) :=
              div_lt_div_of_pos_right hlt hQR
          _ = 1 / (2 * (j : ℝ) * (Qsel j : ℝ) ^ 2) := by rw [div_div]; ring
      have hstep2 : 1 / (2 * (j : ℝ) * (Qsel j : ℝ) ^ 2) ≤
          (Qsel j : ℝ) ^ (-((2 : NNReal) : ℝ)) := by
        have hrpow : (Qsel j : ℝ) ^ (-((2 : NNReal) : ℝ)) = 1 / (Qsel j : ℝ) ^ 2 := by
          simp only [NNReal.coe_ofNat]
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hQR.le,
            Real.rpow_natCast, one_div]
        rw [hrpow]
        apply one_div_le_one_div_of_le (sq_pos_of_pos hQR)
        have hq2 : 0 ≤ (Qsel j : ℝ) ^ 2 := sq_nonneg _
        nlinarith
      exact lt_of_lt_of_le hstep hstep2
    have hinj : Set.InjOn f (Set.Ici 1) := by
      intro j₁ hj₁ j₂ hj₂ hEq
      have h2 : (Qsel j₁).toNat = (Qsel j₂).toNat := congrArg Prod.snd hEq
      have hQeq : Qsel j₁ = Qsel j₂ := by
        have h1' : ((Qsel j₁).toNat : ℤ) = Qsel j₁ := Int.toNat_of_nonneg (Qsel_pos j₁ hj₁).le
        have h2' : ((Qsel j₂).toNat : ℤ) = Qsel j₂ := Int.toNat_of_nonneg (Qsel_pos j₂ hj₂).le
        omega
      exact Qsel_strictMono.injOn hj₁ hj₂ hQeq
    exact Set.Infinite.mono hsub (Set.Ici_infinite 1 |>.image hinj)
  have hle : ((2 : NNReal) : ENNReal) ≤ irrMeasure (Real.exp 1) :=
    le_sSup ⟨2, hmem, rfl⟩
  simpa using hle

/-- Upper bound: `irrMeasure (Real.exp 1) ≤ 2`. -/
theorem mu_e_le_two : irrMeasure (Real.exp 1) ≤ (2 : ENNReal) := by
  unfold irrMeasure
  refine sSup_le ?_
  rintro _ ⟨ν, hν, rfl⟩
  by_contra hgt
  push Not at hgt
  have h2lt : (2 : ℝ) < (ν : ℝ) := by
    have : ((2 : NNReal) : ENNReal) < (ν : ENNReal) := by simpa using hgt
    exact_mod_cast ENNReal.coe_lt_coe.mp this
  set ε : ℝ := (ν : ℝ) - 2 with hε_def
  have hε : 0 < ε := by linarith
  obtain ⟨J₀, hJ₀⟩ := exists_poly_le_two_rpow ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((16 * (4 * (J₀ : ℝ) + 3)) ^ (1 / ε))
  obtain ⟨⟨p, q⟩, ⟨hq_pos, happrox⟩, hqN⟩ := apprPairs_denom_unbounded hν N
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  obtain ⟨j, hj1, hQle, hlb⟩ := abs_exp_sub_rat_ge p q hq_pos
  have hdom : 16 * (4 * (j : ℝ) + 3) ≤ (q : ℝ) ^ ε := by
    by_cases hjJ : j < J₀
    · have hj_le : (j : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hjJ.le
      have h1 : 16 * (4 * (j : ℝ) + 3) ≤ 16 * (4 * (J₀ : ℝ) + 3) := by linarith
      have hN_lt_q : ((16 * (4 * (J₀ : ℝ) + 3)) ^ (1 / ε)) < (q : ℝ) :=
        lt_trans hN (by exact_mod_cast hqN)
      have hbase_pos : 0 < 16 * (4 * (J₀ : ℝ) + 3) := by positivity
      have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg hbase_pos.le _) hN_lt_q hε
      rw [← Real.rpow_mul hbase_pos.le, one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at hpow
      exact h1.trans hpow.le
    · have hgeJ : J₀ ≤ j := not_lt.mp hjJ
      have hpoly := hJ₀ j hgeJ
      have h2Q : (2 : ℝ) ^ (j - 1) ≤ 4 * (q : ℝ) := by
        have h1 : (2 : ℤ) ^ (j - 1) ≤ 4 * (q : ℤ) := (two_pow_le_Qsel j hj1).trans hQle
        exact_mod_cast h1
      have h2pow_eq : ((2 : ℝ) ^ ε) ^ (j - 1) = ((2 : ℝ) ^ (j - 1)) ^ ε := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ ε) (j - 1), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_natCast (2 : ℝ) (j - 1), ← Real.rpow_mul (by norm_num), mul_comm]
      have hpow_le : ((2 : ℝ) ^ (j - 1)) ^ ε ≤ (q : ℝ) ^ ε * (4 : ℝ) ^ ε := by
        calc ((2 : ℝ) ^ (j - 1)) ^ ε
            ≤ (4 * (q : ℝ)) ^ ε := Real.rpow_le_rpow (by positivity) h2Q hε.le
          _ = (4 : ℝ) ^ ε * (q : ℝ) ^ ε := Real.mul_rpow (by norm_num) hqR.le
          _ = (q : ℝ) ^ ε * (4 : ℝ) ^ ε := mul_comm _ _
      rw [h2pow_eq] at hpoly
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ ε := Real.rpow_pos_of_pos (by norm_num) _
      exact (mul_le_mul_iff_left₀ h4pos).mp (hpoly.trans hpow_le)
  have hden_le : 16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ (ν : ℝ) := by
    have hq_split : (q : ℝ) ^ ε * (q : ℝ) ^ 2 = (q : ℝ) ^ (ν : ℝ) := by
      rw [← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_add hqR]
      congr 1
      dsimp only [ε]
      push_cast; ring
    rw [← hq_split]
    exact mul_le_mul_of_nonneg_right hdom (sq_nonneg _)
  have hcontra : (q : ℝ) ^ (-(ν : ℝ)) ≤ 1 / (16 * (4 * (j : ℝ) + 3) * (q : ℝ) ^ 2) := by
    rw [Real.rpow_neg hqR.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hden_le
  linarith [hcontra.trans hlb]

end MuEEqTwo

/-- **Unconditional Layer A Proof of `μ(e) = 2`**:
    Proves `irrMeasure (Real.exp 1) = 2` strictly on Lean's three base axioms
    (`propext`, `Classical.choice`, `Quot.sound`), without `mu_e_eq_two` or any other axiom. -/
theorem mu_e_eq_two_proved : irrMeasure (Real.exp 1) = 2 :=
  le_antisymm MuEEqTwo.mu_e_le_two MuEEqTwo.two_le_mu_e
