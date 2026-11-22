import EpiFormal.NoShortDimRatio
import EpiFormal.WindowFrostmanDischarge

/-!
# Paper-scale instantiation (`H_j = ⌊Q_j √j⌋`) & non-vacuity witness

Discharges all `H_j` scale, decay, and logarithmic growth hypotheses of
`WindowFrostmanDischarge` for the paper's actual scale sequence
`NoShortDim.H j = ⌊Q_j √j⌋` (from `NoShortDimRatio.lean`), and closes:

1. `Hpaper_inv_sq_tendsto`: `1 / (Hpaper j)² → 0` (from `H_ratio_lo`: `3 j ≤ H_{j+1}/H_j`).
2. `Hpaper_log_le`: `∃ C_H, ∀ j ≥ 3, log (Hpaper (j + 1)) ≤ j log j + C_H * j`
   (from `H_ratio_hi`: `H_{j+1}/H_j ≤ 20 j` + `WindowLogFact.log_factorial_le`).
3. `dimH_ge_one_windows_paper_scale`: `thm:windows` full-dimensional parity (`1 ≤ dimH`),
   using paper cylinder lengths `[2/(25 H_j²), 9/(16 H_j²)]` and `WindowMobiusCount.copCount`.
4. `dimH_ge_half_prescribed_paper_scale`: `thm:windows` prescribed-count (`1/2 ≤ dimH`).
5. `dimH_ge_gamma_no_short_paper_scale` & `dimH_ge_one_of_gamma_family`:
   `thm:no-short-dim` dimension assembly (`1 - η log φ ≤ dimH`, and `η ↓ 0 ⇒ 1 ≤ dimH`),
   using `NoShortDim.gamma_pos` and `NoShortDim.copCountS`.
6. `nonvacuous_factorial_tree_dimH`: constructs an explicit concrete `StoppedTree.TreeData`
   on `[0, 1]` and discharges EVERY hypothesis of `dimH_ge_of_stopped_tree_rpow` with zero
   remaining assumptions, machine-certifying that the Frostman interface is non-vacuous.

Only Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace WindowPaperScale

open MeasureTheory Set Filter Finset ENNReal Metric Real
open scoped NNReal BigOperators Topology MeasureTheory

/-! ### Part 1: Scale properties of the paper's `H_j = ⌊Q_j √j⌋` -/

/-- Real-valued paper scale sequence padded at `j = 0` so `Hpaper j > 0` for all `j`. -/
noncomputable def Hpaper (j : ℕ) : ℝ :=
  max 1 ((NoShortDim.H j : ℕ) : ℝ)

theorem Hpaper_pos (j : ℕ) : 0 < Hpaper j :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem Hpaper_eq {j : ℕ} (hj : 1 ≤ j) : Hpaper j = ((NoShortDim.H j : ℕ) : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((NoShortDim.H j : ℕ) : ℝ) := by
    exact_mod_cast NoShortDim.H_ge_one j hj
  exact max_eq_right h1

/-- Paper scale ratio `R_j = H_{j+1} / H_j`. -/
noncomputable def Rpaper (j : ℕ) : ℝ := Hpaper (j + 1) / Hpaper j

theorem Rpaper_ge_three_mul {j : ℕ} (hj : 1 ≤ j) : 3 * (j : ℝ) ≤ Rpaper j := by
  unfold Rpaper
  rw [Hpaper_eq hj, Hpaper_eq (by omega : 1 ≤ j + 1)]
  exact NoShortDim.H_ratio_lo j hj

theorem Rpaper_ge_ten_pow_six {j : ℕ} (hj : 10 ^ 6 ≤ j) : (10 ^ 6 : ℝ) ≤ Rpaper j := by
  have h1 := Rpaper_ge_three_mul (by omega : 1 ≤ j)
  have h2 : (10 ^ 6 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  linarith

/-- Exponential lower bound `3^(j - 1) ≤ Hpaper j` for all `j ≥ 1`. -/
theorem Hpaper_ge_three_pow {j : ℕ} (hj : 1 ≤ j) : (3 : ℝ) ^ (j - 1) ≤ Hpaper j := by
  induction j, hj using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, pow_zero]
    exact le_max_left _ _
  | succ j hj ih =>
    have hrat := Rpaper_ge_three_mul hj
    have hHj : 0 < Hpaper j := Hpaper_pos j
    have hstep : 3 * (j : ℝ) * Hpaper j ≤ Hpaper (j + 1) := (le_div_iff₀ hHj).mp hrat
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have h3 : 3 * Hpaper j ≤ 3 * (j : ℝ) * Hpaper j := by nlinarith
    have hsub : j + 1 - 1 = (j - 1) + 1 := by omega
    rw [hsub, pow_succ']
    linarith [mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 3)]

/-- Inverse-square decay: `1 / (Hpaper j)² → 0`. -/
theorem Hpaper_inv_sq_tendsto :
    Filter.Tendsto (fun j => 1 / (Hpaper j) ^ 2) Filter.atTop (nhds 0) := by
  have hgeo : Filter.Tendsto (fun j : ℕ => (1 / 9 : ℝ) ^ (j - 1)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun k : ℕ => (1 / 9 : ℝ) ^ k) Filter.atTop (nhds 0) :=
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact h0.comp (Filter.tendsto_sub_atTop_nat 1)
  refine squeeze_zero_norm' (a := fun j : ℕ => (1 / 9 : ℝ) ^ (j - 1)) ?_ hgeo
  rw [Filter.eventually_atTop]
  refine ⟨1, fun j hj => ?_⟩
  have hHpos : 0 < Hpaper j := Hpaper_pos j
  rw [Real.norm_of_nonneg (by positivity)]
  have hpow := Hpaper_ge_three_pow hj
  have hsq : ((3 : ℝ) ^ (j - 1)) ^ 2 ≤ (Hpaper j) ^ 2 := by
    have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (j - 1) := by positivity
    nlinarith
  have hinv : 1 / (Hpaper j) ^ 2 ≤ 1 / ((3 : ℝ) ^ (j - 1)) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  have heq : 1 / ((3 : ℝ) ^ (j - 1)) ^ 2 = (1 / 9 : ℝ) ^ (j - 1) := by
    rw [← pow_mul, mul_comm (j - 1) 2, pow_mul, ← one_div_pow]
    norm_num
  linarith

/-- Factorial upper bound on `Hpaper (j + 1)` from `NoShortDim.H_ratio_hi`. -/
theorem Hpaper_le_fact {j : ℕ} (hj : 3 ≤ j) :
    Hpaper (j + 1) ≤ Hpaper 3 * (20 : ℝ) ^ j * (Nat.factorial j : ℝ) := by
  induction j, hj using Nat.le_induction with
  | base =>
    have hrat := NoShortDim.H_ratio_hi 3 le_rfl
    rw [← Hpaper_eq (by omega : 1 ≤ 3), ← Hpaper_eq (by omega : 1 ≤ 4)] at hrat
    have hH3 : 0 < Hpaper 3 := Hpaper_pos 3
    have hstep : Hpaper 4 ≤ 20 * (3 : ℝ) * Hpaper 3 := (div_le_iff₀ hH3).mp hrat
    have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hfac]
    nlinarith
  | succ j hj ih =>
    have hrat := NoShortDim.H_ratio_hi (j + 1) (by omega)
    rw [← Hpaper_eq (by omega : 1 ≤ j + 1), ← Hpaper_eq (by omega : 1 ≤ j + 2)] at hrat
    have hHj1 : 0 < Hpaper (j + 1) := Hpaper_pos (j + 1)
    have hstep : Hpaper (j + 2) ≤ 20 * ((j + 1 : ℕ) : ℝ) * Hpaper (j + 1) :=
      (div_le_iff₀ hHj1).mp hrat
    have hmul : 20 * ((j + 1 : ℕ) : ℝ) * Hpaper (j + 1) ≤
        20 * ((j + 1 : ℕ) : ℝ) * (Hpaper 3 * (20 : ℝ) ^ j * (Nat.factorial j : ℝ)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have hrw : 20 * ((j + 1 : ℕ) : ℝ) * (Hpaper 3 * (20 : ℝ) ^ j * (Nat.factorial j : ℝ)) =
        Hpaper 3 * (20 : ℝ) ^ (j + 1) * (Nat.factorial (j + 1) : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      ring
    linarith

/-- Logarithmic upper bound `log (Hpaper (j + 1)) ≤ j log j + C_H * j` for `j ≥ 3`. -/
theorem Hpaper_log_le :
    ∃ C_H : ℝ, ∀ j ≥ 3,
      Real.log (Hpaper (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + C_H * (j : ℝ) := by
  refine ⟨|Real.log (Hpaper 3)| + Real.log 20, ?_⟩
  intro j hj
  have hle := Hpaper_le_fact hj
  have hHpos : 0 < Hpaper (j + 1) := Hpaper_pos (j + 1)
  have hH3pos : 0 < Hpaper 3 := Hpaper_pos 3
  have hFpos : (0 : ℝ) < (Nat.factorial j : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
  have hlog : Real.log (Hpaper (j + 1)) ≤
      Real.log (Hpaper 3 * (20 : ℝ) ^ j * (Nat.factorial j : ℝ)) :=
    Real.log_le_log hHpos hle
  rw [Real.log_mul (by positivity) (ne_of_gt hFpos),
    Real.log_mul (ne_of_gt hH3pos) (by positivity),
    Real.log_pow] at hlog
  have hfact := WindowLogFact.log_factorial_le j (by omega)
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    have : 1 ≤ j := by omega
    exact_mod_cast this
  have hH3_le : Real.log (Hpaper 3) ≤ |Real.log (Hpaper 3)| * (j : ℝ) := by
    have h1 := le_abs_self (Real.log (Hpaper 3))
    nlinarith [abs_nonneg (Real.log (Hpaper 3)), hj1]
  linarith

/-! ### Part 2: Paper-scale dimension theorems (`thm:windows` & `thm:no-short-dim`) -/

/-- `thm:windows` (full-dimensional parity construction, `b = 2`) at the paper's actual
    scale `H_j = ⌊Q_j √j⌋` (`Hpaper`), exact cylinder length bounds `[2/(25 H_j²), 9/(16 H_j²)]`,
    and Paper 2 L2446's actual parent-dependent scale `R j u = H_{j+1} / u ≥ (2/5) * Rpaper j`
    (since `u ≤ (5/2) H_j`). -/
theorem dimH_ge_one_windows_paper_scale
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 10 ^ 6 ≤ j0)
    {R : ℕ → (ℝ × ℝ) → ℝ}
    (hR_lo : ∀ j ≥ j0, ∀ u ∈ T.atoms j, (2 / 5 : ℝ) * Rpaper j ≤ R j u)
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      (2 / 25 : ℝ) / (Hpaper j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ (9 / 16 : ℝ) / (Hpaper j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_cop : ∀ j ≥ j0, ∀ u ∈ T.atoms j,
      WindowMobiusCount.copCount (R j u) ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    (1 : ℝ≥0∞) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  obtain ⟨C_H, hHlog⟩ := Hpaper_log_le
  have hRlin : ∀ i ≥ j0, ∀ u ∈ T.atoms i, (6 / 5 : ℝ) * (i : ℝ) ≤ R i u := by
    intro i hi u hu
    have h1 := Rpaper_ge_three_mul (by omega : 1 ≤ i)
    have h2 := hR_lo i hi u hu
    linarith
  have hR106 : ∀ i ≥ j0, ∀ u ∈ T.atoms i, (10 ^ 6 : ℝ) ≤ R i u := by
    intro i hi u hu
    have h1 := hRlin i hi u hu
    have h2 : (10 ^ 6 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (le_trans hj0 hi)
    linarith
  exact WindowFrostmanDischarge.dimH_ge_one_of_coprime_tree
    (by omega : 1 ≤ j0) (c_R := 6 / 5) (d0_c := 2 / 25) (L_c := 9 / 16) (C_H := C_H)
    (by norm_num) (by norm_num) (by norm_num)
    hR106 hRlin Hpaper_pos Hpaper_inv_sq_tendsto
    (fun j hj => hHlog j (by omega))
    hne0 htriv hlen hdisj hchild_mem hchild_cop hdisj_child hnest

/-- `thm:windows` (prescribed-count construction, `b = 1`) at the paper's actual
    scale `H_j = ⌊Q_j √j⌋`: linear branching `B j ≥ c * j` yields `1/2 ≤ dimH`. -/
theorem dimH_ge_half_prescribed_paper_scale
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 3 ≤ j0)
    {B : ℕ → ℕ} (hB1 : ∀ j ≥ j0, 1 ≤ B j)
    {c : ℝ} (hc : 0 < c)
    (hbranch : ∀ i ≥ j0, c * (i : ℝ) ≤ (B i : ℝ))
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      (2 / 25 : ℝ) / (Hpaper j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ (9 / 16 : ℝ) / (Hpaper j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_card : ∀ j ≥ j0, ∀ u ∈ T.atoms j, B j ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    ENNReal.ofReal (1 / 2) ≤ dimH (WindowTreePrune.cantorSet T j0) := by
  obtain ⟨C_H, hHlog⟩ := Hpaper_log_le
  have hdim := WindowFrostmanDischarge.dimH_ge_of_stopped_tree_rpow (b := (1 : ℝ))
    (by omega : 1 ≤ j0) hB1 hc (d0_c := 2 / 25) (L_c := 9 / 16) (C_H := C_H)
    (by norm_num) (by norm_num)
    (fun i hi => by simpa [Real.rpow_one] using hbranch i hi)
    Hpaper_pos Hpaper_inv_sq_tendsto (fun j hj => hHlog j (by omega))
    hne0 htriv hlen hdisj hchild_mem hchild_card hdisj_child hnest
  have hmin : min (1 : ℝ) ((1 : ℝ) / 2) = 1 / 2 := by norm_num
  rwa [hmin] at hdim

/-- Paper 2 L2771 scale lower bound for `thm:no-short-dim`: for `0 < η < 1 / log φ`,
    the effective scale `(2 / (5 φ²)) * Rpaper j * j^(-η log φ)` is bounded below by
    `(6 / (5 φ²)) * j^(1 - η log φ)` and eventually exceeds `10^6`. -/
theorem exists_j0_no_short {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / Real.log Real.goldenRatio) :
    ∃ J0 : ℕ, 3 ≤ J0 ∧
      ∀ j ≥ J0, (10 ^ 6 : ℝ) ≤
        (6 / (5 * Real.goldenRatio ^ 2)) * (j : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by
  set γ : ℝ := 1 - η * Real.log Real.goldenRatio
  have hγpos : 0 < γ := NoShortDim.gamma_pos η hη0 hη1
  have hφpos : 0 < Real.goldenRatio := lt_trans zero_lt_one Real.one_lt_goldenRatio
  set cR : ℝ := 6 / (5 * Real.goldenRatio ^ 2)
  have hcRpos : 0 < cR := by positivity
  set M : ℝ := ((10 ^ 6 : ℝ) / cR) ^ (1 / γ)
  refine ⟨max 3 (Nat.ceil M + 1), le_max_left _ _, ?_⟩
  intro j hj
  have hjM : M ≤ (j : ℝ) := by
    have h1 : Nat.ceil M ≤ j := le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hj)
    have h2 : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    have h3 : (Nat.ceil M : ℝ) ≤ (j : ℝ) := by exact_mod_cast h1
    linarith
  have hMnn : 0 ≤ M := Real.rpow_nonneg (by positivity) _
  have hrpow : M ^ γ ≤ (j : ℝ) ^ γ := Real.rpow_le_rpow hMnn hjM (le_of_lt hγpos)
  have hMγ : M ^ γ = (10 ^ 6 : ℝ) / cR := by
    dsimp only [M]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hγpos), Real.rpow_one]
  rw [hMγ] at hrpow
  have hmul := mul_le_mul_of_nonneg_left hrpow (le_of_lt hcRpos)
  rwa [mul_div_cancel₀ _ (ne_of_gt hcRpos)] at hmul

/-- `thm:no-short-dim` fixed-`η` dimension bound at the paper's actual scale `H_j = ⌊Q_j √j⌋`:
    discharges `c_R = 6 / (5 φ²)` and `R j u ≥ c_R * j^(1 - η log φ)` directly from
    Paper 2 L2771 (`R = H_{j+1} / u' ≥ (2 / (5 φ²)) * Rpaper j * j^(-η log φ)`). -/
theorem dimH_ge_gamma_no_short_paper_scale
    {T : StoppedTree.TreeData} {j0 : ℕ} (hj0 : 3 ≤ j0)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / Real.log Real.goldenRatio)
    (hj0_scale : (10 ^ 6 : ℝ) ≤
      (6 / (5 * Real.goldenRatio ^ 2)) * (j0 : ℝ) ^ (1 - η * Real.log Real.goldenRatio))
    {R : ℕ → (ℝ × ℝ) → ℝ}
    (hR_lo : ∀ j ≥ j0, ∀ u ∈ T.atoms j,
      (2 / (5 * Real.goldenRatio ^ 2)) * Rpaper j *
        (j : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤ R j u)
    (hne0 : (T.atoms j0).Nonempty)
    (htriv : ∀ j ≥ j0, ∀ I ∈ T.atoms j, I.1 < I.2)
    (hlen : ∀ j ≥ j0, ∀ I ∈ T.atoms j,
      (2 / 25 : ℝ) / (Hpaper j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ (9 / 16 : ℝ) / (Hpaper j) ^ 2)
    (hdisj : ∀ j ≥ j0, ∀ I ∈ T.atoms j, ∀ J ∈ T.atoms j, I ≠ J →
      Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2))
    (hchild_mem : ∀ j ≥ j0, ∀ u ∈ T.atoms j, T.child j u ⊆ T.atoms (j + 1))
    (hchild_cop : ∀ j ≥ j0, ∀ u ∈ T.atoms j,
      NoShortDim.copCountS (R j u) ≤ (T.child j u).card)
    (hdisj_child : ∀ j ≥ j0, ∀ u₁ ∈ T.atoms j, ∀ u₂ ∈ T.atoms j, u₁ ≠ u₂ →
      Disjoint (T.child j u₁) (T.child j u₂))
    (hnest : ∀ j ≥ j0, ∀ u ∈ T.atoms j, ∀ c ∈ T.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2) :
    ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) ≤
      dimH (WindowTreePrune.cantorSet T j0) := by
  obtain ⟨C_H, hHlog⟩ := Hpaper_log_le
  have hlogφ : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hφpos : 0 < Real.goldenRatio := lt_trans zero_lt_one Real.one_lt_goldenRatio
  have hγpos : 0 < 1 - η * Real.log Real.goldenRatio := NoShortDim.gamma_pos η hη0 hη1
  have hγle1 : 1 - η * Real.log Real.goldenRatio ≤ 1 := by
    have : 0 < η * Real.log Real.goldenRatio := mul_pos hη0 hlogφ
    linarith
  set cR : ℝ := 6 / (5 * Real.goldenRatio ^ 2)
  have hcR : 0 < cR := by positivity
  have hRpow : ∀ i ≥ j0, ∀ u ∈ T.atoms i,
      cR * (i : ℝ) ^ (1 - η * Real.log Real.goldenRatio) ≤ R i u := by
    intro i hi u hu
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
    have hrat := Rpaper_ge_three_mul (by omega : 1 ≤ i)
    have hlo := hR_lo i hi u hu
    have hcoeff : 0 ≤ (2 / (5 * Real.goldenRatio ^ 2)) *
        (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by positivity
    have hmul : (2 / (5 * Real.goldenRatio ^ 2)) * (3 * (i : ℝ)) *
        (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤ R i u := by
      have h1 : (2 / (5 * Real.goldenRatio ^ 2)) * (3 * (i : ℝ)) *
          (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) ≤
          (2 / (5 * Real.goldenRatio ^ 2)) * Rpaper i *
          (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by
        have h2 := mul_le_mul_of_nonneg_right hrat hcoeff
        linarith
      linarith
    have hrp : (i : ℝ) * (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) =
        (i : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by
      calc (i : ℝ) * (i : ℝ) ^ (-(η * Real.log Real.goldenRatio))
          = (i : ℝ) ^ (1 : ℝ) * (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by
            rw [Real.rpow_one]
        _ = (i : ℝ) ^ (1 + -(η * Real.log Real.goldenRatio)) := (Real.rpow_add hipos _ _).symm
        _ = (i : ℝ) ^ (1 - η * Real.log Real.goldenRatio) := by rw [sub_eq_add_neg]
    have heq : cR * (i : ℝ) ^ (1 - η * Real.log Real.goldenRatio) =
        (2 / (5 * Real.goldenRatio ^ 2)) * (3 * (i : ℝ)) *
        (i : ℝ) ^ (-(η * Real.log Real.goldenRatio)) := by
      rw [← hrp]; dsimp only [cR]; ring
    linarith
  have hR106 : ∀ i ≥ j0, ∀ u ∈ T.atoms i, (10 ^ 6 : ℝ) ≤ R i u := by
    intro i hi u hu
    have hj0_le : (j0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hmono : (j0 : ℝ) ^ (1 - η * Real.log Real.goldenRatio) ≤
        (i : ℝ) ^ (1 - η * Real.log Real.goldenRatio) :=
      Real.rpow_le_rpow (Nat.cast_nonneg j0) hj0_le (le_of_lt hγpos)
    have hmul := mul_le_mul_of_nonneg_left hmono (le_of_lt hcR)
    exact le_trans hj0_scale (le_trans hmul (hRpow i hi u hu))
  have hdim := WindowFrostmanDischarge.dimH_ge_gamma_of_coprimeS_tree
    (by omega : 1 ≤ j0) (d0_c := 2 / 25) (L_c := 9 / 16) (C_H := C_H)
    hcR (by norm_num) (by norm_num) hR106 hRpow
    Hpaper_pos Hpaper_inv_sq_tendsto (fun j hj => hHlog j (by omega))
    hne0 htriv hlen hdisj hchild_mem hchild_cop hdisj_child hnest
  rwa [min_eq_right hγle1] at hdim

/-- Final `η ↓ 0` limit step of `thm:no-short-dim`: if `E` contains subsets of
    Hausdorff dimension `≥ 1 - η log φ` for every `0 < η < 1 / log φ`, then `1 ≤ dimH E`. -/
theorem dimH_ge_one_of_gamma_family {E : Set ℝ}
    (hE : ∀ η : ℝ, 0 < η → η < 1 / Real.log Real.goldenRatio →
      ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) ≤ dimH E) :
    (1 : ℝ≥0∞) ≤ dimH E := by
  have hlogφ : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  apply le_of_forall_lt
  intro r hr
  have hr_ne_top : r ≠ ⊤ := ne_of_lt (lt_trans hr ENNReal.one_lt_top)
  have hr_lt1 : r.toReal < 1 := by
    have h1 := (ENNReal.toReal_lt_toReal hr_ne_top ENNReal.one_ne_top).mpr hr
    simpa using h1
  set η : ℝ := (1 - r.toReal) / (2 * Real.log Real.goldenRatio)
  have hη0 : 0 < η := by
    dsimp only [η]
    exact div_pos (by linarith) (by linarith)
  have hη1 : η < 1 / Real.log Real.goldenRatio := by
    dsimp only [η]
    have hrnn : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    rw [div_lt_div_iff₀ (by linarith) hlogφ]
    nlinarith
  have hγ_gt : r.toReal < 1 - η * Real.log Real.goldenRatio := by
    have hmul : η * Real.log Real.goldenRatio = (1 - r.toReal) / 2 := by
      dsimp only [η]
      field_simp
    linarith
  have hγ_pos : 0 < 1 - η * Real.log Real.goldenRatio :=
    NoShortDim.gamma_pos η hη0 hη1
  have hr_lt_ofReal : r < ENNReal.ofReal (1 - η * Real.log Real.goldenRatio) := by
    rw [← ENNReal.ofReal_toReal hr_ne_top]
    exact (ENNReal.ofReal_lt_ofReal_iff hγ_pos).mpr hγ_gt
  exact lt_of_lt_of_le hr_lt_ofReal (hE η hη0 hη1)

/-! ### Part 3: Concrete non-vacuity witness (factorial subdivision of `[0, 1]`) -/

section NonVacuity

open Classical in
/-- Concrete factorial-subdivision children: splits `[a, b]` into `j` equal subintervals. -/
noncomputable def factChild (j : ℕ) (I : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  (Finset.range j).image (fun k : ℕ =>
    (I.1 + (k : ℝ) * (I.2 - I.1) / (j : ℝ),
     I.1 + ((k + 1 : ℕ) : ℝ) * (I.2 - I.1) / (j : ℝ)))

open Classical in
/-- Level `j ≥ 2` atoms of the factorial subdivision of `[0, 1]`:
    intervals `[m / (j - 1)!, (m + 1) / (j - 1)!]` for `m < (j - 1)!`. -/
noncomputable def factAtoms (j : ℕ) : Finset (ℝ × ℝ) :=
  (Finset.range (Nat.factorial (j - 1))).image (fun m : ℕ =>
    ((m : ℝ) / (Nat.factorial (j - 1) : ℝ),
     ((m + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ)))

/-- Concrete `StoppedTree.TreeData` on `[0, 1]` with branching `B j = j` (`b = 1`). -/
noncomputable def factTree : StoppedTree.TreeData where
  atoms := factAtoms
  child := factChild

/-- Matching scale `Hfact j = √((j - 1)!)` so `1 / (Hfact j)² = 1 / (j - 1)!`. -/
noncomputable def Hfact (j : ℕ) : ℝ :=
  Real.sqrt (Nat.factorial (j - 1) : ℝ)

theorem Hfact_pos (j : ℕ) : 0 < Hfact j :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos (j - 1)))

theorem Hfact_sq (j : ℕ) : (Hfact j) ^ 2 = (Nat.factorial (j - 1) : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)

private theorem fact_Hlim :
    Filter.Tendsto (fun j => 1 / (Hfact j) ^ 2) Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun j : ℕ => (1 : ℝ) / ((j - 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    exact h1.comp (Filter.tendsto_sub_atTop_nat 1)
  refine squeeze_zero_norm' ?_ hinv
  rw [Filter.eventually_atTop]
  refine ⟨2, fun j hj => ?_⟩
  rw [Hfact_sq, Real.norm_of_nonneg (by positivity)]
  have hfac_ge : ((j - 1 : ℕ) : ℝ) ≤ (Nat.factorial (j - 1) : ℝ) := by
    exact_mod_cast Nat.self_le_factorial (j - 1)
  have hj1pos : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by
    have : 0 < j - 1 := by omega
    exact_mod_cast this
  exact one_div_le_one_div_of_le hj1pos hfac_ge

private theorem fact_Hlog : ∀ j ≥ 2,
    Real.log (Hfact (j + 1)) ≤ (j : ℝ) * Real.log (j : ℝ) + (0 : ℝ) * (j : ℝ) := by
  intro j hj
  have hsub : j + 1 - 1 = j := by omega
  rw [Hfact, hsub, Real.log_sqrt (Nat.cast_nonneg _), zero_mul, add_zero]
  have hfac := WindowLogFact.log_factorial_le j (by omega)
  have hnn : 0 ≤ (j : ℝ) * Real.log (j : ℝ) :=
    mul_nonneg (Nat.cast_nonneg j) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j)))
  linarith

private theorem fact_hlen : ∀ j ≥ 2, ∀ I ∈ factTree.atoms j,
    (1 : ℝ) / (Hfact j) ^ 2 ≤ I.2 - I.1 ∧ I.2 - I.1 ≤ (1 : ℝ) / (Hfact j) ^ 2 := by
  classical
  intro j _ I hI
  simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hI
  obtain ⟨m, _, rfl⟩ := hI
  rw [Hfact_sq]
  have hdiff : ((m + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ) -
      (m : ℝ) / (Nat.factorial (j - 1) : ℝ) = 1 / (Nat.factorial (j - 1) : ℝ) := by
    push_cast; ring
  rw [hdiff]
  exact ⟨le_rfl, le_rfl⟩

private theorem fact_htriv : ∀ j ≥ 2, ∀ I ∈ factTree.atoms j, I.1 < I.2 := by
  intro j hj I hI
  have h1 := (fact_hlen j hj I hI).1
  have hpos : (0 : ℝ) < 1 / (Hfact j) ^ 2 := by have := Hfact_pos j; positivity
  linarith

private theorem fact_hdisj : ∀ j ≥ 2, ∀ I ∈ factTree.atoms j, ∀ J ∈ factTree.atoms j,
    I ≠ J → Disjoint (Set.Ioo I.1 I.2) (Set.Ioo J.1 J.2) := by
  classical
  intro j _ I hI J hJ hne
  simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hI hJ
  obtain ⟨m₁, _, rfl⟩ := hI
  obtain ⟨m₂, _, rfl⟩ := hJ
  have hmn : m₁ ≠ m₂ := fun h => hne (by subst h; rfl)
  have hFpos : (0 : ℝ) < (Nat.factorial (j - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos (j - 1))
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rw [Set.mem_Ioo] at hx1 hx2
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hle : ((m₁ + 1 : ℕ) : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hlt
    have hdiv : ((m₁ + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ) ≤
        (m₂ : ℝ) / (Nat.factorial (j - 1) : ℝ) :=
      div_le_div_of_nonneg_right hle (le_of_lt hFpos)
    linarith
  · have hle : ((m₂ + 1 : ℕ) : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hgt
    have hdiv : ((m₂ + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ) ≤
        (m₁ : ℝ) / (Nat.factorial (j - 1) : ℝ) :=
      div_le_div_of_nonneg_right hle (le_of_lt hFpos)
    linarith

private theorem fact_hchild_eq : ∀ j ≥ 2, ∀ m < Nat.factorial (j - 1), ∀ k < j,
    let F : ℝ := (Nat.factorial (j - 1) : ℝ)
    let I : ℝ × ℝ := ((m : ℝ) / F, ((m + 1 : ℕ) : ℝ) / F)
    (I.1 + (k : ℝ) * (I.2 - I.1) / (j : ℝ),
     I.1 + ((k + 1 : ℕ) : ℝ) * (I.2 - I.1) / (j : ℝ)) =
    (((m * j + k : ℕ) : ℝ) / (Nat.factorial j : ℝ),
     (((m * j + k) + 1 : ℕ) : ℝ) / (Nat.factorial j : ℝ)) := by
  intro j hj m _ k _
  have hj_ne : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hF_ne : (Nat.factorial (j - 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac_eq : (Nat.factorial j : ℝ) = (j : ℝ) * (Nat.factorial (j - 1) : ℝ) := by
    have : j = (j - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.factorial_succ]
    push_cast
    have h1 : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]; ring
    rw [h1]
  ext <;> dsimp only <;> rw [hfac_eq] <;> push_cast <;> field_simp <;> ring

private theorem fact_hmem : ∀ j ≥ 2, ∀ I ∈ factTree.atoms (j + 1),
    ∃ P ∈ factTree.atoms j, I ∈ factTree.child j P := by
  classical
  intro j hj I hI
  simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hI
  obtain ⟨r, hr, rfl⟩ := hI
  have hsub : j + 1 - 1 = j := by omega
  rw [hsub] at hr ⊢
  have hfac_eq : Nat.factorial j = j * Nat.factorial (j - 1) := by
    have : j = (j - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.factorial_succ]
    rw [← this]
  have hjpos : 0 < j := by omega
  set m : ℕ := r / j
  set k : ℕ := r % j
  have hk : k < j := Nat.mod_lt r hjpos
  have hr_eq : m * j + k = r := by
    have hdm := Nat.div_add_mod r j
    dsimp only [m, k]
    linarith [mul_comm j (r / j)]
  have hm : m < Nat.factorial (j - 1) := by
    rw [hfac_eq] at hr
    exact Nat.div_lt_of_lt_mul hr
  refine ⟨((m : ℝ) / (Nat.factorial (j - 1) : ℝ),
      ((m + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ)), ?_, ?_⟩
  · simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range]
    exact ⟨m, hm, rfl⟩
  · simp only [factTree, factChild, Finset.mem_image, Finset.mem_range]
    refine ⟨k, hk, ?_⟩
    have heq := fact_hchild_eq j hj m hm k hk
    simpa only [hr_eq] using heq

/-- The Cantor set of `factTree` starting at `j0 = 2` is literally `[0, 1]`. -/
theorem cantorSet_factTree_eq_Icc :
    WindowTreePrune.cantorSet factTree 2 = Set.Icc (0 : ℝ) 1 := by
  classical
  ext x
  constructor
  · intro hx
    have hx2 := Set.mem_iInter.mp (Set.mem_iInter.mp hx 2) le_rfl
    obtain ⟨I, hI, hxI⟩ := Set.mem_iUnion₂.mp hx2
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hI
    obtain ⟨m, hm, rfl⟩ := hI
    have hm0 : m = 0 := by
      have : Nat.factorial (2 - 1) = 1 := by norm_num [Nat.factorial]
      omega
    subst hm0
    simpa [Nat.factorial] using hxI
  · intro hx
    rw [WindowTreePrune.cantorSet, Set.mem_iInter]
    intro j
    rw [Set.mem_iInter]
    intro hj
    set F : ℕ := Nat.factorial (j - 1)
    have hFpos : 0 < F := Nat.factorial_pos (j - 1)
    have hFRpos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hFpos
    by_cases hx1 : x = 1
    · subst hx1
      rw [Set.mem_iUnion₂]
      refine ⟨(((F - 1 : ℕ) : ℝ) / (F : ℝ),
          (((F - 1) + 1 : ℕ) : ℝ) / (F : ℝ)), ?_, ?_⟩
      · simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range]
        exact ⟨F - 1, by omega, rfl⟩
      · rw [Set.mem_Icc]
        have hF1 : ((F - 1) + 1 : ℕ) = F := by omega
        rw [hF1, div_self (ne_of_gt hFRpos)]
        refine ⟨(div_le_one hFRpos).mpr ?_, le_rfl⟩
        exact_mod_cast (by omega : F - 1 ≤ F)
    · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
      set m : ℕ := Nat.floor (x * (F : ℝ))
      have hm_lt : m < F := by
        have hmul : x * (F : ℝ) < (F : ℝ) := by nlinarith
        exact (Nat.floor_lt (mul_nonneg hx.1 (le_of_lt hFRpos))).mpr hmul
      rw [Set.mem_iUnion₂]
      refine ⟨((m : ℝ) / (F : ℝ), ((m + 1 : ℕ) : ℝ) / (F : ℝ)), ?_, ?_⟩
      · simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range]
        exact ⟨m, hm_lt, rfl⟩
      · rw [Set.mem_Icc]
        have hlo : (m : ℝ) ≤ x * (F : ℝ) := Nat.floor_le (mul_nonneg hx.1 (le_of_lt hFRpos))
        have hhi : x * (F : ℝ) < ((m + 1 : ℕ) : ℝ) := by
          push_cast
          exact Nat.lt_floor_add_one _
        exact ⟨(div_le_iff₀ hFRpos).mpr hlo, (le_div_iff₀ hFRpos).mpr (le_of_lt hhi)⟩

/-- Non-vacuity certification (tree branch): ALL hypotheses of
    `dimH_ge_of_stopped_tree_rpow` are jointly satisfied by `factTree` (`j0 = 2`, `b = 1`),
    yielding `ENNReal.ofReal (1 / 2) ≤ dimH (cantorSet factTree 2)` with ZERO extra assumptions. -/
theorem nonvacuous_factorial_tree_dimH :
    ENNReal.ofReal (1 / 2) ≤ dimH (WindowTreePrune.cantorSet factTree 2) := by
  classical
  have hne0 : (factTree.atoms 2).Nonempty := by
    refine ⟨(0, 1), ?_⟩
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range]
    refine ⟨0, by norm_num [Nat.factorial], ?_⟩
    norm_num [Nat.factorial]
  have hchild_mem : ∀ j ≥ 2, ∀ u ∈ factTree.atoms j,
      factTree.child j u ⊆ factTree.atoms (j + 1) := by
    intro j hj u hu c hc
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨m, hm, rfl⟩ := hu
    simp only [factTree, factChild, Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range]
    refine ⟨m * j + k, ?_, ?_⟩
    · have hsub : j + 1 - 1 = j := by omega
      rw [hsub]
      have hfac_eq : Nat.factorial j = j * Nat.factorial (j - 1) := by
        have : j = (j - 1) + 1 := by omega
        conv_lhs => rw [this, Nat.factorial_succ]
        rw [← this]
      rw [hfac_eq]
      have hm1 : m + 1 ≤ Nat.factorial (j - 1) := hm
      nlinarith
    · have hsub : j + 1 - 1 = j := by omega
      rw [hsub]
      exact (fact_hchild_eq j hj m hm k hk).symm
  have hchild_card : ∀ j ≥ 2, ∀ u ∈ factTree.atoms j, j ≤ (factTree.child j u).card := by
    intro j hj u hu
    have htr : u.1 < u.2 := fact_htriv j hj u hu
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hinj : Set.InjOn
        (fun k : ℕ =>
          (u.1 + (k : ℝ) * (u.2 - u.1) / (j : ℝ),
           u.1 + ((k + 1 : ℕ) : ℝ) * (u.2 - u.1) / (j : ℝ)))
        ↑(Finset.range j) := by
      intro k₁ _ k₂ _ heq
      have h1 := congrArg Prod.fst heq
      have hdpos : 0 < u.2 - u.1 := sub_pos.mpr htr
      have hmul : (k₁ : ℝ) * ((u.2 - u.1) / (j : ℝ)) = (k₂ : ℝ) * ((u.2 - u.1) / (j : ℝ)) := by
        linarith [mul_div_assoc (k₁ : ℝ) (u.2 - u.1) (j : ℝ),
          mul_div_assoc (k₂ : ℝ) (u.2 - u.1) (j : ℝ)]
      have hcast : (k₁ : ℝ) = (k₂ : ℝ) :=
        mul_right_cancel₀ (ne_of_gt (div_pos hdpos hjpos)) hmul
      exact_mod_cast hcast
    have hcard : (factTree.child j u).card = j := by
      simp only [factTree, factChild, Finset.card_image_of_injOn hinj, Finset.card_range]
    omega
  have hdisj_child : ∀ j ≥ 2, ∀ u₁ ∈ factTree.atoms j, ∀ u₂ ∈ factTree.atoms j, u₁ ≠ u₂ →
      Disjoint (factTree.child j u₁) (factTree.child j u₂) := by
    intro j hj u₁ hu₁ u₂ hu₂ hne
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hu₁ hu₂
    obtain ⟨m₁, hm₁, rfl⟩ := hu₁
    obtain ⟨m₂, hm₂, rfl⟩ := hu₂
    have hmn : m₁ ≠ m₂ := fun h => hne (by subst h; rfl)
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [factTree, factChild, Finset.mem_image, Finset.mem_range] at hc1 hc2
    obtain ⟨k₁, hk₁, rfl⟩ := hc1
    obtain ⟨k₂, hk₂, heq⟩ := hc2
    have e1 := fact_hchild_eq j hj m₁ hm₁ k₁ hk₁
    have e2 := fact_hchild_eq j hj m₂ hm₂ k₂ hk₂
    have hpair : (((m₁ * j + k₁ : ℕ) : ℝ) / (Nat.factorial j : ℝ),
        (((m₁ * j + k₁) + 1 : ℕ) : ℝ) / (Nat.factorial j : ℝ)) =
        (((m₂ * j + k₂ : ℕ) : ℝ) / (Nat.factorial j : ℝ),
        (((m₂ * j + k₂) + 1 : ℕ) : ℝ) / (Nat.factorial j : ℝ)) := by
      rw [← e1, ← e2, heq]
    have hfst := congrArg Prod.fst hpair
    have hFne : (Nat.factorial j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hcast : ((m₁ * j + k₁ : ℕ) : ℝ) = ((m₂ * j + k₂ : ℕ) : ℝ) :=
      (div_left_inj' hFne).mp hfst
    have hnat : m₁ * j + k₁ = m₂ * j + k₂ := by exact_mod_cast hcast
    have hdiv1 : (m₁ * j + k₁) / j = m₁ := by
      rw [mul_comm m₁ j, Nat.mul_add_div (by omega : 0 < j), Nat.div_eq_of_lt hk₁, add_zero]
    have hdiv2 : (m₂ * j + k₂) / j = m₂ := by
      rw [mul_comm m₂ j, Nat.mul_add_div (by omega : 0 < j), Nat.div_eq_of_lt hk₂, add_zero]
    exact hmn (by rw [← hdiv1, hnat, hdiv2])
  have hnest : ∀ j ≥ 2, ∀ u ∈ factTree.atoms j, ∀ c ∈ factTree.child j u,
      Set.Icc c.1 c.2 ⊆ Set.Icc u.1 u.2 := by
    intro j hj u hu c hc
    have htr : u.1 < u.2 := fact_htriv j hj u hu
    simp only [factTree, factChild, Finset.mem_image, Finset.mem_range] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ j)
    have hlo : 0 ≤ (k : ℝ) * (u.2 - u.1) / (j : ℝ) := by
      have : 0 ≤ u.2 - u.1 := sub_nonneg.mpr (le_of_lt htr)
      positivity
    have hhi : ((k + 1 : ℕ) : ℝ) * (u.2 - u.1) / (j : ℝ) ≤ u.2 - u.1 := by
      rw [div_le_iff₀ hjpos]
      have : 0 ≤ u.2 - u.1 := sub_nonneg.mpr (le_of_lt htr)
      nlinarith
    exact ⟨by linarith, by linarith⟩
  have hdim := WindowFrostmanDischarge.dimH_ge_of_stopped_tree_rpow
    (T := factTree) (j0 := 2) (B := id) (b := 1) (c := 1) (d0_c := 1) (L_c := 1) (C_H := 0)
    (by omega) (fun j hj => by simpa using (by omega : 1 ≤ j))
    (by norm_num) (by norm_num) (by norm_num)
    (fun i _ => by simp)
    Hfact_pos fact_Hlim fact_Hlog hne0 fact_htriv fact_hlen fact_hdisj
    hchild_mem hchild_card hdisj_child hnest
  have hmin : min (1 : ℝ) ((1 : ℝ) / 2) = 1 / 2 := by norm_num
  rwa [hmin] at hdim

/-- Non-vacuity certification (measure branch): ALL hypotheses of `mu_window_cascade_full`
    and `dimH_ge_of_mu_window_cascade` (composing with `mass_distrib_of_local_diam_bound`)
    are jointly satisfied by Lebesgue measure restricted to `[0, 1]` on `factTree`,
    yielding `ENNReal.ofReal (1 / 2) ≤ dimH (cantorSet factTree 2)` with ZERO extra assumptions. -/
theorem nonvacuous_factorial_measure_dimH :
    ENNReal.ofReal (1 / 2) ≤ dimH (WindowTreePrune.cantorSet factTree 2) := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hmu_K : μ (WindowTreePrune.cantorSet factTree 2) = 1 := by
    rw [cantorSet_factTree_eq_Icc, Measure.restrict_apply_self, Real.volume_Icc]
    norm_num
  have hKpos : 0 < μ (WindowTreePrune.cantorSet factTree 2) := by rw [hmu_K]; norm_num
  have hsupp : μ (WindowTreePrune.cantorSet factTree 2)ᶜ = 0 := by
    rw [cantorSet_factTree_eq_Icc,
      Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self, measure_empty]
  have hprob : ∀ V : Set ℝ, μ V ≤ 1 := by
    intro V
    calc μ V ≤ μ Set.univ := measure_mono (Set.subset_univ V)
      _ = volume (Set.Icc (0 : ℝ) 1) := by simp [μ]
      _ = 1 := by rw [Real.volume_Icc]; norm_num
  let m : ℕ → ℝ := fun j => 1 / (Nat.factorial (j - 1) : ℝ)
  let B : ℕ → ℝ := fun j => max 1 (j : ℝ)
  have hB2 : ∀ j ≥ 2, (2 : ℝ) ≤ B j := by
    intro j hj
    have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    exact le_trans hj2 (le_max_right _ _)
  have hBpos : ∀ i, 0 < B i := fun i => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbranch : ∀ i : ℕ, i ≥ 2 → (1 : ℝ) * (i : ℝ) ^ (1 : ℝ) ≤ B i := by
    intro i _
    rw [one_mul, Real.rpow_one]
    exact le_max_right _ _
  have hm0 : ∀ I ∈ factTree.atoms 2, μ (Set.Icc I.1 I.2) ≤ ENNReal.ofReal (m 2) := by
    intro I _
    have hm2 : m 2 = 1 := by simp [m]
    rw [hm2, ENNReal.ofReal_one]
    exact hprob _
  have hm0pos : 0 < m 2 := by simp [m]
  have hmrec : ∀ j ≥ 2, m (j + 1) = m j / B j := by
    intro j hj
    have hBeq : B j = (j : ℝ) := max_eq_right (by exact_mod_cast (by omega : 1 ≤ j))
    rw [hBeq]
    have hsub : j + 1 - 1 = j := by omega
    have hfac : (Nat.factorial j : ℝ) = (j : ℝ) * (Nat.factorial (j - 1) : ℝ) := by
      have : j = (j - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.factorial_succ]
      push_cast
      have h1 : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]; ring
      rw [h1]
    simp only [m, hsub, hfac, div_div, mul_comm]
  have hsub01 : ∀ j ≥ 2, ∀ I ∈ factTree.atoms j, Set.Icc I.1 I.2 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j _ I hI x hx
    simp only [factTree, factAtoms, Finset.mem_image, Finset.mem_range] at hI
    obtain ⟨r, hr, rfl⟩ := hI
    have hFpos : (0 : ℝ) < (Nat.factorial (j - 1) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos (j - 1))
    rw [Set.mem_Icc] at hx ⊢
    have hlo : (0 : ℝ) ≤ (r : ℝ) / (Nat.factorial (j - 1) : ℝ) := by positivity
    have hhi : ((r + 1 : ℕ) : ℝ) / (Nat.factorial (j - 1) : ℝ) ≤ 1 :=
      (div_le_one hFpos).mpr (by exact_mod_cast (by omega : r + 1 ≤ Nat.factorial (j - 1)))
    exact ⟨by linarith, by linarith⟩
  have hsplit : ∀ j ≥ 2, ∀ I ∈ factTree.atoms j, ∀ C ∈ factTree.child j I,
      μ (Set.Icc C.1 C.2) ≤ μ (Set.Icc I.1 I.2) / ENNReal.ofReal (B j) := by
    intro j hj I hI C hC
    have hBeq : B j = (j : ℝ) := max_eq_right (by exact_mod_cast (by omega : 1 ≤ j))
    rw [hBeq]
    have hIsub := hsub01 j hj I hI
    have htr : I.1 < I.2 := fact_htriv j hj I hI
    simp only [factTree, factChild, Finset.mem_image, Finset.mem_range] at hC
    obtain ⟨k, hk, rfl⟩ := hC
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hCsubI : Set.Icc
        (I.1 + (k : ℝ) * (I.2 - I.1) / (j : ℝ))
        (I.1 + ((k + 1 : ℕ) : ℝ) * (I.2 - I.1) / (j : ℝ)) ⊆ Set.Icc I.1 I.2 := by
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ j)
      have hlo : 0 ≤ (k : ℝ) * (I.2 - I.1) / (j : ℝ) := by
        have : 0 ≤ I.2 - I.1 := sub_nonneg.mpr (le_of_lt htr); positivity
      have hhi : ((k + 1 : ℕ) : ℝ) * (I.2 - I.1) / (j : ℝ) ≤ I.2 - I.1 := by
        rw [div_le_iff₀ hjpos]
        have : 0 ≤ I.2 - I.1 := sub_nonneg.mpr (le_of_lt htr); nlinarith
      exact ⟨by linarith, by linarith⟩
    have hCsub01 := Set.Subset.trans hCsubI hIsub
    have hmuI : μ (Set.Icc I.1 I.2) = ENNReal.ofReal (I.2 - I.1) := by
      rw [Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hIsub, Real.volume_Icc]
    have hmuC : μ (Set.Icc (I.1 + (k : ℝ) * (I.2 - I.1) / (j : ℝ))
        (I.1 + ((k + 1 : ℕ) : ℝ) * (I.2 - I.1) / (j : ℝ))) =
        ENNReal.ofReal ((I.2 - I.1) / (j : ℝ)) := by
      rw [Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hCsub01, Real.volume_Icc]
      congr 1
      push_cast; ring
    rw [hmuC, hmuI, ENNReal.ofReal_div_of_pos hjpos]
  have hdim := WindowFrostmanDischarge.dimH_ge_of_mu_window_cascade
    (μ := μ) (T := factTree) (j0 := 2) (m := m) (B := B) (H := Hfact)
    (b := 1) (c := 1) (d0_c := 1) (L_c := 1) (C_H := 0)
    (by omega) (by norm_num) (by norm_num) (by norm_num)
    hKpos hsupp hB2 hBpos hbranch hm0 hm0pos hmrec hsplit fact_hmem
    Hfact_pos fact_Hlim fact_Hlog fact_htriv fact_hlen fact_hdisj hprob
  exact hdim

end NonVacuity

#print axioms WindowPaperScale.Hpaper_pos
#print axioms WindowPaperScale.Hpaper_eq
#print axioms WindowPaperScale.Rpaper_ge_three_mul
#print axioms WindowPaperScale.Rpaper_ge_ten_pow_six
#print axioms WindowPaperScale.Hpaper_ge_three_pow
#print axioms WindowPaperScale.Hpaper_inv_sq_tendsto
#print axioms WindowPaperScale.Hpaper_le_fact
#print axioms WindowPaperScale.Hpaper_log_le
#print axioms WindowPaperScale.dimH_ge_one_windows_paper_scale
#print axioms WindowPaperScale.dimH_ge_half_prescribed_paper_scale
#print axioms WindowPaperScale.exists_j0_no_short
#print axioms WindowPaperScale.dimH_ge_gamma_no_short_paper_scale
#print axioms WindowPaperScale.dimH_ge_one_of_gamma_family
#print axioms WindowPaperScale.cantorSet_factTree_eq_Icc
#print axioms WindowPaperScale.nonvacuous_factorial_tree_dimH
#print axioms WindowPaperScale.nonvacuous_factorial_measure_dimH

end WindowPaperScale
