import Mathlib
import EpiFormal.GeneralGrowingRec
import EpiFormal.WeightedExactDim

/-!
# Universal Weighted Approximation Dimensions & Supercritical Collapse (`GeneralGrowingDim`)

This module establishes the second major extension of Paper 2 for **arbitrary** growing-quotient
three-term integer recurrences `Q_{j+1} = A_j Q_j + Q_{j-1}` (`A_j ≥ 2`, `A_j → ∞`):

1. **Universal Subcritical Dimension Distortion (`0 ≤ τ < 1`)**:
   With growth exponent
   `growGammaSup G := limsup_{j→∞} (log A_j / log Q_j) ∈ [0, ∞]`,
   we prove for EVERY `t ≠ ⊤` (`0 ≤ τ < 1`):
   `dimH {x : limsup A_j^τ ‖Q_j x‖ ≤ t} = dimH {x ∈ [0, 1] : A_j^τ ‖Q_j x‖ → 0}`
   `= (1 - τ) / (1 + τ * γ_sup)` (equal to `1` at `τ = 0` even when `γ_sup = ∞`, and equal
   to `0` for all `0 < τ < 1` when `γ_sup = ∞`).
   The lower bound uses a unified two-parameter Cantor construction
   `ε_j = 1 / min(j + 6, A_j^η)` that handles every growth rate from logarithmic to
   super-double-exponential simultaneously.
2. **Universal Supercritical Phase Transition & Secondary Collapse (`τ > 1`)**:
   Always `{growWeightedLambda G τ ≤ t} ⊆ L_G` (`L_G = (ℤ + ℤ θ)/g`) and
   `growRatLattice G = (1/g) ℤ ⊆ {growWeightedLambda G τ ≤ t}`.
   Inside `L_G \ (1/g) ℤ`, `growWeightedSeq τ x j ≍ |n| g A_j^{τ-1} / Q_j`, splitting the
   supercritical regime at `τ_crit = 1 + 1 / γ_sup`:
   - `(τ - 1) γ_sup < 1` ⇒ `{growWeightedLambda G τ ≤ t} = L_G`;
   - `(τ - 1) γ_sup > 1` ⇒ `{growWeightedLambda G τ ≤ t} = growRatLattice G ⊊ L_G`.
3. **Three Concrete Regimes** (`expGrowingRec`, `doubleExpGrowingRec`,
   `superDoubleExpGrowingRec`), including the exact critical boundary `τ = 2` of
   `doubleExpGrowingRec` (`A_j = 2^{2^j}`, `γ_sup = 1`).
-/

open Real Filter Topology Set Finset MeasureTheory Classification SpectralGap DimHCore
  WeightedExactDim GeneralGrowingRec PolyGaugeAndPhaseTransition
open scoped ENNReal NNReal BigOperators

namespace GeneralGrowingDim

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Core Definitions and Denominator Product Bounds -/

/-- Weighted approximation sequence `|A_j|^τ * ‖Q_j x‖`. -/
def growWeightedSeq (G : GrowingRecData) (τ x : ℝ) (j : ℕ) : ℝ :=
  |(G.A j : ℝ)| ^ τ * distToNearestInt ((G.Q j : ℝ) * x)

/-- Weighted limsup exponent `Λ_{G,τ}(x) := limsup_{j→∞} |A_j|^τ * ‖Q_j x‖`. -/
def growWeightedLambda (G : GrowingRecData) (τ x : ℝ) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (growWeightedSeq G τ x j)) atTop

/-- Weighted sub-level set `{x : Λ_{G,τ}(x) ≤ t}`. -/
def growWeightedLevelSet (G : GrowingRecData) (τ : ℝ) (t : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | growWeightedLambda G τ x ≤ t}

/-- Weighted exact limit set `{x ∈ [0, 1] : |A_j|^τ * ‖Q_j x‖ → t}`. -/
def growWeightedExactLimitSet (G : GrowingRecData) (τ t : ℝ) : Set ℝ :=
  {x ∈ Set.Icc (0 : ℝ) 1 | Tendsto (growWeightedSeq G τ x) atTop (nhds t)}

/-- Quotient-to-denominator logarithmic growth exponent `γ_sup = limsup log A_j / log Q_j`. -/
def growGammaSup (G : GrowingRecData) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ))) atTop

/-- Target Hausdorff dimension formula `(1 - τ) / (1 + τ * γ_sup)`, guarded at `τ = 0`. -/
def growTargetDim (G : GrowingRecData) (τ : ℝ) : ℝ≥0∞ :=
  if τ ≤ 0 then 1
  else if 1 ≤ τ then 0
  else ENNReal.ofReal (1 - τ) / (1 + ENNReal.ofReal τ * growGammaSup G)

lemma growWeightedSeq_nonneg (G : GrowingRecData) (τ x : ℝ) (j : ℕ) :
    0 ≤ growWeightedSeq G τ x j :=
  mul_nonneg (Real.rpow_nonneg (abs_nonneg _) τ) (distToNearestInt_nonneg _)

lemma growWeightedSeq_eq_of_ge (G : GrowingRecData) (τ x : ℝ) {j : ℕ} (hj : G.J₀ ≤ j) :
    growWeightedSeq G τ x j = (G.A j : ℝ) ^ τ * distToNearestInt ((G.Q j : ℝ) * x) := by
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  rw [growWeightedSeq, abs_of_pos hA]

lemma grow_Q_ge_three (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j) :
    (3 : ℝ) ≤ (G.Q j : ℝ) := by
  have hQ0 : (1 : ℤ) ≤ G.Q G.J₀ := G.hQ_pos G.J₀
  have hQ1 : (2 : ℤ) * G.Q G.J₀ < G.Q (G.J₀ + 1) := G.grow_Q_succ_ge_two_mul le_rfl
  have hmono : G.Q (G.J₀ + 1) ≤ G.Q j := G.grow_Q_monoOn (by omega) hj
  have h3 : (3 : ℤ) ≤ G.Q j := by linarith
  exact_mod_cast h3

lemma grow_A_ge_two (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    (2 : ℝ) ≤ (G.A j : ℝ) := by
  exact_mod_cast G.hA_ge j hj

lemma grow_log_Q_pos (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j) :
    0 < Real.log (G.Q j : ℝ) := by
  apply Real.log_pos
  linarith [grow_Q_ge_three G hj]

lemma grow_log_A_pos (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < Real.log (G.A j : ℝ) := by
  apply Real.log_pos
  linarith [grow_A_ge_two G hj]

lemma grow_Q_succ_le_two_mul_A_mul (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j) :
    (G.Q (j + 1) : ℝ) ≤ 2 * (G.A j : ℝ) * (G.Q j : ℝ) := by
  have hQpos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hrat := (G.grow_Q_ratio_bounds hj).2
  have hAj : (2 : ℝ) ≤ (G.A j : ℝ) := grow_A_ge_two G (by omega)
  have hstep : (G.Q (j + 1) : ℝ) ≤ ((G.A j : ℝ) + 1) * (G.Q j : ℝ) :=
    ((div_lt_iff₀ hQpos).mp hrat).le
  nlinarith

lemma grow_Q_le_two_pow_mul_prod_A (G : GrowingRecData) {J : ℕ} (hJ : G.J₀ + 1 ≤ J) :
    ∀ n : ℕ, (G.Q (J + n) : ℝ) ≤
      (2 : ℝ) ^ n * (∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * (G.Q J : ℝ) := by
  intro n
  have h1 := G.grow_Q_le_prod_A_add_one hJ n
  have hprod : ∀ m : ℕ, ∏ k ∈ Finset.range m, ((G.A (J + k) : ℝ) + 1) ≤
      (2 : ℝ) ^ m * ∏ k ∈ Finset.range m, (G.A (J + k) : ℝ) := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
      have hAm_pos : (0 : ℝ) ≤ (G.A (J + m) : ℝ) := (G.grow_A_pos (j := J + m) (by omega)).le
      have hAm2 : (G.A (J + m) : ℝ) + 1 ≤ 2 * (G.A (J + m) : ℝ) := by
        linarith [grow_A_ge_two G (j := J + m) (by omega)]
      have hp2_nn : 0 ≤ (2 : ℝ) ^ m * ∏ k ∈ Finset.range m, (G.A (J + k) : ℝ) :=
        mul_nonneg (pow_nonneg (by norm_num) m)
          (Finset.prod_nonneg fun k _ => (G.grow_A_pos (j := J + k) (by omega)).le)
      calc (∏ k ∈ Finset.range m, ((G.A (J + k) : ℝ) + 1)) * ((G.A (J + m) : ℝ) + 1)
          ≤ ((2 : ℝ) ^ m * ∏ k ∈ Finset.range m, (G.A (J + k) : ℝ)) * (2 * (G.A (J + m) : ℝ)) :=
            mul_le_mul ih hAm2 (by linarith) hp2_nn
        _ = (2 : ℝ) ^ m * 2 * ((∏ k ∈ Finset.range m, (G.A (J + k) : ℝ)) * (G.A (J + m) : ℝ)) := by
            ring
  have hQJ : 0 ≤ (G.Q J : ℝ) := by exact_mod_cast (G.hQ_pos J).le
  exact h1.trans (mul_le_mul_of_nonneg_right (hprod n) hQJ)

lemma grow_prod_A_le_Q_simple (G : GrowingRecData) {J : ℕ} (hJ : G.J₀ ≤ J) (n : ℕ) :
    ∏ k ∈ Finset.range n, (G.A (J + k) : ℝ) ≤ (G.Q (J + n) : ℝ) := by
  have h1 := G.grow_prod_A_le_Q hJ n
  have hQJ : (1 : ℝ) ≤ (G.Q J : ℝ) := by exact_mod_cast G.hQ_pos J
  have hprod_nn : 0 ≤ ∏ k ∈ Finset.range n, (G.A (J + k) : ℝ) :=
    Finset.prod_nonneg (fun k _ => (G.grow_A_pos (by omega)).le)
  calc ∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)
      = (∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * 1 := (mul_one _).symm
    _ ≤ (∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * (G.Q J : ℝ) :=
        mul_le_mul_of_nonneg_left hQJ hprod_nn
    _ ≤ (G.Q (J + n) : ℝ) := h1

private lemma exists_subseq_of_frequently {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, P (φ k) := by
  have h' : ∀ a : ℕ, ∃ b : ℕ, a ≤ b ∧ P b := fun a => Filter.frequently_atTop.mp h a
  choose f hf_ge hf_P using h'
  let φ : ℕ → ℕ := Nat.rec (f 0) (fun _ prev => f (prev + 1))
  have hmono : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
    change φ k < f (φ k + 1)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (φ k)) (hf_ge (φ k + 1))
  have hP : ∀ k : ℕ, P (φ k) := fun k => by
    induction k with
    | zero => exact hf_P 0
    | succ k _ => exact hf_P (φ k + 1)
  exact ⟨φ, hmono, hP⟩

private lemma grow_rpow_ge_of_gamma_le (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j)
    {γ : ℝ} (hγ : γ ≤ Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ)) :
    (G.Q j : ℝ) ^ γ ≤ (G.A j : ℝ) := by
  have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos (by omega)
  have hlQ : 0 < Real.log (G.Q j : ℝ) := grow_log_Q_pos G hj
  have hmul : γ * Real.log (G.Q j : ℝ) ≤ Real.log (G.A j : ℝ) := (le_div_iff₀ hlQ).mp hγ
  rw [Real.rpow_def_of_pos hQ_pos]
  calc Real.exp (Real.log (G.Q j : ℝ) * γ)
      = Real.exp (γ * Real.log (G.Q j : ℝ)) := by rw [mul_comm]
    _ ≤ Real.exp (Real.log (G.A j : ℝ)) := Real.exp_le_exp.mpr hmul
    _ = (G.A j : ℝ) := Real.exp_log hA_pos

private lemma grow_rpow_le_of_gamma_ge (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j)
    {γ : ℝ} (hγ : Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) ≤ γ) :
    (G.A j : ℝ) ≤ (G.Q j : ℝ) ^ γ := by
  have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos (by omega)
  have hlQ : 0 < Real.log (G.Q j : ℝ) := grow_log_Q_pos G hj
  have hmul : Real.log (G.A j : ℝ) ≤ γ * Real.log (G.Q j : ℝ) := (div_le_iff₀ hlQ).mp hγ
  rw [Real.rpow_def_of_pos hQ_pos]
  calc (G.A j : ℝ)
      = Real.exp (Real.log (G.A j : ℝ)) := (Real.exp_log hA_pos).symm
    _ ≤ Real.exp (γ * Real.log (G.Q j : ℝ)) := Real.exp_le_exp.mpr hmul
    _ = Real.exp (Real.log (G.Q j : ℝ) * γ) := by rw [mul_comm]

/-! ### Part 2: Universal Subcritical Upper Bound (`0 ≤ τ < 1`) -/

private def uDigits (G : GrowingRecData) (τ T : ℝ) (j : ℕ) : Finset ℤ :=
  Finset.Icc (-⌊(T + 1) * (G.A j : ℝ) ^ (1 - τ)⌋) ⌊(T + 1) * (G.A j : ℝ) ^ (1 - τ)⌋

private lemma mem_uDigits (G : GrowingRecData) {τ T : ℝ} {d : ℤ} {j : ℕ}
    (h : |(d : ℝ)| ≤ (T + 1) * (G.A j : ℝ) ^ (1 - τ)) :
    d ∈ uDigits G τ T j := by
  rw [uDigits, Finset.mem_Icc]
  have habs := abs_le.mp h
  constructor
  · have hl : -d ≤ ⌊(T + 1) * (G.A j : ℝ) ^ (1 - τ)⌋ :=
      Int.le_floor.mpr (by push_cast; linarith)
    omega
  · exact Int.le_floor.mpr habs.2

private lemma card_uDigits_le (G : GrowingRecData) {τ T : ℝ} (hT : 0 ≤ T) (hτ1 : τ ≤ 1)
    {j : ℕ} (hj : G.J₀ ≤ j) :
    ((uDigits G τ T j).card : ℝ) ≤ (2 * T + 3) * (G.A j : ℝ) ^ (1 - τ) := by
  have hA1 : (1 : ℝ) ≤ (G.A j : ℝ) := by linarith [grow_A_ge_two G hj]
  have hpow : (1 : ℝ) ≤ (G.A j : ℝ) ^ (1 - τ) := Real.one_le_rpow hA1 (sub_nonneg.mpr hτ1)
  let B : ℝ := (T + 1) * (G.A j : ℝ) ^ (1 - τ)
  have hB : 0 ≤ B := mul_nonneg (by linarith) (by positivity)
  have hf : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hcard : ((uDigits G τ T j).card : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
    change ((Finset.Icc (-⌊B⌋) ⌊B⌋).card : ℝ) = _
    have hc : ((Int.toNat (⌊B⌋ + 1 - -⌊B⌋) : ℕ) : ℝ) = ((⌊B⌋ + 1 - -⌊B⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊B⌋ + 1 - -⌊B⌋)
    rw [Int.card_Icc, hc]
    push_cast; ring
  rw [hcard]
  have hfloor := Int.floor_le B
  dsimp [B] at hfloor
  nlinarith

private def uTree (G : GrowingRecData) (τ T : ℝ) (N : ℕ) (u v : ℤ) : ℕ → Finset (ℤ × ℤ)
  | 0 => {(u, v)}
  | k + 1 => (uTree G τ T N u v k).biUnion fun p =>
      (uDigits G τ T (N + k + 1)).image fun d => (p.2, G.A (N + k + 1) * p.2 + p.1 + d)

private lemma uTree_card_le (G : GrowingRecData) {τ T : ℝ} (hT : 0 ≤ T) (hτ1 : τ ≤ 1)
    {N : ℕ} (hN : G.J₀ ≤ N) (u v : ℤ) (k : ℕ) :
    ((uTree G τ T N u v k).card : ℝ) ≤
      (2 * T + 3) ^ k * (G.Q (N + k + 1) : ℝ) ^ (1 - τ) := by
  have hprod : ∀ m : ℕ, ((uTree G τ T N u v m).card : ℝ) ≤
      (2 * T + 3) ^ m * ∏ i ∈ Finset.range m, (G.A (N + 1 + i) : ℝ) ^ (1 - τ) := by
    intro m
    induction m with
    | zero => simp [uTree]
    | succ m ih =>
      let j := N + m + 1
      have hcard : (uTree G τ T N u v (m + 1)).card ≤
          (uTree G τ T N u v m).card * (uDigits G τ T j).card := by
        change ((uTree G τ T N u v m).biUnion _).card ≤ _
        exact Finset.card_biUnion_le_card_mul _ _ _ (fun _ _ => Finset.card_image_le)
      have hcard' : ((uTree G τ T N u v (m + 1)).card : ℝ) ≤
          ((uTree G τ T N u v m).card : ℝ) * ((uDigits G τ T j).card : ℝ) := by
        exact_mod_cast hcard
      have hj : G.J₀ ≤ j := by omega
      have hdig := card_uDigits_le G hT hτ1 hj
      calc ((uTree G τ T N u v (m + 1)).card : ℝ)
          ≤ ((uTree G τ T N u v m).card : ℝ) * ((uDigits G τ T j).card : ℝ) := hcard'
        _ ≤ ((2 * T + 3) ^ m * ∏ i ∈ Finset.range m, (G.A (N + 1 + i) : ℝ) ^ (1 - τ)) *
              ((2 * T + 3) * (G.A j : ℝ) ^ (1 - τ)) :=
            mul_le_mul ih hdig (Nat.cast_nonneg _)
              (mul_nonneg (pow_nonneg (by linarith) m)
                (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (G.grow_A_pos (by omega)).le _))
        _ = (2 * T + 3) ^ (m + 1) *
              ∏ i ∈ Finset.range (m + 1), (G.A (N + 1 + i) : ℝ) ^ (1 - τ) := by
            rw [Finset.prod_range_succ, pow_succ]
            change _ = (2 * T + 3) ^ m * (2 * T + 3) *
              ((∏ i ∈ Finset.range m, (G.A (N + 1 + i) : ℝ) ^ (1 - τ)) *
                (G.A (N + 1 + m) : ℝ) ^ (1 - τ))
            have hidx : N + 1 + m = j := by omega
            rw [hidx]; ring
  have hQ_ge : ∏ i ∈ Finset.range k, (G.A (N + 1 + i) : ℝ) ≤ (G.Q (N + k + 1) : ℝ) := by
    have h1 := grow_prod_A_le_Q_simple G (J := N + 1) (by omega) k
    have hidx : N + 1 + k = N + k + 1 := by omega
    rwa [hidx] at h1
  have hrpow : ∏ i ∈ Finset.range k, (G.A (N + 1 + i) : ℝ) ^ (1 - τ) ≤
      (G.Q (N + k + 1) : ℝ) ^ (1 - τ) := by
    rw [Real.finsetProd_rpow (Finset.range k) (fun i => (G.A (N + 1 + i) : ℝ))
      (fun i _ => (G.grow_A_pos (by omega)).le) (1 - τ)]
    exact Real.rpow_le_rpow
      (Finset.prod_nonneg (fun i _ => (G.grow_A_pos (by omega)).le))
      hQ_ge (sub_nonneg.mpr hτ1)
  have hC : 0 ≤ (2 * T + 3) ^ k := pow_nonneg (by linarith) k
  exact (hprod k).trans (mul_le_mul_of_nonneg_left hrpow hC)

private def uTail (G : GrowingRecData) (τ T : ℝ) (N : ℕ) (u v : ℤ) : Set ℝ :=
  {x | round ((G.Q N : ℝ) * x) = u ∧ round ((G.Q (N + 1) : ℝ) * x) = v ∧
    ∀ j ≥ N, growWeightedSeq G τ x j ≤ T}

private def uInterv (G : GrowingRecData) (τ T : ℝ) (m : ℕ) (p : ℤ) : Set ℝ :=
  Set.Icc ((p : ℝ) / (G.Q m : ℝ) - T / ((G.A m : ℝ) ^ τ * (G.Q m : ℝ)))
    ((p : ℝ) / (G.Q m : ℝ) + T / ((G.A m : ℝ) ^ τ * (G.Q m : ℝ)))

private lemma ediam_uInterv_le (G : GrowingRecData) {τ T : ℝ} (_hT : 0 ≤ T) {m : ℕ}
    (hm : G.J₀ ≤ m) (p : ℤ) :
    Metric.ediam (uInterv G τ T m p) ≤
      ENNReal.ofReal (2 * T / ((G.A m : ℝ) ^ τ * (G.Q m : ℝ))) := by
  have hQ : (0 : ℝ) < (G.Q m : ℝ) := by exact_mod_cast G.hQ_pos m
  have hA : (0 : ℝ) < (G.A m : ℝ) := G.grow_A_pos hm
  rw [uInterv, Real.ediam_Icc]
  apply ENNReal.ofReal_le_ofReal
  ring_nf; rfl

private lemma uDefect_bound (G : GrowingRecData) {τ T x : ℝ} (hτ1 : τ ≤ 1)
    {j : ℕ} (hj : G.J₀ ≤ j) (hx : growWeightedSeq G τ x j ≤ T) :
    |(G.growDefect x j : ℝ)| ≤ (T + 1) * (G.A j : ℝ) ^ (1 - τ) := by
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  have hA1 : (1 : ℝ) ≤ (G.A j : ℝ) := by linarith [grow_A_ge_two G hj]
  have hseq : (G.A j : ℝ) ^ τ * |G.growEps x j| ≤ T := by
    rwa [growWeightedSeq_eq_of_ge G τ x hj, ← G.abs_growEps_eq_dist] at hx
  have hmul : (G.A j : ℝ) * |G.growEps x j| ≤ T * (G.A j : ℝ) ^ (1 - τ) := by
    have hsplit : (G.A j : ℝ) = (G.A j : ℝ) ^ (1 - τ) * (G.A j : ℝ) ^ τ := by
      rw [← Real.rpow_add hA, sub_add_cancel, Real.rpow_one]
    calc (G.A j : ℝ) * |G.growEps x j|
        = (G.A j : ℝ) ^ (1 - τ) * ((G.A j : ℝ) ^ τ * |G.growEps x j|) := by nth_rw 1 [hsplit]; ring
      _ ≤ (G.A j : ℝ) ^ (1 - τ) * T :=
          mul_le_mul_of_nonneg_left hseq (Real.rpow_nonneg hA.le _)
      _ = T * (G.A j : ℝ) ^ (1 - τ) := by ring
  have hpow1 : (1 : ℝ) ≤ (G.A j : ℝ) ^ (1 - τ) := Real.one_le_rpow hA1 (sub_nonneg.mpr hτ1)
  rw [G.grow_defect_identity x hj]
  have htri1 : |(G.A j : ℝ) * G.growEps x j - G.growEps x (j + 1)| ≤
      |(G.A j : ℝ) * G.growEps x j| + |G.growEps x (j + 1)| := by
    simpa [sub_eq_add_neg] using
      abs_add_le ((G.A j : ℝ) * G.growEps x j) (-G.growEps x (j + 1))
  have htri : |(G.A j : ℝ) * G.growEps x j - G.growEps x (j + 1) + G.growEps x (j - 1)| ≤
      |(G.A j : ℝ) * G.growEps x j| + |G.growEps x (j + 1)| + |G.growEps x (j - 1)| :=
    (abs_add_le _ _).trans (add_le_add htri1 le_rfl)
  have hAbsmul : |(G.A j : ℝ) * G.growEps x j| = (G.A j : ℝ) * |G.growEps x j| := by
    rw [abs_mul, abs_of_pos hA]
  have h1 := G.abs_growEps_le_half x (j + 1)
  have h2 := G.abs_growEps_le_half x (j - 1)
  linarith

private lemma uTail_cover (G : GrowingRecData) {τ T : ℝ} (hτ1 : τ ≤ 1)
    {N : ℕ} (hN : G.J₀ ≤ N) (u v : ℤ) (k : ℕ) :
    uTail G τ T N u v ⊆
      ⋃ z : (uTree G τ T N u v k : Set (ℤ × ℤ)), uInterv G τ T (N + k + 1) z.1.2 := by
  intro x hx
  let M (j : ℕ) := round ((G.Q j : ℝ) * x)
  have hm : ∀ r : ℕ, (M (N + r), M (N + r + 1)) ∈ uTree G τ T N u v r := by
    intro r
    induction r with
    | zero => simp [M, uTree, hx.1, hx.2.1]
    | succ r ih =>
      have hd := mem_uDigits G (uDefect_bound G hτ1 (by omega : G.J₀ ≤ N + r + 1)
        (hx.2.2 (N + r + 1) (by omega)))
      refine Finset.mem_biUnion.mpr
        ⟨_, ih, Finset.mem_image.mpr ⟨G.growDefect x (N + r + 1), hd, ?_⟩⟩
      apply Prod.ext
      · rfl
      · change G.A (N + r + 1) * M (N + r + 1) + M (N + r) + G.growDefect x (N + r + 1) =
          M (N + (r + 1) + 1)
        unfold GrowingRecData.growDefect
        rw [show N + r + 1 + 1 = N + (r + 1) + 1 by omega, show N + r + 1 - 1 = N + r by omega]
        change _ + (M _ - _ - _) = _
        ring
  refine Set.mem_iUnion.mpr ⟨⟨_, hm k⟩, ?_⟩
  have hjk : G.J₀ ≤ N + k + 1 := by omega
  have hQ : (0 : ℝ) < (G.Q (N + k + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hA : (0 : ℝ) < (G.A (N + k + 1) : ℝ) := G.grow_A_pos hjk
  have hseq := hx.2.2 (N + k + 1) (by omega)
  rw [growWeightedSeq_eq_of_ge G τ x hjk] at hseq
  change (G.A (N + k + 1) : ℝ) ^ τ *
      |(G.Q (N + k + 1) : ℝ) * x - (M (N + k + 1) : ℝ)| ≤ T at hseq
  have hdiff : |x - (M (N + k + 1) : ℝ) / (G.Q (N + k + 1) : ℝ)| ≤
      T / ((G.A (N + k + 1) : ℝ) ^ τ * (G.Q (N + k + 1) : ℝ)) := by
    have hid : x - (M (N + k + 1) : ℝ) / (G.Q (N + k + 1) : ℝ) =
        ((G.Q (N + k + 1) : ℝ) * x - (M (N + k + 1) : ℝ)) / (G.Q (N + k + 1) : ℝ) := by
      field_simp [hQ.ne']
    rw [hid, abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
    calc |(G.Q (N + k + 1) : ℝ) * x - (M (N + k + 1) : ℝ)|
        ≤ T / (G.A (N + k + 1) : ℝ) ^ τ :=
          (le_div_iff₀' (Real.rpow_pos_of_pos hA τ)).mpr hseq
      _ = (T / ((G.A (N + k + 1) : ℝ) ^ τ * (G.Q (N + k + 1) : ℝ))) *
            (G.Q (N + k + 1) : ℝ) := by field_simp
  rw [uInterv, Set.mem_Icc]
  have habs := abs_sub_le_iff.mp hdiff
  constructor <;> linarith

private lemma uTail_measure_zero (G : GrowingRecData) {τ T s γ' : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hT : 0 ≤ T) (hs : 0 < s)
    (hexp : 1 - τ < s * (1 + τ * γ'))
    (hfreq : ∃ᶠ m in atTop, γ' ≤ Real.log (G.A m : ℝ) / Real.log (G.Q m : ℝ))
    (N : ℕ) (hN : G.J₀ ≤ N) (u v : ℤ) :
    μH[s] (uTail G τ T N u v) = 0 := by
  obtain ⟨φ₀, hφ₀_mono, hφ₀_gam⟩ := exists_subseq_of_frequently hfreq
  let φ : ℕ → ℕ := fun n => φ₀ (n + (N + 1))
  have hφ_ge : ∀ n : ℕ, N + 1 ≤ φ n := fun n =>
    le_trans (Nat.le_add_left (N + 1) n) (hφ₀_mono.id_le (n + (N + 1)))
  have hφ_mono : StrictMono φ := fun a b hab => hφ₀_mono (by omega)
  have hφ_gam : ∀ n : ℕ, γ' ≤ Real.log (G.A (φ n) : ℝ) / Real.log (G.Q (φ n) : ℝ) :=
    fun n => hφ₀_gam (n + (N + 1))
  let k_idx : ℕ → ℕ := fun n => φ n - (N + 1)
  have hk_eq : ∀ n : ℕ, N + k_idx n + 1 = φ n := fun n => by
    dsimp [k_idx]; have := hφ_ge n; omega
  let radius : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ)))
  have hrad_zero : Tendsto radius atTop (nhds 0) := by
    have hQ_top : Tendsto (fun n : ℕ => (G.Q (φ n) : ℝ)) atTop atTop :=
      G.grow_Q_tendsto_atTop.comp hφ_mono.tendsto_atTop
    have hdiv0 : Tendsto (fun n : ℕ => 2 * T / (G.Q (φ n) : ℝ)) atTop (nhds 0) := by
      simpa using hQ_top.const_div_atTop (2 * T)
    have hr0 : Tendsto (fun n : ℕ => 2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ)))
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv0
        (Eventually.of_forall fun n => by
          have := G.grow_A_pos (by have := hφ_ge n; omega : G.J₀ ≤ φ n)
          have : (0 : ℝ) < (G.Q (φ n) : ℝ) := by exact_mod_cast G.hQ_pos _
          positivity)
        (Eventually.of_forall fun n => ?_)
      have hj : G.J₀ ≤ φ n := by have := hφ_ge n; omega
      have hA1 : (1 : ℝ) ≤ (G.A (φ n) : ℝ) := by linarith [grow_A_ge_two G hj]
      have hAτ : (1 : ℝ) ≤ (G.A (φ n) : ℝ) ^ τ := Real.one_le_rpow hA1 hτ0
      have hQpos : (0 : ℝ) < (G.Q (φ n) : ℝ) := by exact_mod_cast G.hQ_pos _
      exact div_le_div_of_nonneg_left (by linarith) hQpos (le_mul_of_one_le_left hQpos.le hAτ)
    simpa [radius] using ENNReal.tendsto_ofReal hr0
  let F : ℕ → Finset (ℤ × ℤ) := fun n => uTree G τ T N u v (k_idx n)
  let cov (n : ℕ) (z : (F n : Set (ℤ × ℤ))) := uInterv G τ T (φ n) z.1.2
  have hmain := mkMetric_le_liminf_of_seq_cover (uTail G τ T N u v) radius hrad_zero cov
    (Eventually.of_forall fun n z => ediam_uInterv_le G hT (by have := hφ_ge n; omega) z.1.2)
    (Eventually.of_forall fun n => by
      have hcov := uTail_cover G (T := T) hτ1 hN u v (k_idx n)
      simpa only [cov, hk_eq n] using hcov)
    (fun x => x ^ s) (fun _ _ h => ENNReal.rpow_le_rpow h hs.le)
  let B : ℝ := 2 * T + 3
  have hB1 : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  let δ : ℝ := s * (1 + τ * γ') - (1 - τ)
  have hδ : 0 < δ := sub_pos.mpr hexp
  have hcore : Tendsto (fun m : ℕ => (2 * T) ^ s * (B ^ m / (G.Q m : ℝ) ^ δ)) atTop (nhds 0) := by
    simpa using (G.grow_pow_div_Q_rpow_tendsto_zero hB0 hδ).const_mul ((2 * T) ^ s)
  have hsub0 : Tendsto (fun n : ℕ =>
      ENNReal.ofReal ((2 * T) ^ s * (B ^ (φ n) / (G.Q (φ n) : ℝ) ^ δ))) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal (hcore.comp hφ_mono.tendsto_atTop)
  have hbound : ∀ n : ℕ,
      ((Fintype.card (F n : Set (ℤ × ℤ)) : ℕ) : ℝ≥0∞) * radius n ^ s ≤
        ENNReal.ofReal ((2 * T) ^ s * (B ^ (φ n) / (G.Q (φ n) : ℝ) ^ δ)) := by
    intro n
    have hcard := Fintype.card_coe (F n)
    change (↑(Fintype.card {z // z ∈ F n}) : ℝ≥0∞) * radius n ^ s ≤ _
    rw [hcard]
    have hm_ge : G.J₀ + 1 ≤ φ n := by have := hφ_ge n; omega
    have hQ : (0 : ℝ) < (G.Q (φ n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hA : (0 : ℝ) < (G.A (φ n) : ℝ) := G.grow_A_pos (by omega)
    have hd : 0 ≤ 2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ)) := by positivity
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hd hs.le,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have htree := uTree_card_le G hT hτ1 hN u v (k_idx n)
    rw [hk_eq n] at htree
    have hA_gam : (G.Q (φ n) : ℝ) ^ (τ * γ') ≤ (G.A (φ n) : ℝ) ^ τ := by
      rw [mul_comm τ γ', Real.rpow_mul hQ.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hQ.le _)
        (grow_rpow_ge_of_gamma_le G hm_ge (hφ_gam n)) hτ0
    have hden_ge : (G.Q (φ n) : ℝ) ^ (1 + τ * γ') ≤
        (G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ) := by
      rw [Real.rpow_add hQ, Real.rpow_one, mul_comm (G.Q (φ n) : ℝ) _]
      exact mul_le_mul_of_nonneg_right hA_gam hQ.le
    have hrad_le : (2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ))) ^ s ≤
        (2 * T) ^ s / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ')) := by
      calc (2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ))) ^ s
          ≤ (2 * T / (G.Q (φ n) : ℝ) ^ (1 + τ * γ')) ^ s :=
            Real.rpow_le_rpow hd
              (div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos hQ _) hden_ge) hs.le
        _ = (2 * T) ^ s / ((G.Q (φ n) : ℝ) ^ (1 + τ * γ')) ^ s :=
            Real.div_rpow (mul_nonneg zero_le_two hT) (Real.rpow_nonneg hQ.le _) s
        _ = (2 * T) ^ s / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ')) := by
            rw [← Real.rpow_mul hQ.le, mul_comm (1 + τ * γ') s]
    have hB_pow : B ^ (k_idx n) ≤ B ^ (φ n) := pow_le_pow_right₀ hB1 (Nat.sub_le _ _)
    have hrpow_sub : (G.Q (φ n) : ℝ) ^ (1 - τ) / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ')) =
        1 / (G.Q (φ n) : ℝ) ^ δ := by
      rw [div_eq_div_iff (Real.rpow_pos_of_pos hQ _).ne' (Real.rpow_pos_of_pos hQ _).ne',
        one_mul, ← Real.rpow_add hQ]
      congr 1; dsimp [δ]; ring
    calc ((F n).card : ℝ) * (2 * T / ((G.A (φ n) : ℝ) ^ τ * (G.Q (φ n) : ℝ))) ^ s
        ≤ (B ^ (k_idx n) * (G.Q (φ n) : ℝ) ^ (1 - τ)) *
            ((2 * T) ^ s / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ'))) :=
          mul_le_mul htree hrad_le (Real.rpow_nonneg hd _) (by positivity)
      _ ≤ (B ^ (φ n) * (G.Q (φ n) : ℝ) ^ (1 - τ)) *
            ((2 * T) ^ s / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ'))) := by gcongr
      _ = (2 * T) ^ s * (B ^ (φ n) *
            ((G.Q (φ n) : ℝ) ^ (1 - τ) / (G.Q (φ n) : ℝ) ^ (s * (1 + τ * γ')))) := by ring
      _ = (2 * T) ^ s * (B ^ (φ n) / (G.Q (φ n) : ℝ) ^ δ) := by
          rw [hrpow_sub]; ring
  have hlim := Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hbound)
    (by isBoundedDefault) (by isBoundedDefault)
  rw [hsub0.liminf_eq] at hlim
  exact le_antisymm (hmain.trans hlim) bot_le

private lemma exists_gamma_below_of_target_lt (G : GrowingRecData) {τ s : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (hlt : growTargetDim G τ < ENNReal.ofReal s) :
    ∃ γ' : ℝ, 0 ≤ γ' ∧ 1 - τ < s * (1 + τ * γ') ∧
      ∃ᶠ m in atTop, γ' ≤ Real.log (G.A m : ℝ) / Real.log (G.Q m : ℝ) := by
  have htd : growTargetDim G τ =
      ENNReal.ofReal (1 - τ) / (1 + ENNReal.ofReal τ * growGammaSup G) := by
    have hnot1 : ¬ τ ≤ 0 := not_le.mpr hτ
    have hnot2 : ¬ 1 ≤ τ := not_le.mpr hτ1
    simp [growTargetDim, hnot1, hnot2]
  rw [htd] at hlt
  by_cases htop : growGammaSup G = ⊤
  · refine ⟨max 0 ((1 - τ) / (s * τ) + 1), le_max_left _ _, ?_, ?_⟩
    · have hgt : (1 - τ) / (s * τ) < max 0 ((1 - τ) / (s * τ) + 1) :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hst : 0 < s * τ := mul_pos hs hτ
      have h1 : 1 - τ < s * τ * max 0 ((1 - τ) / (s * τ) + 1) := (div_lt_iff₀' hst).mp hgt
      nlinarith
    · have hltE : ENNReal.ofReal (max 0 ((1 - τ) / (s * τ) + 1)) < growGammaSup G := by
        rw [htop]; exact ENNReal.ofReal_lt_top
      exact (frequently_lt_of_lt_limsup (by isBoundedDefault) hltE).mono fun m hm => by
        by_contra! hnot
        have : ENNReal.ofReal (Real.log (G.A m : ℝ) / Real.log (G.Q m : ℝ)) ≤
            ENNReal.ofReal (max 0 ((1 - τ) / (s * τ) + 1)) := ENNReal.ofReal_le_ofReal hnot.le
        exact not_le.mpr hm this
  · set g : ℝ := (growGammaSup G).toReal
    have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
    have hEq : growGammaSup G = ENNReal.ofReal g := (ENNReal.ofReal_toReal htop).symm
    have hden_pos : 0 < 1 + τ * g := by nlinarith
    have hdiv_lt : (1 - τ) / (1 + τ * g) < s := by
      have hLHS : ENNReal.ofReal (1 - τ) / (1 + ENNReal.ofReal τ * growGammaSup G) =
          ENNReal.ofReal ((1 - τ) / (1 + τ * g)) := by
        rw [hEq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mul hτ.le,
          ← ENNReal.ofReal_add zero_le_one (mul_nonneg hτ.le hg0),
          ENNReal.ofReal_div_of_pos hden_pos]
      rw [hLHS] at hlt
      have htoR := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hlt
      rwa [ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hτ1.le) hden_pos.le),
        ENNReal.toReal_ofReal hs.le] at htoR
    have hmul : 1 - τ < s * (1 + τ * g) := (div_lt_iff₀ hden_pos).mp hdiv_lt
    by_cases hg_pos : g = 0
    · refine ⟨0, le_rfl, by simpa [hg_pos] using hmul, ?_⟩
      exact (eventually_ge_atTop (G.J₀ + 1)).frequently.mono fun m hm =>
        div_nonneg (grow_log_A_pos G (by omega)).le (grow_log_Q_pos G hm).le
    · have hgp : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg_pos)
      let δ := s * (1 + τ * g) - (1 - τ)
      have hδ : 0 < δ := sub_pos.mpr hmul
      let γ' := max (g / 2) (g - δ / (2 * s * τ))
      have hγ'0 : 0 ≤ γ' := le_trans (by linarith) (le_max_left _ _)
      have hγ'_lt : γ' < g := max_lt (by linarith) (by
        have hpos : 0 < δ / (2 * s * τ) := by positivity
        linarith)
      have hst : 0 < s * τ := mul_pos hs hτ
      have hdiff_le : g - γ' ≤ δ / (2 * s * τ) := by
        have := le_max_right (g / 2) (g - δ / (2 * s * τ))
        change g - δ / (2 * s * τ) ≤ γ' at this
        linarith
      have hstrict : 1 - τ < s * (1 + τ * γ') := by
        have hdrop : s * τ * (g - γ') ≤ δ / 2 := by
          calc s * τ * (g - γ') ≤ s * τ * (δ / (2 * s * τ)) :=
                mul_le_mul_of_nonneg_left hdiff_le hst.le
            _ = δ / 2 := by field_simp [hst.ne']
        nlinarith [hdrop, show δ = s * (1 + τ * g) - (1 - τ) from rfl]
      refine ⟨γ', hγ'0, hstrict, ?_⟩
      have hltE : ENNReal.ofReal γ' < growGammaSup G := by
        rw [hEq, ENNReal.ofReal_lt_ofReal_iff hgp]; exact hγ'_lt
      exact (frequently_lt_of_lt_limsup (by isBoundedDefault) hltE).mono fun m hm => by
        by_contra! hnot
        have : ENNReal.ofReal (Real.log (G.A m : ℝ) / Real.log (G.Q m : ℝ)) ≤ ENNReal.ofReal γ' :=
          ENNReal.ofReal_le_ofReal hnot.le
        exact not_le.mpr hm this

/-- **Universal Subcritical Upper Bound (`0 ≤ τ < 1`, `t ≠ ⊤`)**:
for any growing-quotient recurrence, `dimH {Λ_{G,τ} ≤ t} ≤ (1 - τ) / (1 + τ γ_sup)`. -/
theorem dimH_growWeightedLevelSet_le (G : GrowingRecData) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet G τ t) ≤ growTargetDim G τ := by
  rcases eq_or_lt_of_le hτ0 with rfl | hτ
  · have htd : growTargetDim G 0 = 1 := by simp [growTargetDim]
    rw [htd]
    exact GaugeExact.dimH_real_subset_le_one _
  · rw [dimH_eq_iInf]
    apply le_of_forall_gt
    intro d hd
    obtain ⟨s, hs₁, hs₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hd
    have hsp : (0 : ℝ) < (s : ℝ) := by
      have := lt_of_le_of_lt zero_le hs₁
      exact_mod_cast this
    have hltE : growTargetDim G τ < ENNReal.ofReal (s : ℝ) := by
      simpa using hs₁
    obtain ⟨γ', _, hexp, hfreq⟩ := exists_gamma_below_of_target_lt G hτ hτ1 hsp hltE
    let T : ℝ := t.toReal + 1
    have hT0 : 0 < T := by have := ENNReal.toReal_nonneg (a := t); linarith
    have ht_lt : t < ENNReal.ofReal T := by
      have h1 : t = ENNReal.ofReal t.toReal := (ENNReal.ofReal_toReal ht).symm
      rw [h1, ENNReal.ofReal_lt_ofReal_iff hT0]
      linarith
    have hsub : growWeightedLevelSet G τ t ⊆
        ⋃ N : {N : ℕ // G.J₀ ≤ N}, ⋃ uv : ℤ × ℤ, uTail G τ T N.1 uv.1 uv.2 := by
      intro x hx
      have hev := eventually_lt_of_limsup_lt (lt_of_le_of_lt hx ht_lt)
      obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
      let N := max G.J₀ N0
      refine Set.mem_iUnion.mpr ⟨⟨N, le_max_left _ _⟩, Set.mem_iUnion.mpr
        ⟨(round ((G.Q N : ℝ) * x), round ((G.Q (N + 1) : ℝ) * x)), rfl, rfl, fun j hj => ?_⟩⟩
      exact ((ENNReal.ofReal_lt_ofReal_iff hT0).mp (hN0 j ((le_max_right _ _).trans hj))).le
    have hμ0 : μH[(s : ℝ)] (growWeightedLevelSet G τ t) = 0 :=
      measure_mono_null hsub (measure_iUnion_null fun N =>
        measure_iUnion_null fun uv =>
          uTail_measure_zero G hτ.le hτ1.le hT0.le hsp hexp hfreq N.1 N.2 uv.1 uv.2)
    exact (iInf₂_le s hμ0).trans_lt hs₂

/-! ### Part 3: Universal Subcritical Lower Bound (`0 ≤ τ < 1`) and Exact Dimension Equality -/

private structure LowerSpec where
  G : GrowingRecData
  τ : ℝ
  hτ0 : 0 ≤ τ
  hτ1 : τ < 1
  η : ℝ
  hη_pos : 0 < η
  hη_lt : η < (1 - τ) / 4
  γ_hi : ℝ
  hγ_nn : 0 ≤ γ_hi
  J : ℕ
  hJ_ge : G.J₀ + 2 ≤ J
  hA_bound : ∀ j : ℕ, J ≤ j → (G.A j : ℝ) ^ τ ≤ (G.Q j : ℝ) ^ (τ * γ_hi)

private def epsW (L : LowerSpec) (j : ℕ) : ℝ :=
  1 / min ((j : ℝ) + 6) ((L.G.A j : ℝ) ^ L.η)

private def cWidth (L : LowerSpec) (j : ℕ) : ℝ :=
  (1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (-L.τ)

private def cRadW (L : LowerSpec) (j : ℕ) : ℝ :=
  cWidth L j / (L.G.Q j : ℝ)

private def cBranch (L : LowerSpec) (j : ℕ) : ℕ :=
  Nat.floor ((1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ))

private lemma epsW_pos_le_one (L : LowerSpec) {j : ℕ} (hj : L.G.J₀ ≤ j) :
    0 < epsW L j ∧ epsW L j ≤ 1 := by
  have hA1 : (1 : ℝ) ≤ (L.G.A j : ℝ) := by linarith [grow_A_ge_two L.G hj]
  have hAη : 1 ≤ (L.G.A j : ℝ) ^ L.η := Real.one_le_rpow hA1 L.hη_pos.le
  have hj6 : (1 : ℝ) ≤ (j : ℝ) + 6 := by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hmin : 1 ≤ min ((j : ℝ) + 6) ((L.G.A j : ℝ) ^ L.η) := le_min hj6 hAη
  exact ⟨one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hmin),
    div_le_one_of_le₀ hmin (by linarith)⟩

private lemma epsW_ge_neg_eta (L : LowerSpec) {j : ℕ} (hj : L.G.J₀ ≤ j) :
    (L.G.A j : ℝ) ^ (-L.η) ≤ epsW L j := by
  have hA : (0 : ℝ) < (L.G.A j : ℝ) := L.G.grow_A_pos hj
  have hmin_pos : 0 < min ((j : ℝ) + 6) ((L.G.A j : ℝ) ^ L.η) :=
    lt_min (by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]) (Real.rpow_pos_of_pos hA L.η)
  rw [epsW, Real.rpow_neg hA.le, ← one_div]
  exact one_div_le_one_div_of_le hmin_pos (min_le_right _ _)

private lemma inv_epsW_le (L : LowerSpec) (j : ℕ) :
    1 / epsW L j ≤ (j : ℝ) + 6 := by
  unfold epsW; rw [one_div_one_div]; exact min_le_left _ _

private lemma epsW_tendsto_zero (L : LowerSpec) :
    Tendsto (epsW L) atTop (nhds 0) := by
  have hAη : Tendsto (fun j : ℕ => (L.G.A j : ℝ) ^ L.η) atTop atTop :=
    (tendsto_rpow_atTop L.hη_pos).comp L.G.hA_tendsto
  have hj6 : Tendsto (fun j : ℕ => (j : ℝ) + 6) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hmin : Tendsto (fun j : ℕ => min ((j : ℝ) + 6) ((L.G.A j : ℝ) ^ L.η)) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hj6.eventually_ge_atTop b)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hAη.eventually_ge_atTop b)
    exact eventually_atTop.mpr ⟨max N₁ N₂, fun j hj =>
      le_min (hN₁ j (le_trans (le_max_left _ _) hj)) (hN₂ j (le_trans (le_max_right _ _) hj))⟩
  exact hmin.const_div_atTop (1 : ℝ)

private lemma cWidth_pos_le (L : LowerSpec) {j : ℕ} (hj : L.G.J₀ ≤ j) :
    0 < cWidth L j ∧ cWidth L j ≤ 1 / 8 := by
  have hA1 : (1 : ℝ) ≤ (L.G.A j : ℝ) := by linarith [grow_A_ge_two L.G hj]
  have he := epsW_pos_le_one L hj
  have hAneg : (L.G.A j : ℝ) ^ (-L.τ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hA1 (neg_nonpos.mpr L.hτ0)
  have hApos : 0 < (L.G.A j : ℝ) ^ (-L.τ) := Real.rpow_pos_of_pos (L.G.grow_A_pos hj) _
  exact ⟨mul_pos (mul_pos (by norm_num) he.1) hApos,
    by dsimp [cWidth]; nlinarith [he.2, hAneg]⟩

private lemma cRadW_pos (L : LowerSpec) {j : ℕ} (hj : L.G.J₀ ≤ j) : 0 < cRadW L j :=
  div_pos (cWidth_pos_le L hj).1 (by exact_mod_cast L.G.hQ_pos j)

private lemma exists_large_branch_start (L : LowerSpec) :
    ∃ K0 : ℕ, L.J ≤ K0 ∧
      ∀ j : ℕ, K0 ≤ j → 16 ≤ cBranch L j ∧
        (1 / 16 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ) ≤ (cBranch L j : ℝ) := by
  have hsub : 0 < 1 - L.τ - L.η := by linarith [L.hη_lt, L.hτ1]
  have hA : Tendsto (fun j : ℕ => (L.G.A j : ℝ) ^ (1 - L.τ - L.η)) atTop atTop :=
    (tendsto_rpow_atTop hsub).comp L.G.hA_tendsto
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hA.eventually_ge_atTop (16 * 8))
  refine ⟨max L.J N0, le_max_left _ _, fun j hj => ?_⟩
  have hj_J₀ : L.G.J₀ ≤ j := by have := L.hJ_ge; omega
  have hAj : (0 : ℝ) < (L.G.A j : ℝ) := L.G.grow_A_pos hj_J₀
  have hpow_ge : 16 * 8 ≤ (L.G.A j : ℝ) ^ (1 - L.τ - L.η) := hN0 j (le_trans (le_max_right _ _) hj)
  have heps := epsW_ge_neg_eta L hj_J₀
  have hprod_ge : (16 : ℝ) ≤ (1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ) := by
    have hrw : (L.G.A j : ℝ) ^ (-L.η) * (L.G.A j : ℝ) ^ (1 - L.τ) =
        (L.G.A j : ℝ) ^ (1 - L.τ - L.η) := by
      rw [← Real.rpow_add hAj]; congr 1; ring
    have h1 : (1 / 8 : ℝ) * (L.G.A j : ℝ) ^ (1 - L.τ - L.η) ≤
        (1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ) := by
      rw [← hrw]
      have hpos1 : 0 ≤ (1 / 8 : ℝ) * (L.G.A j : ℝ) ^ (1 - L.τ) := by positivity
      calc (1 / 8 : ℝ) * ((L.G.A j : ℝ) ^ (-L.η) * (L.G.A j : ℝ) ^ (1 - L.τ))
          = ((1 / 8 : ℝ) * (L.G.A j : ℝ) ^ (1 - L.τ)) * (L.G.A j : ℝ) ^ (-L.η) := by ring
        _ ≤ ((1 / 8 : ℝ) * (L.G.A j : ℝ) ^ (1 - L.τ)) * epsW L j :=
            mul_le_mul_of_nonneg_left heps hpos1
        _ = (1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ) := by ring
    linarith
  have hb_ge16 : 16 ≤ cBranch L j := Nat.le_floor (by exact_mod_cast hprod_ge)
  have hlt := Nat.lt_floor_add_one ((1 / 8 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ))
  change _ < (cBranch L j : ℝ) + 1 at hlt
  have h16R : (16 : ℝ) ≤ (cBranch L j : ℝ) := by exact_mod_cast hb_ge16
  exact ⟨hb_ge16, by linarith⟩

private structure CantorSpec where
  L : LowerSpec
  K : ℕ
  hK_ge : L.J ≤ K
  hcB_ge : ∀ j : ℕ, K ≤ j → 16 ≤ cBranch L j ∧
    (1 / 16 : ℝ) * epsW L j * (L.G.A j : ℝ) ^ (1 - L.τ) ≤ (cBranch L j : ℝ)

private def cChildInt (C : CantorSpec) (j : ℕ) (k : ℤ) (d : ℕ) : ℤ :=
  Int.ceil (((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) * ((k : ℝ) + cWidth C.L j)) + (d : ℤ)

private abbrev cWord (C : CantorSpec) (n : ℕ) : Type :=
  ∀ i : Fin n, Fin (cBranch C.L (C.K + i.1))

private def cWordCount (C : CantorSpec) (n : ℕ) : ℕ :=
  ∏ i : Fin n, cBranch C.L (C.K + i.1)

private lemma cBranch_pos (C : CantorSpec) (i : ℕ) : 0 < cBranch C.L (C.K + i) := by
  have := (C.hcB_ge (C.K + i) (by omega)).1; omega

private lemma cWordCount_pos (C : CantorSpec) (n : ℕ) : 0 < cWordCount C n :=
  Finset.prod_pos fun i _ => cBranch_pos C i.1

private lemma cWordCount_succ (C : CantorSpec) (n : ℕ) :
    cWordCount C (n + 1) = cWordCount C n * cBranch C.L (C.K + n) := by
  unfold cWordCount; rw [Fin.prod_univ_castSucc]; rfl

private def cPrefix (C : CantorSpec) {m n : ℕ} (hmn : m ≤ n) (w : cWord C n) : cWord C m :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 hmn⟩

private def cCenterInt (C : CantorSpec) : ∀ n : ℕ, cWord C n → ℤ
  | 0, _ => 0
  | n + 1, w => cChildInt C (C.K + n) (cCenterInt C n (fun i => w i.castSucc)) (w ⟨n, by omega⟩).1

private lemma cCenterInt_succ (C : CantorSpec) (n : ℕ) (w : cWord C (n + 1)) :
    cCenterInt C (n + 1) w =
      cChildInt C (C.K + n) (cCenterInt C n (cPrefix C (Nat.le_succ n) w)) (w ⟨n, by omega⟩).1 :=
  rfl

private def cwInterv (C : CantorSpec) (j : ℕ) (k : ℤ) : Set ℝ :=
  Set.Icc (((k : ℝ) + cWidth C.L j) / (C.L.G.Q j : ℝ))
    (((k : ℝ) + 3 * cWidth C.L j) / (C.L.G.Q j : ℝ))

private lemma cwInterv_nonempty (C : CantorSpec) {j : ℕ} (hj : C.L.G.J₀ ≤ j) (k : ℤ) :
    (cwInterv C j k).Nonempty := by
  have hQ : (0 : ℝ) < (C.L.G.Q j : ℝ) := by exact_mod_cast C.L.G.hQ_pos j
  have hw := (cWidth_pos_le C.L hj).1
  refine ⟨((k : ℝ) + cWidth C.L j) / (C.L.G.Q j : ℝ), le_rfl, ?_⟩
  exact div_le_div_of_nonneg_right (by linarith) hQ.le

private lemma cwInterv_isCompact (C : CantorSpec) (j : ℕ) (k : ℤ) : IsCompact (cwInterv C j k) :=
  isCompact_Icc

private lemma cwInterv_isClosed (C : CantorSpec) (j : ℕ) (k : ℤ) : IsClosed (cwInterv C j k) :=
  isClosed_Icc

private lemma cwInterv_dist_of_ne (C : CantorSpec) {j : ℕ} (hj : C.L.G.J₀ ≤ j)
    {k₁ k₂ : ℤ} (hne : k₁ ≠ k₂) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ cwInterv C j k₁)
    (hx₂ : x₂ ∈ cwInterv C j k₂) :
    1 / (2 * (C.L.G.Q j : ℝ)) < |x₁ - x₂| := by
  have hQ : (0 : ℝ) < (C.L.G.Q j : ℝ) := by exact_mod_cast C.L.G.hQ_pos j
  have hw := cWidth_pos_le C.L hj
  have hord : ∀ {a b : ℤ} {y₁ y₂ : ℝ}, a < b →
      y₁ ∈ cwInterv C j a → y₂ ∈ cwInterv C j b →
      1 / (2 * (C.L.G.Q j : ℝ)) < |y₁ - y₂| := fun {a b y₁ y₂} hab hy₁ hy₂ => by
    simp only [cwInterv, Set.mem_Icc] at hy₁ hy₂
    have hk : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hab
    have hdiff : 5 / 8 ≤ (b : ℝ) + cWidth C.L j - ((a : ℝ) + 3 * cWidth C.L j) := by
      linarith [hw.1, hw.2]
    have hgap : (5 / 8 : ℝ) / (C.L.G.Q j : ℝ) ≤ y₂ - y₁ := by
      calc (5 / 8 : ℝ) / (C.L.G.Q j : ℝ)
          ≤ ((b : ℝ) + cWidth C.L j - ((a : ℝ) + 3 * cWidth C.L j)) / (C.L.G.Q j : ℝ) :=
            div_le_div_of_nonneg_right hdiff hQ.le
        _ = ((b : ℝ) + cWidth C.L j) / (C.L.G.Q j : ℝ) -
              ((a : ℝ) + 3 * cWidth C.L j) / (C.L.G.Q j : ℝ) := by ring
        _ ≤ y₂ - y₁ := by linarith [hy₁.2, hy₂.1]
    have hpos : 1 / (2 * (C.L.G.Q j : ℝ)) < (5 / 8 : ℝ) / (C.L.G.Q j : ℝ) := by
      have : (1 / 2 : ℝ) / (C.L.G.Q j : ℝ) < (5 / 8 : ℝ) / (C.L.G.Q j : ℝ) :=
        div_lt_div_of_pos_right (by norm_num) hQ
      linarith [show (1 / 2 : ℝ) / (C.L.G.Q j : ℝ) = 1 / (2 * (C.L.G.Q j : ℝ)) by ring]
    exact lt_of_lt_of_le (lt_of_lt_of_le hpos hgap)
      (le_trans (le_abs_self _) (by rw [abs_sub_comm]))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hord hlt hx₁ hx₂
  · rw [abs_sub_comm]; exact hord hgt hx₂ hx₁

private lemma cwInterv_child_subset (C : CantorSpec) {j : ℕ} (hj : C.K ≤ j) (k : ℤ)
    (d : ℕ) (hd : d < cBranch C.L j) :
    cwInterv C (j + 1) (cChildInt C j k d) ⊆ cwInterv C j k := by
  have hj_J₀ : C.L.G.J₀ + 1 ≤ j := by have := C.L.hJ_ge; have := C.hK_ge; omega
  have hQj : (0 : ℝ) < (C.L.G.Q j : ℝ) := by exact_mod_cast C.L.G.hQ_pos j
  have hQj1 : (0 : ℝ) < (C.L.G.Q (j + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos (j + 1)
  have hj0 : C.L.G.J₀ ≤ j := Nat.le_trans (Nat.le_succ _) hj_J₀
  have hw := cWidth_pos_le C.L hj0
  have hw1 := cWidth_pos_le C.L (Nat.le_succ_of_le hj0)
  let t0 : ℝ := ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) * ((k : ℝ) + cWidth C.L j)
  have hceil_ge : t0 ≤ (Int.ceil t0 : ℝ) := Int.le_ceil t0
  have hceil_lt : (Int.ceil t0 : ℝ) < t0 + 1 := Int.ceil_lt_add_one t0
  have hd_le : (d : ℝ) + 1 ≤ (cBranch C.L j : ℝ) := by exact_mod_cast hd
  have hepsj : 0 < epsW C.L j := (epsW_pos_le_one C.L hj0).1
  have hAj_pos : 0 < (C.L.G.A j : ℝ) := C.L.G.grow_A_pos hj0
  have hb_le : (cBranch C.L j : ℝ) ≤ (1 / 8 : ℝ) * epsW C.L j * (C.L.G.A j : ℝ) ^ (1 - C.L.τ) :=
    Nat.floor_le (mul_nonneg (mul_nonneg (by norm_num) hepsj.le) (Real.rpow_nonneg hAj_pos.le _))
  have hb16 : (16 : ℝ) ≤ (cBranch C.L j : ℝ) := by exact_mod_cast (C.hcB_ge j hj).1
  have hA_gt : (C.L.G.A j : ℝ) < (C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ) :=
    (C.L.G.grow_Q_ratio_bounds hj_J₀).1
  have hAj : (0 : ℝ) < (C.L.G.A j : ℝ) := C.L.G.grow_A_pos (by omega)
  have hAw : 2 * cWidth C.L j * (C.L.G.A j : ℝ) =
      (1 / 4 : ℝ) * epsW C.L j * (C.L.G.A j : ℝ) ^ (1 - C.L.τ) := by
    have hsplit : (C.L.G.A j : ℝ) ^ (-C.L.τ) * (C.L.G.A j : ℝ) =
        (C.L.G.A j : ℝ) ^ (1 - C.L.τ) := by
      calc (C.L.G.A j : ℝ) ^ (-C.L.τ) * (C.L.G.A j : ℝ)
          = (C.L.G.A j : ℝ) ^ (-C.L.τ) * (C.L.G.A j : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (C.L.G.A j : ℝ) ^ (-C.L.τ + 1) := (Real.rpow_add hAj _ _).symm
        _ = (C.L.G.A j : ℝ) ^ (1 - C.L.τ) := by ring_nf
    dsimp [cWidth]
    calc 2 * ((1 / 8 : ℝ) * epsW C.L j * (C.L.G.A j : ℝ) ^ (-C.L.τ)) * (C.L.G.A j : ℝ)
        = (1 / 4 : ℝ) * epsW C.L j * ((C.L.G.A j : ℝ) ^ (-C.L.τ) * (C.L.G.A j : ℝ)) := by ring
      _ = _ := by rw [hsplit]
  have hbig : (cBranch C.L j : ℝ) + 1 ≤
      2 * cWidth C.L j * ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) := by
    have hmul : 2 * cWidth C.L j * (C.L.G.A j : ℝ) ≤
        2 * cWidth C.L j * ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) :=
      mul_le_mul_of_nonneg_left hA_gt.le (by linarith [hw.1])
    linarith [hb_le, hb16, hAw, hmul]
  intro x hx
  simp only [cwInterv, Set.mem_Icc] at hx ⊢
  have hchi : (cChildInt C j k d : ℝ) = (Int.ceil t0 : ℝ) + (d : ℝ) := by
    unfold cChildInt; push_cast; rfl
  constructor
  · have hleft_num : t0 ≤ (cChildInt C j k d : ℝ) + cWidth C.L (j + 1) := by
      rw [hchi]; linarith [hceil_ge, hw1.1, show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    have ht0_eq : t0 / (C.L.G.Q (j + 1) : ℝ) = ((k : ℝ) + cWidth C.L j) / (C.L.G.Q j : ℝ) := by
      dsimp [t0]; field_simp [hQj.ne', hQj1.ne']
    have hL : ((k : ℝ) + cWidth C.L j) / (C.L.G.Q j : ℝ) ≤
        ((cChildInt C j k d : ℝ) + cWidth C.L (j + 1)) / (C.L.G.Q (j + 1) : ℝ) := by
      rw [← ht0_eq]; exact div_le_div_of_nonneg_right hleft_num hQj1.le
    exact hL.trans hx.1
  · have hright_num : (cChildInt C j k d : ℝ) + 3 * cWidth C.L (j + 1) ≤
        ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) * ((k : ℝ) + 3 * cWidth C.L j) := by
      rw [hchi]
      have hmid : (Int.ceil t0 : ℝ) + (d : ℝ) + 3 * cWidth C.L (j + 1) ≤
          t0 + ((cBranch C.L j : ℝ) + 1) := by linarith [hceil_lt, hd_le, hw1.2]
      have hrhs : t0 + 2 * cWidth C.L j * ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) =
          ((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) * ((k : ℝ) + 3 * cWidth C.L j) := by
        dsimp [t0]; ring
      linarith [hbig, hmid, hrhs]
    have hid : (((C.L.G.Q (j + 1) : ℝ) / (C.L.G.Q j : ℝ)) * ((k : ℝ) + 3 * cWidth C.L j)) /
        (C.L.G.Q (j + 1) : ℝ) = ((k : ℝ) + 3 * cWidth C.L j) / (C.L.G.Q j : ℝ) := by
      field_simp [hQj.ne', hQj1.ne']
    have hR : ((cChildInt C j k d : ℝ) + 3 * cWidth C.L (j + 1)) / (C.L.G.Q (j + 1) : ℝ) ≤
        ((k : ℝ) + 3 * cWidth C.L j) / (C.L.G.Q j : ℝ) := by
      rw [← hid]; exact div_le_div_of_nonneg_right hright_num hQj1.le
    exact hx.2.trans hR

private lemma cwInterv_prefix_subset (C : CantorSpec) {m n : ℕ} (hmn : m ≤ n) (w : cWord C n) :
    cwInterv C (C.K + n) (cCenterInt C n w) ⊆
      cwInterv C (C.K + m) (cCenterInt C m (cPrefix C hmn w)) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := by omega
    have hw : cPrefix C hmn w = w := funext fun i => Fin.elim0 i
    rw [hw]
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact subset_rfl
    · have hsub1 : cwInterv C (C.K + (n + 1)) (cCenterInt C (n + 1) w) ⊆
          cwInterv C (C.K + n) (cCenterInt C n (cPrefix C (Nat.le_succ n) w)) := by
        rw [cCenterInt_succ, show C.K + (n + 1) = (C.K + n) + 1 by omega]
        exact cwInterv_child_subset C (by omega) _ _ (w ⟨n, by omega⟩).2
      have hsub2 := ih (Nat.lt_succ_iff.mp hlt) (cPrefix C (Nat.le_succ n) w)
      have hpre : cPrefix C (Nat.lt_succ_iff.mp hlt) (cPrefix C (Nat.le_succ n) w) =
          cPrefix C hmn w := rfl
      rw [hpre] at hsub2
      exact hsub1.trans hsub2

private lemma cCenterInt_injective (C : CantorSpec) (n : ℕ) :
    Function.Injective (cCenterInt C n) := by
  intro w₁ w₂ heq
  by_contra hne
  have hex : ∃ i : Fin n, w₁ i ≠ w₂ i := by
    by_contra! hall; exact hne (funext hall)
  classical
  have hex' : ∃ k : ℕ, ∃ hk : k < n, w₁ ⟨k, hk⟩ ≠ w₂ ⟨k, hk⟩ :=
    let ⟨i, hi⟩ := hex; ⟨i.1, i.2, hi⟩
  let m0 := Nat.find hex'
  obtain ⟨hm0_lt, hm0_ne⟩ := Nat.find_spec hex'
  have hpre_eq : cPrefix C (show m0 ≤ n by omega) w₁ = cPrefix C (show m0 ≤ n by omega) w₂ := by
    funext i
    by_contra hi
    exact Nat.find_min hex' i.2 ⟨lt_trans i.2 hm0_lt, hi⟩
  have hk1_ne : cCenterInt C (m0 + 1) (cPrefix C (show m0 + 1 ≤ n by omega) w₁) ≠
      cCenterInt C (m0 + 1) (cPrefix C (show m0 + 1 ≤ n by omega) w₂) := by
    rw [cCenterInt_succ, cCenterInt_succ]
    have hpre1 : cPrefix C (Nat.le_succ m0) (cPrefix C (show m0 + 1 ≤ n by omega) w₁) =
        cPrefix C (show m0 ≤ n by omega) w₁ := rfl
    have hpre2 : cPrefix C (Nat.le_succ m0) (cPrefix C (show m0 + 1 ≤ n by omega) w₂) =
        cPrefix C (show m0 ≤ n by omega) w₂ := rfl
    rw [hpre1, hpre2, hpre_eq]
    unfold cChildInt
    intro heq_c
    have hd_eq : (w₁ ⟨m0, hm0_lt⟩).1 = (w₂ ⟨m0, hm0_lt⟩).1 := by
      have := Int.add_left_cancel heq_c
      exact_mod_cast this
    exact hm0_ne (Fin.ext hd_eq)
  have hsub1 := cwInterv_prefix_subset C (show m0 + 1 ≤ n by omega) w₁
  have hsub2 := cwInterv_prefix_subset C (show m0 + 1 ≤ n by omega) w₂
  rw [heq] at hsub1
  have hjKn : C.L.G.J₀ ≤ C.K + n := by have := C.L.hJ_ge; have := C.hK_ge; omega
  have hjKm : C.L.G.J₀ ≤ C.K + (m0 + 1) := by have := C.L.hJ_ge; have := C.hK_ge; omega
  obtain ⟨x, hx⟩ := cwInterv_nonempty C hjKn (cCenterInt C n w₂)
  have hgap := cwInterv_dist_of_ne C hjKm hk1_ne (hsub1 hx) (hsub2 hx)
  rw [sub_self, abs_zero] at hgap
  have hQpos : (0 : ℝ) < (C.L.G.Q (C.K + (m0 + 1)) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
  linarith [show (0 : ℝ) < 1 / (2 * (C.L.G.Q (C.K + (m0 + 1)) : ℝ)) by positivity]

private lemma card_prefix_fiber_mul (C : CantorSpec) (n N : ℕ) (h : n ≤ N) (u : cWord C n) :
    (Finset.univ.filter (fun w : cWord C N => cPrefix C h w = u)).card * cWordCount C n =
      cWordCount C N := by
  let b : ℕ → ℕ := fun k => cBranch C.L (C.K + k)
  change (Finset.univ.filter (fun w : ∀ i : Fin N, Fin (b i.1) =>
    (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)).card * (∏ i : Fin n, b i.1) =
    ∏ i : Fin N, b i.1
  induction N with
  | zero =>
    obtain rfl : n = 0 := by omega
    have hcard : (Finset.univ.filter (fun w : ∀ i : Fin 0, Fin (b i.1) =>
        (fun i : Fin 0 => w ⟨i.1, i.2⟩) = u)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨u, Finset.ext fun w => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hcard, one_mul]
  | succ N ih =>
    rcases eq_or_lt_of_le h with rfl | hlt
    · have hcard : (Finset.univ.filter (fun w : ∀ i : Fin (N + 1), Fin (b i.1) =>
          (fun i : Fin (N + 1) => w ⟨i.1, i.2⟩) = u)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨u, Finset.ext fun w => ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hcard, one_mul]
    · have h' : n ≤ N := Nat.lt_succ_iff.mp hlt
      specialize ih h'
      let e : (∀ i : Fin (N + 1), Fin (b i.1)) ≃
          (∀ i : Fin N, Fin (b i.1)) × Fin (b N) :=
        { toFun := fun w => (fun i => w i.castSucc, w (Fin.last N))
          invFun := fun p => Fin.lastCases p.2 p.1
          left_inv := fun w => funext fun j => by
            refine Fin.lastCases ?_ (fun j => ?_) j
            · exact Fin.lastCases_last
            · exact Fin.lastCases_castSucc j
          right_inv := fun p => by
            apply Prod.ext
            · funext j; dsimp only; exact Fin.lastCases_castSucc j
            · dsimp only; exact Fin.lastCases_last }
      have hbij : (Finset.univ.filter (fun w : (∀ i : Fin (N + 1), Fin (b i.1)) =>
            (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)).card =
          ((Finset.univ.filter (fun w : (∀ i : Fin N, Fin (b i.1)) =>
            (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h'⟩) = u)) ×ˢ
            (Finset.univ : Finset (Fin (b N)))).card := by
        apply Finset.card_bij (fun w _ => e w)
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
            and_true] at hw ⊢
          exact hw
        · intro w₁ _ w₂ _ heq; exact e.injective heq
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
            and_true] at hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          funext i
          have hcast : e.symm p ⟨i.1, lt_of_lt_of_le i.2 h⟩ =
              p.1 ⟨i.1, lt_of_lt_of_le i.2 h'⟩ := by
            change Fin.lastCases (motive := fun j : Fin (N + 1) => Fin (b j.1))
              p.2 (fun j => p.1 j) (⟨i.1, lt_of_lt_of_le i.2 h'⟩ : Fin N).castSucc =
              p.1 ⟨i.1, lt_of_lt_of_le i.2 h'⟩
            exact Fin.lastCases_castSucc (⟨i.1, lt_of_lt_of_le i.2 h'⟩ : Fin N)
          rw [hcast]
          exact congrFun hp i
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin, Fin.prod_univ_castSucc]
      calc (Finset.univ.filter (fun w : ∀ i : Fin N, Fin (b i.1) =>
              (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h'⟩) = u)).card *
              b N * (∏ i : Fin n, b i.1)
          = ((Finset.univ.filter (fun w : ∀ i : Fin N, Fin (b i.1) =>
              (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h'⟩) = u)).card *
              (∏ i : Fin n, b i.1)) * b N := by ring
        _ = (∏ i : Fin N, b i.1) * b N := by rw [ih]

private def cwLevel (C : CantorSpec) (n : ℕ) : Set ℝ :=
  ⋃ w : cWord C n, cwInterv C (C.K + n) (cCenterInt C n w)

private def cwCantorSet (C : CantorSpec) : Set ℝ :=
  ⋂ n : ℕ, cwLevel C n

private lemma isCompact_cwCantorSet (C : CantorSpec) : IsCompact (cwCantorSet C) := by
  have hL : ∀ n : ℕ, IsCompact (cwLevel C n) := fun n => isCompact_iUnion fun _ => isCompact_Icc
  apply IsCompact.of_isClosed_subset (hL 0) (isClosed_iInter fun n => (hL n).isClosed)
  exact Set.iInter_subset _ 0

private def cwExtendZero (C : CantorSpec) {n : ℕ} (u : cWord C n) (m : ℕ) : cWord C (n + m) :=
  fun i => if h : i.1 < n then u ⟨i.1, h⟩ else ⟨0, cBranch_pos C i.1⟩

private lemma cwInterv_inter_cantor_nonempty (C : CantorSpec) (n : ℕ) (u : cWord C n) :
    (cwInterv C (C.K + n) (cCenterInt C n u) ∩ cwCantorSet C).Nonempty := by
  let F : ℕ → Set ℝ := fun m =>
    cwInterv C (C.K + (n + m)) (cCenterInt C (n + m) (cwExtendZero C u m))
  have hanti : ∀ m, F (m + 1) ⊆ F m := fun m => by
    have hsub :=
      cwInterv_prefix_subset C (show n + m ≤ n + (m + 1) by omega) (cwExtendZero C u (m + 1))
    have hpre : cPrefix C (show n + m ≤ n + (m + 1) by omega) (cwExtendZero C u (m + 1)) =
        cwExtendZero C u m := funext fun i => by simp [cPrefix, cwExtendZero]
    rwa [hpre] at hsub
  have hne : ∀ m, (F m).Nonempty := fun m =>
    cwInterv_nonempty C (by have := C.L.hJ_ge; have := C.hK_ge; omega) _
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hanti hne
    (isCompact_Icc) (fun _ => isClosed_Icc)
  have hpre0 : cwExtendZero C u 0 = u := funext fun i => by
    have hi : i.1 < n := i.2
    simp only [cwExtendZero, hi, ↓reduceDIte]
    rfl
  refine ⟨x, ?_, ?_⟩
  · simpa [F, hpre0] using Set.mem_iInter.mp hx 0
  · rw [cwCantorSet, Set.mem_iInter]
    intro k
    by_cases hkn : k ≤ n
    · have hxu : x ∈ cwInterv C (C.K + n) (cCenterInt C n u) := by
        simpa [F, hpre0] using Set.mem_iInter.mp hx 0
      exact Set.mem_iUnion.mpr ⟨cPrefix C hkn u, cwInterv_prefix_subset C hkn u hxu⟩
    · have hxk := Set.mem_iInter.mp hx (k - n)
      generalize hm : k - n = m at hxk
      have heq : n + m = k := by omega
      subst heq
      exact Set.mem_iUnion.mpr ⟨cwExtendZero C u m, hxk⟩

private lemma cwCantorSet_subset_exactLimit (C : CantorSpec) :
    cwCantorSet C ⊆ growWeightedExactLimitSet C.L.G C.L.τ 0 := by
  intro x hx
  have hx0 := Set.mem_iInter.mp hx 0
  obtain ⟨w0, hw0⟩ := Set.mem_iUnion.mp hx0
  have hc0 : cCenterInt C 0 w0 = 0 := rfl
  rw [hc0, Nat.add_zero] at hw0
  have hjK : C.L.G.J₀ ≤ C.K := by have := C.L.hJ_ge; have := C.hK_ge; omega
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [cwInterv, Set.mem_Icc, Int.cast_zero, zero_add] at hw0 ⊢
    have hQpos : (0 : ℝ) < (C.L.G.Q C.K : ℝ) := by exact_mod_cast C.L.G.hQ_pos C.K
    have hQ1 : (1 : ℝ) ≤ (C.L.G.Q C.K : ℝ) := by exact_mod_cast C.L.G.hQ_pos C.K
    have hwK := cWidth_pos_le C.L hjK
    exact ⟨le_trans (div_nonneg hwK.1.le hQpos.le) hw0.1,
      le_trans hw0.2 (div_le_one_of_le₀ (by linarith [hwK.2]) hQpos.le)⟩
  refine ⟨hxIcc, ?_⟩
  have hlim0 : Tendsto (fun j : ℕ => (3 / 8 : ℝ) * epsW C.L j) atTop (nhds 0) := by
    simpa using (epsW_tendsto_zero C.L).const_mul (3 / 8 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0
    (Eventually.of_forall fun j => growWeightedSeq_nonneg C.L.G C.L.τ x j) ?_
  filter_upwards [eventually_ge_atTop C.K] with j hj
  have hj_J₀ : C.L.G.J₀ ≤ j := le_trans hjK hj
  have hxj := Set.mem_iInter.mp hx (j - C.K)
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hxj
  rw [show C.K + (j - C.K) = j by omega] at hw
  simp only [cwInterv, Set.mem_Icc] at hw
  have hQj : (0 : ℝ) < (C.L.G.Q j : ℝ) := by exact_mod_cast C.L.G.hQ_pos j
  have hwj := cWidth_pos_le C.L hj_J₀
  let m := cCenterInt C (j - C.K) w
  have hlo : (m : ℝ) ≤ (C.L.G.Q j : ℝ) * x := by
    have := (div_le_iff₀ hQj).mp hw.1
    linarith [hwj.1]
  have hhi : (C.L.G.Q j : ℝ) * x ≤ (m : ℝ) + 1 / 2 := by
    have := (le_div_iff₀ hQj).mp hw.2
    linarith [hwj.2]
  have hdist_eq : distToNearestInt ((C.L.G.Q j : ℝ) * x) = (C.L.G.Q j : ℝ) * x - (m : ℝ) :=
    WeightedExactDim.distToNearestInt_eq_sub_of_mem_Icc m _ hlo hhi
  have hdist_le : distToNearestInt ((C.L.G.Q j : ℝ) * x) ≤ 3 * cWidth C.L j := by
    rw [hdist_eq]
    have := (le_div_iff₀ hQj).mp hw.2
    linarith
  have hApos : (0 : ℝ) < (C.L.G.A j : ℝ) := C.L.G.grow_A_pos hj_J₀
  rw [growWeightedSeq_eq_of_ge C.L.G C.L.τ x hj_J₀]
  have hmul : (C.L.G.A j : ℝ) ^ C.L.τ * (3 * cWidth C.L j) = (3 / 8 : ℝ) * epsW C.L j := by
    dsimp [cWidth]
    have hid : (C.L.G.A j : ℝ) ^ C.L.τ * (C.L.G.A j : ℝ) ^ (-C.L.τ) = 1 := by
      rw [← Real.rpow_add hApos, add_neg_cancel, Real.rpow_zero]
    calc (C.L.G.A j : ℝ) ^ C.L.τ *
          (3 * ((1 / 8 : ℝ) * epsW C.L j * (C.L.G.A j : ℝ) ^ (-C.L.τ)))
        = 3 * (1 / 8 : ℝ) * epsW C.L j *
            ((C.L.G.A j : ℝ) ^ C.L.τ * (C.L.G.A j : ℝ) ^ (-C.L.τ)) := by ring
      _ = _ := by rw [hid]; ring
  exact (mul_le_mul_of_nonneg_left hdist_le (Real.rpow_nonneg hApos.le _)).trans_eq hmul

private lemma cwCantorSet_pos_measure (C : CantorSpec) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hs_gap : s * (1 + C.L.τ * C.L.γ_hi) < 1 - C.L.τ - 2 * C.L.η) :
    0 < μH[s] (cwCantorSet C) := by
  have hK_J₀ : C.L.G.J₀ + 1 ≤ C.K := by have := C.L.hJ_ge; have := C.hK_ge; omega
  have hA1 : ∀ m : ℕ, C.L.G.J₀ ≤ C.K + m := fun m => by omega
  -- Uniform constant M' bounding (4 Q_{K+n+1} / b_{K+n})^s / N_n for all n ≥ 0
  have hcoeff_tendsto : Tendsto (fun n : ℕ =>
      ((128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
        ((64 : ℝ) ^ n / (C.L.G.Q (C.K + n) : ℝ) ^ C.L.η))) atTop (nhds 0) := by
    have hcore := (C.L.G.grow_pow_div_Q_rpow_tendsto_zero (by norm_num : (0 : ℝ) ≤ 64) C.L.hη_pos).comp
      ((tendsto_add_atTop_nat C.K).congr fun n => Nat.add_comm n C.K)
    have hdiv : Tendsto (fun n : ℕ => (64 : ℝ) ^ n / (C.L.G.Q (C.K + n) : ℝ) ^ C.L.η)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcore
        (Eventually.of_forall fun n => by
          have : (0 : ℝ) < (C.L.G.Q (C.K + n) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
          positivity)
        (Eventually.of_forall fun n => by
          have hQpos : (0 : ℝ) < (C.L.G.Q (C.K + n) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
          have hpow : (64 : ℝ) ^ n ≤ (64 : ℝ) ^ (C.K + n) :=
            pow_le_pow_right₀ (by norm_num) (Nat.le_add_left n C.K)
          exact div_le_div_of_nonneg_right hpow (Real.rpow_nonneg hQpos.le _))
    simpa using hdiv.const_mul _
  obtain ⟨Nbound, hNbound⟩ :=
    eventually_atTop.mp (hcoeff_tendsto.eventually (gt_mem_nhds one_pos))
  let seqVal : ℕ → ℝ := fun n =>
    (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ)) ^ s / (cWordCount C n : ℝ)
  let M_fin : ℝ := (Finset.range (Nbound + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    seqVal
  let M' : ℝ := max 1 M_fin
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hseq_bound : ∀ n : ℕ, seqVal n ≤ M' := fun n => by
    by_cases hn : n < Nbound + 1
    · exact le_trans (Finset.le_sup' seqVal (Finset.mem_range.mpr hn)) (le_max_right _ _)
    · have hnge : Nbound ≤ n := by omega
      have hsmall := (hNbound n hnge).le
      have hjK : C.L.J ≤ C.K + n := by have := C.hK_ge; omega
      have hj_J₀1 : C.L.G.J₀ + 1 ≤ C.K + n := by omega
      have hQn : (0 : ℝ) < (C.L.G.Q (C.K + n) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
      have hQn1 : (0 : ℝ) < (C.L.G.Q (C.K + n + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
      have hAn : (0 : ℝ) < (C.L.G.A (C.K + n) : ℝ) := C.L.G.grow_A_pos (by omega)
      have hb_pos : (0 : ℝ) < (cBranch C.L (C.K + n) : ℝ) := by
        exact_mod_cast cBranch_pos C n
      have hN_pos : (0 : ℝ) < (cWordCount C n : ℝ) := by exact_mod_cast cWordCount_pos C n
      have hQ_ub : (C.L.G.Q (C.K + n + 1) : ℝ) ≤
          2 * (C.L.G.A (C.K + n) : ℝ) * (C.L.G.Q (C.K + n) : ℝ) :=
        grow_Q_succ_le_two_mul_A_mul C.L.G hj_J₀1
      have hb_lb := (C.hcB_ge (C.K + n) (by omega)).2
      have h1_ratio : 4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ) ≤
          128 * ((C.K + n : ℝ) + 6) * (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi) := by
        have hinv_e : 1 / epsW C.L (C.K + n) ≤ (C.K + n : ℝ) + 6 := by
          simpa [Nat.cast_add] using inv_epsW_le C.L (C.K + n)
        have hAb := C.L.hA_bound (C.K + n) hjK
        have hnJ₀ : C.L.G.J₀ ≤ C.K + n := by have := C.L.hJ_ge; have := C.hK_ge; omega
        have heps_pos := (epsW_pos_le_one C.L hnJ₀).1
        have hQgam : (C.L.G.A (C.K + n) : ℝ) ^ C.L.τ * (C.L.G.Q (C.K + n) : ℝ) ≤
            (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi) := by
          rw [Real.rpow_add hQn, Real.rpow_one, mul_comm (C.L.G.Q (C.K + n) : ℝ) _]
          exact mul_le_mul_of_nonneg_right hAb hQn.le
        have hsplitA : (C.L.G.A (C.K + n) : ℝ) / (C.L.G.A (C.K + n) : ℝ) ^ (1 - C.L.τ) =
            (C.L.G.A (C.K + n) : ℝ) ^ C.L.τ := by
          rw [div_eq_iff (Real.rpow_pos_of_pos hAn _).ne', ← Real.rpow_add hAn, add_sub_cancel,
            Real.rpow_one]
        have hden_pos : 0 < (1 / 16 : ℝ) * epsW C.L (C.K + n) *
            (C.L.G.A (C.K + n) : ℝ) ^ (1 - C.L.τ) :=
          mul_pos (mul_pos (by norm_num) heps_pos) (Real.rpow_pos_of_pos hAn _)
        calc 4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ)
            ≤ 4 * (2 * (C.L.G.A (C.K + n) : ℝ) * (C.L.G.Q (C.K + n) : ℝ)) /
                ((1 / 16 : ℝ) * epsW C.L (C.K + n) * (C.L.G.A (C.K + n) : ℝ) ^ (1 - C.L.τ)) :=
              div_le_div₀ (by positivity) (by gcongr) hden_pos hb_lb
          _ = 128 * (1 / epsW C.L (C.K + n)) *
                (((C.L.G.A (C.K + n) : ℝ) / (C.L.G.A (C.K + n) : ℝ) ^ (1 - C.L.τ)) *
                  (C.L.G.Q (C.K + n) : ℝ)) := by
              field_simp [heps_pos.ne', (Real.rpow_pos_of_pos hAn (1 - C.L.τ)).ne']; ring
          _ = 128 * (1 / epsW C.L (C.K + n)) *
                ((C.L.G.A (C.K + n) : ℝ) ^ C.L.τ * (C.L.G.Q (C.K + n) : ℝ)) := by rw [hsplitA]
          _ ≤ 128 * ((C.K + n : ℝ) + 6) * (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi) := by
              gcongr
      have hK_pow : ((C.K + n : ℝ) + 6) ≤ ((C.K : ℝ) + 6) * (2 : ℝ) ^ n := by
        have hK0 : (0 : ℝ) ≤ (C.K : ℝ) := Nat.cast_nonneg C.K
        have h2n : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
          have hnat : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
          exact_mod_cast hnat
        have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have hprod : 0 ≤ ((C.K : ℝ) + 5) * ((2 : ℝ) ^ n - 1) :=
          mul_nonneg (by linarith) (sub_nonneg.mpr h1_le)
        have hprod_exp : ((C.K : ℝ) + 5) * ((2 : ℝ) ^ n - 1) =
            ((C.K : ℝ) + 6) * (2 : ℝ) ^ n - (C.K : ℝ) - (2 : ℝ) ^ n - 5 := by ring
        rw [hprod_exp] at hprod
        linarith
      have hnum_rpow : (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ)) ^ s ≤
          (128 : ℝ) ^ s * ((C.K : ℝ) + 6) * (2 : ℝ) ^ n *
            (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi)) := by
        have hmid_le : 128 * ((C.K + n : ℝ) + 6) * (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi) ≤
            (128 * (((C.K : ℝ) + 6) * (2 : ℝ) ^ n)) *
              (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi) := by
          gcongr
        have h1 : (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ)) ^ s ≤
            ((128 * (((C.K : ℝ) + 6) * (2 : ℝ) ^ n)) *
              (C.L.G.Q (C.K + n) : ℝ) ^ (1 + C.L.τ * C.L.γ_hi)) ^ s :=
          Real.rpow_le_rpow (by positivity) (h1_ratio.trans hmid_le) hs0.le
        have h2 : (((C.K : ℝ) + 6) * (2 : ℝ) ^ n) ^ s ≤ ((C.K : ℝ) + 6) * (2 : ℝ) ^ n :=
          Real.rpow_le_self_of_one_le (by
            have hK1 : (1 : ℝ) ≤ (C.K : ℝ) + 6 := by
              linarith [show (0 : ℝ) ≤ C.K from Nat.cast_nonneg C.K]
            have h21 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
            exact one_le_mul_of_one_le_of_one_le hK1 h21) hs1
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hQn.le,
          mul_comm (1 + C.L.τ * C.L.γ_hi) s] at h1
        calc _ ≤ (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (2 : ℝ) ^ n) ^ s *
                  (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi)) := h1
          _ ≤ (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (2 : ℝ) ^ n) *
                  (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi)) := by gcongr
          _ = _ := by ring
      have hN_lb : (1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 32 : ℝ) ^ n *
          (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η) ≤ (cWordCount C n : ℝ) := by
        have h_exp : 0 ≤ 1 - C.L.τ - C.L.η := by linarith [C.L.hη_lt, C.L.hτ1]
        have h_exp1 : 1 - C.L.τ - C.L.η ≤ 1 := by linarith [C.L.hτ0, C.L.hη_pos]
        have hN_prod : (1 / 16 : ℝ) ^ n *
            (∏ i ∈ Finset.range n, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η) ≤
            (cWordCount C n : ℝ) := by
          have hrec : ∀ m : ℕ, (1 / 16 : ℝ) ^ m *
              (∏ i ∈ Finset.range m, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η) ≤
              (cWordCount C m : ℝ) := fun m => by
            induction m with
            | zero => simp [cWordCount]
            | succ m ih =>
              rw [cWordCount_succ, Nat.cast_mul, Finset.prod_range_succ, pow_succ,
                Real.mul_rpow (Finset.prod_nonneg fun i _ =>
                  (C.L.G.grow_A_pos (by have := C.L.hJ_ge; have := C.hK_ge; omega)).le)
                  (C.L.G.grow_A_pos (by have := C.L.hJ_ge; have := C.hK_ge; omega)).le]
              have hm_step : (1 / 16 : ℝ) * (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η) ≤
                  (cBranch C.L (C.K + m) : ℝ) := by
                have hmJ : C.L.G.J₀ ≤ C.K + m := by have := C.L.hJ_ge; have := C.hK_ge; omega
                have hAm : (0 : ℝ) < (C.L.G.A (C.K + m) : ℝ) := C.L.G.grow_A_pos hmJ
                have hrw : (C.L.G.A (C.K + m) : ℝ) ^ (-C.L.η) *
                    (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ) =
                    (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η) := by
                  rw [← Real.rpow_add hAm]; congr 1; ring
                have h1 := (C.hcB_ge (C.K + m) (by omega)).2
                have h2 := epsW_ge_neg_eta C.L hmJ
                calc (1 / 16 : ℝ) * (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η)
                    = (1 / 16 : ℝ) * (C.L.G.A (C.K + m) : ℝ) ^ (-C.L.η) *
                        (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ) := by rw [← hrw]; ring
                  _ ≤ (1 / 16 : ℝ) * epsW C.L (C.K + m) *
                        (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ) := by gcongr
                  _ ≤ (cBranch C.L (C.K + m) : ℝ) := h1
              have hm_nn : 0 ≤ (1 / 16 : ℝ) * (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η) :=
                mul_nonneg (by norm_num)
                  (Real.rpow_nonneg (C.L.G.grow_A_pos (by have := C.L.hJ_ge; have := C.hK_ge; omega)).le _)
              calc (1 / 16 : ℝ) ^ m * (1 / 16 : ℝ) *
                    ((∏ i ∈ Finset.range m, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η) *
                      (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η))
                  = ((1 / 16 : ℝ) ^ m *
                      (∏ i ∈ Finset.range m, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η)) *
                    ((1 / 16 : ℝ) * (C.L.G.A (C.K + m) : ℝ) ^ (1 - C.L.τ - C.L.η)) := by ring
                _ ≤ (cWordCount C m : ℝ) * (cBranch C.L (C.K + m) : ℝ) :=
                    mul_le_mul ih hm_step hm_nn (Nat.cast_nonneg _)
          exact hrec n
        have hQ_range := grow_Q_le_two_pow_mul_prod_A C.L.G (J := C.K) (by omega) n
        have hQKpos : (0 : ℝ) < (C.L.G.Q C.K : ℝ) := by exact_mod_cast C.L.G.hQ_pos C.K
        have hprod_ge : (C.L.G.Q (C.K + n) : ℝ) / ((2 : ℝ) ^ n * (C.L.G.Q C.K : ℝ)) ≤
            ∏ i ∈ Finset.range n, (C.L.G.A (C.K + i) : ℝ) :=
          (div_le_iff₀' (by positivity)).mpr (by linarith)
        have hrpow_ge : (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η) /
            (((2 : ℝ) ^ n) ^ (1 - C.L.τ - C.L.η) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) ≤
            (∏ i ∈ Finset.range n, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η) := by
          rw [← Real.mul_rpow (by positivity) hQKpos.le, ← Real.div_rpow hQn.le (by positivity)]
          exact Real.rpow_le_rpow (by positivity) hprod_ge h_exp
        have h2pow_le : ((2 : ℝ) ^ n) ^ (1 - C.L.τ - C.L.η) ≤ (2 : ℝ) ^ n :=
          Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) h_exp1
        have hrpow_ge2 : (1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 2 : ℝ) ^ n *
            (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η) ≤
            (∏ i ∈ Finset.range n, (C.L.G.A (C.K + i) : ℝ)) ^ (1 - C.L.τ - C.L.η) := by
          have h1 : (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η) /
              ((2 : ℝ) ^ n * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) ≤ _ :=
            (div_le_div_of_nonneg_left (Real.rpow_nonneg hQn.le _) (by positivity)
              (mul_le_mul_of_nonneg_right h2pow_le (Real.rpow_nonneg hQKpos.le _))).trans hrpow_ge
          calc (1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 2 : ℝ) ^ n *
                  (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η)
              = (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η) /
                  ((2 : ℝ) ^ n * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) := by
                rw [one_div, one_div, inv_pow]; ring
            _ ≤ _ := h1
        calc (1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 32 : ℝ) ^ n *
                (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η)
            = (1 / 16 : ℝ) ^ n * ((1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 2 : ℝ) ^ n *
                (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η)) := by
              rw [show (1 / 32 : ℝ) = (1 / 16 : ℝ) * (1 / 2 : ℝ) by norm_num, mul_pow]; ring
          _ ≤ _ := (mul_le_mul_of_nonneg_left hrpow_ge2 (by positivity)).trans hN_prod
      have hQ1_ge : (1 : ℝ) ≤ (C.L.G.Q (C.K + n) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
      have hQ_gap : (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi) - (1 - C.L.τ - C.L.η)) ≤
          (C.L.G.Q (C.K + n) : ℝ) ^ (-C.L.η) := by
        apply Real.rpow_le_rpow_of_exponent_le hQ1_ge
        linarith
      have hseq_le : seqVal n ≤
          (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
            ((64 : ℝ) ^ n / (C.L.G.Q (C.K + n) : ℝ) ^ C.L.η) := by
        dsimp [seqVal]
        have hQK : (0 : ℝ) < (C.L.G.Q C.K : ℝ) := by exact_mod_cast C.L.G.hQ_pos C.K
        set R1 := (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi))
        set R2 := (C.L.G.Q (C.K + n) : ℝ) ^ (1 - C.L.τ - C.L.η)
        have hR2_pos : 0 < R2 := Real.rpow_pos_of_pos hQn _
        have hQK_pow_pos : 0 < (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η) :=
          Real.rpow_pos_of_pos hQK _
        have hden_pos : 0 < (1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
            (1 / 32 : ℝ) ^ n * R2 := by positivity
        have halg : ((128 : ℝ) ^ s * ((C.K : ℝ) + 6) * (2 : ℝ) ^ n * R1) /
              ((1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 32 : ℝ) ^ n * R2) =
            (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
              ((64 : ℝ) ^ n * (R1 / R2)) := by
          have h232 : (2 : ℝ) ^ n * (32 : ℝ) ^ n = (64 : ℝ) ^ n := by rw [← mul_pow]; norm_num
          rw [one_div, one_div, inv_pow, ← h232]
          field_simp [hQK_pow_pos.ne', hR2_pos.ne']
        calc (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / (cBranch C.L (C.K + n) : ℝ)) ^ s /
                (cWordCount C n : ℝ)
            ≤ ((128 : ℝ) ^ s * ((C.K : ℝ) + 6) * (2 : ℝ) ^ n * R1) /
                ((1 / (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) * (1 / 32 : ℝ) ^ n * R2) :=
              div_le_div₀ (by positivity) hnum_rpow hden_pos hN_lb
          _ = (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
                ((64 : ℝ) ^ n * (R1 / R2)) := halg
          _ = (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
                ((64 : ℝ) ^ n * (C.L.G.Q (C.K + n) : ℝ) ^ (s * (1 + C.L.τ * C.L.γ_hi) -
                  (1 - C.L.τ - C.L.η))) := by
              have hrdiv : R1 / R2 = (C.L.G.Q (C.K + n) : ℝ) ^
                  (s * (1 + C.L.τ * C.L.γ_hi) - (1 - C.L.τ - C.L.η)) :=
                (Real.rpow_sub hQn (s * (1 + C.L.τ * C.L.γ_hi)) (1 - C.L.τ - C.L.η)).symm
              rw [hrdiv]
          _ ≤ (128 : ℝ) ^ s * (((C.K : ℝ) + 6) * (C.L.G.Q C.K : ℝ) ^ (1 - C.L.τ - C.L.η)) *
                ((64 : ℝ) ^ n * (C.L.G.Q (C.K + n) : ℝ) ^ (-C.L.η)) := by gcongr
          _ = _ := by rw [Real.rpow_neg hQn.le, div_eq_mul_inv]
      exact hseq_le.trans (hsmall.trans (by exact_mod_cast le_max_left 1 M_fin))
  suffices hpos_lb : ENNReal.ofReal (1 / M') ≤ μH[s] (cwCantorSet C) from
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hM'_pos)) hpos_lb
  have hQK_pos : (0 : ℝ) < (C.L.G.Q C.K : ℝ) := by exact_mod_cast C.L.G.hQ_pos C.K
  set r0R : ℝ := 1 / (2 * (C.L.G.Q C.K : ℝ))
  have hr0R_pos : 0 < r0R := by positivity
  set r0_half : ℝ≥0∞ := ENNReal.ofReal (r0R / 2)
  have hr0_half_pos : 0 < r0_half := ENNReal.ofReal_pos.mpr (by positivity)
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : cwCantorSet C ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) r0_half hr0_half_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push Not at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (hlt.trans_le le_top)
  have hSR_lt : S.toReal < 1 / M' := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal (one_div_pos.mpr hM'_pos).le] at h1
  set δ0 : ℝ := (1 / M' - S.toReal) / 2
  have hδ0 : 0 < δ0 := by dsimp [δ0]; linarith
  let ρ : ℕ → ℝ := fun i => min (r0R / 8) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
  have hρ_pos : ∀ i, 0 < ρ i := fun i =>
    lt_min (by positivity) (by
      have : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
      linarith [Real.rpow_pos_of_pos this (1 / s)])
  have h2ρ_le_quarter : ∀ i, 2 * ρ i ≤ r0R / 4 := fun i => by
    have := min_le_left (r0R / 8) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
    linarith
  have h2ρ_rpow : ∀ i, (2 * ρ i) ^ s ≤ δ0 / (2 : ℝ) ^ (i + 1) := fun i => by
    have h1 : 2 * ρ i ≤ (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := by
      have := min_le_right (r0R / 8) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
      linarith
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    calc (2 * ρ i) ^ s
        ≤ ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) ^ s :=
          Real.rpow_le_rpow (by linarith [hρ_pos i]) h1 hs0.le
      _ = (δ0 / (2 : ℝ) ^ (i + 1)) ^ ((1 / s) * s) :=
          (Real.rpow_mul hpos1.le (1 / s) s).symm
      _ = δ0 / (2 : ℝ) ^ (i + 1) := by rw [one_div_mul_cancel hs0.ne', Real.rpow_one]
  let V : ℕ → Set ℝ := fun i => Metric.thickening (ρ i) (t i)
  have hV_cov : cwCantorSet C ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, Metric.self_subset_thickening (hρ_pos i) (t i) hi⟩
  obtain ⟨F, hFcov⟩ := (isCompact_cwCantorSet C).elim_finite_subcover
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) (fun _ => Metric.isOpen_thickening) hV_cov
  have hV_ediam_le : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal (3 * r0R / 4) := fun i => by
    calc Metric.ediam (V i)
        ≤ Metric.ediam (t i) + 2 * ENNReal.ofReal (ρ i) :=
          WeightedExactDim.ediam_thickening_le (hρ_pos i).le
      _ ≤ r0_half + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]; gcongr; exact hdiam i
      _ ≤ ENNReal.ofReal (r0R / 2) + ENNReal.ofReal (r0R / 4) := by
          gcongr; exact h2ρ_le_quarter i
      _ = ENNReal.ofReal (3 * r0R / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hV_bd : ∀ i, Bornology.IsBounded (V i) := fun i =>
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top))
  have hV_diam_lt : ∀ i, Metric.diam (V i) < r0R := fun i => by
    unfold Metric.diam
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    linarith
  have hV_diam_pos : ∀ i : {i : ℕ // (t i).Nonempty}, 0 < Metric.diam (V i.1) := fun i =>
    WeightedExactDim.diam_thickening_pos i.2 (hρ_pos i.1) (hV_bd i.1)
  have hex_lvl : ∀ i : {i : ℕ // (t i).Nonempty},
      ∃ n : ℕ, 1 / (2 * (C.L.G.Q (C.K + n + 1) : ℝ)) ≤ Metric.diam (V i.1) ∧
        Metric.diam (V i.1) < 1 / (2 * (C.L.G.Q (C.K + n) : ℝ)) := by
    intro i
    set d := Metric.diam (V i.1)
    have hd_pos : 0 < d := hV_diam_pos i
    have hd_lt : d < 1 / (2 * (C.L.G.Q C.K : ℝ)) := hV_diam_lt i.1
    have hex_m : ∃ m : ℕ, 1 / (2 * (C.L.G.Q (C.K + m) : ℝ)) ≤ d := by
      have hshift : Tendsto (fun m : ℕ => C.K + m) atTop atTop :=
        (tendsto_add_atTop_nat C.K).congr (fun m => Nat.add_comm m C.K)
      have hdiv0 : Tendsto (fun m : ℕ => 1 / (2 * (C.L.G.Q (C.K + m) : ℝ))) atTop (nhds 0) :=
        ((C.L.G.grow_Q_tendsto_atTop.comp hshift).const_mul_atTop
          (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1
      obtain ⟨M, hM⟩ := eventually_atTop.mp (hdiv0.eventually (Iic_mem_nhds hd_pos))
      exact ⟨M, hM M le_rfl⟩
    let m0 := Nat.find hex_m
    have hm0 : 1 / (2 * (C.L.G.Q (C.K + m0) : ℝ)) ≤ d := Nat.find_spec hex_m
    have hm0_pos : 0 < m0 := by
      by_contra hz
      have heq : m0 = 0 := by omega
      rw [heq, Nat.add_zero] at hm0
      linarith
    refine ⟨m0 - 1, ?_, ?_⟩
    · have heq : C.K + (m0 - 1) + 1 = C.K + m0 := by omega
      rwa [heq]
    · by_contra! hle
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) hle
  choose lvl hlvl_lb hlvl_lt using hex_lvl
  set N : ℕ := F.sup (fun i => lvl i + 1)
  have hN_ge : ∀ i ∈ F, lvl i + 1 ≤ N := fun i hi => Finset.le_sup (f := fun i => lvl i + 1) hi
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F,
      M' * Metric.diam (V i.1) ^ s := by
    have hMN_pos : (0 : ℝ) < (cWordCount C N : ℝ) := by exact_mod_cast cWordCount_pos C N
    have hcov_words : (Finset.univ : Finset (cWord C N)) ⊆
        F.biUnion (fun i => Finset.univ.filter fun w : cWord C N =>
          (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty) := by
      intro w _
      obtain ⟨x, hxI, hxK⟩ := cwInterv_inter_cantor_nonempty C N w
      obtain ⟨i, hiF, hxV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
      exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI⟩⟩⟩
    have hcard_sum : (cWordCount C N : ℝ) ≤ ∑ i ∈ F,
        ((Finset.univ.filter fun w : cWord C N =>
          (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card : ℝ) := by
      have h1 : (Finset.univ : Finset (cWord C N)).card ≤ ∑ i ∈ F,
          (Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card :=
        (Finset.card_le_card hcov_words).trans Finset.card_biUnion_le
      have hcardN : (Finset.univ : Finset (cWord C N)).card = cWordCount C N := by
        simp [cWord, cWordCount, Fintype.card_pi]
      rw [hcardN] at h1
      exact_mod_cast h1
    have hterm_le : ∀ i ∈ F,
        ((Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card : ℝ) /
          (cWordCount C N : ℝ) ≤ M' * Metric.diam (V i.1) ^ s := fun i hiF => by
      let n := lvl i
      have hn1 : n + 1 ≤ N := hN_ge i hiF
      have hn_J₀ : C.L.G.J₀ ≤ C.K + n := by omega
      have hn1_J₀ : C.L.G.J₀ ≤ C.K + n + 1 := by omega
      let P_i := Finset.univ.filter fun u : cWord C n =>
        (V i.1 ∩ cwInterv C (C.K + n) (cCenterInt C n u)).Nonempty
      have hP_le1 : P_i.card ≤ 1 := Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => by
        obtain ⟨x₁, hx₁V, hx₁I⟩ := (Finset.mem_filter.mp hu₁).2
        obtain ⟨x₂, hx₂V, hx₂I⟩ := (Finset.mem_filter.mp hu₂).2
        have hdist : |x₁ - x₂| ≤ Metric.diam (V i.1) := by
          rw [← Real.dist_eq]
          exact Metric.dist_le_diam_of_mem (hV_bd i.1) hx₁V hx₂V
        have hne : cCenterInt C n u₁ = cCenterInt C n u₂ := by
          by_contra hne_c
          have hgap := cwInterv_dist_of_ne C hn_J₀ hne_c hx₁I hx₂I
          linarith [hlvl_lt i, hdist]
        exact cCenterInt_injective C n hne
      let A_i := Finset.univ.filter fun v : cWord C (n + 1) =>
        (V i.1 ∩ cwInterv C (C.K + (n + 1)) (cCenterInt C (n + 1) v)).Nonempty
      have hAi_le_branch : (A_i.card : ℝ) ≤ (cBranch C.L (C.K + n) : ℝ) := by
        by_cases hAne : A_i.Nonempty
        · obtain ⟨v₀, hv₀⟩ := hAne
          have hinj : ∀ v₁ ∈ A_i, ∀ v₂ ∈ A_i,
              v₁ ⟨n, by omega⟩ = v₂ ⟨n, by omega⟩ → v₁ = v₂ := by
            intro v₁ hv₁ v₂ hv₂ hlast
            have hu₁ : cPrefix C (Nat.le_succ n) v₁ ∈ P_i := by
              obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hv₁).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                ⟨x, hxV, cwInterv_prefix_subset C (Nat.le_succ n) v₁ hxI⟩⟩
            have hu₂ : cPrefix C (Nat.le_succ n) v₂ ∈ P_i := by
              obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hv₂).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                ⟨x, hxV, cwInterv_prefix_subset C (Nat.le_succ n) v₂ hxI⟩⟩
            have hpre_eq : cPrefix C (Nat.le_succ n) v₁ = cPrefix C (Nat.le_succ n) v₂ :=
              Finset.card_le_one.mp hP_le1 _ hu₁ _ hu₂
            funext j
            by_cases hj : j.1 < n
            · exact congrFun hpre_eq ⟨j.1, hj⟩
            · have hj_lt : j.1 < n + 1 := j.2
              have hjn : j = ⟨n, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hjn, hlast]
          have hcard_le : A_i.card ≤ Fintype.card (Fin (cBranch C.L (C.K + n))) :=
            Finset.card_le_card_of_injOn (fun v => v ⟨n, by omega⟩)
              (fun _ _ => Finset.mem_univ _) hinj
          rw [Fintype.card_fin] at hcard_le
          exact_mod_cast hcard_le
        · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.card_empty, Nat.cast_zero]
          exact Nat.cast_nonneg _
      have hAi_le_diam : (A_i.card : ℝ) ≤
          4 * (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) := by
        by_cases hAne : A_i.Nonempty
        · let S_k := A_i.image (fun v => cCenterInt C (n + 1) v)
          have hSk_card : S_k.card = A_i.card :=
            Finset.card_image_of_injective _ (cCenterInt_injective C (n + 1))
          have hSk_ne : S_k.Nonempty := hAne.image _
          let k_min := S_k.min' hSk_ne
          have hQ1 : (0 : ℝ) < (C.L.G.Q (C.K + n + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
          have hw1 := cWidth_pos_le C.L
            (by have := C.L.hJ_ge; have := C.hK_ge; omega : C.L.G.J₀ ≤ C.K + (n + 1))
          let R : ℝ := (3 / 2 : ℝ) * (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1)
          have hR_nn : 0 ≤ R := by have := (hV_diam_pos i).le; positivity
          have hk_sub : S_k ⊆ Finset.Icc k_min (k_min + ⌊R⌋) := by
            intro k hk
            have hk_ge : k_min ≤ k := Finset.min'_le S_k k hk
            obtain ⟨v₁, hv₁A, rfl⟩ := Finset.mem_image.mp hk
            obtain ⟨v₂, hv₂A, hk₂⟩ := Finset.mem_image.mp (Finset.min'_mem S_k hSk_ne)
            obtain ⟨x₁, hx₁V, hx₁I⟩ := (Finset.mem_filter.mp hv₁A).2
            obtain ⟨x₂, hx₂V, hx₂I⟩ := (Finset.mem_filter.mp hv₂A).2
            simp only [cwInterv, Set.mem_Icc] at hx₁I hx₂I
            have hQ1' : (0 : ℝ) < (C.L.G.Q (C.K + (n + 1)) : ℝ) := by
              exact_mod_cast C.L.G.hQ_pos _
            have hx₁_lo : (cCenterInt C (n + 1) v₁ : ℝ) + cWidth C.L (C.K + (n + 1)) ≤
                x₁ * (C.L.G.Q (C.K + (n + 1)) : ℝ) := (div_le_iff₀ hQ1').mp hx₁I.1
            have hx₂_hi : x₂ * (C.L.G.Q (C.K + (n + 1)) : ℝ) ≤
                (k_min : ℝ) + 3 * cWidth C.L (C.K + (n + 1)) := by
              dsimp [k_min]; rw [← hk₂]
              exact (le_div_iff₀ hQ1').mp hx₂I.2
            have hdist_x : x₁ - x₂ ≤ Metric.diam (V i.1) := by
              have := Metric.dist_le_diam_of_mem (hV_bd i.1) hx₁V hx₂V
              rw [Real.dist_eq] at this
              exact le_trans (le_abs_self _) this
            have hdiff_k : (cCenterInt C (n + 1) v₁ : ℝ) - (k_min : ℝ) ≤ R := by
              have h14 : 1 / 4 ≤
                  (1 / 2 : ℝ) * (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) := by
                have := hlvl_lb i
                have hle : (1 / 2 : ℝ) ≤ (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) := by
                  have hmul := (div_le_iff₀
                    (by positivity : (0 : ℝ) < 2 * (C.L.G.Q (C.K + n + 1) : ℝ))).mp this
                  linarith
                linarith
              have hQeq : C.K + (n + 1) = C.K + n + 1 := by omega
              have hQx : (x₁ - x₂) * (C.L.G.Q (C.K + n + 1) : ℝ) ≤
                  (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) := by
                rw [mul_comm]; exact mul_le_mul_of_nonneg_left hdist_x hQ1.le
              rw [hQeq] at hx₁_lo hx₂_hi hw1
              dsimp [R]; linarith [hw1.1, hw1.2, h14, hQx, hx₁_lo, hx₂_hi]
            have hk_sub_le : cCenterInt C (n + 1) v₁ - k_min ≤ ⌊R⌋ :=
              Int.le_floor.mpr (by push_cast; exact hdiff_k)
            exact Finset.mem_Icc.mpr ⟨hk_ge, by omega⟩
          have hcard_Sk : (A_i.card : ℝ) ≤ R + 1 := by
            rw [← hSk_card]
            have h1 := Finset.card_le_card hk_sub
            have hcc : ((Finset.Icc k_min (k_min + ⌊R⌋)).card : ℝ) = (⌊R⌋ : ℝ) + 1 := by
              have hf : 0 ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR_nn
              have hc : ((Int.toNat (k_min + ⌊R⌋ + 1 - k_min) : ℕ) : ℝ) = (⌊R⌋ : ℝ) + 1 := by
                have heq : Int.toNat (k_min + ⌊R⌋ + 1 - k_min) = Int.toNat (⌊R⌋ + 1) := by ring_nf
                rw [heq]; exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊R⌋ + 1)
              simpa [Int.card_Icc] using hc
            have hR1 : (S_k.card : ℝ) ≤ (⌊R⌋ : ℝ) + 1 := by
              rw [← hcc]; exact_mod_cast h1
            linarith [Int.floor_le R]
          have h12 : (1 : ℝ) ≤ 2 * (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) := by
            have := hlvl_lb i
            have hmul := (div_le_iff₀'
              (by positivity : (0 : ℝ) < 2 * (C.L.G.Q (C.K + n + 1) : ℝ))).mp this
            linarith
          have hQd_nn : 0 ≤ (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1) :=
            mul_nonneg hQ1.le (hV_diam_pos i).le
          dsimp [R] at hcard_Sk
          linarith
        · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.card_empty, Nat.cast_zero]
          have hQ1 : (0 : ℝ) < (C.L.G.Q (C.K + n + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
          exact mul_nonneg (mul_nonneg zero_le_four hQ1.le) (hV_diam_pos i).le
      have hN_mul : (Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card *
            cWordCount C (n + 1) ≤ A_i.card * cWordCount C N := by
        have hsub : Finset.univ.filter (fun w : cWord C N =>
              (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty) ⊆
            A_i.biUnion fun v => Finset.univ.filter fun w : cWord C N =>
              cPrefix C hn1 w = v := fun w hw => by
          obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hw).2
          have hxI' := cwInterv_prefix_subset C hn1 w hxI
          exact Finset.mem_biUnion.mpr ⟨cPrefix C hn1 w,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        calc (Finset.univ.filter fun w : cWord C N =>
                (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card *
                cWordCount C (n + 1)
            ≤ (A_i.biUnion fun v => Finset.univ.filter fun w : cWord C N =>
                cPrefix C hn1 w = v).card * cWordCount C (n + 1) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
          _ ≤ (∑ v ∈ A_i, (Finset.univ.filter fun w : cWord C N =>
                cPrefix C hn1 w = v).card) * cWordCount C (n + 1) :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ v ∈ A_i, ((Finset.univ.filter fun w : cWord C N =>
                cPrefix C hn1 w = v).card * cWordCount C (n + 1)) := Finset.sum_mul _ _ _
          _ = ∑ _v ∈ A_i, cWordCount C N :=
              Finset.sum_congr rfl fun v _ => card_prefix_fiber_mul C (n + 1) N hn1 v
          _ = A_i.card * cWordCount C N := by simp
      have hMn1_pos : (0 : ℝ) < (cWordCount C (n + 1) : ℝ) := by
        exact_mod_cast cWordCount_pos C (n + 1)
      have hMn_pos : (0 : ℝ) < (cWordCount C n : ℝ) := by exact_mod_cast cWordCount_pos C n
      have hratio1 : ((Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card : ℝ) /
            (cWordCount C N : ℝ) ≤ (A_i.card : ℝ) / (cWordCount C (n + 1) : ℝ) := by
        rw [div_le_div_iff₀ hMN_pos hMn1_pos]
        exact_mod_cast hN_mul
      let B : ℝ := (cBranch C.L (C.K + n) : ℝ)
      let X : ℝ := 4 * (C.L.G.Q (C.K + n + 1) : ℝ) * Metric.diam (V i.1)
      have hB_pos : 0 < B := by dsimp [B]; exact_mod_cast cBranch_pos C n
      have hX_pos : 0 < X := by
        have hQ1 : (0 : ℝ) < (C.L.G.Q (C.K + n + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
        exact mul_pos (mul_pos zero_lt_four hQ1) (hV_diam_pos i)
      have hAB : (A_i.card : ℝ) / B ≤ (X / B) ^ s := by
        by_cases hXB : X / B ≤ 1
        · calc (A_i.card : ℝ) / B ≤ X / B := div_le_div_of_nonneg_right hAi_le_diam hB_pos.le
            _ = (X / B) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (X / B) ^ s :=
              Real.rpow_le_rpow_of_exponent_ge (div_pos hX_pos hB_pos) hXB hs1
        · have hXB1 : 1 ≤ X / B := (not_le.mp hXB).le
          calc (A_i.card : ℝ) / B ≤ B / B := div_le_div_of_nonneg_right hAi_le_branch hB_pos.le
            _ = 1 := div_self hB_pos.ne'
            _ ≤ (X / B) ^ s := Real.one_le_rpow hXB1 hs0.le
      have hsplit : (X / B) ^ s =
          (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / B) ^ s * Metric.diam (V i.1) ^ s := by
        have hQ1 : (0 : ℝ) < (C.L.G.Q (C.K + n + 1) : ℝ) := by exact_mod_cast C.L.G.hQ_pos _
        rw [show X / B = (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / B) * Metric.diam (V i.1) by
          dsimp [X]; ring, Real.mul_rpow (div_nonneg (by positivity) hB_pos.le) (hV_diam_pos i).le]
      have hMn1_eq : (cWordCount C (n + 1) : ℝ) = (cWordCount C n : ℝ) * B := by
        dsimp [B]; exact_mod_cast cWordCount_succ C n
      have hratio2 : (A_i.card : ℝ) / (cWordCount C (n + 1) : ℝ) ≤
          seqVal n * Metric.diam (V i.1) ^ s := by
        rw [hMn1_eq, div_mul_eq_div_div_swap, div_le_iff₀ hMn_pos]
        calc (A_i.card : ℝ) / B ≤ (X / B) ^ s := hAB
          _ = (4 * (C.L.G.Q (C.K + n + 1) : ℝ) / B) ^ s * Metric.diam (V i.1) ^ s := hsplit
          _ = (seqVal n * Metric.diam (V i.1) ^ s) * (cWordCount C n : ℝ) := by
              dsimp [seqVal, B]; field_simp [hMn_pos.ne']
      exact hratio1.trans (hratio2.trans (mul_le_mul_of_nonneg_right (hseq_bound n)
        (Real.rpow_nonneg (hV_diam_pos i).le s)))
    calc (1 : ℝ) = (cWordCount C N : ℝ) / (cWordCount C N : ℝ) := (div_self hMN_pos.ne').symm
      _ ≤ (∑ i ∈ F, ((Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card : ℝ)) /
            (cWordCount C N : ℝ) := div_le_div_of_nonneg_right hcard_sum hMN_pos.le
      _ = ∑ i ∈ F, ((Finset.univ.filter fun w : cWord C N =>
            (V i.1 ∩ cwInterv C (C.K + N) (cCenterInt C N w)).Nonempty).card : ℝ) /
            (cWordCount C N : ℝ) := Finset.sum_div _ _ _
      _ ≤ ∑ i ∈ F, M' * Metric.diam (V i.1) ^ s := Finset.sum_le_sum hterm_le
  have hsum_ge_invM : 1 / M' ≤ ∑ i ∈ F, Metric.diam (V i.1) ^ s := by
    have h1 : 1 ≤ M' * ∑ i ∈ F, Metric.diam (V i.1) ^ s := by
      rwa [← Finset.mul_sum] at hsum_ge_one
    exact (div_le_iff₀' hM'_pos).mpr h1
  have hdiam_bound : ∀ i : {i : ℕ // (t i).Nonempty},
      Metric.diam (V i.1) ^ s ≤ (Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1) := by
    intro i
    have h_diam_le : Metric.diam (V i.1) ≤ Metric.diam (t i.1) + 2 * ρ i.1 := by
      unfold Metric.diam
      have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨ne_of_lt (lt_of_le_of_lt (hdiam i.1) ENNReal.ofReal_lt_top),
          ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top⟩)
        (WeightedExactDim.ediam_thickening_le (hρ_pos i.1).le)
      rw [ENNReal.toReal_add (ne_of_lt (lt_of_le_of_lt (hdiam i.1) ENNReal.ofReal_lt_top))
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top),
        ENNReal.toReal_mul, show (2 : ℝ≥0∞).toReal = 2 by rfl,
        ENNReal.toReal_ofReal (hρ_pos i.1).le] at h1
      exact h1
    have h_rpow := WeightedExactDim.rpow_add_le_add_rpow (a := Metric.diam (t i.1))
      (b := 2 * ρ i.1) Metric.diam_nonneg (by linarith [hρ_pos i.1]) hs0 hs1
    have h_mono := Real.rpow_le_rpow Metric.diam_nonneg h_diam_le hs0.le
    have h_t_s : Metric.diam (t i.1) ^ s = (Metric.ediam (t i.1) ^ s).toReal := by
      unfold Metric.diam
      rw [ENNReal.toReal_rpow]
    linarith [h_mono, h_rpow, h2ρ_rpow i.1, h_t_s]
  let G_idx : Finset ℕ := F.image (fun i : {i : ℕ // (t i).Nonempty} => i.1)
  have hsum_t : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal ≤ S.toReal := by
    have hinj : ∀ a ∈ F, ∀ b ∈ F, a.1 = b.1 → a = b := fun _ _ _ _ h => Subtype.ext h
    have heq_img : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal =
        ∑ k ∈ G_idx, (⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ s).toReal := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.2]
    rw [heq_img]
    have hleS : ∑ k ∈ G_idx, ⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ s ≤ S :=
      ENNReal.sum_le_tsum G_idx
    have hfin : ∀ k ∈ G_idx, (⨆ _ : (t k).Nonempty, Metric.ediam (t k) ^ s) ≠ ⊤ := fun k _ => by
      by_cases hk : (t k).Nonempty
      · simp only [hk, ciSup_unique]
        exact ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hs0.le
          (ne_of_lt (lt_of_le_of_lt (hdiam k) ENNReal.ofReal_lt_top)))
      · simp [hk]
    have hto := ENNReal.toReal_mono hS_ne_top hleS
    rwa [ENNReal.toReal_sum hfin] at hto
  have hsum_geom : ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) ≤ δ0 := by
    have hinj : ∀ a ∈ F, ∀ b ∈ F, a.1 = b.1 → a = b := fun _ _ _ _ h => Subtype.ext h
    rw [← Finset.sum_image hinj (f := fun k => δ0 / (2 : ℝ) ^ (k + 1))]
    have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) :=
      (summable_geometric_two).comp_injective (fun _ _ h => Nat.succ.inj h)
    have htsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
      have h2 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n :=
        funext fun n => by rw [pow_succ']
      rw [h2, tsum_mul_left, tsum_geometric_two]; norm_num
    have hle1 : ∑ k ∈ G_idx, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 :=
      (hsumm.sum_le_tsum G_idx (fun _ _ => by positivity)).trans_eq htsum
    calc ∑ k ∈ G_idx, δ0 / (2 : ℝ) ^ (k + 1)
        = ∑ k ∈ G_idx, δ0 * (1 / 2 : ℝ) ^ (k + 1) :=
          Finset.sum_congr rfl fun k _ => by rw [one_div, inv_pow, div_eq_mul_inv]
      _ = δ0 * ∑ k ∈ G_idx, (1 / 2 : ℝ) ^ (k + 1) := (Finset.mul_sum _ _ _).symm
      _ ≤ δ0 * 1 := mul_le_mul_of_nonneg_left hle1 hδ0.le
      _ = δ0 := mul_one δ0
  have htotal_lt : ∑ i ∈ F, Metric.diam (V i.1) ^ s < 1 / M' := by
    calc ∑ i ∈ F, Metric.diam (V i.1) ^ s
        ≤ ∑ i ∈ F, ((Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1)) :=
          Finset.sum_le_sum fun i _ => hdiam_bound i
      _ = (∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal) + ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) :=
          Finset.sum_add_distrib
      _ ≤ S.toReal + δ0 := add_le_add hsum_t hsum_geom
      _ < 1 / M' := by dsimp [δ0]; linarith
  linarith

private lemma exists_lower_spec (G : GrowingRecData) {τ s : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hs0 : 0 < s) (hs_lt : ENNReal.ofReal s < growTargetDim G τ) :
    ∃ L : LowerSpec, L.G = G ∧ L.τ = τ ∧ s * (1 + τ * L.γ_hi) < 1 - τ - 2 * L.η := by
  rcases eq_or_lt_of_le hτ0 with rfl | hτ
  · have htd : growTargetDim G 0 = 1 := by simp [growTargetDim]
    rw [htd, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one] at hs_lt
    let η := min ((1 - (0 : ℝ)) / 5) ((1 - s) / 4)
    have hη_pos : 0 < η := lt_min (by norm_num) (by linarith)
    have hη_lt : η < (1 - 0) / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨⟨G, 0, le_rfl, zero_lt_one, η, hη_pos, hη_lt, 0, le_rfl, G.J₀ + 2, le_rfl,
      fun _ _ => by simp⟩, rfl, rfl, ?_⟩
    have h2η : η ≤ (1 - s) / 4 := min_le_right _ _
    linarith
  · have htd : growTargetDim G τ =
        ENNReal.ofReal (1 - τ) / (1 + ENNReal.ofReal τ * growGammaSup G) := by
      have hnot1 : ¬ τ ≤ 0 := not_le.mpr hτ
      have hnot2 : ¬ 1 ≤ τ := not_le.mpr hτ1
      simp [growTargetDim, hnot1, hnot2]
    have htop : growGammaSup G ≠ ⊤ := by
      intro htop_eq
      rw [htd, htop_eq, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hτ).ne',
        add_top, ENNReal.div_top] at hs_lt
      exact not_lt_bot hs_lt
    set g := (growGammaSup G).toReal
    have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
    have hEq : growGammaSup G = ENNReal.ofReal g := (ENNReal.ofReal_toReal htop).symm
    have hden_pos : 0 < 1 + τ * g := by nlinarith
    have hs_real : s < (1 - τ) / (1 + τ * g) := by
      have hLHS : growTargetDim G τ = ENNReal.ofReal ((1 - τ) / (1 + τ * g)) := by
        rw [htd, hEq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mul hτ.le,
          ← ENNReal.ofReal_add zero_le_one (mul_nonneg hτ.le hg0),
          ENNReal.ofReal_div_of_pos hden_pos]
      rw [hLHS] at hs_lt
      have hto := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hs_lt
      rwa [ENNReal.toReal_ofReal hs0.le,
        ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hτ1.le) hden_pos.le)] at hto
    have hmul : s * (1 + τ * g) < 1 - τ := (lt_div_iff₀ hden_pos).mp hs_real
    let δ := (1 - τ) - s * (1 + τ * g)
    have hδ : 0 < δ := sub_pos.mpr hmul
    let η := min ((1 - τ) / 5) (δ / 4)
    have hη_pos : 0 < η := lt_min (by linarith) (by positivity)
    have hη_lt : η < (1 - τ) / 4 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let γ_hi := g + δ / (4 * s * τ)
    have hγ_nn : 0 ≤ γ_hi := by dsimp [γ_hi]; positivity
    have hgam_lt : growGammaSup G < ENNReal.ofReal γ_hi := by
      rw [hEq, ENNReal.ofReal_lt_ofReal_iff (by dsimp [γ_hi]; positivity)]
      dsimp [γ_hi]; linarith [show 0 < δ / (4 * s * τ) by positivity]
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hgam_lt)
    let J := max (G.J₀ + 2) N0
    have hAb : ∀ j : ℕ, J ≤ j → (G.A j : ℝ) ^ τ ≤ (G.Q j : ℝ) ^ (τ * γ_hi) := fun j hj => by
      have hjN : N0 ≤ j := (le_max_right _ _).trans hj
      have hjJ : G.J₀ + 1 ≤ j := by omega
      have hQpos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
      have hlog_nn : 0 ≤ Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) :=
        div_nonneg (grow_log_A_pos G (by omega)).le (grow_log_Q_pos G hjJ).le
      have hltE := hN0 j hjN
      have hleR : Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) ≤ γ_hi := by
        have hto := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hltE
        rw [ENNReal.toReal_ofReal hlog_nn, ENNReal.toReal_ofReal hγ_nn] at hto
        exact hto.le
      rw [mul_comm τ γ_hi, Real.rpow_mul hQpos.le]
      exact Real.rpow_le_rpow (G.grow_A_pos (by omega)).le
        (grow_rpow_le_of_gamma_ge G hjJ hleR) hτ.le
    have hgap : s * (1 + τ * γ_hi) < 1 - τ - 2 * η := by
      have hst : 0 < s * τ := mul_pos hs0 hτ
      have hmul_eq : s * (1 + τ * γ_hi) = s * (1 + τ * g) + δ / 4 := by
        dsimp [γ_hi]; field_simp [hst.ne']; ring
      have h2η : 2 * η ≤ δ / 2 := by linarith [min_le_right ((1 - τ) / 5) (δ / 4)]
      linarith [hmul_eq, h2η, show δ = (1 - τ) - s * (1 + τ * g) from rfl]
    exact ⟨⟨G, τ, hτ0, hτ1, η, hη_pos, hη_lt, γ_hi, hγ_nn, J, le_max_left _ _, hAb⟩,
      rfl, rfl, hgap⟩

/-- **Universal Subcritical Lower Bound (`0 ≤ τ < 1`)**:
`growTargetDim G τ ≤ dimH (growWeightedExactLimitSet G τ 0)`. -/
theorem le_dimH_growWeightedExactLimitSet_zero (G : GrowingRecData) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    growTargetDim G τ ≤ dimH (growWeightedExactLimitSet G τ 0) := by
  by_cases h0 : growTargetDim G τ = 0
  · simp [h0]
  have hd_pos : 0 < growTargetDim G τ := pos_iff_ne_zero.mpr h0
  have hd_le1 : growTargetDim G τ ≤ 1 := by
    by_cases hτ : τ ≤ 0
    · simp [growTargetDim, hτ]
    · have hnot : ¬ 1 ≤ τ := not_le.mpr hτ1
      simp only [growTargetDim, hτ, ↓reduceIte, hnot]
      calc ENNReal.ofReal (1 - τ) / (1 + ENNReal.ofReal τ * growGammaSup G)
          ≤ ENNReal.ofReal (1 - τ) / 1 := ENNReal.div_le_div_left (by simp) _
        _ = ENNReal.ofReal (1 - τ) := div_one _
        _ ≤ 1 := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (by linarith)
  have hfor : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < growTargetDim G τ →
      ENNReal.ofReal s ≤ dimH (growWeightedExactLimitSet G τ 0) := by
    intro s hs0 hs_lt
    have hs1 : s ≤ 1 := by
      have h1 := lt_of_lt_of_le hs_lt hd_le1
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one] at h1
      exact h1.le
    obtain ⟨L, rfl, rfl, hgap⟩ := exists_lower_spec G hτ0 hτ1 hs0 hs_lt
    obtain ⟨K, hKJ, hcB⟩ := exists_large_branch_start L
    let C : CantorSpec := ⟨L, K, hKJ, hcB⟩
    have hμ := cwCantorSet_pos_measure C hs0 hs1 hgap
    have hsub := cwCantorSet_subset_exactLimit C
    let s' : ℝ≥0 := ⟨s, hs0.le⟩
    have hs' : (s' : ℝ≥0∞) = ENNReal.ofReal s := by
      simp only [s', ENNReal.ofReal]
      congr 1
      exact (Real.toNNReal_of_nonneg hs0.le).symm
    have hdim : (s' : ℝ≥0∞) ≤ dimH (cwCantorSet C) :=
      le_dimH_of_hausdorffMeasure_ne_zero hμ.ne'
    rw [hs'] at hdim
    exact hdim.trans (dimH_mono hsub)
  by_contra! h
  have hfin : dimH (growWeightedExactLimitSet G τ 0) ≠ ⊤ := ne_of_lt (h.trans_le le_top)
  have hd_ne_top : growTargetDim G τ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hd_le1 ENNReal.one_lt_top)
  have hR_lt : (dimH (growWeightedExactLimitSet G τ 0)).toReal < (growTargetDim G τ).toReal :=
    (ENNReal.toReal_lt_toReal hfin hd_ne_top).mpr h
  have hdR_pos : 0 < (growTargetDim G τ).toReal :=
    ENNReal.toReal_pos hd_pos.ne' hd_ne_top
  let s : ℝ := max ((growTargetDim G τ).toReal / 2)
    (((dimH (growWeightedExactLimitSet G τ 0)).toReal + (growTargetDim G τ).toReal) / 2)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs_ltR : s < (growTargetDim G τ).toReal := max_lt (by linarith) (by linarith)
  have hs_ltE : ENNReal.ofReal s < growTargetDim G τ := by
    rw [← ENNReal.ofReal_toReal hd_ne_top, ENNReal.ofReal_lt_ofReal_iff hdR_pos]
    exact hs_ltR
  have h1 := ENNReal.toReal_mono hfin (hfor s hs0 hs_ltE)
  rw [ENNReal.toReal_ofReal hs0.le] at h1
  have h2 := le_max_right ((growTargetDim G τ).toReal / 2)
    (((dimH (growWeightedExactLimitSet G τ 0)).toReal + (growTargetDim G τ).toReal) / 2)
  change _ ≤ s at h2
  linarith

private lemma growWeightedExactLimitSet_zero_subset_levelSet (G : GrowingRecData)
    (τ : ℝ) (t : ℝ≥0∞) :
    growWeightedExactLimitSet G τ 0 ⊆ growWeightedLevelSet G τ t := by
  intro x hx
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (growWeightedSeq G τ x j))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hx.2
  change growWeightedLambda G τ x ≤ t
  unfold growWeightedLambda
  rw [hlim.limsup_eq]
  exact zero_le

/-- **Universal Subcritical Exact Level-Set Hausdorff Dimension (`0 ≤ τ < 1`, `t ≠ ⊤`)**. -/
theorem dimH_growWeightedLevelSet_eq (G : GrowingRecData) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet G τ t) = growTargetDim G τ :=
  le_antisymm
    (dimH_growWeightedLevelSet_le G hτ0 hτ1 ht)
    ((le_dimH_growWeightedExactLimitSet_zero G hτ0 hτ1).trans
      (dimH_mono (growWeightedExactLimitSet_zero_subset_levelSet G τ t)))

/-- **Universal Subcritical Exact-Zero Limit Dimension (`0 ≤ τ < 1`)**. -/
theorem dimH_growWeightedExactLimitSet_zero_eq (G : GrowingRecData) {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    dimH (growWeightedExactLimitSet G τ 0) = growTargetDim G τ :=
  le_antisymm
    ((dimH_mono (growWeightedExactLimitSet_zero_subset_levelSet G τ 0)).trans
      (dimH_growWeightedLevelSet_le G hτ0 hτ1 (by simp)))
    (le_dimH_growWeightedExactLimitSet_zero G hτ0 hτ1)

/-! ### Part 4: Universal Supercritical Phase Transition & Secondary Collapse (`τ > 1`) -/

private lemma tendsto_zero_iff_abs_tendsto_zero' {f : ℕ → ℝ} :
    Tendsto f atTop (nhds 0) ↔ Tendsto (fun n : ℕ => |f n|) atTop (nhds 0) := by
  simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero (f := f))

/-- **Universal Supercritical Lattice Inclusion (`τ > 1`, `t ≠ ⊤`)**:
For any `1 < τ` and any finite `t ≠ ⊤`, every `x ∈ growWeightedLevelSet G τ t` satisfies
`G.growLambda x = 0`, and therefore `growWeightedLevelSet G τ t ⊆ G.growLatticeL`. -/
theorem growWeightedLevelSet_subset_lattice (G : GrowingRecData) {τ : ℝ} (hτ : 1 < τ)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet G τ t ⊆ G.growLatticeL := by
  intro x hx
  rw [← G.growLambda_eq_zero_iff]
  let M : ℝ := t.toReal + 1
  have hM_pos : 0 < M := by positivity
  have hlt : growWeightedLambda G τ x < ENNReal.ofReal M := by
    refine lt_of_le_of_lt hx ?_
    rw [← ENNReal.ofReal_toReal ht]
    exact (ENNReal.ofReal_lt_ofReal_iff hM_pos).mpr (by linarith)
  have hev := eventually_lt_of_limsup_lt hlt
  have hseq0 : Tendsto (G.growSeq x) atTop (nhds 0) := by
    have hA_rpow : Tendsto (fun j : ℕ => M * (G.A j : ℝ) ^ (-(τ - 1))) atTop (nhds 0) := by
      have hneg := (tendsto_rpow_neg_atTop (sub_pos.mpr hτ)).comp G.hA_tendsto
      simpa using hneg.const_mul M
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA_rpow
      (Eventually.of_forall (G.growSeq_nonneg x)) ?_
    filter_upwards [hev, eventually_ge_atTop G.J₀] with j hj hjJ₀
    have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hjJ₀
    have hjR : growWeightedSeq G τ x j < M :=
      (ENNReal.ofReal_lt_ofReal_iff hM_pos).mp hj
    rw [growWeightedSeq_eq_of_ge G τ x hjJ₀] at hjR
    rw [G.growSeq_eq_of_ge x hjJ₀, G.abs_growEps_eq_dist]
    have hsplit : (G.A j : ℝ) = (G.A j : ℝ) ^ (-(τ - 1)) * (G.A j : ℝ) ^ τ := by
      rw [← Real.rpow_add hA_pos, show -(τ - 1) + τ = 1 by ring, Real.rpow_one]
    calc (G.A j : ℝ) * distToNearestInt ((G.Q j : ℝ) * x)
        = (G.A j : ℝ) ^ (-(τ - 1)) *
            ((G.A j : ℝ) ^ τ * distToNearestInt ((G.Q j : ℝ) * x)) := by
          nth_rw 1 [hsplit]; ring
      _ ≤ (G.A j : ℝ) ^ (-(τ - 1)) * M :=
          mul_le_mul_of_nonneg_left hjR.le (Real.rpow_nonneg hA_pos.le _)
      _ = M * (G.A j : ℝ) ^ (-(τ - 1)) := mul_comm _ _
  have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal (G.growSeq x j)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hseq0
  exact hlimE.limsup_eq

theorem growWeightedLevelSet_countable_of_one_lt (G : GrowingRecData) {τ : ℝ} (hτ : 1 < τ)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    (growWeightedLevelSet G τ t).Countable :=
  G.growLatticeL_countable.mono (growWeightedLevelSet_subset_lattice G hτ ht)

theorem dimH_growWeightedLevelSet_of_one_lt (G : GrowingRecData) {τ : ℝ} (hτ : 1 < τ)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet G τ t) = 0 :=
  (growWeightedLevelSet_countable_of_one_lt G hτ ht).dimH_zero

theorem volume_growWeightedLevelSet_of_one_lt (G : GrowingRecData) {τ : ℝ} (hτ : 1 < τ)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    volume (growWeightedLevelSet G τ t) = 0 :=
  (growWeightedLevelSet_countable_of_one_lt G hτ ht).measure_zero volume

/-- Every element of `G.growRatLattice = (1 / g) ℤ` has `Q_j x = m * Q̃_j ∈ ℤ` for all `j ≥ J₀ - 1`,
and hence belongs to `growWeightedLevelSet G τ t` for every `τ : ℝ` and every `t : ℝ≥0∞`. -/
theorem growRatLattice_subset_weightedLevelSet (G : GrowingRecData) (τ : ℝ) (t : ℝ≥0∞) :
    G.growRatLattice ⊆ growWeightedLevelSet G τ t := by
  rintro x ⟨m, rfl⟩
  have hev0 : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (growWeightedSeq G τ
      ((m : ℝ) / (G.growGFactor : ℝ)) j) = 0 := by
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    have hg_ne : (G.growGFactor : ℝ) ≠ 0 := by exact_mod_cast G.growGFactor_pos.ne'
    have hQ : (G.Q j : ℝ) = (G.growGFactor : ℝ) * (G.growQtilde j : ℝ) := by
      exact_mod_cast (G.grow_g_mul_Qtilde (by omega)).symm
    have hmul : (G.Q j : ℝ) * ((m : ℝ) / (G.growGFactor : ℝ)) =
        ((m * G.growQtilde j : ℤ) : ℝ) := by
      rw [hQ]; push_cast; field_simp [hg_ne]
    have hdist0 : distToNearestInt ((G.Q j : ℝ) * ((m : ℝ) / (G.growGFactor : ℝ))) = 0 := by
      refine le_antisymm ?_ (distToNearestInt_nonneg _)
      have hle := distToNearestInt_le ((G.Q j : ℝ) * ((m : ℝ) / (G.growGFactor : ℝ)))
        (m * G.growQtilde j)
      calc distToNearestInt ((G.Q j : ℝ) * ((m : ℝ) / (G.growGFactor : ℝ)))
          ≤ |(G.Q j : ℝ) * ((m : ℝ) / (G.growGFactor : ℝ)) - ((m * G.growQtilde j : ℤ) : ℝ)| := hle
        _ = 0 := by rw [hmul, sub_self, abs_zero]
    simp [growWeightedSeq, hdist0]
  have hlim0 : Tendsto (fun j : ℕ => ENNReal.ofReal (growWeightedSeq G τ
      ((m : ℝ) / (G.growGFactor : ℝ)) j)) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm)
  change growWeightedLambda G τ ((m : ℝ) / (G.growGFactor : ℝ)) ≤ t
  unfold growWeightedLambda
  rw [hlim0.limsup_eq]
  exact zero_le

/-- `G.growRatLattice` is a strict sublattice of `G.growLatticeL` (since `θ / g ∈ L_G \ (1/g) ℤ`). -/
theorem growRatLattice_ssubset_growLatticeL (G : GrowingRecData) :
    G.growRatLattice ⊂ G.growLatticeL := by
  refine ⟨G.growRatLattice_subset_growLatticeL, ?_⟩
  intro hsub
  have hmemL : G.growTheta / (G.growGFactor : ℝ) ∈ G.growLatticeL := by
    rw [G.growLatticeL_eq_inv_g]
    exact ⟨0, 1, by simp⟩
  obtain ⟨m, hm⟩ := hsub hmemL
  have hg_ne : (G.growGFactor : ℝ) ≠ 0 := by exact_mod_cast G.growGFactor_pos.ne'
  have hth_eq : G.growTheta = (m : ℝ) := by
    have := congrArg (fun y : ℝ => y * (G.growGFactor : ℝ)) hm
    rwa [div_mul_cancel₀ _ hg_ne, div_mul_cancel₀ _ hg_ne] at this
  exact G.growTheta_irrational ⟨m, hth_eq.symm⟩

/-- **Two-Sided Weighted Approximation Asymptotics on `L_G \ (1 / g) ℤ`**:
For `x = (m + n * θ) / g` with `n ≠ 0`, for all sufficiently large `j`:
`(|n| * g / 6) * (A_j ^ (τ - 1) / Q_j) ≤ growWeightedSeq G τ x j ≤ (|n| * g) * (A_j ^ (τ - 1) / Q_j)`. -/
lemma growWeightedSeq_bounds_of_lattice_irrational (G : GrowingRecData) (τ : ℝ) (m : ℤ)
    {n : ℤ} (hn : n ≠ 0) :
    let x := ((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)
    ∀ᶠ j : ℕ in atTop,
      (|(n : ℝ)| * (G.growGFactor : ℝ) / 6) * ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) ≤
        growWeightedSeq G τ x j ∧
      growWeightedSeq G τ x j ≤
        (|(n : ℝ)| * (G.growGFactor : ℝ)) * ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) := by
  intro x
  have hg_pos : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
  have hn_pos : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hQ_large : ∀ᶠ j : ℕ in atTop, 2 * |(n : ℝ)| * (G.growGFactor : ℝ) < (G.Q (j + 1) : ℝ) :=
    (G.grow_Q_tendsto_atTop.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop _
  filter_upwards [hQ_large, eventually_ge_atTop (G.J₀ + 1)] with j hjQ hjJ₀
  have hj0 : G.J₀ ≤ j := by omega
  have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj0
  have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hQ1_pos : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
  have hQt_pos : (0 : ℝ) < (G.growQtilde j : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hQt1_pos : (0 : ℝ) < (G.growQtilde (j + 1) : ℝ) := by
    exact_mod_cast G.growQtilde_pos (by omega)
  have hgQ : (G.Q j : ℝ) = (G.growGFactor : ℝ) * (G.growQtilde j : ℝ) := by
    exact_mod_cast (G.grow_g_mul_Qtilde (by omega)).symm
  have hgQ1 : (G.Q (j + 1) : ℝ) = (G.growGFactor : ℝ) * (G.growQtilde (j + 1) : ℝ) := by
    exact_mod_cast (G.grow_g_mul_Qtilde (by omega)).symm
  let M : ℤ := m * G.growQtilde j + n * G.growPtilde j
  have hQx_sub : (G.Q j : ℝ) * x - (M : ℝ) =
      (n : ℝ) * (G.growQtilde j : ℝ) *
        (G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)) := by
    dsimp [x, M]
    rw [hgQ]; push_cast; field_simp [hg_pos.ne', hQt_pos.ne']; ring
  have hth_b := G.growTheta_sub_ratio_bounds hj0
  have habs_hi : |(G.Q j : ℝ) * x - (M : ℝ)| <
      |(n : ℝ)| * (G.growGFactor : ℝ) / (G.Q (j + 1) : ℝ) := by
    rw [hQx_sub, abs_mul, abs_mul, abs_of_pos hQt_pos]
    calc |(n : ℝ)| * (G.growQtilde j : ℝ) *
            |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)|
        < |(n : ℝ)| * (G.growQtilde j : ℝ) *
            (1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ))) :=
          mul_lt_mul_of_pos_left hth_b.2 (mul_pos hn_pos hQt_pos)
      _ = |(n : ℝ)| / (G.growQtilde (j + 1) : ℝ) := by field_simp [hQt_pos.ne']
      _ = |(n : ℝ)| * (G.growGFactor : ℝ) / (G.Q (j + 1) : ℝ) := by
          rw [hgQ1]; field_simp [hg_pos.ne']
  have habs_lo : |(n : ℝ)| * (G.growGFactor : ℝ) / (2 * (G.Q (j + 1) : ℝ)) <
      |(G.Q j : ℝ) * x - (M : ℝ)| := by
    rw [hQx_sub, abs_mul, abs_mul, abs_of_pos hQt_pos]
    calc |(n : ℝ)| * (G.growGFactor : ℝ) / (2 * (G.Q (j + 1) : ℝ))
        = |(n : ℝ)| * (G.growQtilde j : ℝ) *
            (1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ))) := by
          rw [hgQ1]; field_simp [hg_pos.ne', hQt_pos.ne']
      _ < |(n : ℝ)| * (G.growQtilde j : ℝ) *
            |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| :=
          mul_lt_mul_of_pos_left hth_b.1 (mul_pos hn_pos hQt_pos)
  have hhalf : |(G.Q j : ℝ) * x - (M : ℝ)| < 1 / 2 := by
    refine habs_hi.trans ?_
    rw [div_lt_iff₀ hQ1_pos]
    linarith
  have hround : round ((G.Q j : ℝ) * x) = M :=
    GrowingRecData.round_eq_of_abs_sub_lt_half_grow hhalf
  have hdist_eq : distToNearestInt ((G.Q j : ℝ) * x) = |(G.Q j : ℝ) * x - (M : ℝ)| := by
    unfold distToNearestInt; rw [hround]
  have hQ1_lo : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
    exact_mod_cast (G.grow_Q_succ_gt_A_mul hj0).le
  have hQ1_hi : (G.Q (j + 1) : ℝ) ≤ 2 * (G.A j : ℝ) * (G.Q j : ℝ) :=
    grow_Q_succ_le_two_mul_A_mul G hjJ₀
  have hA_split : (G.A j : ℝ) ^ τ / (G.A j : ℝ) = (G.A j : ℝ) ^ (τ - 1) := by
    simpa using (Real.rpow_sub_one hA_pos.ne' τ).symm
  rw [growWeightedSeq_eq_of_ge G τ x hj0, hdist_eq]
  constructor
  · have h1 : |(n : ℝ)| * (G.growGFactor : ℝ) / (6 * (G.A j : ℝ) * (G.Q j : ℝ)) ≤
        |(G.Q j : ℝ) * x - (M : ℝ)| := by
      refine le_trans ?_ habs_lo.le
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith [hQ1_hi]
    calc (|(n : ℝ)| * (G.growGFactor : ℝ) / 6) * ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ))
        = (G.A j : ℝ) ^ τ *
            (|(n : ℝ)| * (G.growGFactor : ℝ) / (6 * (G.A j : ℝ) * (G.Q j : ℝ))) := by
          rw [← hA_split]; field_simp [hA_pos.ne', hQ_pos.ne']
      _ ≤ (G.A j : ℝ) ^ τ * |(G.Q j : ℝ) * x - (M : ℝ)| :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA_pos.le _)
  · have h2 : |(G.Q j : ℝ) * x - (M : ℝ)| ≤
        |(n : ℝ)| * (G.growGFactor : ℝ) / ((G.A j : ℝ) * (G.Q j : ℝ)) := by
      refine habs_hi.le.trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hQ1_lo
    calc (G.A j : ℝ) ^ τ * |(G.Q j : ℝ) * x - (M : ℝ)|
        ≤ (G.A j : ℝ) ^ τ *
            (|(n : ℝ)| * (G.growGFactor : ℝ) / ((G.A j : ℝ) * (G.Q j : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hA_pos.le _)
      _ = (|(n : ℝ)| * (G.growGFactor : ℝ)) * ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) := by
          rw [← hA_split]; field_simp [hA_pos.ne', hQ_pos.ne']

/-- **Supercritical Regime 1 (`A_j^(τ-1) / Q_j → 0`)**:
If `1 < τ`, `t ≠ ⊤`, and `A_j^(τ - 1) / Q_j → 0`, then
`growWeightedLevelSet G τ t = G.growLatticeL`. -/
theorem growWeightedLevelSet_eq_lattice_of_tendsto_zero (G : GrowingRecData) {τ : ℝ}
    (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (h0 : Tendsto (fun j : ℕ => (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) atTop (nhds 0)) :
    growWeightedLevelSet G τ t = G.growLatticeL := by
  refine Subset.antisymm (growWeightedLevelSet_subset_lattice G hτ ht) ?_
  intro x hx
  rw [G.growLatticeL_eq_inv_g] at hx
  rcases hx with ⟨m, n, rfl⟩
  by_cases hn : n = 0
  · subst hn
    apply growRatLattice_subset_weightedLevelSet G τ t
    exact ⟨m, by simp⟩
  · have hbd := growWeightedSeq_bounds_of_lattice_irrational G τ m hn
    have hseq0 : Tendsto (growWeightedSeq G τ
        (((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ))) atTop (nhds 0) := by
      have hup : Tendsto (fun j : ℕ => (|(n : ℝ)| * (G.growGFactor : ℝ)) *
          ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ))) atTop (nhds 0) := by
        simpa using h0.const_mul (|(n : ℝ)| * (G.growGFactor : ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall (growWeightedSeq_nonneg G τ _)) (hbd.mono fun _ h => h.2)
    have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal (growWeightedSeq G τ
        (((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)) j)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hseq0
    change growWeightedLambda G τ _ ≤ t
    unfold growWeightedLambda
    rw [hlimE.limsup_eq]
    exact zero_le

/-- **Supercritical Corollary 1A (`(τ - 1) * growGammaSup G < 1`)**:
Whenever `1 < τ`, `t ≠ ⊤`, and `ENNReal.ofReal (τ - 1) * growGammaSup G < 1`,
`growWeightedLevelSet G τ t = G.growLatticeL`. -/
theorem growWeightedLevelSet_eq_lattice_of_mul_gamma_lt_one (G : GrowingRecData) {τ : ℝ}
    (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hγ : ENNReal.ofReal (τ - 1) * growGammaSup G < 1) :
    growWeightedLevelSet G τ t = G.growLatticeL := by
  apply growWeightedLevelSet_eq_lattice_of_tendsto_zero G hτ ht
  have hτ_pos : 0 < τ - 1 := sub_pos.mpr hτ
  have htop : growGammaSup G ≠ ⊤ := by
    intro htop_eq
    rw [htop_eq, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hτ_pos).ne'] at hγ
    exact not_top_lt hγ
  set g := (growGammaSup G).toReal
  have hg_nn : 0 ≤ g := ENNReal.toReal_nonneg
  have hEq : growGammaSup G = ENNReal.ofReal g := (ENNReal.ofReal_toReal htop).symm
  have hmul_lt : (τ - 1) * g < 1 := by
    rw [hEq, ← ENNReal.ofReal_mul hτ_pos.le, ← ENNReal.ofReal_one] at hγ
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp hγ
  let δ := 1 - (τ - 1) * g
  have hδ : 0 < δ := sub_pos.mpr hmul_lt
  let γ_hi := g + δ / (2 * (τ - 1))
  have hγ_nn : 0 ≤ γ_hi := by dsimp [γ_hi]; positivity
  have hlt_gam : growGammaSup G < ENNReal.ofReal γ_hi := by
    rw [hEq, ENNReal.ofReal_lt_ofReal_iff (by dsimp [γ_hi]; positivity)]
    dsimp [γ_hi]; linarith [show 0 < δ / (2 * (τ - 1)) by positivity]
  have hev := eventually_lt_of_limsup_lt hlt_gam
  have hQ_rpow0 : Tendsto (fun j : ℕ => (1 : ℝ) ^ j / (G.Q j : ℝ) ^ (δ / 2)) atTop (nhds 0) :=
    G.grow_pow_div_Q_rpow_tendsto_zero zero_le_one (half_pos hδ)
  have hnn : ∀ᶠ j : ℕ in atTop, 0 ≤ (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ) := by
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    exact div_nonneg (Real.rpow_nonneg (G.grow_A_pos hj).le _) (by exact_mod_cast (G.hQ_pos j).le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ_rpow0 hnn ?_
  filter_upwards [hev, eventually_ge_atTop (G.J₀ + 1)] with j hj hjJ₀
  have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos (by omega)
  have hlog_nn : 0 ≤ Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) :=
    div_nonneg (grow_log_A_pos G (by omega)).le (grow_log_Q_pos G hjJ₀).le
  have hleR : Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) ≤ γ_hi := by
    have hto := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hj
    rw [ENNReal.toReal_ofReal hlog_nn, ENNReal.toReal_ofReal hγ_nn] at hto
    exact hto.le
  have hA_le : (G.A j : ℝ) ^ (τ - 1) ≤ (G.Q j : ℝ) ^ ((τ - 1) * γ_hi) := by
    rw [mul_comm (τ - 1) γ_hi, Real.rpow_mul hQ_pos.le]
    exact Real.rpow_le_rpow hA_pos.le (grow_rpow_le_of_gamma_ge G hjJ₀ hleR) hτ_pos.le
  have hexp_eq : (τ - 1) * γ_hi - 1 = -(δ / 2) := by
    dsimp [γ_hi, δ]; field_simp [hτ_pos.ne']; ring
  calc (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)
      ≤ (G.Q j : ℝ) ^ ((τ - 1) * γ_hi) / (G.Q j : ℝ) :=
        div_le_div_of_nonneg_right hA_le hQ_pos.le
    _ = (G.Q j : ℝ) ^ ((τ - 1) * γ_hi - 1) := (Real.rpow_sub_one hQ_pos.ne' _).symm
    _ = (1 : ℝ) ^ j / (G.Q j : ℝ) ^ (δ / 2) := by
        rw [hexp_eq, one_pow, Real.rpow_neg hQ_pos.le, one_div]

theorem growWeightedLevelSet_eq_lattice_of_gamma_zero (G : GrowingRecData)
    (hγ : growGammaSup G = 0) {τ : ℝ} (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet G τ t = G.growLatticeL :=
  growWeightedLevelSet_eq_lattice_of_mul_gamma_lt_one G hτ ht (by simp [hγ])

/-- **Supercritical Regime 2 (`limsup A_j^(τ-1) / Q_j = ⊤`)**:
If `1 < τ`, `t ≠ ⊤`, and `limsup (A_j^(τ-1) / Q_j) = ⊤`, then EVERY irrational lattice element
in `L_G \ (1 / g) ℤ` has `growWeightedLambda G τ x = ⊤`, so
`growWeightedLevelSet G τ t = G.growRatLattice` (`⊊ G.growLatticeL`). -/
theorem growWeightedLevelSet_eq_ratLattice_of_limsup_top (G : GrowingRecData) {τ : ℝ}
    (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (htop : limsup (fun j : ℕ => ENNReal.ofReal ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)))
      atTop = ⊤) :
    growWeightedLevelSet G τ t = G.growRatLattice := by
  refine Subset.antisymm ?_ (growRatLattice_subset_weightedLevelSet G τ t)
  intro x hx
  have hxL := growWeightedLevelSet_subset_lattice G hτ ht hx
  rw [G.growLatticeL_eq_inv_g] at hxL
  rcases hxL with ⟨m, n, rfl⟩
  by_cases hn : n = 0
  · subst hn; exact ⟨m, by simp⟩
  · exfalso
    have hbd := growWeightedSeq_bounds_of_lattice_irrational G τ m hn
    let c : ℝ := |(n : ℝ)| * (G.growGFactor : ℝ) / 6
    have hc_pos : 0 < c := by
      have hn_pos : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
      have hg_pos : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
      dsimp [c]; positivity
    let M : ℝ := (t.toReal + 1) / c
    have hM_pos : 0 < M := by positivity
    have hlt_top : ENNReal.ofReal M <
        limsup (fun j : ℕ => ENNReal.ofReal ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ))) atTop := by
      rw [htop]; exact ENNReal.ofReal_lt_top
    have hfreq := frequently_lt_of_lt_limsup (by isBoundedDefault) hlt_top
    have hfreq_seq : ∃ᶠ j : ℕ in atTop,
        ENNReal.ofReal (t.toReal + 1) ≤
          ENNReal.ofReal (growWeightedSeq G τ
            (((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)) j) := by
      refine (hfreq.and_eventually hbd).mono fun j ⟨hjM, hj_lo, _⟩ => ?_
      apply ENNReal.ofReal_le_ofReal
      have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
      have hratio_gt : M < (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM_pos.le).mp hjM
      have hmul : c * M < c * ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) :=
        mul_lt_mul_of_pos_left hratio_gt hc_pos
      have hcM : c * M = t.toReal + 1 := mul_div_cancel₀ _ hc_pos.ne'
      dsimp [c] at hmul hcM
      linarith [hmul, hcM, hj_lo]
    have hle_limsup : ENNReal.ofReal (t.toReal + 1) ≤
        growWeightedLambda G τ (((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)) :=
      le_limsup_of_frequently_le hfreq_seq (by isBoundedDefault)
    have hle_t : ENNReal.ofReal (t.toReal + 1) ≤ t := hle_limsup.trans hx
    have hlt_t : t < ENNReal.ofReal (t.toReal + 1) := by
      nth_rw 1 [← ENNReal.ofReal_toReal ht]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    exact not_lt_of_ge hle_t hlt_t

/-- **Supercritical Corollary 2A (`1 < (τ - 1) * growGammaSup G`)**:
Whenever `1 < τ`, `t ≠ ⊤`, and `1 < ENNReal.ofReal (τ - 1) * growGammaSup G`,
`growWeightedLevelSet G τ t = G.growRatLattice`. -/
theorem growWeightedLevelSet_eq_ratLattice_of_one_lt_mul_gamma (G : GrowingRecData) {τ : ℝ}
    (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hγ : 1 < ENNReal.ofReal (τ - 1) * growGammaSup G) :
    growWeightedLevelSet G τ t = G.growRatLattice := by
  apply growWeightedLevelSet_eq_ratLattice_of_limsup_top G hτ ht
  have hτ_pos : 0 < τ - 1 := sub_pos.mpr hτ
  have hex_γ : ∃ γ_lo : ℝ, 1 / (τ - 1) < γ_lo ∧ ENNReal.ofReal γ_lo < growGammaSup G := by
    by_cases htop : growGammaSup G = ⊤
    · refine ⟨1 / (τ - 1) + 1, by linarith, ?_⟩
      rw [htop]; exact ENNReal.ofReal_lt_top
    · set g := (growGammaSup G).toReal
      have hEq : growGammaSup G = ENNReal.ofReal g := (ENNReal.ofReal_toReal htop).symm
      have hmul_gt : 1 < (τ - 1) * g := by
        rw [hEq, ← ENNReal.ofReal_mul hτ_pos.le, ← ENNReal.ofReal_one] at hγ
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).mp hγ
      have hg_gt : 1 / (τ - 1) < g := (div_lt_iff₀ hτ_pos).mpr (by linarith)
      refine ⟨(1 / (τ - 1) + g) / 2, by linarith, ?_⟩
      rw [hEq, ENNReal.ofReal_lt_ofReal_iff (lt_trans (by positivity) hg_gt)]
      linarith
  rcases hex_γ with ⟨γ_lo, hγ_gt, hγ_lt_sup⟩
  have hγ_pos : 0 < γ_lo := lt_trans (by positivity) hγ_gt
  have hδ : 0 < (τ - 1) * γ_lo - 1 := by
    have := (div_lt_iff₀ hτ_pos).mp hγ_gt
    linarith
  have hfreq := frequently_lt_of_lt_limsup (by isBoundedDefault) hγ_lt_sup
  rw [eq_top_iff]
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  have hy_ne_top : y ≠ ⊤ := ne_of_lt hy
  let M : ℝ := y.toReal + 1
  have hM_pos : 0 < M := by positivity
  have hQ_tend : Tendsto (fun j : ℕ => (G.Q j : ℝ) ^ ((τ - 1) * γ_lo - 1)) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp G.grow_Q_tendsto_atTop
  have hev_M : ∀ᶠ j : ℕ in atTop, M ≤ (G.Q j : ℝ) ^ ((τ - 1) * γ_lo - 1) :=
    hQ_tend.eventually_ge_atTop M
  have hfreq_M : ∃ᶠ j : ℕ in atTop,
      y ≤ ENNReal.ofReal ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) := by
    refine (hfreq.and_eventually (hev_M.and (eventually_ge_atTop (G.J₀ + 1)))).mono
      fun j ⟨hj_gam, hjM, hjJ₀⟩ => ?_
    have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
    have hA_pos : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos (by omega)
    have hlog_ge : γ_lo ≤ Real.log (G.A j : ℝ) / Real.log (G.Q j : ℝ) := by
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hγ_pos.le).mp hj_gam).le
    have hA_ge : (G.Q j : ℝ) ^ ((τ - 1) * γ_lo) ≤ (G.A j : ℝ) ^ (τ - 1) := by
      rw [mul_comm (τ - 1) γ_lo, Real.rpow_mul hQ_pos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hQ_pos.le _)
        (grow_rpow_ge_of_gamma_le G hjJ₀ hlog_ge) hτ_pos.le
    have hdiv_ge : M ≤ (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ) := by
      calc M ≤ (G.Q j : ℝ) ^ ((τ - 1) * γ_lo - 1) := hjM
        _ = (G.Q j : ℝ) ^ ((τ - 1) * γ_lo) / (G.Q j : ℝ) := Real.rpow_sub_one hQ_pos.ne' _
        _ ≤ (G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ) := div_le_div_of_nonneg_right hA_ge hQ_pos.le
    calc y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hy_ne_top).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (by dsimp [M]; linarith)
      _ ≤ ENNReal.ofReal ((G.A j : ℝ) ^ (τ - 1) / (G.Q j : ℝ)) :=
          ENNReal.ofReal_le_ofReal hdiv_ge
  exact le_limsup_of_frequently_le hfreq_M (by isBoundedDefault)

theorem growWeightedLevelSet_eq_ratLattice_of_gamma_top (G : GrowingRecData)
    (hγ : growGammaSup G = ⊤) {τ : ℝ} (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet G τ t = G.growRatLattice := by
  apply growWeightedLevelSet_eq_ratLattice_of_one_lt_mul_gamma G hτ ht
  rw [hγ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (sub_pos.mpr hτ)).ne']
  exact ENNReal.one_lt_top

/-! ### Part 5: Three Concrete Growth Regimes (`expGrowingRec`, `doubleExpGrowingRec`, `superDoubleExpGrowingRec`) -/

/-- Canonical constructor for a unit-initialized `GrowingRecData` (`J₀ = 1, Q 0 = Q 1 = 1`). -/
def mkUnitGrowingRec (A : ℕ → ℤ) (hA_ge : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ≤ A j)
    (hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop) : GrowingRecData := by
  let pair : ℕ → ℤ × ℤ := fun j =>
    Nat.rec (1, 1) (fun k p => (p.2, A (k + 1) * p.2 + p.1)) j
  have hpos : ∀ j : ℕ, 0 < (pair j).1 ∧ 0 < (pair j).2 := fun j => by
    induction j with
    | zero => exact ⟨zero_lt_one, zero_lt_one⟩
    | succ k ih =>
      dsimp [pair]
      refine ⟨ih.2, ?_⟩
      have hAk : (2 : ℤ) ≤ A (k + 1) := hA_ge (k + 1) (by omega)
      nlinarith [ih.1, ih.2, hAk]
  refine
    { J₀ := 1
      hJ₀ := le_rfl
      A := A
      hA_ge := hA_ge
      hA_tendsto := hA_tendsto
      Q := fun j => (pair j).1
      hQ_pos := fun j => (hpos j).1
      hQ_rec := fun j hj => ?_ }
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rfl

lemma mkUnitGrowingRec_Q_zero (A : ℕ → ℤ) (hA_ge : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ≤ A j)
    (hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop) :
    (mkUnitGrowingRec A hA_ge hA_tendsto).Q 0 = 1 := rfl

lemma mkUnitGrowingRec_Q_one (A : ℕ → ℤ) (hA_ge : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ≤ A j)
    (hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop) :
    (mkUnitGrowingRec A hA_ge hA_tendsto).Q 1 = 1 := rfl

lemma mkUnitGrowingRec_growGFactor (A : ℕ → ℤ) (hA_ge : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ≤ A j)
    (hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop) :
    (mkUnitGrowingRec A hA_ge hA_tendsto).growGFactor = 1 := by
  unfold GrowingRecData.growGFactor
  change Int.gcd 1 1 = 1
  rfl

lemma mkUnitGrowingRec_growRatLattice (A : ℕ → ℤ) (hA_ge : ∀ j : ℕ, 1 ≤ j → (2 : ℤ) ≤ A j)
    (hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop) :
    (mkUnitGrowingRec A hA_ge hA_tendsto).growRatLattice = Set.range Int.cast := by
  ext x
  simp only [GrowingRecData.growRatLattice, mkUnitGrowingRec_growGFactor, Nat.cast_one, div_one,
    Set.mem_ofPred_eq, Set.mem_range]
  exact ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩

/-! #### 5.1 Regime I: Exponential Partial Quotients (`A_j = 2 ^ (j + 1)`, `γ_sup = 0`) -/

/-- Concrete Regime I: `A_j = 2 ^ (j + 1)` (`Q_0 = Q_1 = 1, Q_{j+1} = 2^{j+1} Q_j + Q_{j-1}`). -/
def expGrowingRec : GrowingRecData :=
  mkUnitGrowingRec (fun j => (2 : ℤ) ^ (j + 1))
    (fun j _ => by
      calc (2 : ℤ) = (2 : ℤ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℤ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
    (by
      have h : Tendsto (fun j : ℕ => (2 : ℝ) ^ (j + 1)) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)
      exact h.congr (fun j => by push_cast; rfl))

private lemma sum_range_add_one (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, (k + 1)) = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- For `expGrowingRec` (`A_j = 2^{j+1}`), `log Q_j ≥ (j(j-1)/2) log 2` while `log A_j = (j+1) log 2`,
so `log A_j / log Q_j → 0` and `growGammaSup expGrowingRec = 0`. -/
theorem growGammaSup_expGrowingRec : growGammaSup expGrowingRec = 0 := by
  have hlim0 : Tendsto (fun j : ℕ =>
      Real.log (expGrowingRec.A j : ℝ) / Real.log (expGrowingRec.Q j : ℝ)) atTop (nhds 0) := by
    have hup : Tendsto (fun j : ℕ => (4 : ℝ) / (j : ℝ)) atTop (nhds 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop 4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with j hj
      exact div_nonneg (grow_log_A_pos expGrowingRec (by dsimp [expGrowingRec, mkUnitGrowingRec]; omega)).le
        (grow_log_Q_pos expGrowingRec (by dsimp [expGrowingRec, mkUnitGrowingRec]; omega)).le
    · filter_upwards [eventually_ge_atTop 3] with j hj
      obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      have hn2 : 2 ≤ n := by omega
      have hQ_ge := grow_prod_A_le_Q_simple expGrowingRec (J := 1) le_rfl n
      rw [Nat.add_comm 1 n] at hQ_ge
      have hprod_eq : ∀ m : ℕ, ∏ k ∈ Finset.range m, (expGrowingRec.A (1 + k) : ℝ) =
          (2 : ℝ) ^ (∑ k ∈ Finset.range m, (k + 2)) := fun m => by
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_add, ← ih]
          change _ * (((2 : ℤ) ^ (1 + m + 1) : ℤ) : ℝ) = _
          push_cast
          rw [show 1 + m + 1 = m + 2 by omega]
      have hsum_ge : n * (n + 1) ≤ 2 * (∑ k ∈ Finset.range n, (k + 2)) := by
        have h1 := sum_range_add_one n
        have h2 : ∑ k ∈ Finset.range n, (k + 1) ≤ ∑ k ∈ Finset.range n, (k + 2) :=
          Finset.sum_le_sum fun k _ => by omega
        omega
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (∑ k ∈ Finset.range n, (k + 2)) := by positivity
      have hlogQ_ge : ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log 2 ≤
          Real.log (expGrowingRec.Q (n + 1) : ℝ) := by
        have h1 := Real.log_le_log hpow_pos ((hprod_eq n) ▸ hQ_ge)
        rw [Real.log_pow] at h1
        have h2 : (n : ℝ) * ((n : ℝ) + 1) / 2 ≤ ((∑ k ∈ Finset.range n, (k + 2) : ℕ) : ℝ) := by
          have hcast : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * ((∑ k ∈ Finset.range n, (k + 2) : ℕ) : ℝ) := by
            exact_mod_cast hsum_ge
          linarith
        exact (mul_le_mul_of_nonneg_right h2 (Real.log_pos one_lt_two).le).trans h1
      have hlogA_eq : Real.log (expGrowingRec.A (n + 1) : ℝ) = ((n : ℝ) + 2) * Real.log 2 := by
        change Real.log (((2 : ℤ) ^ (n + 1 + 1) : ℤ) : ℝ) = _
        push_cast
        rw [Real.log_pow]; push_cast; ring
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hden_pos : 0 < ((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log 2 := by positivity
      rw [hlogA_eq]
      calc (((n : ℝ) + 2) * Real.log 2) / Real.log (expGrowingRec.Q (n + 1) : ℝ)
          ≤ (((n : ℝ) + 2) * Real.log 2) / (((n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log 2) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hlogQ_ge
        _ = (2 * ((n : ℝ) + 2)) / ((n : ℝ) * ((n : ℝ) + 1)) := by
            field_simp [hl2.ne', hn_pos.ne']
        _ ≤ 4 / ((n + 1 : ℕ) : ℝ) := by
            push_cast
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
            nlinarith
  have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal
      (Real.log (expGrowingRec.A j : ℝ) / Real.log (expGrowingRec.Q j : ℝ))) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hlim0
  exact hlimE.limsup_eq

/-- Subcritical & supercritical phase diagram for `expGrowingRec` (`A_j = 2^{j+1}`, `γ_sup = 0`):
no subcritical distortion (`dimH = 1 - τ` for all `0 ≤ τ < 1`) and full rank-2 lattice preservation
(`growWeightedLevelSet = L_G` for all `τ > 1`). -/
theorem dimH_expGrowingRec_subcritical {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet expGrowingRec τ t) = ENNReal.ofReal (1 - τ) ∧
    dimH (growWeightedExactLimitSet expGrowingRec τ 0) = ENNReal.ofReal (1 - τ) := by
  have htd : growTargetDim expGrowingRec τ = ENNReal.ofReal (1 - τ) := by
    by_cases h0 : τ ≤ 0
    · have hτ_eq : τ = 0 := le_antisymm h0 hτ0
      subst hτ_eq; simp [growTargetDim]
    · have hnot1 : ¬ 1 ≤ τ := not_le.mpr hτ1
      simp [growTargetDim, h0, hnot1, growGammaSup_expGrowingRec]
  rw [← htd]
  exact ⟨dimH_growWeightedLevelSet_eq expGrowingRec hτ0 hτ1 ht,
    dimH_growWeightedExactLimitSet_zero_eq expGrowingRec hτ0 hτ1⟩

theorem expGrowingRec_supercritical {τ : ℝ} (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet expGrowingRec τ t = expGrowingRec.growLatticeL :=
  growWeightedLevelSet_eq_lattice_of_gamma_zero expGrowingRec growGammaSup_expGrowingRec hτ ht

/-! #### 5.2 Regime II: Double-Exponential Partial Quotients (`A_j = 2 ^ (2 ^ j)`, `γ_sup = 1`) -/

/-- Concrete Regime II: `A_j = 2 ^ (2 ^ j)` (`Q_0 = Q_1 = 1, Q_{j+1} = 2^{2^j} Q_j + Q_{j-1}`). -/
def doubleExpGrowingRec : GrowingRecData :=
  mkUnitGrowingRec (fun j => (2 : ℤ) ^ (2 ^ j))
    (fun j hj => by
      have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      calc (2 : ℤ) = (2 : ℤ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℤ) ^ (2 ^ j) := pow_le_pow_right₀ (by norm_num) h1)
    (by
      have h : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt one_lt_two
      refine tendsto_atTop_mono (fun j => ?_) h
      change (2 : ℝ) ^ j ≤ (((2 : ℤ) ^ (2 ^ j) : ℤ) : ℝ)
      push_cast
      exact pow_le_pow_right₀ one_le_two Nat.lt_two_pow_self.le)

private lemma sum_two_pow_shift (n : ℕ) :
    (∑ k ∈ Finset.range n, 2 ^ (1 + k)) + 2 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih]
    have h1 : 1 + n = n + 1 := Nat.add_comm 1 n
    rw [h1, pow_succ]
    ring

/-- Exact two-sided denominator bounds for `doubleExpGrowingRec`:
for all `j ≥ 2`, `(1 / 4) * A_j ≤ Q_j ≤ (2 : ℝ) ^ (j - 1) * (1 / 4) * A_j`. -/
lemma doubleExpGrowingRec_Q_bounds {j : ℕ} (hj : 2 ≤ j) :
    (1 / 4 : ℝ) * (doubleExpGrowingRec.A j : ℝ) ≤ (doubleExpGrowingRec.Q j : ℝ) ∧
    (doubleExpGrowingRec.Q j : ℝ) ≤
      (2 : ℝ) ^ (j - 1) * ((1 / 4 : ℝ) * (doubleExpGrowingRec.A j : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = 1 + (n + 1) := ⟨j - 2, by omega⟩
  have hprod_eq : ∏ k ∈ Finset.range (n + 1), (doubleExpGrowingRec.A (1 + k) : ℝ) =
      (1 / 4 : ℝ) * (doubleExpGrowingRec.A (1 + (n + 1)) : ℝ) := by
    have h1 : ∏ k ∈ Finset.range (n + 1), (doubleExpGrowingRec.A (1 + k) : ℝ) =
        (2 : ℝ) ^ (∑ k ∈ Finset.range (n + 1), 2 ^ (1 + k)) := by
      clear hj
      induction (n + 1) with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_add, ← ih]
        change _ * (((2 : ℤ) ^ (2 ^ (1 + m)) : ℤ) : ℝ) = _
        push_cast; rfl
    have hA_end : (doubleExpGrowingRec.A (1 + (n + 1)) : ℝ) =
        (2 : ℝ) ^ (2 ^ (1 + (n + 1))) := by
      change (((2 : ℤ) ^ (2 ^ (1 + (n + 1))) : ℤ) : ℝ) = _
      push_cast; rfl
    have hsum := sum_two_pow_shift (n + 1)
    rw [Nat.add_comm (n + 1) 1] at hsum
    rw [h1, hA_end, ← hsum, pow_add]
    ring
  have hQ1 : (doubleExpGrowingRec.Q 1 : ℝ) = 1 := by
    have h1 : doubleExpGrowingRec.Q 1 = 1 := rfl
    rw [h1, Int.cast_one]
  constructor
  · have hlo := grow_prod_A_le_Q_simple doubleExpGrowingRec (J := 1) le_rfl (n + 1)
    rwa [hprod_eq] at hlo
  · have hJ0 : doubleExpGrowingRec.J₀ + 1 ≤ 2 := le_rfl
    -- wait: grow_Q_le_two_pow_mul_prod_A needs G.J₀ + 1 ≤ J (so J ≥ 2 for J₀ = 1), OR we can prove it from J = 1 directly!
    have hhi : (doubleExpGrowingRec.Q (1 + (n + 1)) : ℝ) ≤
        (2 : ℝ) ^ (n + 1) * (∏ k ∈ Finset.range (n + 1), (doubleExpGrowingRec.A (1 + k) : ℝ)) := by
      clear hprod_eq hj
      induction (n + 1) with
      | zero => simp [hQ1]
      | succ m ih =>
        have hrec : (doubleExpGrowingRec.Q (1 + m + 1) : ℝ) =
            (doubleExpGrowingRec.A (1 + m) : ℝ) * (doubleExpGrowingRec.Q (1 + m) : ℝ) +
              (doubleExpGrowingRec.Q (1 + m - 1) : ℝ) := by
          exact_mod_cast doubleExpGrowingRec.hQ_rec (1 + m)
            (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
        have hQprev : (doubleExpGrowingRec.Q (1 + m - 1) : ℝ) ≤
            (doubleExpGrowingRec.Q (1 + m) : ℝ) := by
          rcases m with _ | m'
          · have h0 : (doubleExpGrowingRec.Q 0 : ℝ) = 1 := by
              have : doubleExpGrowingRec.Q 0 = 1 := rfl; rw [this, Int.cast_one]
            simp [h0, hQ1]
          · exact_mod_cast doubleExpGrowingRec.grow_Q_monoOn
              (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega) (by omega)
        have hAm2 : (2 : ℝ) ≤ (doubleExpGrowingRec.A (1 + m) : ℝ) :=
          grow_A_ge_two doubleExpGrowingRec (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
        have hQpos : (0 : ℝ) < (doubleExpGrowingRec.Q (1 + m) : ℝ) := by
          exact_mod_cast doubleExpGrowingRec.hQ_pos _
        have hstep : (doubleExpGrowingRec.Q (1 + m + 1) : ℝ) ≤
            2 * (doubleExpGrowingRec.A (1 + m) : ℝ) * (doubleExpGrowingRec.Q (1 + m) : ℝ) := by
          nlinarith
        rw [show 1 + (m + 1) = 1 + m + 1 by omega, Finset.prod_range_succ, pow_succ]
        calc (doubleExpGrowingRec.Q (1 + m + 1) : ℝ)
            ≤ (2 * (doubleExpGrowingRec.A (1 + m) : ℝ)) * (doubleExpGrowingRec.Q (1 + m) : ℝ) := hstep
          _ ≤ (2 * (doubleExpGrowingRec.A (1 + m) : ℝ)) *
                ((2 : ℝ) ^ m * ∏ k ∈ Finset.range m, (doubleExpGrowingRec.A (1 + k) : ℝ)) :=
              mul_le_mul_of_nonneg_left ih (by linarith)
          _ = (2 : ℝ) ^ m * 2 *
                ((∏ k ∈ Finset.range m, (doubleExpGrowingRec.A (1 + k) : ℝ)) *
                  (doubleExpGrowingRec.A (1 + m) : ℝ)) := by ring
    rw [hprod_eq] at hhi
    simpa using hhi

/-- Constant-ratio denominator upper bound for `doubleExpGrowingRec`:
for all `j ≥ 2`, `Q_j ≤ A_j`. -/
lemma doubleExpGrowingRec_Q_le_A {j : ℕ} (hj : 2 ≤ j) :
    (doubleExpGrowingRec.Q j : ℝ) ≤ (doubleExpGrowingRec.A j : ℝ) := by
  have hA_eq : ∀ k : ℕ, (doubleExpGrowingRec.A k : ℝ) = (2 : ℝ) ^ (2 ^ k) := fun k => by
    change (((2 : ℤ) ^ (2 ^ k) : ℤ) : ℝ) = _
    push_cast; rfl
  have hA_sq : ∀ k : ℕ, (doubleExpGrowingRec.A k : ℝ) * (doubleExpGrowingRec.A k : ℝ) =
      (doubleExpGrowingRec.A (k + 1) : ℝ) := fun k => by
    rw [hA_eq k, hA_eq (k + 1), ← pow_add, pow_succ, Nat.mul_two]
  have hQ2 : (doubleExpGrowingRec.Q 2 : ℝ) = 5 := by
    have hrec := doubleExpGrowingRec.hQ_rec 1 le_rfl
    change (doubleExpGrowingRec.Q (1 + 1) : ℝ) = 5
    rw [hrec]
    change (((2 : ℤ) ^ (2 ^ 1) * 1 + 1 : ℤ) : ℝ) = 5
    norm_num
  have h38 : ∀ k : ℕ, (doubleExpGrowingRec.Q (k + 2) : ℝ) ≤
      (doubleExpGrowingRec.A (k + 2) : ℝ) - 1 := fun k => by
    induction k with
    | zero => rw [zero_add, hQ2, hA_eq 2]; norm_num
    | succ k ihk =>
      have hrec : (doubleExpGrowingRec.Q (k + 2 + 1) : ℝ) =
          (doubleExpGrowingRec.A (k + 2) : ℝ) * (doubleExpGrowingRec.Q (k + 2) : ℝ) +
            (doubleExpGrowingRec.Q (k + 2 - 1) : ℝ) := by
        exact_mod_cast doubleExpGrowingRec.hQ_rec (k + 2)
          (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
      have hQprev : (doubleExpGrowingRec.Q (k + 2 - 1) : ℝ) ≤
          (doubleExpGrowingRec.Q (k + 2) : ℝ) := by
        exact_mod_cast doubleExpGrowingRec.grow_Q_monoOn
          (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega) (by omega)
      have hA_pos : (0 : ℝ) < (doubleExpGrowingRec.A (k + 2) : ℝ) := by rw [hA_eq]; positivity
      have hmul1 : (doubleExpGrowingRec.A (k + 2) : ℝ) * (doubleExpGrowingRec.Q (k + 2) : ℝ) ≤
          (doubleExpGrowingRec.A (k + 2) : ℝ) *
            ((doubleExpGrowingRec.A (k + 2) : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left ihk hA_pos.le
      rw [show k + 1 + 2 = k + 2 + 1 by omega, hrec, ← hA_sq (k + 2)]
      linarith
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  linarith [h38 k]

/-- For `doubleExpGrowingRec` (`A_j = 2^{2^j}`), `(1 / 4) A_j ≤ Q_j ≤ A_j` for all `j ≥ 2`,
so `log A_j / log Q_j → 1` and `growGammaSup doubleExpGrowingRec = 1`. -/
theorem growGammaSup_doubleExpGrowingRec : growGammaSup doubleExpGrowingRec = 1 := by
  have hlim1 : Tendsto (fun j : ℕ =>
      Real.log (doubleExpGrowingRec.A j : ℝ) / Real.log (doubleExpGrowingRec.Q j : ℝ))
      atTop (nhds 1) := by
    have hup : Tendsto (fun j : ℕ =>
        1 + Real.log 4 / Real.log (doubleExpGrowingRec.Q j : ℝ)) atTop (nhds 1) := by
      have hlogQ_atTop : Tendsto (fun j : ℕ => Real.log (doubleExpGrowingRec.Q j : ℝ))
          atTop atTop :=
        Real.tendsto_log_atTop.comp doubleExpGrowingRec.grow_Q_tendsto_atTop
      have h0 : Tendsto (fun j : ℕ => Real.log 4 / Real.log (doubleExpGrowingRec.Q j : ℝ))
          atTop (nhds 0) :=
        hlogQ_atTop.const_div_atTop (Real.log 4)
      simpa using tendsto_const_nhds.add h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with j hj
      have hle := doubleExpGrowingRec_Q_le_A hj
      have hQ_pos : (0 : ℝ) < (doubleExpGrowingRec.Q j : ℝ) := by
        exact_mod_cast doubleExpGrowingRec.hQ_pos j
      have hlQ_pos : 0 < Real.log (doubleExpGrowingRec.Q j : ℝ) :=
        grow_log_Q_pos doubleExpGrowingRec (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
      exact (one_le_div hlQ_pos).mpr (Real.log_le_log hQ_pos hle)
    · filter_upwards [eventually_ge_atTop 2] with j hj
      have hlo := (doubleExpGrowingRec_Q_bounds hj).1
      have hA_pos : (0 : ℝ) < (doubleExpGrowingRec.A j : ℝ) :=
        doubleExpGrowingRec.grow_A_pos (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
      have hlQ_pos : 0 < Real.log (doubleExpGrowingRec.Q j : ℝ) :=
        grow_log_Q_pos doubleExpGrowingRec (by dsimp [doubleExpGrowingRec, mkUnitGrowingRec]; omega)
      have hlog_le : Real.log (doubleExpGrowingRec.A j : ℝ) ≤
          Real.log (doubleExpGrowingRec.Q j : ℝ) + Real.log 4 := by
        have h1 := Real.log_le_log (by positivity) hlo
        rw [Real.log_mul (by norm_num) hA_pos.ne', one_div, Real.log_inv] at h1
        linarith
      rw [div_le_iff₀ hlQ_pos]
      calc Real.log (doubleExpGrowingRec.A j : ℝ)
          ≤ Real.log (doubleExpGrowingRec.Q j : ℝ) + Real.log 4 := hlog_le
        _ = (1 + Real.log 4 / Real.log (doubleExpGrowingRec.Q j : ℝ)) *
              Real.log (doubleExpGrowingRec.Q j : ℝ) := by
            field_simp [hlQ_pos.ne']
  have hlimE : Tendsto (fun j : ℕ => ENNReal.ofReal
      (Real.log (doubleExpGrowingRec.A j : ℝ) / Real.log (doubleExpGrowingRec.Q j : ℝ)))
      atTop (nhds 1) := by
    simpa using ENNReal.tendsto_ofReal hlim1
  exact hlimE.limsup_eq

/-- Subcritical distorted Hausdorff dimension for `doubleExpGrowingRec` (`A_j = 2^{2^j}`, `γ_sup = 1`):
for all `0 ≤ τ < 1` and `t ≠ ⊤`,
`dimH (growWeightedLevelSet doubleExpGrowingRec τ t) = ENNReal.ofReal ((1 - τ) / (1 + τ))`. -/
theorem dimH_doubleExpGrowingRec_subcritical {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet doubleExpGrowingRec τ t) =
      ENNReal.ofReal ((1 - τ) / (1 + τ)) ∧
    dimH (growWeightedExactLimitSet doubleExpGrowingRec τ 0) =
      ENNReal.ofReal ((1 - τ) / (1 + τ)) := by
  have htd : growTargetDim doubleExpGrowingRec τ = ENNReal.ofReal ((1 - τ) / (1 + τ)) := by
    by_cases h0 : τ ≤ 0
    · have hτ_eq : τ = 0 := le_antisymm h0 hτ0
      subst hτ_eq; simp [growTargetDim]
    · have hnot1 : ¬ 1 ≤ τ := not_le.mpr hτ1
      have hτ_pos : 0 < τ := not_le.mp h0
      simp only [growTargetDim, h0, ↓reduceIte, hnot1, growGammaSup_doubleExpGrowingRec, mul_one]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hτ_pos.le,
        ← ENNReal.ofReal_div_of_pos (by linarith)]
  rw [← htd]
  exact ⟨dimH_growWeightedLevelSet_eq doubleExpGrowingRec hτ0 hτ1 ht,
    dimH_growWeightedExactLimitSet_zero_eq doubleExpGrowingRec hτ0 hτ1⟩

/-- First supercritical regime (`1 < τ < 2`) for `doubleExpGrowingRec`:
full rank-2 lattice `growLatticeL` is preserved. -/
theorem doubleExpGrowingRec_supercritical_lt_two {τ : ℝ} (hτ1 : 1 < τ) (hτ2 : τ < 2)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet doubleExpGrowingRec τ t = doubleExpGrowingRec.growLatticeL := by
  apply growWeightedLevelSet_eq_lattice_of_mul_gamma_lt_one doubleExpGrowingRec hτ1 ht
  rw [growGammaSup_doubleExpGrowingRec, mul_one, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by linarith)

/-- Second supercritical regime (`τ > 2`) for `doubleExpGrowingRec`:
secondary collapse to the rational sublattice `growRatLattice = ℤ ⊊ growLatticeL`. -/
theorem doubleExpGrowingRec_supercritical_gt_two {τ : ℝ} (hτ2 : 2 < τ)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet doubleExpGrowingRec τ t = doubleExpGrowingRec.growRatLattice := by
  apply growWeightedLevelSet_eq_ratLattice_of_one_lt_mul_gamma doubleExpGrowingRec (by linarith) ht
  rw [growGammaSup_doubleExpGrowingRec, mul_one, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

/-- **Exact Critical Boundary `τ = 2` for `doubleExpGrowingRec` (`A_j = 2^{2^j}`)**:
At the secondary phase-transition boundary `τ_crit = 1 + 1 / γ_sup = 2`:
1. For `t = 0`, `growWeightedLevelSet doubleExpGrowingRec 2 0 = doubleExpGrowingRec.growRatLattice`;
2. The irrational generator `θ = doubleExpGrowingRec.growTheta` satisfies
   `θ ∈ growWeightedLevelSet doubleExpGrowingRec 2 4 \ doubleExpGrowingRec.growRatLattice`;
3. The countable union over finite thresholds recovers the full rank-2 lattice:
   `(⋃ k : ℕ, growWeightedLevelSet doubleExpGrowingRec 2 (k : ℝ≥0∞)) = doubleExpGrowingRec.growLatticeL`. -/
theorem doubleExpGrowingRec_critical_two :
    growWeightedLevelSet doubleExpGrowingRec 2 0 = doubleExpGrowingRec.growRatLattice ∧
    (doubleExpGrowingRec.growTheta ∈ growWeightedLevelSet doubleExpGrowingRec 2 4 ∧
      doubleExpGrowingRec.growTheta ∉ doubleExpGrowingRec.growRatLattice) ∧
    (⋃ k : ℕ, growWeightedLevelSet doubleExpGrowingRec 2 (k : ℝ≥0∞)) =
      doubleExpGrowingRec.growLatticeL := by
  have hg1 : (doubleExpGrowingRec.growGFactor : ℝ) = 1 := by
    exact_mod_cast (mkUnitGrowingRec_growGFactor _ _ _)
  have hratio_bounds : ∀ᶠ j : ℕ in atTop,
      (1 : ℝ) ≤ (doubleExpGrowingRec.A j : ℝ) ^ ((2 : ℝ) - 1) / (doubleExpGrowingRec.Q j : ℝ) ∧
      (doubleExpGrowingRec.A j : ℝ) ^ ((2 : ℝ) - 1) / (doubleExpGrowingRec.Q j : ℝ) ≤ 4 := by
    filter_upwards [eventually_ge_atTop 2] with j hj
    have hQ_pos : (0 : ℝ) < (doubleExpGrowingRec.Q j : ℝ) := by
      exact_mod_cast doubleExpGrowingRec.hQ_pos j
    have hlo := (doubleExpGrowingRec_Q_bounds hj).1
    have hhi := doubleExpGrowingRec_Q_le_A hj
    rw [show (2 : ℝ) - 1 = 1 by ring, Real.rpow_one]
    exact ⟨(one_le_div hQ_pos).mpr hhi, (div_le_iff₀ hQ_pos).mpr (by linarith)⟩
  refine ⟨?_, ?_, ?_⟩
  · refine Subset.antisymm ?_ (growRatLattice_subset_weightedLevelSet doubleExpGrowingRec 2 0)
    intro x hx
    have hxL := growWeightedLevelSet_subset_lattice doubleExpGrowingRec one_lt_two (by simp) hx
    rw [doubleExpGrowingRec.growLatticeL_eq_inv_g] at hxL
    rcases hxL with ⟨m, n, rfl⟩
    by_cases hn : n = 0
    · subst hn; exact ⟨m, by simp⟩
    · exfalso
      have hbd := growWeightedSeq_bounds_of_lattice_irrational doubleExpGrowingRec 2 m hn
      have hn_ge1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hZ : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
        exact_mod_cast hZ
      have hev_ge : ∀ᶠ j : ℕ in atTop,
          ENNReal.ofReal (1 / 6 : ℝ) ≤ ENNReal.ofReal (growWeightedSeq doubleExpGrowingRec 2
            (((m : ℝ) + (n : ℝ) * doubleExpGrowingRec.growTheta) /
              (doubleExpGrowingRec.growGFactor : ℝ)) j) := by
        filter_upwards [hbd, hratio_bounds] with j hj hrat
        have h1 : (1 / 6 : ℝ) ≤ (|(n : ℝ)| * (doubleExpGrowingRec.growGFactor : ℝ) / 6) *
            ((doubleExpGrowingRec.A j : ℝ) ^ ((2 : ℝ) - 1) / (doubleExpGrowingRec.Q j : ℝ)) := by
          rw [hg1, mul_one]
          nlinarith [hrat.1, hn_ge1]
        exact ENNReal.ofReal_le_ofReal (h1.trans hj.1)
      have hle_sup : ENNReal.ofReal (1 / 6 : ℝ) ≤ growWeightedLambda doubleExpGrowingRec 2
          (((m : ℝ) + (n : ℝ) * doubleExpGrowingRec.growTheta) /
            (doubleExpGrowingRec.growGFactor : ℝ)) :=
        le_limsup_of_frequently_le hev_ge.frequently (by isBoundedDefault)
      have h0 : ENNReal.ofReal (1 / 6 : ℝ) ≤ 0 := hle_sup.trans hx
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 6 : ℝ) := ENNReal.ofReal_pos.mpr (by norm_num)
      exact not_lt_of_ge h0 hpos
  · constructor
    · have hbd := growWeightedSeq_bounds_of_lattice_irrational doubleExpGrowingRec 2 0
        (one_ne_zero : (1 : ℤ) ≠ 0)
      have hx_eq : (((0 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * doubleExpGrowingRec.growTheta) /
          (doubleExpGrowingRec.growGFactor : ℝ) = doubleExpGrowingRec.growTheta := by
        rw [hg1]; ring
      rw [hx_eq] at hbd
      change growWeightedLambda doubleExpGrowingRec 2 doubleExpGrowingRec.growTheta ≤ 4
      unfold growWeightedLambda
      have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by norm_num
      rw [h4]
      refine limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hbd, hratio_bounds] with j hj hrat
      apply ENNReal.ofReal_le_ofReal
      have hj2 := hj.2
      rw [hg1] at hj2
      have h1 : |(1 : ℝ)| * 1 = 1 := by norm_num
      linarith [hj2, hrat.2, h1]
    · intro hrat
      unfold doubleExpGrowingRec at hrat
      rw [mkUnitGrowingRec_growRatLattice] at hrat
      rcases hrat with ⟨m, hm⟩
      exact doubleExpGrowingRec.growTheta_irrational ⟨m, hm⟩
  · refine Subset.antisymm ?_ ?_
    · refine iUnion_subset fun k => ?_
      exact growWeightedLevelSet_subset_lattice doubleExpGrowingRec one_lt_two (by simp)
    · intro x hx
      rw [doubleExpGrowingRec.growLatticeL_eq_inv_g] at hx
      rcases hx with ⟨m, n, rfl⟩
      by_cases hn : n = 0
      · subst hn
        refine mem_iUnion.mpr ⟨0, ?_⟩
        apply growRatLattice_subset_weightedLevelSet doubleExpGrowingRec 2 ((0 : ℕ) : ℝ≥0∞)
        exact ⟨m, by simp⟩
      · let K : ℕ := 4 * n.natAbs
        refine mem_iUnion.mpr ⟨K, ?_⟩
        have hbd := growWeightedSeq_bounds_of_lattice_irrational doubleExpGrowingRec 2 m hn
        change growWeightedLambda doubleExpGrowingRec 2 _ ≤ (K : ℝ≥0∞)
        unfold growWeightedLambda
        rw [← ENNReal.ofReal_natCast K]
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [hbd, hratio_bounds] with j hj hrat
        have hn_abs : |(n : ℝ)| = (n.natAbs : ℝ) := by
          rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
        have hK_eq : (K : ℝ) = 4 * |(n : ℝ)| := by dsimp [K]; push_cast; rw [hn_abs]
        have h2 : (|(n : ℝ)| * (doubleExpGrowingRec.growGFactor : ℝ)) *
            ((doubleExpGrowingRec.A j : ℝ) ^ ((2 : ℝ) - 1) / (doubleExpGrowingRec.Q j : ℝ)) ≤
            (K : ℝ) := by
          rw [hg1, mul_one, hK_eq]
          nlinarith [hrat.2, abs_nonneg (n : ℝ)]
        exact ENNReal.ofReal_le_ofReal (hj.2.trans h2)

/-! #### 5.3 Regime III: Super-Double-Exponential Partial Quotients (`A_j = 2 ^ (2 ^ (j^2))`, `γ_sup = ⊤`) -/

/-- Concrete Regime III: `A_j = 2 ^ (2 ^ (j * j))` (`γ_sup = ⊤`). -/
def superDoubleExpGrowingRec : GrowingRecData :=
  mkUnitGrowingRec (fun j => (2 : ℤ) ^ (2 ^ (j * j)))
    (fun j _ => by
      have h1 : 1 ≤ 2 ^ (j * j) := Nat.one_le_two_pow
      calc (2 : ℤ) = (2 : ℤ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℤ) ^ (2 ^ (j * j)) := pow_le_pow_right₀ (by norm_num) h1)
    (by
      have h : Tendsto (fun j : ℕ => (2 : ℝ) ^ j) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt one_lt_two
      refine tendsto_atTop_mono (fun j => ?_) h
      change (2 : ℝ) ^ j ≤ (((2 : ℤ) ^ (2 ^ (j * j)) : ℤ) : ℝ)
      push_cast
      have hj : j ≤ 2 ^ (j * j) := le_trans (Nat.le_mul_self j) Nat.lt_two_pow_self.le
      exact pow_le_pow_right₀ one_le_two hj)

private lemma superDoubleExp_Q_le {j : ℕ} (hj : 1 ≤ j) :
    (superDoubleExpGrowingRec.Q j : ℝ) ≤ (2 : ℝ) ^ (j * 2 ^ ((j - 1) * (j - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = 1 + n := ⟨j - 1, by omega⟩
  have hQ1 : (superDoubleExpGrowingRec.Q 1 : ℝ) = 1 := by
    have h1 : superDoubleExpGrowingRec.Q 1 = 1 := rfl
    rw [h1, Int.cast_one]
  have hhi : (superDoubleExpGrowingRec.Q (1 + n) : ℝ) ≤
      (2 : ℝ) ^ n * ∏ k ∈ Finset.range n, (superDoubleExpGrowingRec.A (1 + k) : ℝ) := by
    clear hj
    induction n with
    | zero => simp [hQ1]
    | succ m ih =>
      have hrec : (superDoubleExpGrowingRec.Q (1 + m + 1) : ℝ) =
          (superDoubleExpGrowingRec.A (1 + m) : ℝ) * (superDoubleExpGrowingRec.Q (1 + m) : ℝ) +
            (superDoubleExpGrowingRec.Q (1 + m - 1) : ℝ) := by
        exact_mod_cast superDoubleExpGrowingRec.hQ_rec (1 + m)
          (by dsimp [superDoubleExpGrowingRec, mkUnitGrowingRec]; omega)
      have hQprev : (superDoubleExpGrowingRec.Q (1 + m - 1) : ℝ) ≤
          (superDoubleExpGrowingRec.Q (1 + m) : ℝ) := by
        rcases m with _ | m'
        · have h0 : (superDoubleExpGrowingRec.Q 0 : ℝ) = 1 := by
            have : superDoubleExpGrowingRec.Q 0 = 1 := rfl; rw [this, Int.cast_one]
          simp [h0, hQ1]
        · exact_mod_cast superDoubleExpGrowingRec.grow_Q_monoOn
            (by dsimp [superDoubleExpGrowingRec, mkUnitGrowingRec]; omega) (by omega)
      have hAm2 : (2 : ℝ) ≤ (superDoubleExpGrowingRec.A (1 + m) : ℝ) :=
        grow_A_ge_two superDoubleExpGrowingRec
          (by dsimp [superDoubleExpGrowingRec, mkUnitGrowingRec]; omega)
      have hQpos : (0 : ℝ) < (superDoubleExpGrowingRec.Q (1 + m) : ℝ) := by
        exact_mod_cast superDoubleExpGrowingRec.hQ_pos _
      have hstep : (superDoubleExpGrowingRec.Q (1 + m + 1) : ℝ) ≤
          2 * (superDoubleExpGrowingRec.A (1 + m) : ℝ) *
            (superDoubleExpGrowingRec.Q (1 + m) : ℝ) := by
        nlinarith
      rw [show 1 + (m + 1) = 1 + m + 1 by omega, Finset.prod_range_succ, pow_succ]
      calc (superDoubleExpGrowingRec.Q (1 + m + 1) : ℝ)
          ≤ (2 * (superDoubleExpGrowingRec.A (1 + m) : ℝ)) *
              (superDoubleExpGrowingRec.Q (1 + m) : ℝ) := hstep
        _ ≤ (2 * (superDoubleExpGrowingRec.A (1 + m) : ℝ)) *
              ((2 : ℝ) ^ m * ∏ k ∈ Finset.range m, (superDoubleExpGrowingRec.A (1 + k) : ℝ)) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (2 : ℝ) ^ m * 2 *
              ((∏ k ∈ Finset.range m, (superDoubleExpGrowingRec.A (1 + k) : ℝ)) *
                (superDoubleExpGrowingRec.A (1 + m) : ℝ)) := by ring
  rw [Nat.add_sub_cancel_left]
  have hprod_le : ∏ k ∈ Finset.range n, (superDoubleExpGrowingRec.A (1 + k) : ℝ) ≤
      (2 : ℝ) ^ (n * 2 ^ (n * n)) := by
    have h1 : ∏ k ∈ Finset.range n, (superDoubleExpGrowingRec.A (1 + k) : ℝ) ≤
        ∏ _k ∈ Finset.range n, (2 : ℝ) ^ (2 ^ (n * n)) := by
      clear hhi hj
      induction n with
      | zero => simp
      | succ m _ =>
        have hterm : ∀ k ∈ Finset.range (m + 1),
            (superDoubleExpGrowingRec.A (1 + k) : ℝ) ≤ (2 : ℝ) ^ (2 ^ ((m + 1) * (m + 1))) := by
          intro k hk
          rw [Finset.mem_range] at hk
          change (((2 : ℤ) ^ (2 ^ ((1 + k) * (1 + k))) : ℤ) : ℝ) ≤ _
          push_cast
          have hle1 : 1 + k ≤ m + 1 := by omega
          have hle2 : (1 + k) * (1 + k) ≤ (m + 1) * (m + 1) := Nat.mul_le_mul hle1 hle1
          exact pow_le_pow_right₀ one_le_two (Nat.pow_le_pow_right (by norm_num) hle2)
        -- Simple induction on range s for product bound:
        have hfin : ∀ s : Finset ℕ, (∀ k ∈ s, (superDoubleExpGrowingRec.A (1 + k) : ℝ) ≤
            (2 : ℝ) ^ (2 ^ ((m + 1) * (m + 1)))) →
            ∏ k ∈ s, (superDoubleExpGrowingRec.A (1 + k) : ℝ) ≤
              ∏ _k ∈ s, (2 : ℝ) ^ (2 ^ ((m + 1) * (m + 1))) := by
          intro s
          refine Finset.induction_on s (by simp) fun a s has ihs hs => ?_
          rw [Finset.prod_insert has, Finset.prod_insert has]
          have ha := hs a (Finset.mem_insert_self a s)
          have hs' := ihs (fun k hk => hs k (Finset.mem_insert_of_mem hk))
          have ha_nn : 0 ≤ (superDoubleExpGrowingRec.A (1 + a) : ℝ) := by
            change (0 : ℝ) ≤ (((2 : ℤ) ^ (2 ^ ((1 + a) * (1 + a))) : ℤ) : ℝ)
            positivity
          exact mul_le_mul ha hs' (Finset.prod_nonneg fun k _ => by
            change (0 : ℝ) ≤ (((2 : ℤ) ^ (2 ^ ((1 + k) * (1 + k))) : ℤ) : ℝ); positivity)
            (by positivity)
        exact hfin _ hterm
    simpa [pow_mul'] using h1
  refine hhi.trans ?_
  calc (2 : ℝ) ^ n * ∏ k ∈ Finset.range n, (superDoubleExpGrowingRec.A (1 + k) : ℝ)
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ (n * 2 ^ (n * n)) :=
        mul_le_mul_of_nonneg_left hprod_le (by positivity)
    _ = (2 : ℝ) ^ (n + n * 2 ^ (n * n)) := (pow_add 2 n _).symm
    _ ≤ (2 : ℝ) ^ ((1 + n) * 2 ^ (n * n)) := by
        apply pow_le_pow_right₀ one_le_two
        have h1 : n ≤ 2 ^ (n * n) := le_trans (Nat.le_mul_self n) Nat.lt_two_pow_self.le
        linarith

/-- For `superDoubleExpGrowingRec` (`A_j = 2^{2^{j^2}}`), `log A_j / log Q_j → ∞` and
`growGammaSup superDoubleExpGrowingRec = ⊤`. -/
theorem growGammaSup_superDoubleExpGrowingRec : growGammaSup superDoubleExpGrowingRec = ⊤ := by
  rw [eq_top_iff]
  refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
  have hy_ne_top : y ≠ ⊤ := ne_of_lt hy
  let M : ℝ := y.toReal + 1
  have hM_pos : 0 < M := by positivity
  have hratio_atTop : Tendsto (fun j : ℕ => ((2 : ℝ) ^ j) / ((j : ℝ) + 1)) atTop atTop := by
    have h1 : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop 5] with j hj
    have hquad : (j + 1) * j ≤ 2 ^ j := by
      clear hy hy_ne_top hM_pos h1
      induction j, hj using Nat.le_induction with
      | base => decide
      | succ k hk ih =>
        have hk2 : 2 * k + 2 ≤ (k + 1) * k := by nlinarith
        calc (k + 1 + 1) * (k + 1) = (k + 1) * k + (2 * k + 2) := by ring
          _ ≤ (k + 1) * k + (k + 1) * k := by omega
          _ ≤ 2 ^ k + 2 ^ k := add_le_add ih ih
          _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_two]
    have hquadR : ((j : ℝ) + 1) * (j : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hquad
    have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    exact (le_div_iff₀ hj1_pos).mpr (by linarith)
  have hevM := hratio_atTop.eventually_ge_atTop M
  have hev_gam : ∀ᶠ j : ℕ in atTop,
      y ≤ ENNReal.ofReal (Real.log (superDoubleExpGrowingRec.A j : ℝ) /
        Real.log (superDoubleExpGrowingRec.Q j : ℝ)) := by
    filter_upwards [hevM, eventually_ge_atTop 2] with j hjM hj2
    have hQ_pos : (0 : ℝ) < (superDoubleExpGrowingRec.Q j : ℝ) := by
      exact_mod_cast superDoubleExpGrowingRec.hQ_pos j
    have hlQ_pos : 0 < Real.log (superDoubleExpGrowingRec.Q j : ℝ) :=
      grow_log_Q_pos superDoubleExpGrowingRec
        (by dsimp [superDoubleExpGrowingRec, mkUnitGrowingRec]; omega)
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hQ_ub := superDoubleExp_Q_le (by omega : 1 ≤ j)
    have hlogQ_le : Real.log (superDoubleExpGrowingRec.Q j : ℝ) ≤
        ((j : ℝ) * (2 : ℝ) ^ ((j - 1) * (j - 1))) * Real.log 2 := by
      have h1 := Real.log_le_log hQ_pos hQ_ub
      rw [Real.log_pow] at h1
      push_cast at h1
      exact h1
    have hlogA_eq : Real.log (superDoubleExpGrowingRec.A j : ℝ) =
        ((2 : ℝ) ^ (j * j)) * Real.log 2 := by
      change Real.log (((2 : ℤ) ^ (2 ^ (j * j)) : ℤ) : ℝ) = _
      push_cast; rw [Real.log_pow]; push_cast; rfl
    have hexp_ge : (j - 1) * (j - 1) + j ≤ j * j := by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have hsub : m + 2 - 1 = m + 1 := by omega
      rw [hsub]
      nlinarith
    have hpow_ge : (2 : ℝ) ^ j * (2 : ℝ) ^ ((j - 1) * (j - 1)) ≤ (2 : ℝ) ^ (j * j) := by
      rw [← pow_add, add_comm j]
      exact pow_le_pow_right₀ one_le_two hexp_ge
    have hratio_ge : M ≤ Real.log (superDoubleExpGrowingRec.A j : ℝ) /
        Real.log (superDoubleExpGrowingRec.Q j : ℝ) := by
      calc M ≤ (2 : ℝ) ^ j / ((j : ℝ) + 1) := hjM
        _ ≤ (2 : ℝ) ^ j / (j : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast (by omega : 0 < j))
              (by linarith)
        _ = ((2 : ℝ) ^ j * (2 : ℝ) ^ ((j - 1) * (j - 1)) * Real.log 2) /
              (((j : ℝ) * (2 : ℝ) ^ ((j - 1) * (j - 1))) * Real.log 2) := by
            have hpow_ne : (2 : ℝ) ^ ((j - 1) * (j - 1)) ≠ 0 := by positivity
            field_simp [hl2.ne', hpow_ne]
        _ ≤ (((2 : ℝ) ^ (j * j)) * Real.log 2) /
              (((j : ℝ) * (2 : ℝ) ^ ((j - 1) * (j - 1))) * Real.log 2) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hpow_ge hl2.le
        _ ≤ Real.log (superDoubleExpGrowingRec.A j : ℝ) /
              Real.log (superDoubleExpGrowingRec.Q j : ℝ) := by
            rw [hlogA_eq]
            exact div_le_div_of_nonneg_left (by positivity) hlQ_pos hlogQ_le
    calc y = ENNReal.ofReal y.toReal := (ENNReal.ofReal_toReal hy_ne_top).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (by dsimp [M]; linarith)
      _ ≤ ENNReal.ofReal (Real.log (superDoubleExpGrowingRec.A j : ℝ) /
            Real.log (superDoubleExpGrowingRec.Q j : ℝ)) :=
          ENNReal.ofReal_le_ofReal hratio_ge
  exact le_limsup_of_frequently_le hev_gam.frequently (by isBoundedDefault)

/-- Subcritical & supercritical phase diagram for `superDoubleExpGrowingRec` (`γ_sup = ⊤`):
1. At `τ = 0`, `dimH = 1`;
2. For all `0 < τ < 1`, the subcritical Hausdorff dimension collapses completely to `0`;
3. For all `τ > 1`, the supercritical level set collapses immediately to `growRatLattice = ℤ`
   (no intermediate `growLatticeL` regime exists). -/
theorem dimH_superDoubleExpGrowingRec_zero {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet superDoubleExpGrowingRec 0 t) = 1 ∧
    dimH (growWeightedExactLimitSet superDoubleExpGrowingRec 0 0) = 1 := by
  have htd : growTargetDim superDoubleExpGrowingRec 0 = 1 := by simp [growTargetDim]
  rw [← htd]
  exact ⟨dimH_growWeightedLevelSet_eq superDoubleExpGrowingRec le_rfl zero_lt_one ht,
    dimH_growWeightedExactLimitSet_zero_eq superDoubleExpGrowingRec le_rfl zero_lt_one⟩

theorem dimH_superDoubleExpGrowingRec_pos_subcritical {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet superDoubleExpGrowingRec τ t) = 0 ∧
    dimH (growWeightedExactLimitSet superDoubleExpGrowingRec τ 0) = 0 := by
  have htd : growTargetDim superDoubleExpGrowingRec τ = 0 := by
    have hnot0 : ¬ τ ≤ 0 := not_le.mpr hτ0
    have hnot1 : ¬ 1 ≤ τ := not_le.mpr hτ1
    simp [growTargetDim, hnot0, hnot1, growGammaSup_superDoubleExpGrowingRec,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hτ0).ne']
  rw [← htd]
  exact ⟨dimH_growWeightedLevelSet_eq superDoubleExpGrowingRec hτ0.le hτ1 ht,
    dimH_growWeightedExactLimitSet_zero_eq superDoubleExpGrowingRec hτ0.le hτ1⟩

theorem superDoubleExpGrowingRec_supercritical {τ : ℝ} (hτ : 1 < τ) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    growWeightedLevelSet superDoubleExpGrowingRec τ t = superDoubleExpGrowingRec.growRatLattice :=
  growWeightedLevelSet_eq_ratLattice_of_gamma_top superDoubleExpGrowingRec
    growGammaSup_superDoubleExpGrowingRec hτ ht

end

end GeneralGrowingDim

