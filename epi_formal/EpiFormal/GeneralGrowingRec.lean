import Mathlib
import EpiFormal.TrichotomyAndPolyExtension
import EpiFormal.PolyGaugeAndPhaseTransition
import EpiFormal.GaugeCircle

/-!
# Universal Growing-Quotient Recurrences (`GrowingRecData`, `GeneralGrowingRec`)

This module extends the polynomial-growth theory (`PolyRecData`) to ANY three-term integer
recurrence `Q_{j+1} = A_j * Q_j + Q_{j-1}` with `A_j ≥ 2` (`j ≥ J₀`) and `A_j → ∞`:

1. `PolyRecData.toGrowingRecData`: canonical coercion from polynomial growth to `GrowingRecData`.
2. Super-exponential denominator growth `B^n / Q_n → 0` and `n / log Q_n → 0` (no factorial rate
   needed), Casorati fundamental solutions `U_j, V_j`, limits `α_U, α_V`, irrational slope `θ`,
   and intrinsic rank-2 lattice `L_G = ℤ α_U + ℤ α_V` (`1 ∈ L_G` unconditionally).
3. Kraaikamp–Liardet exact ratio equivalence `growKLRatio G x = growLambda G x`, zero-level
   equivalence `growLambda G x = 0 ↔ x ∈ L_G`, arbitrary bounded digit realization
   `grow_telescoping_digit_realize`, full spectrum `growLambda(ℝ) = ℕ ∪ {⊤}`, and open spectral
   gaps `(k, k + 1)`.
4. Universal `dimH {growLambda ≤ t} = 0`, `Leb {growLambda < ⊤} = 0`, `dimH {growLambda = ⊤} = 1`,
   and universal critical gauges `h_k^G(1/Q_n) = (2k+1)^{-n}` / `g_2^G(1/Q_n) = 2^{-n}` with the
   three-way positive-level splitting on both `ℝ` and `UnitAddCircle`.
-/

open Real Filter Topology Set MeasureTheory Classification SpectralGap DimHCore DimHFinite
  FullSpectrumDiscrete GaugeNull GaugeExact WeightedExactDim TrichotomyAndPolyExtension
  PolyGaugeAndPhaseTransition
open scoped ENNReal NNReal

namespace GeneralGrowingRec

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: `GrowingRecData` Structure, Embedding, and Growth Estimates -/

/-- General growing-quotient three-term integer recurrence `Q_{j+1} = A_j * Q_j + Q_{j-1}`. -/
structure GrowingRecData where
  J₀ : ℕ
  hJ₀ : 1 ≤ J₀
  A : ℕ → ℤ
  hA_ge : ∀ j : ℕ, J₀ ≤ j → (2 : ℤ) ≤ A j
  hA_tendsto : Tendsto (fun j : ℕ => (A j : ℝ)) atTop atTop
  Q : ℕ → ℤ
  hQ_pos : ∀ j : ℕ, 0 < Q j
  hQ_rec : ∀ j : ℕ, J₀ ≤ j → Q (j + 1) = A j * Q j + Q (j - 1)

/-- Embed any `PolyRecData` cleanly into `GrowingRecData`. -/
def PolyRecData.toGrowingRecData (P : PolyRecData) : GrowingRecData where
  J₀ := P.J₀
  hJ₀ := P.hJ₀
  A := P.A
  hA_ge := fun j hj => by
    have hjr : (P.J₀ : ℤ) ^ P.r ≤ (j : ℤ) ^ P.r := by
      exact_mod_cast Nat.pow_le_pow_left hj P.r
    have hc0 : (0 : ℤ) ≤ (P.c : ℤ) := by positivity
    have hmul : (P.c : ℤ) * (P.J₀ : ℤ) ^ P.r ≤ (P.c : ℤ) * (j : ℤ) ^ P.r :=
      Int.mul_le_mul_of_nonneg_left hjr hc0
    unfold PolyRecData.A
    linarith [P.hinit]
  hA_tendsto := by
    have hc1 : (1 : ℝ) ≤ (P.c : ℝ) := by exact_mod_cast P.hc
    have hlin : Tendsto (fun j : ℕ => (j : ℝ) + (P.d : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjr : (j : ℝ) ≤ (j : ℝ) ^ P.r := by
      calc (j : ℝ) = (j : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (j : ℝ) ^ P.r := pow_le_pow_right₀ hj1 P.hr
    unfold PolyRecData.A
    push_cast
    nlinarith
  Q := P.Q
  hQ_pos := P.hQ_pos
  hQ_rec := P.hQ_rec

namespace GrowingRecData

private lemma tendsto_zero_iff_abs_tendsto_zero {f : ℕ → ℝ} :
    Tendsto f atTop (nhds 0) ↔ Tendsto (fun n : ℕ => |f n|) atTop (nhds 0) := by
  simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero (f := f))

private lemma limsup_add_const_le (f : ℕ → ℝ≥0∞) {c : ℝ≥0∞} (_hc : c ≠ ⊤) :
    limsup (fun j : ℕ => f j + c) atTop ≤ limsup f atTop + c := by
  by_cases htop : limsup f atTop = ⊤
  · simp [htop]
  · have hbd : ∀ ε : ℝ, 0 < ε →
        limsup (fun j : ℕ => f j + c) atTop ≤ limsup f atTop + c + ENNReal.ofReal ε := by
      intro ε hε
      have hlt : limsup f atTop < limsup f atTop + ENNReal.ofReal ε :=
        ENNReal.lt_add_right htop (ENNReal.ofReal_pos.mpr hε).ne'
      have hev := Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
      refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hev] with j hj
      calc f j + c ≤ (limsup f atTop + ENNReal.ofReal ε) + c := add_le_add hj.le le_rfl
        _ = limsup f atTop + c + ENNReal.ofReal ε := add_right_comm _ _ _
    have hlim : Tendsto (fun n : ℕ => limsup f atTop + c + ENNReal.ofReal (1 / (n + 1 : ℝ)))
        atTop (nhds (limsup f atTop + c)) := by
      have hinv : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add hinv
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbd _ (by positivity))

lemma grow_Q_succ_gt_A_mul (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.A j * G.Q j < G.Q (j + 1) := by
  have hrec := G.hQ_rec j hj
  have hpos := G.hQ_pos (j - 1)
  linarith

lemma grow_Q_succ_ge_two_mul (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    2 * G.Q j < G.Q (j + 1) := by
  have h1 : 2 * G.Q j ≤ G.A j * G.Q j :=
    mul_le_mul_of_nonneg_right (G.hA_ge j hj) (G.hQ_pos j).le
  exact lt_of_le_of_lt h1 (grow_Q_succ_gt_A_mul G hj)

lemma grow_Q_lt_succ (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.Q j < G.Q (j + 1) := by
  have h := grow_Q_succ_ge_two_mul G hj
  have hp := G.hQ_pos j
  linarith

lemma grow_Q_strictMonoOn (G : GrowingRecData) : StrictMonoOn G.Q (Set.Ici G.J₀) := by
  intro a ha b _ hab
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by omega⟩
  have haJ : G.J₀ ≤ a := ha
  have hstep : ∀ k : ℕ, G.Q a < G.Q (a + k + 1) := by
    intro k
    induction k with
    | zero => exact grow_Q_lt_succ G haJ
    | succ k ih => exact lt_trans ih (grow_Q_lt_succ G (by omega))
  exact hstep k

lemma grow_Q_monoOn (G : GrowingRecData) {m n : ℕ} (hm : G.J₀ ≤ m) (hmn : m ≤ n) :
    G.Q m ≤ G.Q n :=
  (grow_Q_strictMonoOn G).monotoneOn hm (le_trans hm hmn) hmn

lemma grow_Q_geom (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) (m : ℕ) :
    (2 : ℝ) ^ m * (G.Q j : ℝ) ≤ (G.Q (j + m) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := grow_Q_succ_ge_two_mul G (show G.J₀ ≤ j + m by omega)
    have h2 : 2 * (G.Q (j + m) : ℝ) ≤ (G.Q (j + m + 1) : ℝ) := by exact_mod_cast h.le
    have hadd : j + (m + 1) = j + m + 1 := by omega
    rw [hadd]
    calc (2 : ℝ) ^ (m + 1) * (G.Q j : ℝ)
        = 2 * ((2 : ℝ) ^ m * (G.Q j : ℝ)) := by ring
      _ ≤ 2 * (G.Q (j + m) : ℝ) := by gcongr
      _ ≤ (G.Q (j + m + 1) : ℝ) := h2

lemma grow_Q_tendsto_atTop (G : GrowingRecData) :
    Tendsto (fun j : ℕ => (G.Q j : ℝ)) atTop atTop := by
  have hQ0 : (0 : ℝ) < (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
  have htwo : Tendsto (fun m : ℕ => (2 : ℝ) ^ m * (G.Q G.J₀ : ℝ)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hQ0
  have hshift : Tendsto (fun m : ℕ => (G.Q (G.J₀ + m) : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun m => grow_Q_geom G le_rfl m) htwo
  rw [← tendsto_add_atTop_iff_nat G.J₀]
  exact hshift.congr (fun m => by rw [Nat.add_comm m G.J₀])

lemma grow_Q_prev_lt_half (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j) :
    0 < (G.Q (j - 1) : ℝ) ∧ (G.Q (j - 1) : ℝ) < (1 / 2 : ℝ) * (G.Q j : ℝ) := by
  have h := grow_Q_succ_ge_two_mul G (show G.J₀ ≤ j - 1 by omega)
  have hsub : j - 1 + 1 = j := by omega
  rw [hsub] at h
  have hQ : 2 * (G.Q (j - 1) : ℝ) < (G.Q j : ℝ) := by exact_mod_cast h
  have hpos : 0 < (G.Q (j - 1) : ℝ) := by exact_mod_cast G.hQ_pos (j - 1)
  exact ⟨hpos, by linarith⟩

lemma grow_Q_ratio_bounds (G : GrowingRecData) {j : ℕ} (hj : G.J₀ + 1 ≤ j) :
    (G.A j : ℝ) < (G.Q (j + 1) : ℝ) / (G.Q j : ℝ) ∧
    (G.Q (j + 1) : ℝ) / (G.Q j : ℝ) < (G.A j : ℝ) + 1 := by
  have hQpos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hprev := grow_Q_prev_lt_half G hj
  have hrec : (G.Q (j + 1) : ℝ) = (G.A j : ℝ) * (G.Q j : ℝ) + (G.Q (j - 1) : ℝ) := by
    exact_mod_cast G.hQ_rec j (by omega)
  constructor
  · rw [lt_div_iff₀ hQpos, hrec]; linarith [hprev.1]
  · rw [div_lt_iff₀ hQpos, hrec]; linarith [hprev.2]

lemma grow_A_pos (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) : (0 : ℝ) < (G.A j : ℝ) := by
  have h := G.hA_ge j hj
  exact_mod_cast (by linarith : (0 : ℤ) < G.A j)

lemma grow_prod_A_le_Q (G : GrowingRecData) {J : ℕ} (hJ : G.J₀ ≤ J) :
    ∀ n : ℕ, (∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * (G.Q J : ℝ) ≤ (G.Q (J + n) : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (G.A (J + n) : ℝ) * (G.Q (J + n) : ℝ) ≤ (G.Q (J + n + 1) : ℝ) := by
      exact_mod_cast (grow_Q_succ_gt_A_mul G (by omega)).le
    have hAn : (0 : ℝ) ≤ (G.A (J + n) : ℝ) := (grow_A_pos G (by omega)).le
    rw [Finset.prod_range_succ, show J + (n + 1) = J + n + 1 by omega]
    calc (∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * (G.A (J + n) : ℝ) * (G.Q J : ℝ)
        = (G.A (J + n) : ℝ) *
            ((∏ k ∈ Finset.range n, (G.A (J + k) : ℝ)) * (G.Q J : ℝ)) := by ring
      _ ≤ (G.A (J + n) : ℝ) * (G.Q (J + n) : ℝ) := mul_le_mul_of_nonneg_left ih hAn
      _ ≤ (G.Q (J + n + 1) : ℝ) := hstep

lemma grow_Q_le_prod_A_add_one (G : GrowingRecData) {J : ℕ} (hJ : G.J₀ + 1 ≤ J) :
    ∀ n : ℕ, (G.Q (J + n) : ℝ) ≤
      (∏ k ∈ Finset.range n, ((G.A (J + k) : ℝ) + 1)) * (G.Q J : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hQpos : (0 : ℝ) < (G.Q (J + n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hrat := (grow_Q_ratio_bounds G (j := J + n) (by omega)).2
    have hstep : (G.Q (J + n + 1) : ℝ) ≤ ((G.A (J + n) : ℝ) + 1) * (G.Q (J + n) : ℝ) :=
      (div_lt_iff₀ hQpos).mp hrat |>.le
    have hAnn : 0 ≤ (G.A (J + n) : ℝ) + 1 := by
      linarith [(grow_A_pos G (j := J + n) (by omega)).le]
    rw [Finset.prod_range_succ, show J + (n + 1) = J + n + 1 by omega]
    calc (G.Q (J + n + 1) : ℝ)
        ≤ ((G.A (J + n) : ℝ) + 1) * (G.Q (J + n) : ℝ) := hstep
      _ ≤ ((G.A (J + n) : ℝ) + 1) *
            ((∏ k ∈ Finset.range n, ((G.A (J + k) : ℝ) + 1)) * (G.Q J : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hAnn
      _ = (∏ k ∈ Finset.range n, ((G.A (J + k) : ℝ) + 1)) * ((G.A (J + n) : ℝ) + 1) *
            (G.Q J : ℝ) := by ring

/-- Super-exponential tail domination: for EVERY `B : ℝ`, `B ^ n / Q_n → 0`. -/
theorem grow_pow_div_Q_tendsto_zero (G : GrowingRecData) (B : ℝ) :
    Tendsto (fun n : ℕ => B ^ n / (G.Q n : ℝ)) atTop (nhds 0) := by
  let M : ℝ := max |B| 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (G.hA_tendsto.eventually_ge_atTop (2 * M))
  let N := max G.J₀ N0
  have hNJ₀ : G.J₀ ≤ N := le_max_left _ _
  have hgeom : ∀ m : ℕ, (2 * M) ^ m * (G.Q N : ℝ) ≤ (G.Q (N + m) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hAm : 2 * M ≤ (G.A (N + m) : ℝ) := hN0 (N + m) (by omega)
      have hQpos : (0 : ℝ) ≤ (G.Q (N + m) : ℝ) := by exact_mod_cast (G.hQ_pos _).le
      have hstep : (G.A (N + m) : ℝ) * (G.Q (N + m) : ℝ) ≤ (G.Q (N + m + 1) : ℝ) := by
        exact_mod_cast (grow_Q_succ_gt_A_mul G (by omega)).le
      have hadd : N + (m + 1) = N + m + 1 := by omega
      rw [hadd]
      calc (2 * M) ^ (m + 1) * (G.Q N : ℝ)
          = (2 * M) * ((2 * M) ^ m * (G.Q N : ℝ)) := by ring
        _ ≤ (2 * M) * (G.Q (N + m) : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (G.A (N + m) : ℝ) * (G.Q (N + m) : ℝ) := mul_le_mul_of_nonneg_right hAm hQpos
        _ ≤ (G.Q (N + m + 1) : ℝ) := hstep
  let C : ℝ := M ^ N / (G.Q N : ℝ)
  have hQN : (0 : ℝ) < (G.Q N : ℝ) := by exact_mod_cast G.hQ_pos N
  have hC_nn : 0 ≤ C := by positivity
  have hbound : ∀ n : ℕ, N ≤ n → |B ^ n / (G.Q n : ℝ)| ≤ C * (1 / 2 : ℝ) ^ (n - N) := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hQn_pos : (0 : ℝ) < (G.Q (N + m) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hB_le : |B| ^ (N + m) ≤ M ^ N * M ^ m := by
      rw [← pow_add]
      exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) _
    rw [abs_div, abs_pow, abs_of_pos hQn_pos, Nat.add_sub_cancel_left]
    calc |B| ^ (N + m) / (G.Q (N + m) : ℝ)
        ≤ (M ^ N * M ^ m) / ((2 * M) ^ m * (G.Q N : ℝ)) := by
          exact div_le_div₀ (by positivity) hB_le (by positivity) (hgeom m)
      _ = (M ^ N / (G.Q N : ℝ)) * (1 / 2 : ℝ) ^ m := by
          rw [mul_pow, one_div, inv_pow]
          field_simp [hMpos.ne', hQN.ne']
  have h0 : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ (n - N)) atTop (nhds 0) := by
    have ht : Tendsto (fun m : ℕ => C * (1 / 2 : ℝ) ^ m) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    exact (ht.comp (tendsto_sub_atTop_nat N)).congr (fun _ => rfl)
  have habs0 : Tendsto (fun n : ℕ => |B ^ n / (G.Q n : ℝ)|) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (eventually_atTop.mpr ⟨N, hbound⟩)
  exact tendsto_zero_iff_abs_tendsto_zero.mpr habs0

lemma grow_pow_div_Q_rpow_tendsto_zero (G : GrowingRecData) {B : ℝ} (hB : 0 ≤ B)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => B ^ n / (G.Q n : ℝ) ^ s) atTop (nhds 0) := by
  let C : ℝ := B ^ (1 / s)
  have hC_nn : 0 ≤ C := Real.rpow_nonneg hB _
  have hlimC := grow_pow_div_Q_tendsto_zero G C
  have hrpow : Tendsto (fun n : ℕ => (C ^ n / (G.Q n : ℝ)) ^ s) atTop (nhds 0) := by
    have h0 := (Real.continuousAt_rpow_const 0 s (Or.inr hs.le)).tendsto.comp hlimC
    have h1 : Tendsto (fun n : ℕ => (C ^ n / (G.Q n : ℝ)) ^ s) atTop (nhds ((0 : ℝ) ^ s)) := h0
    simpa [Real.zero_rpow hs.ne'] using h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (pow_nonneg hB _) (Real.rpow_nonneg (by exact_mod_cast (G.hQ_pos n).le) _)) ?_
  filter_upwards with n
  have hQ_pos : (0 : ℝ) < (G.Q n : ℝ) := by exact_mod_cast G.hQ_pos n
  have hCs : C ^ s = B := by
    dsimp [C]
    rw [← Real.rpow_mul hB, one_div_mul_cancel hs.ne', Real.rpow_one]
  have hnum : (C ^ n) ^ s = B ^ n := by
    calc (C ^ n) ^ s = ((C ^ (n : ℝ)) ^ s) := by rw [Real.rpow_natCast]
      _ = C ^ ((n : ℝ) * s) := (Real.rpow_mul hC_nn (n : ℝ) s).symm
      _ = C ^ (s * (n : ℝ)) := by rw [mul_comm (n : ℝ) s]
      _ = (C ^ s) ^ (n : ℝ) := Real.rpow_mul hC_nn s (n : ℝ)
      _ = B ^ n := by rw [hCs, Real.rpow_natCast]
  rw [Real.div_rpow (pow_nonneg hC_nn n) hQ_pos.le, hnum]

/-- Universal sub-logarithmic index ratio `n / log Q_n → 0` for any growing quotient. -/
theorem grow_nat_div_log_Q_tendsto_zero (G : GrowingRecData) :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log (G.Q n : ℝ)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let M : ℝ := Real.exp (2 / ε)
  have hM1 : 1 < M := Real.one_lt_exp_iff.mpr (by positivity)
  have hMpos : 0 < M := lt_trans zero_lt_one hM1
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (G.hA_tendsto.eventually_ge_atTop M)
  let N := max G.J₀ N0
  have hN_pow : ∀ m : ℕ, M ^ m * (G.Q N : ℝ) ≤ (G.Q (N + m) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hAm : M ≤ (G.A (N + m) : ℝ) := hN0 (N + m) (by omega)
      have hQpos : (0 : ℝ) ≤ (G.Q (N + m) : ℝ) := by exact_mod_cast (G.hQ_pos _).le
      have hstep : (G.A (N + m) : ℝ) * (G.Q (N + m) : ℝ) ≤ (G.Q (N + m + 1) : ℝ) := by
        exact_mod_cast (grow_Q_succ_gt_A_mul G (by omega)).le
      have hadd : N + (m + 1) = N + m + 1 := by omega
      rw [hadd]
      calc M ^ (m + 1) * (G.Q N : ℝ) = M * (M ^ m * (G.Q N : ℝ)) := by ring
        _ ≤ M * (G.Q (N + m) : ℝ) := mul_le_mul_of_nonneg_left ih hMpos.le
        _ ≤ (G.A (N + m) : ℝ) * (G.Q (N + m) : ℝ) := mul_le_mul_of_nonneg_right hAm hQpos
        _ ≤ (G.Q (N + m + 1) : ℝ) := hstep
  let N1 := max (4 * N + 4) (Nat.ceil (4 / ε) + 1)
  refine ⟨N1, fun n hn => ?_⟩
  have hn_4N : 4 * N + 4 ≤ n := le_trans (le_max_left _ _) hn
  have hN_n : N ≤ n := by omega
  have hm_ge : (n : ℝ) / 2 ≤ ((n - N : ℕ) : ℝ) := by
    have h1 : n ≤ 2 * (n - N) := by omega
    have h2 : (n : ℝ) ≤ 2 * ((n - N : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hQN_ge1 : (1 : ℝ) ≤ (G.Q N : ℝ) := by exact_mod_cast G.hQ_pos N
  have hQn_ge : M ^ (n - N) ≤ (G.Q n : ℝ) := by
    have h1 := hN_pow (n - N)
    rw [Nat.add_sub_of_le hN_n] at h1
    exact (le_mul_of_one_le_right (pow_nonneg hMpos.le _) hQN_ge1).trans h1
  have hlog_ge : ((n - N : ℕ) : ℝ) * (2 / ε) ≤ Real.log (G.Q n : ℝ) := by
    have h1 := Real.log_le_log (pow_pos hMpos _) hQn_ge
    rw [Real.log_pow, Real.log_exp] at h1
    exact h1
  have hlog_ge2 : (n : ℝ) / ε ≤ Real.log (G.Q n : ℝ) := by
    have h1 : (n : ℝ) / ε ≤ ((n - N : ℕ) : ℝ) * (2 / ε) := by
      have : (n : ℝ) / ε = ((n : ℝ) / 2) * (2 / ε) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hm_ge (by positivity)
    exact h1.trans hlog_ge
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog_pos : 0 < Real.log (G.Q n : ℝ) := lt_of_lt_of_le (div_pos hn_pos hε) hlog_ge2
  have hdiv_le : (n : ℝ) / Real.log (G.Q n : ℝ) ≤ ε := by
    rw [div_le_iff₀ hlog_pos]
    have := (div_le_iff₀ hε).mp hlog_ge2
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hn_pos.le hlog_pos.le)]
  have hstrict : (n : ℝ) / Real.log (G.Q n : ℝ) < ε := by
    have hm_strict : (n : ℝ) * (3 / 4) ≤ ((n - N : ℕ) : ℝ) := by
      have h1 : 3 * n ≤ 4 * (n - N) := by omega
      have h2 : 3 * (n : ℝ) ≤ 4 * ((n - N : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hlog_gt : (3 / 2 : ℝ) * ((n : ℝ) / ε) ≤ Real.log (G.Q n : ℝ) := by
      calc (3 / 2 : ℝ) * ((n : ℝ) / ε) = ((n : ℝ) * (3 / 4)) * (2 / ε) := by ring
        _ ≤ ((n - N : ℕ) : ℝ) * (2 / ε) := mul_le_mul_of_nonneg_right hm_strict (by positivity)
        _ ≤ Real.log (G.Q n : ℝ) := hlog_ge
    calc (n : ℝ) / Real.log (G.Q n : ℝ)
        ≤ (n : ℝ) / ((3 / 2 : ℝ) * ((n : ℝ) / ε)) :=
          div_le_div_of_nonneg_left hn_pos.le (by positivity) hlog_gt
      _ = (2 / 3 : ℝ) * ε := by field_simp [hn_pos.ne', hε.ne']
      _ < ε := by linarith
  exact hstrict

/-! ### Part 2: Fundamental Solutions, Casorati Identity, Irrational Slope, and Rank-2 Lattice -/

/-- Fundamental solution `U_j` initialized by `U_{J₀-1} = 1, U_{J₀} = 0`. -/
def growFundU (G : GrowingRecData) : ℕ → ℤ
  | n =>
      if n < G.J₀ then if n + 1 = G.J₀ then 1 else 0
      else if n = G.J₀ then 0
      else G.A (n - 1) * growFundU G (n - 1) + growFundU G (n - 2)
termination_by n => n

/-- Fundamental solution `V_j` initialized by `V_{J₀-1} = 0, V_{J₀} = 1`. -/
def growFundV (G : GrowingRecData) : ℕ → ℤ
  | n =>
      if n < G.J₀ then 0
      else if n = G.J₀ then 1
      else G.A (n - 1) * growFundV G (n - 1) + growFundV G (n - 2)
termination_by n => n

lemma growFundU_init0 (G : GrowingRecData) : G.growFundU (G.J₀ - 1) = 1 := by
  have h1 : G.J₀ - 1 < G.J₀ := Nat.sub_lt G.hJ₀ zero_lt_one
  have h2 : G.J₀ - 1 + 1 = G.J₀ := Nat.sub_add_cancel G.hJ₀
  unfold growFundU
  simp [h1, h2]

lemma growFundU_init1 (G : GrowingRecData) : G.growFundU G.J₀ = 0 := by
  unfold growFundU
  simp

lemma growFundU_rec (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growFundU (j + 1) = G.A j * G.growFundU j + G.growFundU (j - 1) := by
  have h1 : ¬ (j + 1 < G.J₀) := by omega
  have h2 : j + 1 ≠ G.J₀ := by omega
  conv_lhs => unfold growFundU
  simp [h1, h2]

lemma growFundV_init0 (G : GrowingRecData) : G.growFundV (G.J₀ - 1) = 0 := by
  have h1 : G.J₀ - 1 < G.J₀ := Nat.sub_lt G.hJ₀ zero_lt_one
  unfold growFundV
  simp [h1]

lemma growFundV_init1 (G : GrowingRecData) : G.growFundV G.J₀ = 1 := by
  unfold growFundV
  simp

lemma growFundV_rec (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growFundV (j + 1) = G.A j * G.growFundV j + G.growFundV (j - 1) := by
  have h1 : ¬ (j + 1 < G.J₀) := by omega
  have h2 : j + 1 ≠ G.J₀ := by omega
  conv_lhs => unfold growFundV
  simp [h1, h2]

lemma grow_Q_eq_lincomb (G : GrowingRecData) {j : ℕ} (hj : G.J₀ - 1 ≤ j) :
    G.Q j = G.Q (G.J₀ - 1) * G.growFundU j + G.Q G.J₀ * G.growFundV j := by
  obtain ⟨n, hn⟩ : ∃ n, j = (G.J₀ - 1) + n := ⟨j - (G.J₀ - 1), by omega⟩
  subst hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · rw [Nat.add_zero, growFundU_init0, growFundV_init0]; ring
    · have h1 : G.J₀ - 1 + 1 = G.J₀ := Nat.sub_add_cancel G.hJ₀
      rw [h1, growFundU_init1, growFundV_init1]; ring
    · have hk : G.J₀ ≤ G.J₀ - 1 + (k + 1) := by omega
      have hQ := G.hQ_rec (G.J₀ - 1 + (k + 1)) hk
      have hU := G.growFundU_rec hk
      have hV := G.growFundV_rec hk
      have ih1 := ih (k + 1) (by omega) (by omega)
      have ih0 := ih k (by omega) (by omega)
      have hs1 : G.J₀ - 1 + (k + 1) + 1 = G.J₀ - 1 + (k + 2) := by omega
      have hs0 : G.J₀ - 1 + (k + 1) - 1 = G.J₀ - 1 + k := by omega
      rw [hs1, hs0] at hQ hU hV
      rw [hQ, hU, hV, ih1, ih0]
      ring

theorem grow_casorati (G : GrowingRecData) {j : ℕ} (hj : G.J₀ - 1 ≤ j) :
    G.growFundU j * G.growFundV (j + 1) - G.growFundU (j + 1) * G.growFundV j =
      (-1 : ℤ) ^ (j + 1 - G.J₀) := by
  obtain ⟨n, hn⟩ : ∃ n, j = (G.J₀ - 1) + n := ⟨j - (G.J₀ - 1), by omega⟩
  subst hn
  induction n with
  | zero =>
    have hsub : G.J₀ - 1 + 0 + 1 - G.J₀ = 0 := by have := G.hJ₀; omega
    have hadd1 : G.J₀ - 1 + 0 + 1 = G.J₀ := by have := G.hJ₀; omega
    rw [Nat.add_zero, hsub, hadd1, growFundU_init0, growFundU_init1, growFundV_init0,
      growFundV_init1]
    norm_num
  | succ n ih =>
    have hJ := G.hJ₀
    have hidx : G.J₀ ≤ G.J₀ - 1 + (n + 1) := by omega
    have hU := G.growFundU_rec hidx
    have hV := G.growFundV_rec hidx
    have hsub1 : G.J₀ - 1 + (n + 1) - 1 = G.J₀ - 1 + n := by omega
    rw [hsub1] at hU hV
    rw [hU, hV]
    have ih' := ih (by omega)
    calc G.growFundU (G.J₀ - 1 + (n + 1)) *
            (G.A (G.J₀ - 1 + (n + 1)) * G.growFundV (G.J₀ - 1 + (n + 1)) +
              G.growFundV (G.J₀ - 1 + n)) -
          (G.A (G.J₀ - 1 + (n + 1)) * G.growFundU (G.J₀ - 1 + (n + 1)) +
              G.growFundU (G.J₀ - 1 + n)) *
            G.growFundV (G.J₀ - 1 + (n + 1))
        = -(G.growFundU (G.J₀ - 1 + n) * G.growFundV (G.J₀ - 1 + (n + 1)) -
            G.growFundU (G.J₀ - 1 + (n + 1)) * G.growFundV (G.J₀ - 1 + n)) := by ring
      _ = -((-1 : ℤ) ^ (G.J₀ - 1 + n + 1 - G.J₀)) := by
            have hadd_n : G.J₀ - 1 + (n + 1) = G.J₀ - 1 + n + 1 := by omega
            rw [hadd_n, ih']
      _ = (-1 : ℤ) ^ (G.J₀ - 1 + n + 1 - G.J₀) * (-1 : ℤ) := by ring
      _ = (-1 : ℤ) ^ (G.J₀ - 1 + (n + 1) + 1 - G.J₀) := by
            have hexp : G.J₀ - 1 + (n + 1) + 1 - G.J₀ =
                (G.J₀ - 1 + n + 1 - G.J₀) + 1 := by omega
            rw [hexp, pow_succ]

lemma grow_ratio_diff_U (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    (G.growFundU (j + 1) : ℝ) / (G.Q (j + 1) : ℝ) - (G.growFundU j : ℝ) / (G.Q j : ℝ) =
      (-1 : ℝ) ^ (j - G.J₀) * (G.Q G.J₀ : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  have hQ1 : (G.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast G.hQ_pos j)
  have hQ2 : (G.Q (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast G.hQ_pos (j + 1))
  have hlin1 : (G.Q j : ℝ) =
      (G.Q (G.J₀ - 1) : ℝ) * (G.growFundU j : ℝ) + (G.Q G.J₀ : ℝ) * (G.growFundV j : ℝ) := by
    exact_mod_cast G.grow_Q_eq_lincomb (by omega)
  have hlin2 : (G.Q (j + 1) : ℝ) =
      (G.Q (G.J₀ - 1) : ℝ) * (G.growFundU (j + 1) : ℝ) +
        (G.Q G.J₀ : ℝ) * (G.growFundV (j + 1) : ℝ) := by
    exact_mod_cast G.grow_Q_eq_lincomb (by omega)
  have hcas : (G.growFundU j : ℝ) * (G.growFundV (j + 1) : ℝ) -
      (G.growFundU (j + 1) : ℝ) * (G.growFundV j : ℝ) = (-1 : ℝ) ^ (j + 1 - G.J₀) := by
    exact_mod_cast G.grow_casorati (by omega)
  have hexp : j + 1 - G.J₀ = (j - G.J₀) + 1 := by omega
  rw [hexp, pow_succ] at hcas
  field_simp
  rw [hlin1, hlin2]
  linear_combination -(G.Q G.J₀ : ℝ) * hcas

lemma grow_ratio_diff_V (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    (G.growFundV (j + 1) : ℝ) / (G.Q (j + 1) : ℝ) - (G.growFundV j : ℝ) / (G.Q j : ℝ) =
      (-1 : ℝ) ^ (j + 1 - G.J₀) * (G.Q (G.J₀ - 1) : ℝ) /
        ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  have hQ1 : (G.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast G.hQ_pos j)
  have hQ2 : (G.Q (j + 1) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast G.hQ_pos (j + 1))
  have hlin1 : (G.Q j : ℝ) =
      (G.Q (G.J₀ - 1) : ℝ) * (G.growFundU j : ℝ) + (G.Q G.J₀ : ℝ) * (G.growFundV j : ℝ) := by
    exact_mod_cast G.grow_Q_eq_lincomb (by omega)
  have hlin2 : (G.Q (j + 1) : ℝ) =
      (G.Q (G.J₀ - 1) : ℝ) * (G.growFundU (j + 1) : ℝ) +
        (G.Q G.J₀ : ℝ) * (G.growFundV (j + 1) : ℝ) := by
    exact_mod_cast G.grow_Q_eq_lincomb (by omega)
  have hcas : (G.growFundU j : ℝ) * (G.growFundV (j + 1) : ℝ) -
      (G.growFundU (j + 1) : ℝ) * (G.growFundV j : ℝ) = (-1 : ℝ) ^ (j + 1 - G.J₀) := by
    exact_mod_cast G.grow_casorati (by omega)
  field_simp
  rw [hlin1, hlin2]
  linear_combination (G.Q (G.J₀ - 1) : ℝ) * hcas

lemma grow_summable_inv_Q_mul_succ (G : GrowingRecData) :
    Summable (fun j : ℕ => 1 / ((G.Q (G.J₀ + j) : ℝ) * (G.Q (G.J₀ + j + 1) : ℝ))) := by
  have hQ0 : (0 : ℝ) < (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
  have hQ1 : (0 : ℝ) < (G.Q (G.J₀ + 1) : ℝ) := by exact_mod_cast G.hQ_pos (G.J₀ + 1)
  have hbound : ∀ j : ℕ,
      1 / ((G.Q (G.J₀ + j) : ℝ) * (G.Q (G.J₀ + j + 1) : ℝ)) ≤
        (1 / ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j := by
    intro j
    have hg1 := G.grow_Q_geom le_rfl j
    have hg2 := G.grow_Q_geom (by omega : G.J₀ ≤ G.J₀ + 1) j
    have hadd : G.J₀ + 1 + j = G.J₀ + j + 1 := by omega
    rw [hadd] at hg2
    have hQa : (0 : ℝ) < (G.Q (G.J₀ + j) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hQb : (0 : ℝ) < (G.Q (G.J₀ + j + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hmul : (4 : ℝ) ^ j * ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ)) ≤
        (G.Q (G.J₀ + j) : ℝ) * (G.Q (G.J₀ + j + 1) : ℝ) := by
      calc (4 : ℝ) ^ j * ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ))
          = ((2 : ℝ) ^ j * (G.Q G.J₀ : ℝ)) * ((2 : ℝ) ^ j * (G.Q (G.J₀ + 1) : ℝ)) := by
              rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring
        _ ≤ (G.Q (G.J₀ + j) : ℝ) * (G.Q (G.J₀ + j + 1) : ℝ) :=
            mul_le_mul hg1 hg2 (by positivity) hQa.le
    rw [div_le_iff₀ (mul_pos hQa hQb)]
    have hpow : (1 / 4 : ℝ) ^ j * (4 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
    calc (1 : ℝ) = (1 / 4 : ℝ) ^ j * (4 : ℝ) ^ j := hpow.symm
      _ = ((1 / ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j) *
            ((4 : ℝ) ^ j * ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ))) := by field_simp
      _ ≤ ((1 / ((G.Q G.J₀ : ℝ) * (G.Q (G.J₀ + 1) : ℝ))) * (1 / 4 : ℝ) ^ j) *
            ((G.Q (G.J₀ + j) : ℝ) * (G.Q (G.J₀ + j + 1) : ℝ)) := by gcongr
  exact Summable.of_nonneg_of_le
    (fun j => div_nonneg zero_le_one
      (mul_nonneg (by exact_mod_cast (G.hQ_pos _).le) (by exact_mod_cast (G.hQ_pos _).le)))
    hbound ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

/-- Fundamental solution ratio limit `α_U := lim_{j → ∞} U_j / Q_j`. -/
def growAlphaU (G : GrowingRecData) : ℝ :=
  ∑' n : ℕ, ((G.growFundU (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
    (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ))

/-- Fundamental solution ratio limit `α_V := lim_{j → ∞} V_j / Q_j`. -/
def growAlphaV (G : GrowingRecData) : ℝ :=
  (1 : ℝ) / (G.Q G.J₀ : ℝ) +
    ∑' n : ℕ, ((G.growFundV (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
      (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ))

lemma grow_summable_diffU (G : GrowingRecData) :
    Summable (fun n : ℕ => (G.growFundU (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
      (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) := by
  have hsum : Summable (fun n : ℕ =>
      (G.Q G.J₀ : ℝ) / ((G.Q (G.J₀ + n) : ℝ) * (G.Q (G.J₀ + n + 1) : ℝ))) :=
    (G.grow_summable_inv_Q_mul_succ).mul_left (G.Q G.J₀ : ℝ) |>.congr (fun n => by ring)
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [G.grow_ratio_diff_U (by omega)]
  have hsub : G.J₀ + n - G.J₀ = n := by omega
  rw [hsub, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hQ0 : (0 : ℝ) < (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
  have hQa : (0 : ℝ) < (G.Q (G.J₀ + n) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hQb : (0 : ℝ) < (G.Q (G.J₀ + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  rw [abs_of_pos hQ0, abs_of_pos (mul_pos hQa hQb)]

lemma grow_summable_diffV (G : GrowingRecData) :
    Summable (fun n : ℕ => (G.growFundV (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
      (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) := by
  have hsum : Summable (fun n : ℕ =>
      (G.Q (G.J₀ - 1) : ℝ) / ((G.Q (G.J₀ + n) : ℝ) * (G.Q (G.J₀ + n + 1) : ℝ))) :=
    (G.grow_summable_inv_Q_mul_succ).mul_left (G.Q (G.J₀ - 1) : ℝ) |>.congr (fun n => by ring)
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [G.grow_ratio_diff_V (by omega)]
  have hsub : G.J₀ + n + 1 - G.J₀ = n + 1 := by omega
  rw [hsub, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hQ0 : (0 : ℝ) < (G.Q (G.J₀ - 1) : ℝ) := by exact_mod_cast G.hQ_pos (G.J₀ - 1)
  have hQa : (0 : ℝ) < (G.Q (G.J₀ + n) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hQb : (0 : ℝ) < (G.Q (G.J₀ + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  rw [abs_of_pos hQ0, abs_of_pos (mul_pos hQa hQb)]

theorem growAlphaU_error_bound (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < (-1 : ℝ) ^ (j - G.J₀) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)) ∧
    (-1 : ℝ) ^ (j - G.J₀) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)) <
      (G.Q G.J₀ : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = G.J₀ + m := ⟨j - G.J₀, by omega⟩
  have hsplit := G.grow_summable_diffU.sum_add_tsum_nat_add m
  have htel : ∑ n ∈ Finset.range m,
      ((G.growFundU (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
        (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) =
      (G.growFundU (G.J₀ + m) : ℝ) / (G.Q (G.J₀ + m) : ℝ) := by
    have h := Finset.sum_range_sub
      (fun n => (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) m
    have h0 : (G.growFundU (G.J₀ + 0) : ℝ) / (G.Q (G.J₀ + 0) : ℝ) = 0 := by
      simp [growFundU_init1]
    have hcongr : ∑ n ∈ Finset.range m,
        ((G.growFundU (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
          (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) =
        ∑ n ∈ Finset.range m,
          ((G.growFundU (G.J₀ + (n + 1)) : ℝ) / (G.Q (G.J₀ + (n + 1)) : ℝ) -
            (G.growFundU (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) :=
      Finset.sum_congr rfl (fun n _ => by simp only [add_assoc])
    rw [hcongr, h, h0, sub_zero]
  have hrem : G.growAlphaU - (G.growFundU (G.J₀ + m) : ℝ) / (G.Q (G.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((G.growFundU (G.J₀ + (n + m) + 1) : ℝ) / (G.Q (G.J₀ + (n + m) + 1) : ℝ) -
        (G.growFundU (G.J₀ + (n + m)) : ℝ) / (G.Q (G.J₀ + (n + m)) : ℝ)) := by
    unfold growAlphaU; linarith [hsplit, htel]
  have hsub_m : G.J₀ + m - G.J₀ = m := by omega
  rw [hsub_m, hrem, ← tsum_mul_left]
  let b : ℕ → ℝ := fun n =>
    (G.Q G.J₀ : ℝ) / ((G.Q (G.J₀ + m + n) : ℝ) * (G.Q (G.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have hQ0 : (0 : ℝ) < (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
    have hQa : (0 : ℝ) < (G.Q (G.J₀ + m + n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hQb : (0 : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have hQ0 : (0 : ℝ) < (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
    have hQa : (0 : ℝ) < (G.Q (G.J₀ + m + n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hQb : (0 : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    have h1R : (G.Q (G.J₀ + m + n) : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast G.grow_Q_lt_succ (by omega)
    have hidx : G.J₀ + m + (n + 1) = G.J₀ + m + n + 1 := by omega
    rw [hidx]
    have h2R : (G.Q (G.J₀ + m + n + 1) : ℝ) < (G.Q (G.J₀ + m + n + 1 + 1) : ℝ) := by
      exact_mod_cast G.grow_Q_lt_succ (j := G.J₀ + m + n + 1) (by omega)
    have hden : (G.Q (G.J₀ + m + n) : ℝ) * (G.Q (G.J₀ + m + n + 1) : ℝ) <
        (G.Q (G.J₀ + m + n + 1) : ℝ) * (G.Q (G.J₀ + m + n + 1 + 1) : ℝ) := by
      nlinarith
    exact div_lt_div_of_pos_left hQ0 (mul_pos hQa hQb) hden
  have hb_sum : Summable b :=
    ((G.grow_summable_inv_Q_mul_succ).comp_injective (add_left_injective m)).mul_left
      (G.Q G.J₀ : ℝ) |>.congr (fun n => by
        dsimp [b]; rw [show G.J₀ + (n + m) = G.J₀ + m + n by omega]; ring)
  have heq_term : ∀ n : ℕ, (-1 : ℝ) ^ m *
      ((G.growFundU (G.J₀ + (n + m) + 1) : ℝ) / (G.Q (G.J₀ + (n + m) + 1) : ℝ) -
        (G.growFundU (G.J₀ + (n + m)) : ℝ) / (G.Q (G.J₀ + (n + m)) : ℝ)) = (-1 : ℝ) ^ n * b n := by
    intro n
    rw [G.grow_ratio_diff_U (by omega)]
    rw [show G.J₀ + (n + m) - G.J₀ = n + m by omega, show G.J₀ + (n + m) = G.J₀ + m + n by omega]
    have hpow : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + (n + m) = n + 2 * m by ring, pow_add, pow_mul]; norm_num
    dsimp [b]
    rw [← mul_div_assoc, ← mul_assoc, hpow]; ring
  rw [tsum_congr heq_term]
  simpa [b] using PolyRecData.alt_tsum_bounds hb_pos hb_dec hb_sum

theorem growAlphaV_error_bound (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < (-1 : ℝ) ^ (j + 1 - G.J₀) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)) ∧
    (-1 : ℝ) ^ (j + 1 - G.J₀) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)) <
      (G.Q (G.J₀ - 1) : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = G.J₀ + m := ⟨j - G.J₀, by omega⟩
  have hsplit := G.grow_summable_diffV.sum_add_tsum_nat_add m
  have htel : (1 : ℝ) / (G.Q G.J₀ : ℝ) + ∑ n ∈ Finset.range m,
      ((G.growFundV (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
        (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) =
      (G.growFundV (G.J₀ + m) : ℝ) / (G.Q (G.J₀ + m) : ℝ) := by
    have h := Finset.sum_range_sub
      (fun n => (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) m
    have h0 : (G.growFundV (G.J₀ + 0) : ℝ) / (G.Q (G.J₀ + 0) : ℝ) =
        (1 : ℝ) / (G.Q G.J₀ : ℝ) := by simp [growFundV_init1]
    have hcongr : ∑ n ∈ Finset.range m,
        ((G.growFundV (G.J₀ + n + 1) : ℝ) / (G.Q (G.J₀ + n + 1) : ℝ) -
          (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) =
        ∑ n ∈ Finset.range m,
          ((G.growFundV (G.J₀ + (n + 1)) : ℝ) / (G.Q (G.J₀ + (n + 1)) : ℝ) -
            (G.growFundV (G.J₀ + n) : ℝ) / (G.Q (G.J₀ + n) : ℝ)) :=
      Finset.sum_congr rfl (fun n _ => by simp only [add_assoc])
    rw [hcongr, h, h0]; ring
  have hrem : G.growAlphaV - (G.growFundV (G.J₀ + m) : ℝ) / (G.Q (G.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((G.growFundV (G.J₀ + (n + m) + 1) : ℝ) / (G.Q (G.J₀ + (n + m) + 1) : ℝ) -
        (G.growFundV (G.J₀ + (n + m)) : ℝ) / (G.Q (G.J₀ + (n + m)) : ℝ)) := by
    unfold growAlphaV; linarith [hsplit, htel]
  have hsub_m : G.J₀ + m + 1 - G.J₀ = m + 1 := by omega
  rw [hsub_m, hrem, ← tsum_mul_left]
  let b : ℕ → ℝ := fun n =>
    (G.Q (G.J₀ - 1) : ℝ) / ((G.Q (G.J₀ + m + n) : ℝ) * (G.Q (G.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have hQ0 : (0 : ℝ) < (G.Q (G.J₀ - 1) : ℝ) := by exact_mod_cast G.hQ_pos (G.J₀ - 1)
    have hQa : (0 : ℝ) < (G.Q (G.J₀ + m + n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hQb : (0 : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have hQ0 : (0 : ℝ) < (G.Q (G.J₀ - 1) : ℝ) := by exact_mod_cast G.hQ_pos (G.J₀ - 1)
    have hQa : (0 : ℝ) < (G.Q (G.J₀ + m + n) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hQb : (0 : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    have h1R : (G.Q (G.J₀ + m + n) : ℝ) < (G.Q (G.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast G.grow_Q_lt_succ (by omega)
    have h2R : (G.Q (G.J₀ + m + n + 1) : ℝ) < (G.Q (G.J₀ + m + n + 1 + 1) : ℝ) := by
      exact_mod_cast G.grow_Q_lt_succ (by omega)
    have hden : (G.Q (G.J₀ + m + n) : ℝ) * (G.Q (G.J₀ + m + n + 1) : ℝ) <
        (G.Q (G.J₀ + m + (n + 1)) : ℝ) * (G.Q (G.J₀ + m + (n + 1) + 1) : ℝ) := by
      rw [show G.J₀ + m + (n + 1) = G.J₀ + m + n + 1 by omega]
      nlinarith
    exact div_lt_div_of_pos_left hQ0 (mul_pos hQa hQb) hden
  have hb_sum : Summable b :=
    ((G.grow_summable_inv_Q_mul_succ).comp_injective (add_left_injective m)).mul_left
      (G.Q (G.J₀ - 1) : ℝ) |>.congr (fun n => by
        dsimp [b]; rw [show G.J₀ + (n + m) = G.J₀ + m + n by omega]; ring)
  have heq_term : ∀ n : ℕ, (-1 : ℝ) ^ (m + 1) *
      ((G.growFundV (G.J₀ + (n + m) + 1) : ℝ) / (G.Q (G.J₀ + (n + m) + 1) : ℝ) -
        (G.growFundV (G.J₀ + (n + m)) : ℝ) / (G.Q (G.J₀ + (n + m)) : ℝ)) = (-1 : ℝ) ^ n * b n := by
    intro n
    rw [G.grow_ratio_diff_V (by omega)]
    rw [show G.J₀ + (n + m) + 1 - G.J₀ = n + m + 1 by omega,
      show G.J₀ + (n + m) = G.J₀ + m + n by omega]
    have hpow : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (n + m + 1) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + 1 + (n + m + 1) = n + 2 * (m + 1) by ring, pow_add, pow_mul]
      norm_num
    dsimp [b]
    rw [← mul_div_assoc, ← mul_assoc, hpow]; ring
  rw [tsum_congr heq_term]
  simpa [b] using PolyRecData.alt_tsum_bounds hb_pos hb_dec hb_sum

lemma abs_growAlphaU_sub_lt (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < |G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)| ∧
    |G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)| <
      (G.Q G.J₀ : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  have h := G.growAlphaU_error_bound hj
  have habs : |(-1 : ℝ) ^ (j - G.J₀) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ))| =
      |G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habs, abs_of_pos h.1]
  exact h

lemma abs_growAlphaV_sub_lt (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < |G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)| ∧
    |G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)| <
      (G.Q (G.J₀ - 1) : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) := by
  have h := G.growAlphaV_error_bound hj
  have habs : |(-1 : ℝ) ^ (j + 1 - G.J₀) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ))| =
      |G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habs, abs_of_pos h.1]
  exact h

lemma tendsto_growFundU_div_Q (G : GrowingRecData) :
    Tendsto (fun j : ℕ => (G.growFundU j : ℝ) / (G.Q j : ℝ)) atTop (nhds G.growAlphaU) := by
  have hmul : Tendsto (fun j : ℕ => (G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun j => ?_) G.grow_Q_tendsto_atTop
    have h1 : (1 : ℝ) ≤ (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    exact le_mul_of_one_le_right (by exact_mod_cast (G.hQ_pos j).le) h1
  have hzero := hmul.const_div_atTop (G.Q G.J₀ : ℝ)
  have hdist : Tendsto (fun j : ℕ => |((G.growFundU j : ℝ) / (G.Q j : ℝ)) - G.growAlphaU|)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (eventually_atTop.mpr ⟨G.J₀, fun j hj => by
        rw [abs_sub_comm]; exact (G.abs_growAlphaU_sub_lt hj).2.le⟩)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hdist)

lemma tendsto_growFundV_div_Q (G : GrowingRecData) :
    Tendsto (fun j : ℕ => (G.growFundV j : ℝ) / (G.Q j : ℝ)) atTop (nhds G.growAlphaV) := by
  have hmul : Tendsto (fun j : ℕ => (G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun j => ?_) G.grow_Q_tendsto_atTop
    have h1 : (1 : ℝ) ≤ (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    exact le_mul_of_one_le_right (by exact_mod_cast (G.hQ_pos j).le) h1
  have hzero := hmul.const_div_atTop (G.Q (G.J₀ - 1) : ℝ)
  have hdist : Tendsto (fun j : ℕ => |((G.growFundV j : ℝ) / (G.Q j : ℝ)) - G.growAlphaV|)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (eventually_atTop.mpr ⟨G.J₀, fun j hj => by
        rw [abs_sub_comm]; exact (G.abs_growAlphaV_sub_lt hj).2.le⟩)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hdist)

/-- Exact normalization identity `Q_{J₀ - 1} * α_U + Q_{J₀} * α_V = 1`. -/
theorem grow_alpha_linear_relation (G : GrowingRecData) :
    (G.Q (G.J₀ - 1) : ℝ) * G.growAlphaU + (G.Q G.J₀ : ℝ) * G.growAlphaV = 1 := by
  have hlim : Tendsto (fun j : ℕ =>
      (G.Q (G.J₀ - 1) : ℝ) * ((G.growFundU j : ℝ) / (G.Q j : ℝ)) +
        (G.Q G.J₀ : ℝ) * ((G.growFundV j : ℝ) / (G.Q j : ℝ)))
      atTop (nhds ((G.Q (G.J₀ - 1) : ℝ) * G.growAlphaU + (G.Q G.J₀ : ℝ) * G.growAlphaV)) :=
    (G.tendsto_growFundU_div_Q.const_mul _).add (G.tendsto_growFundV_div_Q.const_mul _)
  have hconst : ∀ᶠ j : ℕ in atTop,
      (G.Q (G.J₀ - 1) : ℝ) * ((G.growFundU j : ℝ) / (G.Q j : ℝ)) +
        (G.Q G.J₀ : ℝ) * ((G.growFundV j : ℝ) / (G.Q j : ℝ)) = 1 := by
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    have hQ : (G.Q j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast G.hQ_pos j)
    have hlin : (G.Q j : ℝ) =
        (G.Q (G.J₀ - 1) : ℝ) * (G.growFundU j : ℝ) + (G.Q G.J₀ : ℝ) * (G.growFundV j : ℝ) := by
      exact_mod_cast G.grow_Q_eq_lincomb (by omega)
    field_simp
    linarith [hlin]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm))

def growGFactor (G : GrowingRecData) : ℕ := Int.gcd (G.Q (G.J₀ - 1)) (G.Q G.J₀)

lemma growGFactor_pos (G : GrowingRecData) : 0 < G.growGFactor :=
  Int.gcd_pos_iff.mpr (Or.inl (ne_of_gt (G.hQ_pos (G.J₀ - 1))))

def growQ0 (G : GrowingRecData) : ℤ := G.Q (G.J₀ - 1) / (G.growGFactor : ℤ)
def growQ1 (G : GrowingRecData) : ℤ := G.Q G.J₀ / (G.growGFactor : ℤ)

lemma growQ0_mul_g (G : GrowingRecData) : (G.growGFactor : ℤ) * G.growQ0 = G.Q (G.J₀ - 1) :=
  Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)

lemma growQ1_mul_g (G : GrowingRecData) : (G.growGFactor : ℤ) * G.growQ1 = G.Q G.J₀ :=
  Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)

lemma growQ0_q1_coprime (G : GrowingRecData) : IsCoprime G.growQ0 G.growQ1 := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hpos := G.growGFactor_pos
  have h1 : Int.gcd ((G.growGFactor : ℤ) * G.growQ0) ((G.growGFactor : ℤ) * G.growQ1) =
      G.growGFactor * Int.gcd G.growQ0 G.growQ1 := by
    rw [Int.gcd_mul_left, Int.natAbs_natCast]
  rw [G.growQ0_mul_g, G.growQ1_mul_g] at h1
  change G.growGFactor = G.growGFactor * Int.gcd G.growQ0 G.growQ1 at h1
  nlinarith

def growP0 (G : GrowingRecData) : ℤ := Int.gcdB G.growQ0 G.growQ1
def growP1 (G : GrowingRecData) : ℤ := -Int.gcdA G.growQ0 G.growQ1

lemma grow_bezout (G : GrowingRecData) : G.growP0 * G.growQ1 - G.growP1 * G.growQ0 = 1 := by
  have hg := Int.gcd_eq_gcd_ab G.growQ0 G.growQ1
  have hcop : Int.gcd G.growQ0 G.growQ1 = 1 := Int.isCoprime_iff_gcd_eq_one.mp G.growQ0_q1_coprime
  rw [hcop] at hg
  unfold growP0 growP1
  linear_combination -hg

def growQtilde (G : GrowingRecData) (j : ℕ) : ℤ :=
  G.growQ0 * G.growFundU j + G.growQ1 * G.growFundV j

def growPtilde (G : GrowingRecData) (j : ℕ) : ℤ :=
  G.growP0 * G.growFundU j + G.growP1 * G.growFundV j

lemma grow_g_mul_Qtilde (G : GrowingRecData) {j : ℕ} (hj : G.J₀ - 1 ≤ j) :
    (G.growGFactor : ℤ) * G.growQtilde j = G.Q j := by
  have hlin := G.grow_Q_eq_lincomb hj
  rw [← G.growQ0_mul_g, ← G.growQ1_mul_g] at hlin
  unfold growQtilde
  linarith

lemma growQtilde_pos (G : GrowingRecData) {j : ℕ} (hj : G.J₀ - 1 ≤ j) : 0 < G.growQtilde j := by
  have hg : (0 : ℤ) < (G.growGFactor : ℤ) := by exact_mod_cast G.growGFactor_pos
  have hQ := G.hQ_pos j
  rw [← G.grow_g_mul_Qtilde hj] at hQ
  nlinarith

lemma growQtilde_lt_succ (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growQtilde j < G.growQtilde (j + 1) := by
  have hg : (0 : ℤ) < (G.growGFactor : ℤ) := by exact_mod_cast G.growGFactor_pos
  have hQ := G.grow_Q_lt_succ hj
  rw [← G.grow_g_mul_Qtilde (by omega), ← G.grow_g_mul_Qtilde (by omega)] at hQ
  nlinarith

lemma grow_PQtilde_casorati (G : GrowingRecData) {j : ℕ} (hj : G.J₀ - 1 ≤ j) :
    G.growPtilde j * G.growQtilde (j + 1) - G.growQtilde j * G.growPtilde (j + 1) =
      (-1 : ℤ) ^ (j + 1 - G.J₀) := by
  have hcas := G.grow_casorati hj
  have hbez := G.grow_bezout
  unfold growQtilde growPtilde
  calc (G.growP0 * G.growFundU j + G.growP1 * G.growFundV j) *
        (G.growQ0 * G.growFundU (j + 1) + G.growQ1 * G.growFundV (j + 1)) -
      (G.growQ0 * G.growFundU j + G.growQ1 * G.growFundV j) *
        (G.growP0 * G.growFundU (j + 1) + G.growP1 * G.growFundV (j + 1))
      = (G.growP0 * G.growQ1 - G.growP1 * G.growQ0) *
          (G.growFundU j * G.growFundV (j + 1) - G.growFundU (j + 1) * G.growFundV j) := by ring
    _ = 1 * (-1 : ℤ) ^ (j + 1 - G.J₀) := by rw [hbez, hcas]
    _ = (-1 : ℤ) ^ (j + 1 - G.J₀) := one_mul _

/-- Intrinsic irrational slope `θ := g (p₀ α_U + p₁ α_V)`. -/
def growTheta (G : GrowingRecData) : ℝ :=
  (G.growGFactor : ℝ) * ((G.growP0 : ℝ) * G.growAlphaU + (G.growP1 : ℝ) * G.growAlphaV)

lemma growTheta_eq_ratio_limit (G : GrowingRecData) :
    Tendsto (fun j : ℕ => (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ))
      atTop (nhds G.growTheta) := by
  have hnum : Tendsto (fun j : ℕ => (G.growPtilde j : ℝ) / (G.Q j : ℝ)) atTop
      (nhds ((G.growP0 : ℝ) * G.growAlphaU + (G.growP1 : ℝ) * G.growAlphaV)) := by
    have h1 := (G.tendsto_growFundU_div_Q.const_mul (G.growP0 : ℝ)).add
      (G.tendsto_growFundV_div_Q.const_mul (G.growP1 : ℝ))
    refine h1.congr (fun j => ?_)
    unfold growPtilde; push_cast; ring
  have hratio : Tendsto (fun j : ℕ => (G.growGFactor : ℝ) * ((G.growPtilde j : ℝ) / (G.Q j : ℝ)))
      atTop (nhds G.growTheta) := hnum.const_mul (G.growGFactor : ℝ)
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop G.J₀] with j hj
  have hgne : (G.growGFactor : ℝ) ≠ 0 := by exact_mod_cast (G.growGFactor_pos).ne'
  have hQtne : (G.growQtilde j : ℝ) ≠ 0 := by exact_mod_cast (G.growQtilde_pos (by omega)).ne'
  have hgQ : (G.growGFactor : ℝ) * (G.growQtilde j : ℝ) = (G.Q j : ℝ) := by
    exact_mod_cast G.grow_g_mul_Qtilde (by omega)
  rw [← hgQ]; field_simp

lemma growTheta_sub_ratio_pos_and_lt (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    0 < |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| ∧
    |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| <
      1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by
  have hdiff : ∀ n : ℕ, G.J₀ ≤ n →
      (G.growPtilde (n + 1) : ℝ) / (G.growQtilde (n + 1) : ℝ) -
        (G.growPtilde n : ℝ) / (G.growQtilde n : ℝ) =
        (-1 : ℝ) ^ (n - G.J₀) / ((G.growQtilde n : ℝ) * (G.growQtilde (n + 1) : ℝ)) := by
    intro n hn
    have hQa : (G.growQtilde n : ℝ) ≠ 0 := by exact_mod_cast (G.growQtilde_pos (by omega)).ne'
    have hQb : (G.growQtilde (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (G.growQtilde_pos (by omega)).ne'
    have hcas : (G.growPtilde n : ℝ) * (G.growQtilde (n + 1) : ℝ) -
        (G.growQtilde n : ℝ) * (G.growPtilde (n + 1) : ℝ) = (-1 : ℝ) ^ (n + 1 - G.J₀) := by
      exact_mod_cast G.grow_PQtilde_casorati (by omega)
    have hexp : n + 1 - G.J₀ = (n - G.J₀) + 1 := by omega
    rw [hexp, pow_succ] at hcas
    have hcas' : (G.growPtilde (n + 1) : ℝ) * (G.growQtilde n : ℝ) -
        (G.growPtilde n : ℝ) * (G.growQtilde (n + 1) : ℝ) = (-1 : ℝ) ^ (n - G.J₀) := by
      linarith [hcas]
    have hdiv : (G.growPtilde (n + 1) : ℝ) / (G.growQtilde (n + 1) : ℝ) -
        (G.growPtilde n : ℝ) / (G.growQtilde n : ℝ) =
        ((G.growPtilde (n + 1) : ℝ) * (G.growQtilde n : ℝ) -
          (G.growPtilde n : ℝ) * (G.growQtilde (n + 1) : ℝ)) /
          ((G.growQtilde n : ℝ) * (G.growQtilde (n + 1) : ℝ)) := by
      field_simp [hQa, hQb]
    rw [hdiv, hcas']
  have hsum_inv : Summable (fun n : ℕ =>
      1 / ((G.growQtilde (G.J₀ + n) : ℝ) * (G.growQtilde (G.J₀ + n + 1) : ℝ))) := by
    have hg : (1 : ℝ) ≤ (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
    have hbig := (G.grow_summable_inv_Q_mul_succ).mul_left
      ((G.growGFactor : ℝ) * (G.growGFactor : ℝ))
    refine Summable.of_nonneg_of_le (fun n => by
      have ha : (0 : ℝ) < (G.growQtilde (G.J₀ + n) : ℝ) := by
        exact_mod_cast G.growQtilde_pos (by omega)
      have hb : (0 : ℝ) < (G.growQtilde (G.J₀ + n + 1) : ℝ) := by
        exact_mod_cast G.growQtilde_pos (by omega)
      positivity) (fun n => ?_) hbig
    have ha : (G.growGFactor : ℝ) * (G.growQtilde (G.J₀ + n) : ℝ) = (G.Q (G.J₀ + n) : ℝ) := by
      exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    have hb : (G.growGFactor : ℝ) * (G.growQtilde (G.J₀ + n + 1) : ℝ) =
        (G.Q (G.J₀ + n + 1) : ℝ) := by exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    have ha0 : (0 : ℝ) < (G.growQtilde (G.J₀ + n) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have hb0 : (0 : ℝ) < (G.growQtilde (G.J₀ + n + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have hg0 : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
    rw [← ha, ← hb]
    have heq : (G.growGFactor : ℝ) * (G.growGFactor : ℝ) *
        (1 / (((G.growGFactor : ℝ) * (G.growQtilde (G.J₀ + n) : ℝ)) *
          ((G.growGFactor : ℝ) * (G.growQtilde (G.J₀ + n + 1) : ℝ)))) =
        1 / ((G.growQtilde (G.J₀ + n) : ℝ) * (G.growQtilde (G.J₀ + n + 1) : ℝ)) := by
      field_simp [hg0.ne', ha0.ne', hb0.ne']
    linarith [heq]
  have hsum_PQ : Summable (fun n : ℕ =>
      (G.growPtilde (G.J₀ + n + 1) : ℝ) / (G.growQtilde (G.J₀ + n + 1) : ℝ) -
        (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) := by
    refine Summable.of_norm_bounded hsum_inv (fun n => ?_)
    rw [hdiff (G.J₀ + n) (by omega)]
    have ha : (0 : ℝ) < (G.growQtilde (G.J₀ + n) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have hb : (0 : ℝ) < (G.growQtilde (G.J₀ + n + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (mul_pos ha hb)]
  have hlim_sum : G.growTheta - (G.growPtilde G.J₀ : ℝ) / (G.growQtilde G.J₀ : ℝ) =
      ∑' n : ℕ, ((G.growPtilde (G.J₀ + n + 1) : ℝ) / (G.growQtilde (G.J₀ + n + 1) : ℝ) -
        (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) := by
    have hpart := hsum_PQ.hasSum.tendsto_sum_nat
    have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        ((G.growPtilde (G.J₀ + n + 1) : ℝ) / (G.growQtilde (G.J₀ + n + 1) : ℝ) -
          (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) =
        (G.growPtilde (G.J₀ + N) : ℝ) / (G.growQtilde (G.J₀ + N) : ℝ) -
          (G.growPtilde G.J₀ : ℝ) / (G.growQtilde G.J₀ : ℝ) := fun N => by
      simpa [add_assoc] using Finset.sum_range_sub
        (fun n => (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) N
    have hshift : Tendsto (fun N : ℕ =>
        (G.growPtilde (G.J₀ + N) : ℝ) / (G.growQtilde (G.J₀ + N) : ℝ) -
          (G.growPtilde G.J₀ : ℝ) / (G.growQtilde G.J₀ : ℝ)) atTop
        (nhds (G.growTheta - (G.growPtilde G.J₀ : ℝ) / (G.growQtilde G.J₀ : ℝ))) :=
      (G.growTheta_eq_ratio_limit.comp
        ((tendsto_add_atTop_nat G.J₀).congr (fun n => Nat.add_comm n G.J₀))).sub_const _
    exact tendsto_nhds_unique hshift (hpart.congr htel)
  obtain ⟨m, rfl⟩ : ∃ m, j = G.J₀ + m := ⟨j - G.J₀, by omega⟩
  have hsplit := hsum_PQ.sum_add_tsum_nat_add m
  have htel_m : ∑ n ∈ Finset.range m,
      ((G.growPtilde (G.J₀ + n + 1) : ℝ) / (G.growQtilde (G.J₀ + n + 1) : ℝ) -
        (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) =
      (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ) -
        (G.growPtilde G.J₀ : ℝ) / (G.growQtilde G.J₀ : ℝ) := by
    simpa [add_assoc] using Finset.sum_range_sub
      (fun n => (G.growPtilde (G.J₀ + n) : ℝ) / (G.growQtilde (G.J₀ + n) : ℝ)) m
  have hrem : G.growTheta - (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ) =
      ∑' n : ℕ, ((G.growPtilde (G.J₀ + (n + m) + 1) : ℝ) / (G.growQtilde (G.J₀ + (n + m) + 1) : ℝ) -
        (G.growPtilde (G.J₀ + (n + m)) : ℝ) / (G.growQtilde (G.J₀ + (n + m)) : ℝ)) := by
    linarith [hlim_sum, hsplit, htel_m]
  let b : ℕ → ℝ := fun n =>
    1 / ((G.growQtilde (G.J₀ + m + n) : ℝ) * (G.growQtilde (G.J₀ + m + n + 1) : ℝ))
  have hb_pos : ∀ n : ℕ, 0 < b n := fun n => by
    have ha : (0 : ℝ) < (G.growQtilde (G.J₀ + m + n) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have hb : (0 : ℝ) < (G.growQtilde (G.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    positivity
  have hb_dec : ∀ n : ℕ, b (n + 1) < b n := fun n => by
    dsimp [b]
    have ha : (0 : ℝ) < (G.growQtilde (G.J₀ + m + n) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have hb : (0 : ℝ) < (G.growQtilde (G.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_pos (by omega)
    have h1 : (G.growQtilde (G.J₀ + m + n) : ℝ) <
        (G.growQtilde (G.J₀ + m + n + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_lt_succ (by omega)
    have h2 : (G.growQtilde (G.J₀ + m + n + 1) : ℝ) <
        (G.growQtilde (G.J₀ + m + n + 1 + 1) : ℝ) := by
      exact_mod_cast G.growQtilde_lt_succ (by omega)
    rw [show G.J₀ + m + (n + 1) = G.J₀ + m + n + 1 by omega]
    exact div_lt_div_of_pos_left zero_lt_one (mul_pos ha hb) (by nlinarith)
  have hb_sum : Summable b :=
    (hsum_inv.comp_injective (add_left_injective m)).congr (fun n => by
      dsimp [b]; rw [show G.J₀ + (n + m) = G.J₀ + m + n by omega])
  have halt := PolyRecData.alt_tsum_bounds hb_pos hb_dec hb_sum
  have hcongr : (-1 : ℝ) ^ m *
      (G.growTheta - (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ)) =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := by
    rw [hrem, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hdiff (G.J₀ + (n + m)) (by omega)]
    rw [show G.J₀ + (n + m) - G.J₀ = n + m by omega, show G.J₀ + (n + m) = G.J₀ + m + n by omega]
    have hpow : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (n + m) = (-1 : ℝ) ^ n := by
      rw [← pow_add, show m + (n + m) = n + 2 * m by ring, pow_add, pow_mul]; norm_num
    dsimp [b]
    rw [← mul_div_assoc, hpow]; ring
  have habs_eq : |G.growTheta - (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ)| =
      ∑' n : ℕ, (-1 : ℝ) ^ n * b n := by
    have h1 : |(-1 : ℝ) ^ m *
        (G.growTheta - (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ))| =
        |G.growTheta - (G.growPtilde (G.J₀ + m) : ℝ) / (G.growQtilde (G.J₀ + m) : ℝ)| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← h1, hcongr, abs_of_pos halt.1]
  rw [habs_eq]
  simpa [b] using halt

lemma growTheta_sub_ratio_bounds (G : GrowingRecData) {j : ℕ} (hj : G.J₀ ≤ j) :
    1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) <
      |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| ∧
    |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| <
      1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by
  have hup := (G.growTheta_sub_ratio_pos_and_lt hj).2
  have hup1 := (G.growTheta_sub_ratio_pos_and_lt (j := j + 1) (by omega)).2
  have hcas : (G.growPtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ) -
      (G.growQtilde j : ℝ) * (G.growPtilde (j + 1) : ℝ) = (-1 : ℝ) ^ (j + 1 - G.J₀) := by
    exact_mod_cast G.grow_PQtilde_casorati (j := j) (by omega)
  have hQt0 : (0 : ℝ) < (G.growQtilde j : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hQt1 : (0 : ℝ) < (G.growQtilde (j + 1) : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hQt2 : (0 : ℝ) < (G.growQtilde (j + 2) : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hdiff_eq : |(G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ) -
      (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| =
      1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by
    have hsub : (G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ) -
        (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ) =
        -((-1 : ℝ) ^ (j + 1 - G.J₀)) /
          ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by
      field_simp [hQt0.ne', hQt1.ne']
      linarith [hcas]
    rw [hsub, abs_div, abs_neg, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (mul_pos hQt0 hQt1)]
  have hQt2_gt : 2 * (G.growQtilde j : ℝ) < (G.growQtilde (j + 2) : ℝ) := by
    have hg_pos : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
    have hg0 : (G.growGFactor : ℝ) * (G.growQtilde j : ℝ) = (G.Q j : ℝ) := by
      exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    have hg1 : (G.growGFactor : ℝ) * (G.growQtilde (j + 1) : ℝ) = (G.Q (j + 1) : ℝ) := by
      exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    have hg2 : (G.growGFactor : ℝ) * (G.growQtilde (j + 2) : ℝ) = (G.Q (j + 2) : ℝ) := by
      exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    have hQ12 : (2 : ℝ) * (G.Q (j + 1) : ℝ) < (G.Q (j + 2) : ℝ) := by
      exact_mod_cast G.grow_Q_succ_ge_two_mul (j := j + 1) (by omega)
    have hQ01 : (G.Q j : ℝ) < (G.Q (j + 1) : ℝ) := by
      exact_mod_cast G.grow_Q_lt_succ hj
    nlinarith
  have hinv_lt : 1 / ((G.growQtilde (j + 1) : ℝ) * (G.growQtilde (j + 2) : ℝ)) <
      1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by
    apply div_lt_div_of_pos_left zero_lt_one (by positivity)
    nlinarith
  have htri : |(G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ) -
      (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| ≤
      |G.growTheta - (G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ)| +
      |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| := by
    have heq : (G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ) -
        (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ) =
        -((G.growTheta - (G.growPtilde (j + 1) : ℝ) / (G.growQtilde (j + 1) : ℝ))) +
          (G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)) := by ring
    rw [heq]
    calc |-(G.growTheta - _) + (G.growTheta - _)|
        ≤ |-(G.growTheta - _)| + |G.growTheta - _| := abs_add_le _ _
      _ = _ + _ := by rw [abs_neg]
  have hlo : 1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) <
      |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| := by
    have hsum : 1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) -
        1 / ((G.growQtilde (j + 1) : ℝ) * (G.growQtilde (j + 2) : ℝ)) =
        1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) -
        1 / ((G.growQtilde (j + 1) : ℝ) * (G.growQtilde (j + 2) : ℝ)) := rfl
    have hhalf : 1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) -
        1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) =
        1 / (2 * (G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ)) := by ring
    linarith [htri, hdiff_eq, hup1, hinv_lt, hhalf]
  exact ⟨hlo, hup⟩

theorem growTheta_irrational (G : GrowingRecData) : Irrational G.growTheta := by
  rw [irrational_iff_ne_rational]
  intro p q hq htheta
  have hQ_tend : Tendsto (fun j : ℕ => (G.growQtilde j : ℝ)) atTop atTop := by
    have hg : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
    refine (G.grow_Q_tendsto_atTop.const_mul_atTop (inv_pos.mpr hg)).congr' ?_
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    have hgQ : (G.growGFactor : ℝ) * (G.growQtilde j : ℝ) = (G.Q j : ℝ) := by
      exact_mod_cast G.grow_g_mul_Qtilde (by omega)
    rw [← hgQ]; field_simp
  have hqR_pos : (0 : ℝ) < |(q : ℝ)| := abs_pos.mpr (by exact_mod_cast hq)
  have hev_Q : ∀ᶠ j : ℕ in atTop, |(q : ℝ)| < (G.growQtilde (j + 1) : ℝ) :=
    (hQ_tend.comp (tendsto_add_atTop_nat 1)).eventually_gt_atTop |(q : ℝ)|
  obtain ⟨j, hj1, hj2⟩ := (hev_Q.and (eventually_ge_atTop G.J₀)).exists
  have hb := G.growTheta_sub_ratio_pos_and_lt hj2
  have hQt_pos : (0 : ℝ) < (G.growQtilde j : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hQt1_pos : (0 : ℝ) < (G.growQtilde (j + 1) : ℝ) := by
    exact_mod_cast G.growQtilde_pos (by omega)
  have hmul_pos : (0 : ℝ) < |(q : ℝ)| * (G.growQtilde j : ℝ) := mul_pos hqR_pos hQt_pos
  have hdiff_eq : |(q : ℝ) * (G.growPtilde j : ℝ) - (p : ℝ) * (G.growQtilde j : ℝ)| =
      |(q : ℝ)| * (G.growQtilde j : ℝ) *
        |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| := by
    rw [htheta]
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have hQtne : (G.growQtilde j : ℝ) ≠ 0 := ne_of_gt hQt_pos
    have hid : (q : ℝ) * (G.growPtilde j : ℝ) - (p : ℝ) * (G.growQtilde j : ℝ) =
        -(q : ℝ) * (G.growQtilde j : ℝ) *
          ((p : ℝ) / (q : ℝ) - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)) := by
      field_simp; ring
    rw [hid, abs_mul, abs_mul, abs_neg, abs_of_pos hQt_pos]
  have hposZ : 0 < |q * G.growPtilde j - p * G.growQtilde j| := by
    have h0 : 0 < |(q : ℝ) * (G.growPtilde j : ℝ) - (p : ℝ) * (G.growQtilde j : ℝ)| := by
      rw [hdiff_eq]; exact mul_pos hmul_pos hb.1
    exact_mod_cast h0
  have hlt1 : |q * G.growPtilde j - p * G.growQtilde j| < 1 := by
    have h1 : |(q : ℝ) * (G.growPtilde j : ℝ) - (p : ℝ) * (G.growQtilde j : ℝ)| < 1 := by
      rw [hdiff_eq]
      calc |(q : ℝ)| * (G.growQtilde j : ℝ) *
              |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)|
          < (|(q : ℝ)| * (G.growQtilde j : ℝ)) *
              (1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ))) :=
            mul_lt_mul_of_pos_left hb.2 hmul_pos
        _ = |(q : ℝ)| / (G.growQtilde (j + 1) : ℝ) := by field_simp
        _ < 1 := (div_lt_one hQt1_pos).mpr hj1
    exact_mod_cast h1
  omega

/-- Intrinsic zero-level rank-2 lattice `L_G := ℤ α_U + ℤ α_V`. -/
def growLatticeL (G : GrowingRecData) : Set ℝ :=
  {x : ℝ | ∃ a b : ℤ, x = (a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV}

/-- Rational sublattice `(1/g) ℤ ⊆ L_G`. -/
def growRatLattice (G : GrowingRecData) : Set ℝ :=
  {x : ℝ | ∃ m : ℤ, x = (m : ℝ) / (G.growGFactor : ℝ)}

lemma growRatLattice_countable (G : GrowingRecData) : G.growRatLattice.Countable := by
  have heq : G.growRatLattice = Set.range (fun m : ℤ => (m : ℝ) / (G.growGFactor : ℝ)) := by
    ext x
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩; exact ⟨m, hm.symm⟩
  rw [heq]
  exact Set.countable_range _

lemma growLatticeL_eq_inv_g (G : GrowingRecData) :
    G.growLatticeL =
      {x : ℝ | ∃ m n : ℤ, x = ((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)} := by
  ext x
  have hgne : (G.growGFactor : ℝ) ≠ 0 := by exact_mod_cast G.growGFactor_pos.ne'
  have hq_rel : (G.growQ0 : ℝ) * G.growAlphaU + (G.growQ1 : ℝ) * G.growAlphaV =
      1 / (G.growGFactor : ℝ) := by
    have h1 := G.grow_alpha_linear_relation
    have hq0 : (G.Q (G.J₀ - 1) : ℝ) = (G.growGFactor : ℝ) * (G.growQ0 : ℝ) := by
      exact_mod_cast G.growQ0_mul_g.symm
    have hq1 : (G.Q G.J₀ : ℝ) = (G.growGFactor : ℝ) * (G.growQ1 : ℝ) := by
      exact_mod_cast G.growQ1_mul_g.symm
    rw [hq0, hq1] at h1
    field_simp
    linarith [h1]
  have hp_rel : (G.growP0 : ℝ) * G.growAlphaU + (G.growP1 : ℝ) * G.growAlphaV =
      G.growTheta / (G.growGFactor : ℝ) := by
    unfold growTheta; field_simp
  have hbez : (G.growP0 : ℝ) * (G.growQ1 : ℝ) - (G.growP1 : ℝ) * (G.growQ0 : ℝ) = 1 := by
    exact_mod_cast G.grow_bezout
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨b * G.growP0 - a * G.growP1, a * G.growQ1 - b * G.growQ0, ?_⟩
    push_cast
    have hA : ((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) * (G.growQ0 : ℝ) +
        ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) * (G.growP0 : ℝ) = (a : ℝ) := by
      linear_combination (a : ℝ) * hbez
    have hB : ((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) * (G.growQ1 : ℝ) +
        ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) * (G.growP1 : ℝ) = (b : ℝ) := by
      linear_combination (b : ℝ) * hbez
    symm
    rw [div_eq_iff hgne]
    have hqg : (G.growGFactor : ℝ) * ((G.growQ0 : ℝ) * G.growAlphaU +
        (G.growQ1 : ℝ) * G.growAlphaV) = 1 := by
      rw [hq_rel, mul_one_div_cancel hgne]
    have hpg : (G.growGFactor : ℝ) * ((G.growP0 : ℝ) * G.growAlphaU +
        (G.growP1 : ℝ) * G.growAlphaV) = G.growTheta := by
      rw [hp_rel, mul_div_cancel₀ _ hgne]
    calc ((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) +
          ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) * G.growTheta
        = ((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) *
            ((G.growGFactor : ℝ) * ((G.growQ0 : ℝ) * G.growAlphaU +
              (G.growQ1 : ℝ) * G.growAlphaV)) +
          ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) *
            ((G.growGFactor : ℝ) * ((G.growP0 : ℝ) * G.growAlphaU +
              (G.growP1 : ℝ) * G.growAlphaV)) := by
            rw [hqg, hpg, mul_one]
      _ = (G.growGFactor : ℝ) * (G.growAlphaU *
            (((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) * (G.growQ0 : ℝ) +
              ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) * (G.growP0 : ℝ)) +
            G.growAlphaV *
            (((b : ℝ) * (G.growP0 : ℝ) - (a : ℝ) * (G.growP1 : ℝ)) * (G.growQ1 : ℝ) +
              ((a : ℝ) * (G.growQ1 : ℝ) - (b : ℝ) * (G.growQ0 : ℝ)) * (G.growP1 : ℝ))) := by
            ring
      _ = ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV) * (G.growGFactor : ℝ) := by
            rw [hA, hB]; ring
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * G.growQ0 + n * G.growP0, m * G.growQ1 + n * G.growP1, ?_⟩
    push_cast
    calc ((m : ℝ) + (n : ℝ) * G.growTheta) / (G.growGFactor : ℝ)
        = (m : ℝ) * (1 / (G.growGFactor : ℝ)) + (n : ℝ) * (G.growTheta / (G.growGFactor : ℝ)) := by
            ring
      _ = (m : ℝ) * ((G.growQ0 : ℝ) * G.growAlphaU + (G.growQ1 : ℝ) * G.growAlphaV) +
          (n : ℝ) * ((G.growP0 : ℝ) * G.growAlphaU + (G.growP1 : ℝ) * G.growAlphaV) := by
            rw [hq_rel, hp_rel]
      _ = _ := by ring

lemma growRatLattice_subset_growLatticeL (G : GrowingRecData) :
    G.growRatLattice ⊆ G.growLatticeL := by
  intro x ⟨m, hm⟩
  rw [hm, G.growLatticeL_eq_inv_g]
  exact ⟨m, 0, by simp⟩

lemma intCast_mem_growLatticeL (G : GrowingRecData) (k : ℤ) : (k : ℝ) ∈ G.growLatticeL := by
  rw [G.growLatticeL_eq_inv_g]
  refine ⟨k * (G.growGFactor : ℤ), 0, ?_⟩
  have hgne : (G.growGFactor : ℝ) ≠ 0 := by exact_mod_cast G.growGFactor_pos.ne'
  push_cast; field_simp; ring

lemma zero_mem_growLatticeL (G : GrowingRecData) : (0 : ℝ) ∈ G.growLatticeL := by
  simpa using G.intCast_mem_growLatticeL 0

lemma neg_mem_growLatticeL (G : GrowingRecData) {y : ℝ} (hy : y ∈ G.growLatticeL) :
    -y ∈ G.growLatticeL := by
  rcases hy with ⟨a, b, rfl⟩
  exact ⟨-a, -b, by push_cast; ring⟩

lemma add_mem_growLatticeL (G : GrowingRecData) {x y : ℝ}
    (hx : x ∈ G.growLatticeL) (hy : y ∈ G.growLatticeL) :
    x + y ∈ G.growLatticeL := by
  rcases hx with ⟨a₁, b₁, rfl⟩
  rcases hy with ⟨a₂, b₂, rfl⟩
  exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩

lemma int_mul_mem_growLatticeL (G : GrowingRecData) {y : ℝ} (hy : y ∈ G.growLatticeL) (m : ℤ) :
    (m : ℝ) * y ∈ G.growLatticeL := by
  rcases hy with ⟨a, b, rfl⟩
  exact ⟨m * a, m * b, by push_cast; ring⟩

theorem growLatticeL_countable (G : GrowingRecData) : G.growLatticeL.Countable := by
  let f : ℤ × ℤ → ℝ := fun p => (p.1 : ℝ) * G.growAlphaU + (p.2 : ℝ) * G.growAlphaV
  have hsub : G.growLatticeL ⊆ Set.range f := by
    rintro x ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩
  exact (Set.countable_range f).mono hsub

lemma grow_dist_le_of_mem_growLatticeL (G : GrowingRecData) {y : ℝ} (hy : y ∈ G.growLatticeL) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, G.J₀ ≤ j →
      distToNearestInt ((G.Q j : ℝ) * y) ≤ C / (G.Q (j + 1) : ℝ) := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨(|(a : ℝ)| * (G.Q G.J₀ : ℝ) + |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ)) + 1,
    by have := G.hQ_pos G.J₀; have := G.hQ_pos (G.J₀ - 1); positivity, fun j hj => ?_⟩
  let M : ℤ := a * G.growFundU j + b * G.growFundV j
  have htri : distToNearestInt ((G.Q j : ℝ) * ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV)) ≤
      |(G.Q j : ℝ) * ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV) - (M : ℝ)| :=
    distToNearestInt_le _ M
  have hQ_pos : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hQ1_pos : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
  have hsplit : (G.Q j : ℝ) * ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV) - (M : ℝ) =
      (a : ℝ) * (G.Q j : ℝ) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)) +
      (b : ℝ) * (G.Q j : ℝ) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)) := by
    simp only [M]; push_cast; field_simp [hQ_pos.ne']; ring
  have hU := (G.abs_growAlphaU_sub_lt hj).2
  have hV := (G.abs_growAlphaV_sub_lt hj).2
  have h1 : |(a : ℝ) * (G.Q j : ℝ) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ))| ≤
      |(a : ℝ)| * (G.Q G.J₀ : ℝ) / (G.Q (j + 1) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_pos hQ_pos]
    calc |(a : ℝ)| * (G.Q j : ℝ) * |G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)|
        ≤ |(a : ℝ)| * (G.Q j : ℝ) *
            ((G.Q G.J₀ : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ))) := by gcongr
      _ = |(a : ℝ)| * (G.Q G.J₀ : ℝ) / (G.Q (j + 1) : ℝ) := by field_simp
  have h2 : |(b : ℝ) * (G.Q j : ℝ) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ))| ≤
      |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ) / (G.Q (j + 1) : ℝ) := by
    rw [abs_mul, abs_mul, abs_of_pos hQ_pos]
    calc |(b : ℝ)| * (G.Q j : ℝ) * |G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ)|
        ≤ |(b : ℝ)| * (G.Q j : ℝ) *
            ((G.Q (G.J₀ - 1) : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ))) := by gcongr
      _ = |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ) / (G.Q (j + 1) : ℝ) := by field_simp
  have hadd : |(G.Q j : ℝ) * ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV) - (M : ℝ)| ≤
      (|(a : ℝ)| * (G.Q G.J₀ : ℝ) + |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ)) / (G.Q (j + 1) : ℝ) := by
    rw [hsplit]
    calc |(a : ℝ) * (G.Q j : ℝ) * (G.growAlphaU - (G.growFundU j : ℝ) / (G.Q j : ℝ)) +
          (b : ℝ) * (G.Q j : ℝ) * (G.growAlphaV - (G.growFundV j : ℝ) / (G.Q j : ℝ))|
        ≤ _ + _ := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  have hpos_div : (|(a : ℝ)| * (G.Q G.J₀ : ℝ) + |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ)) /
      (G.Q (j + 1) : ℝ) ≤
      (|(a : ℝ)| * (G.Q G.J₀ : ℝ) + |(b : ℝ)| * (G.Q (G.J₀ - 1) : ℝ) + 1) / (G.Q (j + 1) : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hQ1_pos.le
  exact htri.trans (hadd.trans hpos_div)

lemma exists_mem_growLatticeL_pos_lt (G : GrowingRecData) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ G.growLatticeL, 0 < y ∧ y < ε := by
  have hev : ∀ᶠ j : ℕ in atTop, 1 / (G.Q (j + 1) : ℝ) < ε :=
    ((G.grow_Q_tendsto_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop 1).eventually
      (Iio_mem_nhds hε)
  obtain ⟨j, hjε, hjJ₀⟩ := (hev.and (eventually_ge_atTop G.J₀)).exists
  have hth := G.growTheta_sub_ratio_pos_and_lt hjJ₀
  have hQt_pos : (0 : ℝ) < (G.growQtilde j : ℝ) := by exact_mod_cast G.growQtilde_pos (by omega)
  have hg_pos : (0 : ℝ) < (G.growGFactor : ℝ) := by exact_mod_cast G.growGFactor_pos
  have hgQ1 : (G.growGFactor : ℝ) * (G.growQtilde (j + 1) : ℝ) = (G.Q (j + 1) : ℝ) := by
    exact_mod_cast G.grow_g_mul_Qtilde (by omega)
  let z : ℝ := ((G.growQtilde j : ℝ) * G.growTheta - (G.growPtilde j : ℝ)) / (G.growGFactor : ℝ)
  have hz_abs : |z| = (G.growQtilde j : ℝ) *
      |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| / (G.growGFactor : ℝ) := by
    have h1 : z = ((G.growQtilde j : ℝ) *
        (G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ))) / (G.growGFactor : ℝ) := by
      dsimp [z]; field_simp
    rw [h1, abs_div, abs_mul, abs_of_pos hQt_pos, abs_of_pos hg_pos]
  have hz_pos : 0 < |z| := by rw [hz_abs]; exact div_pos (mul_pos hQt_pos hth.1) hg_pos
  have hz_lt : |z| < ε := by
    rw [hz_abs]
    have h1 : (G.growQtilde j : ℝ) * |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| <
        1 / (G.growQtilde (j + 1) : ℝ) := by
      have hmul := mul_lt_mul_of_pos_left hth.2 hQt_pos
      have hrhs : (G.growQtilde j : ℝ) *
          (1 / ((G.growQtilde j : ℝ) * (G.growQtilde (j + 1) : ℝ))) =
          1 / (G.growQtilde (j + 1) : ℝ) := by field_simp
      linarith
    have h2 : (G.growQtilde j : ℝ) * |G.growTheta - (G.growPtilde j : ℝ) / (G.growQtilde j : ℝ)| /
        (G.growGFactor : ℝ) < (1 / (G.growQtilde (j + 1) : ℝ)) / (G.growGFactor : ℝ) :=
      div_lt_div_of_pos_right h1 hg_pos
    have h3 : (1 / (G.growQtilde (j + 1) : ℝ)) / (G.growGFactor : ℝ) = 1 / (G.Q (j + 1) : ℝ) := by
      rw [← hgQ1]; field_simp
    linarith
  have hz_mem : z ∈ G.growLatticeL := by
    rw [G.growLatticeL_eq_inv_g]
    refine ⟨-G.growPtilde j, G.growQtilde j, ?_⟩
    push_cast; dsimp [z]; ring
  rcases le_or_gt 0 z with hz0 | hz0
  · exact ⟨z, hz_mem, by rwa [abs_of_nonneg hz0] at hz_pos, by rwa [abs_of_nonneg hz0] at hz_lt⟩
  · exact ⟨-z, G.neg_mem_growLatticeL hz_mem, by rwa [abs_of_neg hz0] at hz_pos,
      by rwa [abs_of_neg hz0] at hz_lt⟩

lemma exists_disjoint_growLattice_translates_in_Ioo (G : GrowingRecData)
    {a b c r : ℝ} (hab : a < b) (hr : 0 < r) :
    let N : ℕ := Nat.floor ((b - a) / (3 * r))
    ∃ t : Fin N → ℝ,
      (∀ i, t i ∈ G.growLatticeL) ∧
      (∀ i, Set.Icc (c + t i - r) (c + t i + r) ⊆ Set.Ioo a b) ∧
      Pairwise (fun i j =>
        Disjoint (Set.Icc (c + t i - r) (c + t i + r))
                 (Set.Icc (c + t j - r) (c + t j + r))) := by
  intro N
  obtain ⟨y, hyL, hy_pos, hy_lt⟩ := exists_mem_growLatticeL_pos_lt G hr
  set m : ℕ := Nat.floor (2 * r / y) + 1
  set s : ℝ := (m : ℝ) * y
  have hs_mem : s ∈ G.growLatticeL := G.int_mul_mem_growLatticeL hyL m
  have hs_gt : 2 * r < s := by
    have hm_gt : 2 * r / y < (m : ℝ) := by
      dsimp [m]; push_cast; exact Nat.lt_floor_add_one _
    exact (div_lt_iff₀ hy_pos).mp hm_gt
  have hs_lt : s < 3 * r := by
    have hm_le : (m : ℝ) ≤ 2 * r / y + 1 := by
      dsimp [m]; push_cast
      linarith [Nat.floor_le (by positivity : 0 ≤ 2 * r / y)]
    have hmul : (m : ℝ) * y ≤ (2 * r / y + 1) * y :=
      mul_le_mul_of_nonneg_right hm_le hy_pos.le
    have hadd : (2 * r / y + 1) * y = 2 * r + y := by field_simp
    linarith
  set k₀ : ℤ := Int.floor ((a + r - c) / y) + 1
  set t₀ : ℝ := (k₀ : ℝ) * y
  have ht₀_mem : t₀ ∈ G.growLatticeL := G.int_mul_mem_growLatticeL hyL k₀
  have ht₀_gt : a + r < c + t₀ := by
    have hk_gt : (a + r - c) / y < (k₀ : ℝ) := by
      dsimp [k₀]; push_cast; exact Int.lt_floor_add_one _
    have := (div_lt_iff₀ hy_pos).mp hk_gt
    linarith
  have ht₀_lt : c + t₀ < a + 2 * r := by
    have hk_le : (k₀ : ℝ) ≤ (a + r - c) / y + 1 := by
      dsimp [k₀]; push_cast
      linarith [Int.floor_le ((a + r - c) / y)]
    have hmul : (k₀ : ℝ) * y ≤ ((a + r - c) / y + 1) * y :=
      mul_le_mul_of_nonneg_right hk_le hy_pos.le
    have hadd : ((a + r - c) / y + 1) * y = a + r - c + y := by field_simp
    linarith
  refine ⟨fun i => t₀ + (i.1 : ℝ) * s, ?_, ?_, ?_⟩
  · intro i
    exact G.add_mem_growLatticeL ht₀_mem (G.int_mul_mem_growLatticeL hs_mem (i.1 : ℤ))
  · intro i x hx
    have hi_nonneg : 0 ≤ (i.1 : ℝ) * s :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hlo : a < x := by linarith [hx.1]
    have hi_le : ((i.1 + 1 : ℕ) : ℝ) ≤ (b - a) / (3 * r) := by
      have h1 : i.1 + 1 ≤ N := i.2
      have h2 : ((i.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have h3 : (N : ℝ) ≤ (b - a) / (3 * r) :=
        Nat.floor_le (div_nonneg (sub_nonneg.mpr hab.le) (by positivity))
      exact h2.trans h3
    have hmul3 : 3 * ((i.1 + 1 : ℕ) : ℝ) * r ≤ b - a := by
      have h3r : 0 < 3 * r := by positivity
      have := (le_div_iff₀ h3r).mp hi_le
      linarith
    have hhi : x < b := by
      have hmul_s : (i.1 : ℝ) * s ≤ (i.1 : ℝ) * (3 * r) :=
        mul_le_mul_of_nonneg_left hs_lt.le (Nat.cast_nonneg _)
      have hcast : ((i.1 + 1 : ℕ) : ℝ) = (i.1 : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hmul3
      linarith [hx.2]
    exact ⟨hlo, hhi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · have hij1 : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hlt
      have h1 : ((i.1 : ℝ) + 1) * s ≤ (j.1 : ℝ) * s :=
        mul_le_mul_of_nonneg_right hij1 (by linarith)
      linarith [hxi.2, hxj.1]
    · have hji1 : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast hlt
      have h1 : ((j.1 : ℝ) + 1) * s ≤ (i.1 : ℝ) * s :=
        mul_le_mul_of_nonneg_right hji1 (by linarith)
      linarith [hxj.2, hxi.1]

/-! ### Part 3: Approximation Exponent, Kraaikamp–Liardet Ratio, and Defect Calculus -/

lemma round_eq_of_abs_sub_lt_half_grow {y : ℝ} {m : ℤ} (h : |y - (m : ℝ)| < 1 / 2) :
    round y = m := by
  have hlt := abs_lt.mp h
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- Signed approximation remainder `u_j(x) = Q_j x - round(Q_j x)`. -/
def growEps (G : GrowingRecData) (x : ℝ) (j : ℕ) : ℝ :=
  (G.Q j : ℝ) * x - (round ((G.Q j : ℝ) * x) : ℝ)

/-- Integer defect `d_j(x) = M_{j+1}(x) - A_j M_j(x) - M_{j-1}(x)`. -/
def growDefect (G : GrowingRecData) (x : ℝ) (j : ℕ) : ℤ :=
  round ((G.Q (j + 1) : ℝ) * x) - G.A j * round ((G.Q j : ℝ) * x) -
    round ((G.Q (j - 1) : ℝ) * x)

/-- Quotient-normalized sequence `|A_j| * ||Q_j x||`. -/
def growSeq (G : GrowingRecData) (x : ℝ) (j : ℕ) : ℝ :=
  |(G.A j : ℝ)| * distToNearestInt ((G.Q j : ℝ) * x)

lemma growSeq_nonneg (G : GrowingRecData) (x : ℝ) (j : ℕ) : 0 ≤ G.growSeq x j :=
  mul_nonneg (abs_nonneg _) (distToNearestInt_nonneg _)

/-- Kraaikamp–Liardet denominator-ratio sequence `(Q_{j+1} / Q_j) * ||Q_j x||`. -/
def growKLSeq (G : GrowingRecData) (x : ℝ) (j : ℕ) : ℝ :=
  ((G.Q (j + 1) : ℝ) / (G.Q j : ℝ)) * distToNearestInt ((G.Q j : ℝ) * x)

lemma growKLSeq_nonneg (G : GrowingRecData) (x : ℝ) (j : ℕ) : 0 ≤ G.growKLSeq x j := by
  have hQ0 : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hQ1 : (0 : ℝ) ≤ (G.Q (j + 1) : ℝ) := by exact_mod_cast (G.hQ_pos (j + 1)).le
  exact mul_nonneg (div_nonneg hQ1 hQ0.le) (distToNearestInt_nonneg _)

/-- Critical approximation exponent `Λ_G(x) := limsup_{j→∞} A_j ||Q_j x||`. -/
def growLambda (G : GrowingRecData) (x : ℝ) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (G.growSeq x j)) atTop

/-- Kraaikamp–Liardet ratio `KL_G(x) := limsup_{j→∞} (Q_{j+1}/Q_j) ||Q_j x||`. -/
def growKLRatio (G : GrowingRecData) (x : ℝ) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (G.growKLSeq x j)) atTop

/-- Sub-level set `{x : Λ_G(x) ≤ t}`. -/
def growLevelSet (G : GrowingRecData) (t : ℝ≥0∞) : Set ℝ :=
  {x : ℝ | G.growLambda x ≤ t}

/-- Strict sub-level set `{x : Λ_G(x) < k}`. -/
def growStrictLevel (G : GrowingRecData) (k : ℕ) : Set ℝ :=
  {x : ℝ | G.growLambda x < (k : ℝ≥0∞)}

/-- Exact integer level set `{x : Λ_G(x) = k}`. -/
def growExactLevel (G : GrowingRecData) (k : ℕ) : Set ℝ :=
  {x : ℝ | G.growLambda x = (k : ℝ≥0∞)}

/-- Unsigned exact limit set `{x : A_j ||Q_j x|| → t}`. -/
def growUnsignedExactLimitSet (G : GrowingRecData) (t : ℝ) : Set ℝ :=
  {x : ℝ | Tendsto (G.growSeq x) atTop (nhds t)}

/-- Signed exact limit set `{x : A_j (Q_j x - round(Q_j x)) → t}`. -/
def growSignedExactLimitSet (G : GrowingRecData) (t : ℝ) : Set ℝ :=
  {x : ℝ | Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps x j) atTop (nhds t)}

/-- Finite-exponent set `{x : Λ_G(x) < ⊤}` and generic infinite-exponent set `{x : Λ_G(x) = ⊤}`. -/
def growFiniteSet (G : GrowingRecData) : Set ℝ :=
  {x : ℝ | G.growLambda x < ⊤}

def growInfiniteSet (G : GrowingRecData) : Set ℝ :=
  {x : ℝ | G.growLambda x = ⊤}

lemma abs_growEps_eq_dist (G : GrowingRecData) (x : ℝ) (j : ℕ) :
    |G.growEps x j| = distToNearestInt ((G.Q j : ℝ) * x) := rfl

lemma abs_growEps_le_half (G : GrowingRecData) (x : ℝ) (j : ℕ) :
    |G.growEps x j| ≤ 1 / 2 := abs_sub_round _

lemma growSeq_eq_of_ge (G : GrowingRecData) (x : ℝ) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growSeq x j = (G.A j : ℝ) * |G.growEps x j| := by
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  rw [growSeq, abs_of_pos hA, abs_growEps_eq_dist]

lemma grow_defect_identity (G : GrowingRecData) (x : ℝ) {j : ℕ} (hj : G.J₀ ≤ j) :
    (G.growDefect x j : ℝ) =
      (G.A j : ℝ) * G.growEps x j - G.growEps x (j + 1) + G.growEps x (j - 1) := by
  have hQ : (G.Q (j + 1) : ℝ) = (G.A j : ℝ) * (G.Q j : ℝ) + (G.Q (j - 1) : ℝ) := by
    exact_mod_cast G.hQ_rec j hj
  simp only [growDefect, growEps]
  push_cast
  rw [hQ]
  ring

lemma grow_signed_defect_approx (G : GrowingRecData) (x : ℝ)
    (hε : Tendsto (G.growEps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => (G.growDefect x j : ℝ) - (G.A j : ℝ) * G.growEps x j)
      atTop (nhds 0) := by
  have h1 : Tendsto (fun j : ℕ => G.growEps x (j + 1)) atTop (nhds 0) :=
    hε.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun j : ℕ => G.growEps x (j - 1)) atTop (nhds 0) :=
    hε.comp tendsto_sub_one_atTop
  have hdiff : Tendsto (fun j : ℕ => G.growEps x (j - 1) - G.growEps x (j + 1))
      atTop (nhds 0) := by
    simpa using h2.sub h1
  refine hdiff.congr' ?_
  filter_upwards [eventually_ge_atTop G.J₀] with j hj
  rw [G.grow_defect_identity x hj]
  ring

lemma grow_abs_defect_approx (G : GrowingRecData) (x : ℝ)
    (hε : Tendsto (G.growEps x) atTop (nhds 0)) :
    Tendsto (fun j : ℕ => |(G.growDefect x j : ℝ)| - G.growSeq x j) atTop (nhds 0) := by
  have hs := G.grow_signed_defect_approx x hε
  have habs0 : Tendsto (fun j : ℕ => |(G.growDefect x j : ℝ) - (G.A j : ℝ) * G.growEps x j|)
      atTop (nhds 0) := by
    simpa using hs.abs
  refine tendsto_zero_iff_abs_tendsto_zero.mpr ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds habs0
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop G.J₀] with j hj
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  have hseq : G.growSeq x j = |(G.A j : ℝ) * G.growEps x j| := by
    rw [G.growSeq_eq_of_ge x hj, abs_mul, abs_of_pos hA]
  rw [hseq]
  exact abs_abs_sub_abs_le (G.growDefect x j : ℝ) ((G.A j : ℝ) * G.growEps x j)

lemma grow_eps_tendsto_zero_of_lambda_ne_top (G : GrowingRecData) {x : ℝ}
    (hx : G.growLambda x ≠ ⊤) :
    Tendsto (G.growEps x) atTop (nhds 0) := by
  set M : ℝ := (G.growLambda x).toReal + 1
  have hMpos : 0 < M := by positivity
  have hlt : G.growLambda x < ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hx]
    exact (ENNReal.ofReal_lt_ofReal_iff hMpos).mpr (by linarith)
  have hev : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (G.growSeq x j) < ENNReal.ofReal M :=
    Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
  have hbound : ∀ᶠ j : ℕ in atTop, |G.growEps x j| ≤ M / (G.A j : ℝ) := by
    filter_upwards [hev, eventually_ge_atTop G.J₀] with j hj hjJ₀
    have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hjJ₀
    have hltR : G.growSeq x j < M := (ENNReal.ofReal_lt_ofReal_iff hMpos).mp hj
    rw [G.growSeq_eq_of_ge x hjJ₀] at hltR
    exact (le_div_iff₀ hA).mpr (by linarith)
  have hlim : Tendsto (fun j : ℕ => M / (G.A j : ℝ)) atTop (nhds 0) :=
    G.hA_tendsto.const_div_atTop M
  exact tendsto_zero_iff_abs_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound)

lemma grow_seq_le_klSeq (G : GrowingRecData) (x : ℝ) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growSeq x j ≤ G.growKLSeq x j := by
  have hQ0 : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hrec : (G.Q (j + 1) : ℝ) = (G.A j : ℝ) * (G.Q j : ℝ) + (G.Q (j - 1) : ℝ) := by
    exact_mod_cast G.hQ_rec j hj
  have hQprev : (0 : ℝ) ≤ (G.Q (j - 1) : ℝ) := by exact_mod_cast (G.hQ_pos (j - 1)).le
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  rw [growSeq, growKLSeq, abs_of_pos hA]
  refine mul_le_mul_of_nonneg_right ?_ (distToNearestInt_nonneg _)
  rw [le_div_iff₀ hQ0, hrec]
  linarith

lemma grow_klSeq_sub_seq_eq (G : GrowingRecData) (x : ℝ) {j : ℕ} (hj : G.J₀ ≤ j) :
    G.growKLSeq x j - G.growSeq x j =
      ((G.Q (j - 1) : ℝ) / (G.Q j : ℝ)) * distToNearestInt ((G.Q j : ℝ) * x) := by
  have hQ0 : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hrec : (G.Q (j + 1) : ℝ) = (G.A j : ℝ) * (G.Q j : ℝ) + (G.Q (j - 1) : ℝ) := by
    exact_mod_cast G.hQ_rec j hj
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  rw [growKLSeq, growSeq, abs_of_pos hA]
  have hdiv : (G.Q (j + 1) : ℝ) / (G.Q j : ℝ) = (G.A j : ℝ) + (G.Q (j - 1) : ℝ) / (G.Q j : ℝ) := by
    rw [hrec]; field_simp
  rw [hdiv]
  ring

/-- Kraaikamp–Liardet exact ratio equivalence:
    `limsup_{j→∞} (Q_{j+1}/Q_j) ||Q_j x|| = limsup_{j→∞} A_j ||Q_j x||` for EVERY `x ∈ ℝ`. -/
theorem growKLRatio_eq_growLambda (G : GrowingRecData) (x : ℝ) :
    G.growKLRatio x = G.growLambda x := by
  have hle : G.growLambda x ≤ G.growKLRatio x := by
    refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    exact ENNReal.ofReal_le_ofReal (G.grow_seq_le_klSeq x hj)
  by_cases htop : G.growLambda x = ⊤
  · rw [htop] at hle ⊢
    exact top_unique hle
  · refine le_antisymm ?_ hle
    have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top htop
    have hdiff0 : Tendsto (fun j : ℕ => G.growKLSeq x j - G.growSeq x j) atTop (nhds 0) := by
      have habs : Tendsto (fun j : ℕ => |G.growEps x j|) atTop (nhds 0) :=
        tendsto_zero_iff_abs_tendsto_zero.mp hε
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds habs ?_ ?_
      · filter_upwards [eventually_ge_atTop G.J₀] with j hj
        rw [G.grow_klSeq_sub_seq_eq x hj]
        have hQ0 : (0 : ℝ) ≤ (G.Q j : ℝ) := by exact_mod_cast (G.hQ_pos j).le
        have hQp : (0 : ℝ) ≤ (G.Q (j - 1) : ℝ) := by exact_mod_cast (G.hQ_pos (j - 1)).le
        exact mul_nonneg (div_nonneg hQp hQ0) (distToNearestInt_nonneg _)
      · filter_upwards [eventually_ge_atTop (G.J₀ + 1)] with j hj
        rw [G.grow_klSeq_sub_seq_eq x (by omega), abs_growEps_eq_dist]
        have hlt := G.grow_Q_prev_lt_half hj
        have hQ0 : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
        have hQp : (0 : ℝ) ≤ (G.Q (j - 1) : ℝ) := by exact_mod_cast (G.hQ_pos (j - 1)).le
        have hQp_pos : (0 : ℝ) < (G.Q (j - 1) : ℝ) := by exact_mod_cast G.hQ_pos (j - 1)
        have hrat : (G.Q (j - 1) : ℝ) / (G.Q j : ℝ) ≤ 1 := by
          rw [div_le_one hQ0]; linarith [hlt.2]
        exact mul_le_of_le_one_left (distToNearestInt_nonneg _) hrat
    have hbound_eps : ∀ ε : ℝ, 0 < ε → G.growKLRatio x ≤ G.growLambda x + ENNReal.ofReal ε := by
      intro ε hε_pos
      have hev : ∀ᶠ j : ℕ in atTop, G.growKLSeq x j - G.growSeq x j < ε :=
        hdiff0.eventually (Iio_mem_nhds hε_pos)
      have hsup_le : G.growKLRatio x ≤
          limsup (fun j : ℕ => ENNReal.ofReal (G.growSeq x j) + ENNReal.ofReal ε) atTop := by
        refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [hev] with j hj
        have hleR : G.growKLSeq x j ≤ G.growSeq x j + ε := by linarith
        exact (ENNReal.ofReal_le_ofReal hleR).trans ENNReal.ofReal_add_le
      have heq_add : limsup (fun j : ℕ => ENNReal.ofReal (G.growSeq x j) + ENNReal.ofReal ε)
          atTop ≤ G.growLambda x + ENNReal.ofReal ε :=
        limsup_add_const_le (fun j : ℕ => ENNReal.ofReal (G.growSeq x j)) ENNReal.ofReal_ne_top
      exact hsup_le.trans heq_add
    have hlim_add : Tendsto (fun n : ℕ => G.growLambda x + ENNReal.ofReal (1 / (n + 1 : ℝ)))
        atTop (nhds (G.growLambda x)) := by
      have hinv : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := G.growLambda x)).add hinv
    exact ge_of_tendsto hlim_add (Filter.Eventually.of_forall fun n =>
      hbound_eps _ (by positivity))

lemma grow_mem_latticeL_of_eventually_defect_zero (G : GrowingRecData) (x : ℝ)
    (hdef : ∀ᶠ j : ℕ in atTop, G.growDefect x j = 0) :
    x ∈ G.growLatticeL := by
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hdef
  let J := max K0 G.J₀
  have hJJ₀ : G.J₀ ≤ J := le_max_right _ _
  let M : ℕ → ℤ := fun j => round ((G.Q j : ℝ) * x)
  have hcas := G.grow_casorati (j := J - 1) (by omega)
  have hsub1 : J - 1 + 1 = J := Nat.sub_add_cancel (le_trans G.hJ₀ hJJ₀)
  let Δ : ℤ := G.growFundU J * G.growFundV (J - 1) - G.growFundU (J - 1) * G.growFundV J
  have hΔ_sq : Δ * Δ = 1 := by
    have hsq : ((-1 : ℤ) ^ (J - G.J₀)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul]
      norm_num
    have hpow := congrArg (fun z : ℤ => z ^ 2) hcas
    have hΔ_eq : Δ * Δ =
        (G.growFundU (J - 1) * G.growFundV J - G.growFundU J * G.growFundV (J - 1)) ^ 2 := by
      dsimp [Δ]; ring
    rw [hsub1] at hpow
    rw [hΔ_eq, hpow, hsq]
  let a : ℤ := Δ * (M J * G.growFundV (J - 1) - M (J - 1) * G.growFundV J)
  let b : ℤ := Δ * (G.growFundU J * M (J - 1) - G.growFundU (J - 1) * M J)
  have ha0 : a * G.growFundU (J - 1) + b * G.growFundV (J - 1) = M (J - 1) := by
    have hId : (M J * G.growFundV (J - 1) - M (J - 1) * G.growFundV J) * G.growFundU (J - 1) +
        (G.growFundU J * M (J - 1) - G.growFundU (J - 1) * M J) * G.growFundV (J - 1) =
        M (J - 1) * Δ := by
      dsimp [Δ]; ring
    calc a * G.growFundU (J - 1) + b * G.growFundV (J - 1)
        = Δ * ((M J * G.growFundV (J - 1) - M (J - 1) * G.growFundV J) * G.growFundU (J - 1) +
            (G.growFundU J * M (J - 1) - G.growFundU (J - 1) * M J) * G.growFundV (J - 1)) := by
            dsimp [a, b]; ring
      _ = Δ * (M (J - 1) * Δ) := by rw [hId]
      _ = M (J - 1) * (Δ * Δ) := by ring
      _ = M (J - 1) := by rw [hΔ_sq, mul_one]
  have ha1 : a * G.growFundU J + b * G.growFundV J = M J := by
    have hId2 : (M J * G.growFundV (J - 1) - M (J - 1) * G.growFundV J) * G.growFundU J +
        (G.growFundU J * M (J - 1) - G.growFundU (J - 1) * M J) * G.growFundV J =
        M J * Δ := by
      dsimp [Δ]; ring
    calc a * G.growFundU J + b * G.growFundV J
        = Δ * ((M J * G.growFundV (J - 1) - M (J - 1) * G.growFundV J) * G.growFundU J +
            (G.growFundU J * M (J - 1) - G.growFundU (J - 1) * M J) * G.growFundV J) := by
            dsimp [a, b]; ring
      _ = Δ * (M J * Δ) := by rw [hId2]
      _ = M J * (Δ * Δ) := by ring
      _ = M J := by rw [hΔ_sq, mul_one]
  have hM_eq : ∀ n : ℕ,
      M (J - 1 + n) = a * G.growFundU (J - 1 + n) + b * G.growFundV (J - 1 + n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | _ | k
      · simpa using ha0.symm
      · simpa [hsub1] using ha1.symm
      · have hk1 : J ≤ J - 1 + (k + 1) := by omega
        have hk0 : K0 ≤ J - 1 + (k + 1) := le_trans (le_max_left _ _) hk1
        have hkJ₀ : G.J₀ ≤ J - 1 + (k + 1) := le_trans hJJ₀ hk1
        have hdefk : M (J - 1 + (k + 2)) =
            G.A (J - 1 + (k + 1)) * M (J - 1 + (k + 1)) + M (J - 1 + k) := by
          have h0 := hK0 (J - 1 + (k + 1)) hk0
          dsimp [growDefect] at h0
          dsimp [M]
          have h1 : J - 1 + (k + 2) = J - 1 + (k + 1) + 1 := by omega
          rw [h1]
          linarith [h0]
        have hU := G.growFundU_rec hkJ₀
        have hV := G.growFundV_rec hkJ₀
        have hsub : J - 1 + (k + 1) - 1 = J - 1 + k := by omega
        have hadd : J - 1 + (k + 1) + 1 = J - 1 + (k + 2) := by omega
        rw [hsub, hadd] at hU hV
        rw [hdefk, ih (k + 1) (by omega), ih k (by omega), hU, hV]
        ring
  have hlim_lin : Tendsto (fun j : ℕ => (M j : ℝ) / (G.Q j : ℝ)) atTop
      (nhds ((a : ℝ) * G.growAlphaU + (b : ℝ) * G.growAlphaV)) := by
    have hcomb := (G.tendsto_growFundU_div_Q.const_mul (a : ℝ)).add
      (G.tendsto_growFundV_div_Q.const_mul (b : ℝ))
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop (J - 1)] with j hj
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [hM_eq n]
    push_cast
    ring
  have hlim_x : Tendsto (fun j : ℕ => (M j : ℝ) / (G.Q j : ℝ)) atTop (nhds x) := by
    have hdiff0 : Tendsto (fun j : ℕ => G.growEps x j / (G.Q j : ℝ)) atTop (nhds 0) := by
      have hlim_half : Tendsto (fun j : ℕ => (1 / 2 : ℝ) / (G.Q j : ℝ)) atTop (nhds 0) :=
        G.grow_Q_tendsto_atTop.const_div_atTop (1 / 2)
      refine tendsto_zero_iff_abs_tendsto_zero.mpr ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_half
        (fun _ => abs_nonneg _) fun j => ?_
      have hQp : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
      rw [abs_div, abs_of_pos hQp]
      exact div_le_div_of_nonneg_right (G.abs_growEps_le_half x j) hQp.le
    have hsub : Tendsto (fun j : ℕ => x - G.growEps x j / (G.Q j : ℝ)) atTop (nhds x) := by
      simpa using tendsto_const_nhds.sub hdiff0
    refine hsub.congr (fun j => ?_)
    have hQp : (0 : ℝ) ≠ (G.Q j : ℝ) := by
      have := G.hQ_pos j; positivity
    simp only [M, growEps]
    field_simp [hQp]
    ring
  rw [tendsto_nhds_unique hlim_x hlim_lin]
  exact ⟨a, b, rfl⟩

/-- Zero-level TFAE equivalence (`growLambda G x = 0 ↔ x ∈ L_G ↔ d_j = 0 a.e. ↔ KL_G x = 0`). -/
theorem growLambda_eq_zero_tfae (G : GrowingRecData) (x : ℝ) :
    List.TFAE
      [x ∈ G.growLatticeL,
       G.growLambda x = 0,
       ∀ᶠ j : ℕ in atTop, G.growDefect x j = 0,
       G.growKLRatio x = 0] := by
  tfae_have 1 → 2 := by
    intro hx
    obtain ⟨C, hC_pos, hdist⟩ := G.grow_dist_le_of_mem_growLatticeL hx
    have hseq0 : Tendsto (G.growSeq x) atTop (nhds 0) := by
      have hQ0 : Tendsto (fun j : ℕ => C / (G.Q j : ℝ)) atTop (nhds 0) :=
        G.grow_Q_tendsto_atTop.const_div_atTop C
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ0
        (Filter.Eventually.of_forall (G.growSeq_nonneg x)) ?_
      filter_upwards [eventually_ge_atTop G.J₀] with j hj
      have hrec := G.grow_Q_succ_gt_A_mul hj
      have hAp : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
      have hQ1 : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
      have hQ0' : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
      rw [G.growSeq_eq_of_ge x hj, abs_growEps_eq_dist]
      calc (G.A j : ℝ) * distToNearestInt ((G.Q j : ℝ) * x)
          ≤ (G.A j : ℝ) * (C / (G.Q (j + 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hdist j hj) hAp.le
        _ ≤ C / (G.Q j : ℝ) := by
            rw [mul_div_assoc', div_le_div_iff₀ hQ1 hQ0']
            have hAQ : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
              exact_mod_cast hrec.le
            nlinarith
    have hlim_enn : Tendsto (fun j : ℕ => ENNReal.ofReal (G.growSeq x j)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hseq0
    exact hlim_enn.limsup_eq
  tfae_have 2 → 3 := by
    intro hx
    have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top (x := x) (by simp [hx])
    have hlt_seq : ∀ᶠ j : ℕ in atTop, G.growSeq x j < 1 / 3 := by
      have hlt : G.growLambda x < ENNReal.ofReal (1 / 3) := by
        rw [hx]; exact ENNReal.ofReal_pos.mpr (by norm_num)
      filter_upwards [Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)] with j hj
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hj
    have hlt_err : ∀ᶠ j : ℕ in atTop, |(G.growDefect x j : ℝ)| - G.growSeq x j < 1 / 3 :=
      (G.grow_abs_defect_approx x hε).eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hlt_seq, hlt_err] with j hjseq hjerr
    have hlt_one : |(G.growDefect x j : ℝ)| < 1 := by linarith
    have hZ : |G.growDefect x j| < 1 := by exact_mod_cast hlt_one
    rcases abs_lt.mp hZ with ⟨h1, h2⟩
    omega
  tfae_have 3 → 1 := fun hdef => G.grow_mem_latticeL_of_eventually_defect_zero x hdef
  tfae_have 2 ↔ 4 := by rw [G.growKLRatio_eq_growLambda x]
  tfae_finish

theorem growLambda_eq_zero_iff (G : GrowingRecData) (x : ℝ) :
    G.growLambda x = 0 ↔ x ∈ G.growLatticeL :=
  (G.growLambda_eq_zero_tfae x).out 2 1

theorem growLevelSet_zero_eq_lattice (G : GrowingRecData) :
    G.growLevelSet 0 = G.growLatticeL := by
  ext x
  simp only [growLevelSet, Set.mem_ofPred_eq, nonpos_iff_eq_zero, G.growLambda_eq_zero_iff]

/-! ### Part 4: Arbitrary Bounded Digit Realization, Full Spectrum, and Open Spectral Gaps -/

/-- Partial-convergent integer sequence realizing arbitrary bounded defects `d_j` for `j ≥ J`. -/
def growDigPair (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 =>
      let p := growDigPair G J d n
      (G.A (J + n) * p.1 + p.2 + d (J + n), p.1)

def growDigM (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (m : ℕ) : ℤ :=
  if m ≤ J then 0 else (growDigPair G J d (m - J)).1

lemma growDigM_eq_zero_of_le (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) {m : ℕ} (hm : m ≤ J) :
    G.growDigM J d m = 0 := by
  simp [growDigM, hm]

lemma growDigPair_snd (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (n : ℕ) :
    (G.growDigPair J d (n + 1)).2 = (G.growDigPair J d n).1 := rfl

lemma growDigM_rec (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) {j : ℕ} (hj : J ≤ j) :
    G.growDigM J d (j + 1) =
      G.A j * G.growDigM J d j + G.growDigM J d (j - 1) + d j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  rcases n with _ | k
  · have h0 : J + 0 ≤ J := by omega
    have h1 : J + 0 - 1 ≤ J := by omega
    have h2 : ¬ (J + 0 + 1 ≤ J) := by omega
    simp only [growDigM, h0, ↓reduceIte, h1, h2]
    have hdiff : J + 0 + 1 - J = 1 := by omega
    simp [hdiff, growDigPair]
  · have hm : ¬ (J + (k + 1) ≤ J) := by omega
    have hm1 : ¬ (J + (k + 1) + 1 ≤ J) := by omega
    have hsubp : J + (k + 1) - 1 = J + k := by omega
    have hsub1 : J + (k + 1) - J = k + 1 := by omega
    have hsub2 : J + (k + 1) + 1 - J = k + 2 := by omega
    simp only [growDigM, hm, ↓reduceIte, hm1, hsubp, hsub1, hsub2, growDigPair]
    rcases k with _ | k'
    · simp [growDigPair]
    · have hnot : ¬ (J + (k' + 1) ≤ J) := by omega
      have hsubk : J + (k' + 1) - J = k' + 1 := by omega
      simp [hnot, hsubk, growDigPair, Nat.add_assoc]

def growDigW (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (j : ℕ) : ℤ :=
  G.growDigM J d (j + 1) * G.Q j - G.growDigM J d j * G.Q (j + 1)

lemma growDigW_init (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (hJ : 1 ≤ J) :
    G.growDigW J d (J - 1) = 0 := by
  have h1 : J - 1 + 1 = J := by omega
  simp [growDigW, h1, G.growDigM_eq_zero_of_le J d (le_refl J),
    G.growDigM_eq_zero_of_le J d (Nat.sub_le J 1)]

lemma growDigW_rec (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) {j : ℕ}
    (hj : J ≤ j) (hJ0 : G.J₀ ≤ j) :
    G.growDigW J d j = d j * G.Q j - G.growDigW J d (j - 1) := by
  have hj1 : 1 ≤ j := le_trans G.hJ₀ hJ0
  have hsub : j - 1 + 1 = j := by omega
  have hMr := G.growDigM_rec J d hj
  have hQr := G.hQ_rec j hJ0
  dsimp [growDigW]
  rw [hsub, hMr, hQr]
  ring

lemma abs_growDigW_le (G : GrowingRecData) (J K : ℕ) (hJ : G.J₀ + 1 ≤ J)
    (d : ℕ → ℤ) (hd : ∀ j : ℕ, J ≤ j → |d j| ≤ (K : ℤ))
    {j : ℕ} (hj : J - 1 ≤ j) :
    |G.growDigW J d j| ≤ 2 * (K : ℤ) * G.Q j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero =>
    rw [add_zero, G.growDigW_init J d (by omega), abs_zero]
    have hQp := (G.hQ_pos (J - 1)).le
    positivity
  | succ k ih =>
    have hJk : J ≤ J - 1 + (k + 1) := by omega
    have hJk0 : G.J₀ ≤ J - 1 + (k + 1) := by omega
    have hrec := G.growDigW_rec J d hJk hJk0
    have hsub : J - 1 + (k + 1) - 1 = J - 1 + k := by omega
    rw [hsub] at hrec
    have hQ2 := G.grow_Q_succ_ge_two_mul (j := J - 1 + k) (by omega)
    rw [hrec]
    calc |d (J - 1 + (k + 1)) * G.Q (J - 1 + (k + 1)) - G.growDigW J d (J - 1 + k)|
        ≤ |d (J - 1 + (k + 1)) * G.Q (J - 1 + (k + 1))| + |G.growDigW J d (J - 1 + k)| :=
          abs_sub _ _
      _ ≤ (K : ℤ) * G.Q (J - 1 + (k + 1)) + 2 * (K : ℤ) * G.Q (J - 1 + k) := by
          rw [abs_mul, abs_of_pos (G.hQ_pos _)]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hd _ hJk) (G.hQ_pos _).le) (ih (by omega))
      _ ≤ (K : ℤ) * G.Q (J - 1 + (k + 1)) + (K : ℤ) * G.Q (J - 1 + (k + 1)) := by
          have hadd : J - 1 + k + 1 = J - 1 + (k + 1) := by omega
          rw [hadd] at hQ2
          nlinarith [(Nat.cast_nonneg K : (0 : ℤ) ≤ (K : ℤ))]
      _ = 2 * (K : ℤ) * G.Q (J - 1 + (k + 1)) := by ring

def growDigDiff (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (j : ℕ) : ℝ :=
  if J - 1 ≤ j then (G.growDigW J d j : ℝ) / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) else 0

lemma sum_growDigDiff_eq (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) (_hJ : 1 ≤ J)
    {m : ℕ} (hm : J - 1 ≤ m) :
    (∑ j ∈ Finset.range m, G.growDigDiff J d j) = (G.growDigM J d m : ℝ) / (G.Q m : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction n with
  | zero =>
    rw [add_zero]
    have hsum0 : ∑ j ∈ Finset.range (J - 1), G.growDigDiff J d j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp [growDigDiff, Nat.not_le.mpr hj]
    rw [hsum0, G.growDigM_eq_zero_of_le J d (Nat.sub_le J 1)]
    simp
  | succ k ih =>
    have hadd : J - 1 + (k + 1) = (J - 1 + k) + 1 := by omega
    rw [hadd, Finset.sum_range_succ, ih (by omega)]
    have hge : J - 1 ≤ J - 1 + k := by omega
    have hQ0 : (G.Q (J - 1 + k) : ℝ) ≠ 0 := by have := G.hQ_pos (J - 1 + k); positivity
    have hQ1 : (G.Q (J - 1 + k + 1) : ℝ) ≠ 0 := by
      have := G.hQ_pos (J - 1 + k + 1); positivity
    simp only [growDigDiff, hge, ↓reduceIte, growDigW]
    push_cast
    field_simp [hQ0, hQ1]
    ring

lemma summable_growDigDiff (G : GrowingRecData) (J K : ℕ) (hJ : G.J₀ + 1 ≤ J)
    (d : ℕ → ℤ) (hd : ∀ j : ℕ, J ≤ j → |d j| ≤ (K : ℤ)) :
    Summable (G.growDigDiff J d) := by
  have hdom : Summable (fun j : ℕ => 2 * (K : ℝ) * (2 : ℝ) ^ G.J₀ * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_two).mul_left (2 * (K : ℝ) * (2 : ℝ) ^ G.J₀)
  refine Summable.of_norm_bounded hdom fun j => ?_
  rw [Real.norm_eq_abs]
  by_cases hj : J - 1 ≤ j
  · have hW : |(G.growDigW J d j : ℝ)| ≤ 2 * (K : ℝ) * (G.Q j : ℝ) := by
      exact_mod_cast G.abs_growDigW_le J K hJ d hd hj
    have hQ0 : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
    have hQ1 : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    have hjJ₀ : G.J₀ ≤ j + 1 := by omega
    have hgeom : (2 : ℝ) ^ (j + 1 - G.J₀) * (G.Q G.J₀ : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
      have hidx : G.J₀ + (j + 1 - G.J₀) = j + 1 := by omega
      have hle := G.grow_Q_geom (le_refl G.J₀) (j + 1 - G.J₀)
      rwa [hidx] at hle
    have hQ1_ge : (2 : ℝ) ^ j / (2 : ℝ) ^ G.J₀ ≤ (G.Q (j + 1) : ℝ) := by
      have hQJ1 : (1 : ℝ) ≤ (G.Q G.J₀ : ℝ) := by exact_mod_cast G.hQ_pos G.J₀
      have hpow : (2 : ℝ) ^ j / (2 : ℝ) ^ G.J₀ ≤ (2 : ℝ) ^ (j + 1 - G.J₀) := by
        rw [div_le_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc (2 : ℝ) ^ j / (2 : ℝ) ^ G.J₀
          ≤ (2 : ℝ) ^ (j + 1 - G.J₀) := hpow
        _ ≤ (2 : ℝ) ^ (j + 1 - G.J₀) * (G.Q G.J₀ : ℝ) := le_mul_of_one_le_right (by positivity) hQJ1
        _ ≤ (G.Q (j + 1) : ℝ) := hgeom
    simp only [growDigDiff, hj, ↓reduceIte, abs_div, abs_mul, abs_of_pos hQ0, abs_of_pos hQ1]
    have h1 : |(G.growDigW J d j : ℝ)| / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ)) ≤
        2 * (K : ℝ) / (G.Q (j + 1) : ℝ) := by
      rw [div_le_div_iff₀ (mul_pos hQ0 hQ1) hQ1]
      nlinarith
    calc |(G.growDigW J d j : ℝ)| / ((G.Q j : ℝ) * (G.Q (j + 1) : ℝ))
        ≤ 2 * (K : ℝ) / (G.Q (j + 1) : ℝ) := h1
      _ ≤ 2 * (K : ℝ) / ((2 : ℝ) ^ j / (2 : ℝ) ^ G.J₀) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hQ1_ge
      _ = 2 * (K : ℝ) * (2 : ℝ) ^ G.J₀ * (1 / 2 : ℝ) ^ j := by
          rw [div_div_eq_mul_div, div_eq_mul_inv, one_div, inv_pow]
  · simp [growDigDiff, hj]

/-- Limit real number defined by the telescoping bounded-digit series. -/
noncomputable def growDigLimit (G : GrowingRecData) (J : ℕ) (d : ℕ → ℤ) : ℝ :=
  ∑' j : ℕ, G.growDigDiff J d j

/-- Master telescoping bounded-digit realization theorem for arbitrary growing quotients. -/
theorem grow_telescoping_digit_realize (G : GrowingRecData) (J K : ℕ)
    (hJ : G.J₀ + 1 ≤ J) (hAK : ∀ j : ℕ, J ≤ j → (8 * (K : ℤ) + 1 : ℤ) ≤ G.A j)
    (d : ℕ → ℤ) (hd : ∀ j : ℕ, J ≤ j → |d j| ≤ (K : ℤ)) :
    |G.growDigLimit J d| < 1 / (2 * (G.Q (J - 1) : ℝ)) ∧
    (∀ m : ℕ, J ≤ m →
      |(G.Q m : ℝ) * G.growDigLimit J d - (G.growDigM J d m : ℝ)| ≤
        4 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + 1) : ℝ)) ∧
    (∀ m : ℕ, J - 1 ≤ m → round ((G.Q m : ℝ) * G.growDigLimit J d) = G.growDigM J d m) ∧
    (∀ j : ℕ, J ≤ j → G.growDefect (G.growDigLimit J d) j = d j) ∧
    Tendsto (G.growEps (G.growDigLimit J d)) atTop (nhds 0) := by
  set x : ℝ := G.growDigLimit J d
  have hsum := G.summable_growDigDiff J K hJ d hd
  have htail : ∀ m : ℕ, J - 1 ≤ m →
      (G.Q m : ℝ) * x - (G.growDigM J d m : ℝ) =
        ∑' n : ℕ, (G.Q m : ℝ) * G.growDigDiff J d (m + n) := by
    intro m hm
    have hx_split := hsum.sum_add_tsum_nat_add m
    rw [G.sum_growDigDiff_eq J d (by omega) hm] at hx_split
    have hx_split' : (G.growDigM J d m : ℝ) / (G.Q m : ℝ) +
        ∑' n : ℕ, G.growDigDiff J d (m + n) = x := by
      dsimp [x, growDigLimit]
      convert hx_split using 2
      exact tsum_congr fun n => by rw [add_comm n m]
    have hQm : (G.Q m : ℝ) ≠ 0 := by have := G.hQ_pos m; positivity
    have hsub : x - (G.growDigM J d m : ℝ) / (G.Q m : ℝ) =
        ∑' n : ℕ, G.growDigDiff J d (m + n) := by linarith [hx_split']
    have hmul : (G.Q m : ℝ) * (x - (G.growDigM J d m : ℝ) / (G.Q m : ℝ)) =
        (G.Q m : ℝ) * x - (G.growDigM J d m : ℝ) := by field_simp [hQm]
    rw [← hmul, hsub, tsum_mul_left]
  have hbound_tail : ∀ m : ℕ, J - 1 ≤ m → ∀ k₀ : ℕ, (∀ n < k₀, G.growDigDiff J d (m + n) = 0) →
      |(G.Q m : ℝ) * x - (G.growDigM J d m : ℝ)| ≤
        4 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ) * (1 / 2 : ℝ) ^ 0 := by
    intro m hm k₀ hk₀
    rw [htail m hm]
    have hQm_pos : (0 : ℝ) < (G.Q m : ℝ) := by exact_mod_cast G.hQ_pos m
    have hQmk1_pos : (0 : ℝ) < (G.Q (m + k₀ + 1) : ℝ) := by exact_mod_cast G.hQ_pos (m + k₀ + 1)
    have hsum_m : Summable (fun n : ℕ => (G.Q m : ℝ) * G.growDigDiff J d (m + n)) :=
      (hsum.comp_injective
        (show Function.Injective (fun n : ℕ => m + n) from
          fun _ _ h => Nat.add_left_cancel h)).mul_left _
    have hsum_tail : Summable (fun n : ℕ =>
        (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀)) := by
      have h0 : Summable (fun n : ℕ =>
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ n) :=
        (summable_geometric_two).mul_left _
      have h1 : Summable (fun n : ℕ =>
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n + k₀ - k₀)) := by
        simpa [Nat.add_sub_cancel] using h0
      exact (summable_nat_add_iff k₀).mp h1
    have hsum_maj : Summable (fun n : ℕ =>
        if n < k₀ then (0 : ℝ) else
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀)) := by
      refine hsum_tail.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) fun n => ?_
      split_ifs with h
      · exact mul_nonneg (div_nonneg (by positivity) hQmk1_pos.le) (pow_nonneg (by norm_num) _)
      · exact le_rfl
    have hle_term : ∀ n : ℕ,
        |(G.Q m : ℝ) * G.growDigDiff J d (m + n)| ≤
          if n < k₀ then 0 else
            (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀) := by
      intro n
      split_ifs with hn
      · simp [hk₀ n hn]
      · have hm_ge : J - 1 ≤ m + n := le_trans hm (Nat.le_add_right m n)
        have hW : |(G.growDigW J d (m + n) : ℝ)| ≤ 2 * (K : ℝ) * (G.Q (m + n) : ℝ) := by
          exact_mod_cast G.abs_growDigW_le J K hJ d hd hm_ge
        have hQm : (0 : ℝ) < (G.Q m : ℝ) := hQm_pos
        have hQmn : (0 : ℝ) < (G.Q (m + n) : ℝ) := by exact_mod_cast G.hQ_pos (m + n)
        have hQmn1 : (0 : ℝ) < (G.Q (m + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos (m + n + 1)
        have hQmk1 : (0 : ℝ) < (G.Q (m + k₀ + 1) : ℝ) := hQmk1_pos
        have hgeom : (2 : ℝ) ^ (n - k₀) * (G.Q (m + k₀ + 1) : ℝ) ≤ (G.Q (m + n + 1) : ℝ) := by
          have hidx : m + k₀ + 1 + (n - k₀) = m + n + 1 := by omega
          have hle := G.grow_Q_geom (j := m + k₀ + 1) (by omega) (n - k₀)
          rwa [hidx] at hle
        simp only [growDigDiff, hm_ge, ↓reduceIte, abs_mul, abs_div, abs_of_pos hQm,
          abs_of_pos hQmn, abs_of_pos hQmn1]
        have h1 : (G.Q m : ℝ) * (|(G.growDigW J d (m + n) : ℝ)| /
            ((G.Q (m + n) : ℝ) * (G.Q (m + n + 1) : ℝ))) ≤
            2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + n + 1) : ℝ) := by
          calc (G.Q m : ℝ) * (|(G.growDigW J d (m + n) : ℝ)| /
                ((G.Q (m + n) : ℝ) * (G.Q (m + n + 1) : ℝ)))
              = ((G.Q m : ℝ) * |(G.growDigW J d (m + n) : ℝ)|) /
                  ((G.Q (m + n) : ℝ) * (G.Q (m + n + 1) : ℝ)) := (mul_div_assoc _ _ _).symm
            _ ≤ 2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + n + 1) : ℝ) := by
                rw [div_le_div_iff₀ (mul_pos hQmn hQmn1) hQmn1]
                calc (G.Q m : ℝ) * |(G.growDigW J d (m + n) : ℝ)| * (G.Q (m + n + 1) : ℝ)
                    ≤ (G.Q m : ℝ) * (2 * (K : ℝ) * (G.Q (m + n) : ℝ)) *
                        (G.Q (m + n + 1) : ℝ) := by gcongr
                  _ = 2 * (K : ℝ) * (G.Q m : ℝ) *
                        ((G.Q (m + n) : ℝ) * (G.Q (m + n + 1) : ℝ)) := by ring
        have h2 : 2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + n + 1) : ℝ) ≤
            2 * (K : ℝ) * (G.Q m : ℝ) / ((2 : ℝ) ^ (n - k₀) * (G.Q (m + k₀ + 1) : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hgeom
        have h3 : 2 * (K : ℝ) * (G.Q m : ℝ) / ((2 : ℝ) ^ (n - k₀) * (G.Q (m + k₀ + 1) : ℝ)) =
            (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀) := by
          rw [one_div, inv_pow]; ring
        exact h1.trans (h2.trans_eq h3)
    have hnorm : |∑' n : ℕ, (G.Q m : ℝ) * G.growDigDiff J d (m + n)| ≤
        ∑' n : ℕ, if n < k₀ then (0 : ℝ) else
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀) := by
      refine le_of_tendsto_of_tendsto' hsum_m.hasSum.tendsto_sum_nat.abs
        hsum_maj.hasSum.tendsto_sum_nat fun N => ?_
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => hle_term n)
    have htsum_eq : (∑' n : ℕ, if n < k₀ then (0 : ℝ) else
        (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀)) =
        4 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ) := by
      have hsplit := hsum_maj.sum_add_tsum_nat_add k₀
      have hzero : (∑ n ∈ Finset.range k₀, if n < k₀ then (0 : ℝ) else
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n - k₀)) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [Finset.mem_range] at hn; simp [hn]
      rw [hzero, zero_add] at hsplit
      rw [← hsplit]
      have hcongr : (∑' n : ℕ, if n + k₀ < k₀ then (0 : ℝ) else
          (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ (n + k₀ - k₀)) =
          ∑' n : ℕ, (2 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + k₀ + 1) : ℝ)) * (1 / 2 : ℝ) ^ n := by
        refine tsum_congr fun n => ?_
        have hnot : ¬ (n + k₀ < k₀) := by omega
        have hsub : n + k₀ - k₀ = n := by omega
        simp [hnot, hsub]
      rw [hcongr, tsum_mul_left, tsum_geometric_two]
      ring
    simpa [pow_zero, mul_one] using hnorm.trans_eq htsum_eq
  have hbm : ∀ m : ℕ, J ≤ m →
      |(G.Q m : ℝ) * x - (G.growDigM J d m : ℝ)| ≤
        4 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + 1) : ℝ) := by
    intro m hm
    simpa using hbound_tail m (by omega) 0 (fun _ hn => (Nat.not_lt_zero _ hn).elim)
  have hhalf_ge : ∀ m : ℕ, J - 1 ≤ m → |(G.Q m : ℝ) * x - (G.growDigM J d m : ℝ)| < 1 / 2 := by
    intro m hm
    rcases eq_or_lt_of_le hm with rfl | hgt
    · have hk1 := hbound_tail (J - 1) (le_refl _) 1 (fun n hn => by
        obtain rfl : n = 0 := by omega
        simp [growDigDiff, G.growDigW_init J d (by omega)])
      have hidx : J - 1 + 1 + 1 = J + 1 := by omega
      rw [hidx, pow_zero, mul_one] at hk1
      have hQJ1 : (2 : ℝ) * (G.Q (J - 1) : ℝ) * (G.A J : ℝ) < (G.Q (J + 1) : ℝ) := by
        have h1 : (2 : ℝ) * (G.Q (J - 1) : ℝ) < (G.Q J : ℝ) := by
          have hq := G.grow_Q_succ_ge_two_mul (j := J - 1) (by omega)
          rw [show J - 1 + 1 = J by omega] at hq
          exact_mod_cast hq
        have h2 : (G.A J : ℝ) * (G.Q J : ℝ) < (G.Q (J + 1) : ℝ) := by
          exact_mod_cast G.grow_Q_succ_gt_A_mul (by omega)
        have hAp := G.grow_A_pos (by omega : G.J₀ ≤ J)
        nlinarith
      have hAK_J : (8 * (K : ℝ) + 1 : ℝ) ≤ (G.A J : ℝ) := by exact_mod_cast hAK J (le_refl _)
      have hQ0 : (0 : ℝ) < (G.Q (J - 1) : ℝ) := by exact_mod_cast G.hQ_pos (J - 1)
      have hQ1 : (0 : ℝ) < (G.Q (J + 1) : ℝ) := by exact_mod_cast G.hQ_pos (J + 1)
      calc |(G.Q (J - 1) : ℝ) * x - (G.growDigM J d (J - 1) : ℝ)|
          ≤ 4 * (K : ℝ) * (G.Q (J - 1) : ℝ) / (G.Q (J + 1) : ℝ) := hk1
        _ < 1 / 2 := by
            rw [div_lt_div_iff₀ hQ1 (by norm_num : (0 : ℝ) < 2)]
            nlinarith
    · have hmJ : J ≤ m := by omega
      have hQm : (0 : ℝ) < (G.Q m : ℝ) := by exact_mod_cast G.hQ_pos m
      have hQm1 : (0 : ℝ) < (G.Q (m + 1) : ℝ) := by exact_mod_cast G.hQ_pos (m + 1)
      have hrec : (G.A m : ℝ) * (G.Q m : ℝ) < (G.Q (m + 1) : ℝ) := by
        exact_mod_cast G.grow_Q_succ_gt_A_mul (by omega)
      have hAm : (8 * (K : ℝ) + 1 : ℝ) ≤ (G.A m : ℝ) := by exact_mod_cast hAK m hmJ
      calc |(G.Q m : ℝ) * x - (G.growDigM J d m : ℝ)|
          ≤ 4 * (K : ℝ) * (G.Q m : ℝ) / (G.Q (m + 1) : ℝ) := hbm m hmJ
        _ < 1 / 2 := by
            rw [div_lt_div_iff₀ hQm1 (by norm_num : (0 : ℝ) < 2)]
            nlinarith
  have hx_lt : |x| < 1 / (2 * (G.Q (J - 1) : ℝ)) := by
    have h0 := hhalf_ge (J - 1) (le_refl _)
    rw [G.growDigM_eq_zero_of_le J d (Nat.sub_le J 1)] at h0
    simp only [Int.cast_zero, sub_zero, abs_mul] at h0
    have hQ0 : (0 : ℝ) < (G.Q (J - 1) : ℝ) := by exact_mod_cast G.hQ_pos (J - 1)
    rw [abs_of_pos hQ0] at h0
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hround : ∀ m : ℕ, J - 1 ≤ m → round ((G.Q m : ℝ) * x) = G.growDigM J d m :=
    fun m hm => round_eq_of_abs_sub_lt_half_grow (hhalf_ge m hm)
  have hdef : ∀ j : ℕ, J ≤ j → G.growDefect x j = d j := by
    intro j hj
    simp only [growDefect, hround (j + 1) (by omega), hround j (by omega),
      hround (j - 1) (by omega), G.growDigM_rec J d hj]
    ring
  have heps0 : Tendsto (G.growEps x) atTop (nhds 0) := by
    have hlim_invA : Tendsto (fun j : ℕ => 4 * (K : ℝ) / (G.A j : ℝ)) atTop (nhds 0) :=
      G.hA_tendsto.const_div_atTop (4 * (K : ℝ))
    refine tendsto_zero_iff_abs_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_invA
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_)
    filter_upwards [eventually_ge_atTop J] with j hj
    have heq : G.growEps x j = (G.Q j : ℝ) * x - (G.growDigM J d j : ℝ) := by
      simp [growEps, hround j (by omega)]
    rw [heq]
    have hbmj := hbm j hj
    have hrec : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
      exact_mod_cast (G.grow_Q_succ_gt_A_mul (by omega)).le
    have hAj : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos (by omega)
    have hQj1 : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    exact hbmj.trans (by rw [div_le_div_iff₀ hQj1 hAj]; nlinarith)
  exact ⟨hx_lt, hbm, hround, hdef, heps0⟩

lemma grow_telescoping_const_defect (G : GrowingRecData) (d₀ : ℤ) :
    ∃ x : ℝ, Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps x j) atTop (nhds (d₀ : ℝ)) ∧
      Tendsto (G.growSeq x) atTop (nhds |(d₀ : ℝ)|) ∧
      G.growLambda x = (d₀.natAbs : ℝ≥0∞) := by
  let K : ℕ := d₀.natAbs
  obtain ⟨J0, hJ0⟩ := eventually_atTop.mp
    (G.hA_tendsto.eventually_ge_atTop ((8 * (K : ℤ) + 1 : ℤ) : ℝ))
  let J := max (G.J₀ + 1) J0
  have hJ : G.J₀ + 1 ≤ J := le_max_left _ _
  have hAK : ∀ j : ℕ, J ≤ j → (8 * (K : ℤ) + 1 : ℤ) ≤ G.A j := fun j hj => by
    have hR : ((8 * (K : ℤ) + 1 : ℤ) : ℝ) ≤ (G.A j : ℝ) := hJ0 j (le_trans (le_max_right _ _) hj)
    exact Int.cast_le.mp hR
  have hd : ∀ j : ℕ, J ≤ j → |(fun _ => d₀) j| ≤ (K : ℤ) := fun _ _ => by simp [K]
  obtain ⟨_, _, _, hdef, heps0⟩ := G.grow_telescoping_digit_realize J K hJ hAK (fun _ => d₀) hd
  set x : ℝ := G.growDigLimit J (fun _ => d₀)
  have hsigned : Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps x j) atTop (nhds (d₀ : ℝ)) := by
    have hsub := G.grow_signed_defect_approx x heps0
    have hcongr : Tendsto (fun j : ℕ => (G.growDefect x j : ℝ) -
        ((G.growDefect x j : ℝ) - (G.A j : ℝ) * G.growEps x j)) atTop (nhds (d₀ : ℝ)) := by
      have hd_lim : Tendsto (fun j : ℕ => (G.growDefect x j : ℝ)) atTop (nhds (d₀ : ℝ)) :=
        tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨J, fun j hj => by
          dsimp only; rw [hdef j hj]⟩)
      simpa using hd_lim.sub hsub
    exact hcongr.congr fun j => by ring
  have hseq : Tendsto (G.growSeq x) atTop (nhds |(d₀ : ℝ)|) := by
    have habs := hsigned.abs
    refine habs.congr' ?_
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    rw [G.growSeq_eq_of_ge x hj, abs_mul, abs_of_pos (G.grow_A_pos hj)]
  have hlam : G.growLambda x = (d₀.natAbs : ℝ≥0∞) := by
    have h1 := (ENNReal.tendsto_ofReal hseq).limsup_eq
    have h2 : ENNReal.ofReal |(d₀ : ℝ)| = (d₀.natAbs : ℝ≥0∞) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, ENNReal.ofReal_natCast]
    exact h1.trans h2
  exact ⟨x, hsigned, hseq, hlam⟩

/-- Open spectral gaps: NO `x ∈ ℝ` has `Λ_G(x) ∈ (k, k + 1)` or `A_j ||Q_j x|| → L ∈ (k, k + 1)`. -/
theorem grow_spectral_gap_open_interval (G : GrowingRecData) (k : ℕ) :
    (∀ x : ℝ, ¬ ((k : ℝ≥0∞) < G.growLambda x ∧ G.growLambda x < ((k + 1 : ℕ) : ℝ≥0∞))) ∧
    (∀ {L : ℝ}, (k : ℝ) < L → L < (k : ℝ) + 1 →
      ∀ x : ℝ, ¬ Tendsto (G.growSeq x) atTop (nhds L)) := by
  have hgap1 : ∀ x : ℝ,
      ¬ ((k : ℝ≥0∞) < G.growLambda x ∧ G.growLambda x < ((k + 1 : ℕ) : ℝ≥0∞)) := by
    rintro x ⟨hk_lt, hk1_lt⟩
    have hne_top : G.growLambda x ≠ ⊤ := ne_top_of_lt hk1_lt
    have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top hne_top
    have habs_diff := G.grow_abs_defect_approx x hε
    let M : ℝ := ((k : ℝ) + 1 + (G.growLambda x).toReal) / 2
    have hlam_real : (G.growLambda x).toReal < (k : ℝ) + 1 := by
      have hk1_ofReal : ((k + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ) + 1) := by
        rw [← ENNReal.ofReal_natCast]; congr 1; push_cast; ring
      have hk1_lt' : G.growLambda x < ENNReal.ofReal ((k : ℝ) + 1) := hk1_ofReal ▸ hk1_lt
      have hst := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hk1_lt'
      rwa [ENNReal.toReal_ofReal (by positivity)] at hst
    have hM_lt : M < (k : ℝ) + 1 := by dsimp [M]; linarith
    have hM_pos : 0 < M := by
      have : 0 ≤ (G.growLambda x).toReal := ENNReal.toReal_nonneg
      dsimp [M]; linarith
    have hlam_lt_M : G.growLambda x < ENNReal.ofReal M := by
      rw [← ENNReal.ofReal_toReal hne_top]
      exact (ENNReal.ofReal_lt_ofReal_iff hM_pos).mpr (by dsimp [M]; linarith)
    have hev_M := Filter.eventually_lt_of_limsup_lt hlam_lt_M (by isBoundedDefault)
    have hev_err : ∀ᶠ j : ℕ in atTop,
        |(G.growDefect x j : ℝ)| - G.growSeq x j < ((k : ℝ) + 1 - M) / 2 :=
      habs_diff.eventually (Iio_mem_nhds (by linarith))
    have hev_d_le : ∀ᶠ j : ℕ in atTop, |(G.growDefect x j : ℝ)| ≤ (k : ℝ) := by
      filter_upwards [hev_M, hev_err] with j hjM hjerr
      have hjR : G.growSeq x j < M := (ENNReal.ofReal_lt_ofReal_iff hM_pos).mp hjM
      have hlt_k1 : |(G.growDefect x j : ℝ)| < ((k + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hlt_Z : |G.growDefect x j| < (k : ℤ) + 1 := by exact_mod_cast hlt_k1
      have hle_Z : |G.growDefect x j| ≤ (k : ℤ) := by omega
      exact_mod_cast hle_Z
    have hlim_diff : ∀ ε : ℝ, 0 < ε → G.growLambda x ≤ (k : ℝ≥0∞) + ENNReal.ofReal ε := by
      intro ε hε_pos
      have herr2 : ∀ᶠ j : ℕ in atTop,
          -ε < |(G.growDefect x j : ℝ)| - G.growSeq x j :=
        habs_diff.eventually (Ioi_mem_nhds (by linarith))
      refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
      filter_upwards [hev_d_le, herr2] with j hdj hej
      have hleR : G.growSeq x j ≤ (k : ℝ) + ε := by linarith
      calc ENNReal.ofReal (G.growSeq x j)
          ≤ ENNReal.ofReal ((k : ℝ) + ε) := ENNReal.ofReal_le_ofReal hleR
        _ ≤ ENNReal.ofReal (k : ℝ) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ = (k : ℝ≥0∞) + ENNReal.ofReal ε := by rw [ENNReal.ofReal_natCast]
    have hlim_k : Tendsto (fun n : ℕ => (k : ℝ≥0∞) + ENNReal.ofReal (1 / ((n : ℝ) + 1)))
        atTop (nhds (k : ℝ≥0∞)) := by
      have hinv : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
        simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := (k : ℝ≥0∞))).add hinv
    have hle_k : G.growLambda x ≤ (k : ℝ≥0∞) :=
      ge_of_tendsto hlim_k (Filter.Eventually.of_forall fun n =>
        hlim_diff _ (div_pos one_pos (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])))
    exact not_lt_of_ge hle_k hk_lt
  refine ⟨hgap1, fun {L} hkL hLk1 x hx => ?_⟩
  have hlam : G.growLambda x = ENNReal.ofReal L := (ENNReal.tendsto_ofReal hx).limsup_eq
  have hL_pos : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg k) hkL
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt1 : (k : ℝ≥0∞) < G.growLambda x := by
    rw [hlam, ← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff hL_pos).mpr hkL
  have hlt2 : G.growLambda x < ((k + 1 : ℕ) : ℝ≥0∞) := by
    rw [hlam, ← ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hk1_pos).mpr hLk1
  exact hgap1 x ⟨hlt1, hlt2⟩

lemma grow_exact_level_iff (G : GrowingRecData) (k : ℕ) (x : ℝ) :
    G.growLambda x ≤ (k : ℝ≥0∞) → G.growLambda x < ((k + 1 : ℕ) : ℝ≥0∞) := fun h =>
  lt_of_le_of_lt h (by exact_mod_cast Nat.lt_succ_self k)

/-! ### Part 5: Universal Hausdorff Dimension Zero, Lebesgue Nullity, and Full Generic Dimension -/

/-- Branching candidate `(m_{j+1}, m_j)` pairs over digit alphabet `D : Finset ℤ`. -/
def growPairTreeA (G : GrowingRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) :
    ℕ → Finset (ℤ × ℤ)
  | 0 => {(m₁, m₀)}
  | n + 1 =>
      (growPairTreeA G D N m₀ m₁ n).biUnion fun p =>
        D.image fun d => (G.A (N + n) * p.1 + p.2 + d, p.1)

lemma card_growPairTreeA_le (G : GrowingRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) (n : ℕ) :
    (G.growPairTreeA D N m₀ m₁ n).card ≤ D.card ^ n := by
  induction n with
  | zero => simp [growPairTreeA]
  | succ n ih =>
    rw [growPairTreeA]
    calc ((G.growPairTreeA D N m₀ m₁ n).biUnion _).card
        ≤ ∑ _p ∈ G.growPairTreeA D N m₀ m₁ n, D.card := by
          exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le)
      _ = (G.growPairTreeA D N m₀ m₁ n).card * D.card := by simp
      _ ≤ D.card ^ n * D.card := Nat.mul_le_mul_right _ ih
      _ = D.card ^ (n + 1) := (pow_succ _ _).symm

def growGaugeInterv (G : GrowingRecData) (j : ℕ) (m : ℤ) : Set ℝ :=
  Set.Icc (((m : ℝ) - 1 / 2) / (G.Q j : ℝ)) (((m : ℝ) + 1 / 2) / (G.Q j : ℝ))

lemma ediam_growGaugeInterv_le (G : GrowingRecData) (j : ℕ) (m : ℤ) :
    Metric.ediam (G.growGaugeInterv j m) ≤ ENNReal.ofReal (1 / (G.Q j : ℝ)) := by
  have hQp : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  rw [growGaugeInterv, Real.ediam_Icc]
  apply ENNReal.ofReal_le_ofReal
  have heq : ((m : ℝ) + 1 / 2) / (G.Q j : ℝ) - ((m : ℝ) - 1 / 2) / (G.Q j : ℝ) =
      1 / (G.Q j : ℝ) := by ring
  linarith

lemma mem_growGaugeInterv_round (G : GrowingRecData) (x : ℝ) (j : ℕ) :
    x ∈ G.growGaugeInterv j (round ((G.Q j : ℝ) * x)) := by
  have hQp : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
  have hle := abs_sub_round ((G.Q j : ℝ) * x)
  have hbd := abs_le.mp hle
  constructor
  · rw [div_le_iff₀ hQp]; linarith
  · rw [le_div_iff₀ hQp]; linarith

/-- Fixed-defect-alphabet class starting at index `N` with initial pair `(m₀, m₁)`. -/
def growAlphabetClass (G : GrowingRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ) : Set ℝ :=
  {x : ℝ | G.J₀ ≤ N ∧ 1 ≤ N ∧
    round ((G.Q (N - 1) : ℝ) * x) = m₀ ∧
    round ((G.Q N : ℝ) * x) = m₁ ∧
    ∀ j : ℕ, N ≤ j → G.growDefect x j ∈ D}

lemma round_pair_mem_growPairTreeA (G : GrowingRecData) (D : Finset ℤ) (N : ℕ) (m₀ m₁ : ℤ)
    {x : ℝ} (hx : x ∈ G.growAlphabetClass D N m₀ m₁) (n : ℕ) :
    (round ((G.Q (N + n) : ℝ) * x), round ((G.Q (N + n - 1) : ℝ) * x)) ∈
      G.growPairTreeA D N m₀ m₁ n := by
  rcases hx with ⟨_, hN1, hm0, hm1, hD⟩
  induction n with
  | zero =>
    simp [growPairTreeA, hm0, hm1]
  | succ n ih =>
    rw [growPairTreeA, Finset.mem_biUnion]
    refine ⟨(round ((G.Q (N + n) : ℝ) * x), round ((G.Q (N + n - 1) : ℝ) * x)), ih, ?_⟩
    rw [Finset.mem_image]
    refine ⟨G.growDefect x (N + n), hD (N + n) (by omega), ?_⟩
    have hsub : N + (n + 1) - 1 = N + n := by omega
    have hadd : N + (n + 1) = N + n + 1 := by omega
    rw [hsub, hadd]
    ext
    · simp only [growDefect]; ring
    · rfl

lemma growAlphabetClass_subset_cover (G : GrowingRecData) (D : Finset ℤ) (N : ℕ)
    (m₀ m₁ : ℤ) (n : ℕ) :
    G.growAlphabetClass D N m₀ m₁ ⊆
      ⋃ p : (G.growPairTreeA D N m₀ m₁ n : Set (ℤ × ℤ)), G.growGaugeInterv (N + n) p.1.1 := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨⟨_, G.round_pair_mem_growPairTreeA D N m₀ m₁ hx n⟩,
    G.mem_growGaugeInterv_round x (N + n)⟩

lemma grow_eventually_abs_defect_le_of_lambda_le (G : GrowingRecData) (k : ℕ)
    {x : ℝ} (hx : G.growLambda x ≤ (k : ℝ≥0∞)) :
    ∀ᶠ j : ℕ in atTop, |G.growDefect x j| ≤ (k : ℤ) := by
  have hne : G.growLambda x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hx
  have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top hne
  have happrox := G.grow_abs_defect_approx x hε
  have hlt : G.growLambda x < ENNReal.ofReal ((k : ℝ) + 1 / 2) := by
    refine lt_of_le_of_lt hx ?_
    rw [← ENNReal.ofReal_natCast]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hev_seq : ∀ᶠ j : ℕ in atTop, G.growSeq x j < (k : ℝ) + 1 / 2 := by
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt (by isBoundedDefault)] with j hj
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hj
  have hev_err : ∀ᶠ j : ℕ in atTop, |(G.growDefect x j : ℝ)| - G.growSeq x j < 1 / 4 :=
    happrox.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hev_seq, hev_err] with j hjseq hjerr
  have hlt_k1 : |(G.growDefect x j : ℝ)| < ((k + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  have hlt_Z : |G.growDefect x j| < (k : ℤ) + 1 := by exact_mod_cast hlt_k1
  omega

lemma growLevelSet_nat_subset_iUnion_alphabet (G : GrowingRecData) (k : ℕ) :
    G.growLevelSet (k : ℝ≥0∞) ⊆
      ⋃ (p : ℕ × ℤ × ℤ), G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2 := by
  intro x hx
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (G.grow_eventually_abs_defect_le_of_lambda_le k hx)
  let N := max N0 G.J₀
  refine Set.mem_iUnion.mpr ⟨(N, round ((G.Q (N - 1) : ℝ) * x), round ((G.Q N : ℝ) * x)),
    le_max_right _ _, le_trans G.hJ₀ (le_max_right _ _), rfl, rfl, fun j hj => ?_⟩
  rw [Finset.mem_Icc]
  exact abs_le.mp (hN0 j (le_trans (le_max_left _ _) hj))

theorem dimH_growAlphabetClass_eq_zero (G : GrowingRecData) (D : Finset ℤ)
    (hD : 1 ≤ D.card) (N : ℕ) (m₀ m₁ : ℤ) :
    dimH (G.growAlphabetClass D N m₀ m₁) = 0 := by
  have hmu_zero : ∀ s : ℝ, 0 < s → μH[s] (G.growAlphabetClass D N m₀ m₁) = 0 := by
    intro s hs
    let ι : ℕ → Type := fun n => (G.growPairTreeA D N m₀ m₁ n : Set (ℤ × ℤ))
    let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (G.Q (N + n) : ℝ))
    have hr : Tendsto r atTop (nhds 0) := by
      have hreal : Tendsto (fun n : ℕ => 1 / (G.Q (N + n) : ℝ)) atTop (nhds 0) := by
        simpa [add_comm N] using
          (G.grow_Q_tendsto_atTop.comp (tendsto_add_atTop_nat N)).const_div_atTop 1
      simpa [r] using ENNReal.tendsto_ofReal hreal
    let cov : ∀ n : ℕ, ι n → Set ℝ := fun n i => G.growGaugeInterv (N + n) i.1.1
    have ht_diam : ∀ᶠ n in atTop, ∀ i : ι n, Metric.ediam (cov n i) ≤ r n :=
      Filter.Eventually.of_forall fun n i => G.ediam_growGaugeInterv_le (N + n) i.1.1
    have hst : ∀ᶠ n in atTop, G.growAlphabetClass D N m₀ m₁ ⊆ ⋃ i : ι n, cov n i := by
      refine Filter.Eventually.of_forall fun n => ?_
      exact G.growAlphabetClass_subset_cover D N m₀ m₁ n
    have hmain := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum s
      (G.growAlphabetClass D N m₀ m₁) r hr cov ht_diam hst
    have hlimR : Tendsto (fun n : ℕ => (D.card : ℝ) ^ n * (1 / (G.Q (N + n) : ℝ)) ^ s)
        atTop (nhds 0) := by
      have h0 := G.grow_pow_div_Q_rpow_tendsto_zero (B := (D.card : ℝ)) (Nat.cast_nonneg _) hs
      have h0' : Tendsto (fun n : ℕ => (D.card : ℝ) ^ (N + n) / (G.Q (N + n) : ℝ) ^ s)
          atTop (nhds 0) :=
        (h0.comp (tendsto_add_atTop_nat N)).congr
          (fun n => by simp only [Function.comp_apply, add_comm n N])
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0' ?_ ?_
      · intro n
        exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (Real.rpow_nonneg (div_nonneg zero_le_one (by exact_mod_cast (G.hQ_pos _).le)) _)
      · intro n
        have hQp : (0 : ℝ) < (G.Q (N + n) : ℝ) := by exact_mod_cast G.hQ_pos _
        have hDc : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hD
        dsimp only
        rw [one_div, Real.inv_rpow hQp.le, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hDc (Nat.le_add_left n N))
          (Real.rpow_nonneg hQp.le _)
    have hsum_le : ∀ n : ℕ, (∑ i : ι n, Metric.ediam (cov n i) ^ s) ≤
        ENNReal.ofReal ((D.card : ℝ) ^ n * (1 / (G.Q (N + n) : ℝ)) ^ s) := by
      intro n
      have hcard : Fintype.card (ι n) = (G.growPairTreeA D N m₀ m₁ n).card := by simp [ι]
      calc ∑ i : ι n, Metric.ediam (cov n i) ^ s
          ≤ ∑ _i : ι n, (r n) ^ s := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact ENNReal.rpow_le_rpow (G.ediam_growGaugeInterv_le (N + n) i.1.1) hs.le
        _ = ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * (r n) ^ s := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal ((D.card : ℝ) ^ n) *
              ENNReal.ofReal ((1 / (G.Q (N + n) : ℝ)) ^ s) := by
              have hcast1 : ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) ≤
                  ENNReal.ofReal ((D.card : ℝ) ^ n) := by
                rw [hcard, ← ENNReal.ofReal_natCast]
                apply ENNReal.ofReal_le_ofReal
                exact_mod_cast G.card_growPairTreeA_le D N m₀ m₁ n
              have hcast2 : (r n) ^ s = ENNReal.ofReal ((1 / (G.Q (N + n) : ℝ)) ^ s) := by
                dsimp [r]
                rw [← ENNReal.ofReal_rpow_of_nonneg (by
                  have := (G.hQ_pos (N + n)).le; positivity) hs.le]
              exact mul_le_mul' hcast1 hcast2.le
        _ = ENNReal.ofReal ((D.card : ℝ) ^ n * (1 / (G.Q (N + n) : ℝ)) ^ s) := by
              rw [← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _)]
    have hlim0 : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((D.card : ℝ) ^ n * (1 / (G.Q (N + n) : ℝ)) ^ s)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hlimR
    have hliminf0 : Filter.liminf (fun n : ℕ => ∑ i : ι n, Metric.ediam (cov n i) ^ s)
        atTop ≤ 0 := by
      have h1 : Filter.liminf (fun n : ℕ => ∑ i : ι n, Metric.ediam (cov n i) ^ s) atTop ≤
          Filter.liminf (fun n : ℕ =>
            ENNReal.ofReal ((D.card : ℝ) ^ n * (1 / (G.Q (N + n) : ℝ)) ^ s)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hsum_le)
          (by isBoundedDefault) (by isBoundedDefault)
      rwa [hlim0.liminf_eq] at h1
    exact le_antisymm (hmain.trans hliminf0) bot_le
  apply le_antisymm _ bot_le
  rw [dimH_eq_iInf]
  by_contra hne
  have hpos : 0 < ⨅ (d : ℝ≥0) (_ : μH[d] (G.growAlphabetClass D N m₀ m₁) = 0), (d : ℝ≥0∞) :=
    not_le.mp hne
  obtain ⟨r, hr0, hrlt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hr2 : 0 < (r : ℝ) / 2 := by positivity
  have hmu := hmu_zero ((r : ℝ) / 2) hr2
  have hle : (⨅ (d : ℝ≥0) (_ : μH[d] (G.growAlphabetClass D N m₀ m₁) = 0), (d : ℝ≥0∞)) ≤
      ((r / 2 : ℝ≥0) : ℝ≥0∞) := by
    apply iInf₂_le (⟨(r : ℝ) / 2, hr2.le⟩ : ℝ≥0)
    exact hmu
  have hlt : ((r / 2 : ℝ≥0) : ℝ≥0∞) < (r : ℝ≥0∞) := by
    exact_mod_cast (by linarith : (r : ℝ) / 2 < (r : ℝ))
  exact (not_le.mpr (lt_of_lt_of_le hrlt hle)) hlt.le

theorem dimH_growLevelSet_nat_eq_zero (G : GrowingRecData) (k : ℕ) :
    dimH (G.growLevelSet (k : ℝ≥0∞)) = 0 := by
  have hcard : 1 ≤ (Finset.Icc (-(k : ℤ)) k).card := by
    rw [Int.card_Icc]; omega
  refine le_antisymm ?_ bot_le
  calc dimH (G.growLevelSet (k : ℝ≥0∞))
      ≤ dimH (⋃ p : ℕ × ℤ × ℤ,
          G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2) :=
        dimH_mono (G.growLevelSet_nat_subset_iUnion_alphabet k)
    _ = ⨆ p : ℕ × ℤ × ℤ,
          dimH (G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2) := by
        rw [dimH_iUnion]
    _ = 0 := by
        simp [G.dimH_growAlphabetClass_eq_zero _ hcard]

theorem dimH_growFiniteSet_eq_zero (G : GrowingRecData) :
    dimH G.growFiniteSet = 0 := by
  have hsub : G.growFiniteSet ⊆ ⋃ k : ℕ, G.growLevelSet (k : ℝ≥0∞) := by
    intro x hx
    rw [growFiniteSet, Set.mem_ofPred_eq, lt_top_iff_ne_top] at hx
    obtain ⟨k, hk⟩ := exists_nat_gt (G.growLambda x).toReal
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [growLevelSet, Set.mem_ofPred_eq, ← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hk.le
  refine le_antisymm ?_ bot_le
  calc dimH G.growFiniteSet
      ≤ dimH (⋃ k : ℕ, G.growLevelSet (k : ℝ≥0∞)) := dimH_mono hsub
    _ = ⨆ k : ℕ, dimH (G.growLevelSet (k : ℝ≥0∞)) := by rw [dimH_iUnion]
    _ = 0 := by simp [G.dimH_growLevelSet_nat_eq_zero]

lemma volume_growAlphabetClass_eq_zero (G : GrowingRecData) (D : Finset ℤ)
    (hD : 1 ≤ D.card) (N : ℕ) (m₀ m₁ : ℤ) :
    MeasureTheory.volume (G.growAlphabetClass D N m₀ m₁) = 0 := by
  refine le_antisymm ?_ bot_le
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((D.card : ℝ) ^ n / (G.Q (N + n) : ℝ)))
      atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => (D.card : ℝ) ^ (N + n) / (G.Q (N + n) : ℝ))
        atTop (nhds 0) :=
      ((G.grow_pow_div_Q_tendsto_zero (D.card : ℝ)).comp (tendsto_add_atTop_nat N)).congr
        (fun n => by simp only [Function.comp_apply, add_comm n N])
    have hle : Tendsto (fun n : ℕ => (D.card : ℝ) ^ n / (G.Q (N + n) : ℝ)) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 ?_ ?_
      · intro n
        have hQp : (0 : ℝ) ≤ (G.Q (N + n) : ℝ) := by exact_mod_cast (G.hQ_pos (N + n)).le
        exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hQp
      · intro n
        have hQp : (0 : ℝ) < (G.Q (N + n) : ℝ) := by exact_mod_cast G.hQ_pos _
        have hDc : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hD
        exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hDc (Nat.le_add_left n N)) hQp.le
    simpa using ENNReal.tendsto_ofReal hle
  refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  have hcov := G.growAlphabetClass_subset_cover D N m₀ m₁ n
  have hQ_pos : (0 : ℝ) < (G.Q (N + n) : ℝ) := by exact_mod_cast G.hQ_pos _
  calc MeasureTheory.volume (G.growAlphabetClass D N m₀ m₁)
      ≤ MeasureTheory.volume
          (⋃ p : (G.growPairTreeA D N m₀ m₁ n : Set (ℤ × ℤ)),
            G.growGaugeInterv (N + n) p.1.1) := measure_mono hcov
    _ ≤ ∑ p : (G.growPairTreeA D N m₀ m₁ n : Set (ℤ × ℤ)),
          MeasureTheory.volume (G.growGaugeInterv (N + n) p.1.1) := measure_iUnion_fintype_le _ _
    _ = ((G.growPairTreeA D N m₀ m₁ n).card : ℝ≥0∞) *
          ENNReal.ofReal (1 / (G.Q (N + n) : ℝ)) := by
          have hvol : ∀ m : ℤ, MeasureTheory.volume (G.growGaugeInterv (N + n) m) =
              ENNReal.ofReal (1 / (G.Q (N + n) : ℝ)) := fun m => by
            rw [growGaugeInterv, Real.volume_Icc]
            congr 1; ring
          simp [hvol, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((D.card : ℝ) ^ n) * ENNReal.ofReal (1 / (G.Q (N + n) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ bot_le
          rw [← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          exact_mod_cast G.card_growPairTreeA_le D N m₀ m₁ n
    _ = ENNReal.ofReal ((D.card : ℝ) ^ n / (G.Q (N + n) : ℝ)) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _), mul_one_div]

theorem volume_growFiniteSet_eq_zero (G : GrowingRecData) :
    MeasureTheory.volume G.growFiniteSet = 0 := by
  have hsub : G.growFiniteSet ⊆
      ⋃ k : ℕ, ⋃ p : ℕ × ℤ × ℤ,
        G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2 := by
    intro x hx
    rw [growFiniteSet, Set.mem_ofPred_eq, lt_top_iff_ne_top] at hx
    obtain ⟨k, hk⟩ := exists_nat_gt (G.growLambda x).toReal
    have hle : G.growLambda x ≤ (k : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hk.le
    exact Set.mem_iUnion.mpr ⟨k, G.growLevelSet_nat_subset_iUnion_alphabet k hle⟩
  refine le_antisymm ?_ bot_le
  calc MeasureTheory.volume G.growFiniteSet
      ≤ MeasureTheory.volume (⋃ k : ℕ, ⋃ p : ℕ × ℤ × ℤ,
          G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2) := measure_mono hsub
    _ ≤ ∑' k : ℕ, ∑' p : ℕ × ℤ × ℤ,
          MeasureTheory.volume
            (G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2) := by
          exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => measure_iUnion_le _)
    _ = 0 := by
          have hvol0 : ∀ k : ℕ, ∀ p : ℕ × ℤ × ℤ,
              MeasureTheory.volume
                (G.growAlphabetClass (Finset.Icc (-(k : ℤ)) k) p.1 p.2.1 p.2.2) = 0 := fun k p =>
            G.volume_growAlphabetClass_eq_zero _ (by rw [Int.card_Icc]; omega) _ _ _
          simp [hvol0]

theorem ae_growLambda_eq_top (G : GrowingRecData) :
    ∀ᵐ x ∂MeasureTheory.volume, G.growLambda x = ⊤ := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ G.growLambda x = ⊤} = G.growFiniteSet := by
    ext x; simp [growFiniteSet, lt_top_iff_ne_top]
  rw [hset]
  exact G.volume_growFiniteSet_eq_zero

theorem dimH_growInfiniteSet_inter_Icc_eq_one (G : GrowingRecData) {a b : ℝ} (hab : a < b) :
    dimH (G.growInfiniteSet ∩ Set.Icc a b) = 1 := by
  have hvol_pos : 0 < MeasureTheory.volume (G.growInfiniteSet ∩ Set.Icc a b) := by
    have hsplit : Set.Icc a b =
        (G.growInfiniteSet ∩ Set.Icc a b) ∪ (G.growFiniteSet ∩ Set.Icc a b) := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, growInfiniteSet, growFiniteSet,
        Set.mem_ofPred_eq, lt_top_iff_ne_top]
      tauto
    have hfin_zero : MeasureTheory.volume (G.growFiniteSet ∩ Set.Icc a b) = 0 :=
      measure_mono_null Set.inter_subset_left G.volume_growFiniteSet_eq_zero
    have hle : MeasureTheory.volume (Set.Icc a b) ≤
        MeasureTheory.volume (G.growInfiniteSet ∩ Set.Icc a b) := by
      calc MeasureTheory.volume (Set.Icc a b)
          ≤ MeasureTheory.volume (G.growInfiniteSet ∩ Set.Icc a b) +
              MeasureTheory.volume (G.growFiniteSet ∩ Set.Icc a b) := by
            conv_lhs => rw [hsplit]
            exact measure_union_le _ _
        _ = MeasureTheory.volume (G.growInfiniteSet ∩ Set.Icc a b) := by rw [hfin_zero, add_zero]
    rw [Real.volume_Icc] at hle
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)) hle
  exact le_antisymm (GaugeExact.dimH_real_subset_le_one _)
    (PolyRecData.dimH_eq_one_of_volume_pos hvol_pos).ge

theorem dimH_growInfiniteSet_eq_one (G : GrowingRecData) :
    dimH G.growInfiniteSet = 1 :=
  le_antisymm (GaugeExact.dimH_real_subset_le_one _)
    (by
      calc (1 : ℝ≥0∞) = dimH (G.growInfiniteSet ∩ Set.Icc 0 1) :=
            (G.dimH_growInfiniteSet_inter_Icc_eq_one zero_lt_one).symm
        _ ≤ dimH G.growInfiniteSet := dimH_mono Set.inter_subset_left)

theorem grow_range_lambda (G : GrowingRecData) :
    Set.range G.growLambda = (Set.range (fun k : ℕ => (k : ℝ≥0∞))) ∪ {⊤} := by
  ext v
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩
    by_cases htop : G.growLambda x = ⊤
    · exact Or.inr htop
    · refine Or.inl ?_
      set k : ℕ := Nat.floor (G.growLambda x).toReal
      refine ⟨k, le_antisymm ?_ ?_⟩
      · rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le ENNReal.toReal_nonneg)
      · have hlt : G.growLambda x < ((k + 1 : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_natCast]
          refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
          push_cast; exact Nat.lt_floor_add_one _
        by_contra hgt
        push Not at hgt
        exact (G.grow_spectral_gap_open_interval k).1 x ⟨hgt, hlt⟩
  · rintro (⟨k, rfl⟩ | rfl)
    · obtain ⟨x, _, _, hx⟩ := G.grow_telescoping_const_defect (k : ℤ)
      exact ⟨x, by simpa using hx⟩
    · have hdim : dimH G.growInfiniteSet = 1 := G.dimH_growInfiniteSet_eq_one
      have hne : G.growInfiniteSet.Nonempty := by
        by_contra hem
        rw [Set.not_nonempty_iff_eq_empty] at hem
        rw [hem, dimH_empty] at hdim
        norm_num at hdim
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx⟩

lemma abs_growSeq_add_sub_le (G : GrowingRecData) (x y : ℝ) (j : ℕ) :
    |G.growSeq (x + y) j - G.growSeq x j| ≤
      |(G.A j : ℝ)| * distToNearestInt ((G.Q j : ℝ) * y) := by
  rw [growSeq, growSeq, ← mul_sub]
  rw [abs_mul, abs_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (G.A j : ℝ))
  have h1 := distToNearestInt_add_le ((G.Q j : ℝ) * x) ((G.Q j : ℝ) * y)
  have h2 := distToNearestInt_add_le ((G.Q j : ℝ) * (x + y)) (-((G.Q j : ℝ) * y))
  have hid1 : (G.Q j : ℝ) * (x + y) = (G.Q j : ℝ) * x + (G.Q j : ℝ) * y := by ring
  have hid2 : (G.Q j : ℝ) * (x + y) + -((G.Q j : ℝ) * y) = (G.Q j : ℝ) * x := by ring
  rw [← hid1] at h1
  rw [hid2, distToNearestInt_neg] at h2
  rw [abs_le]
  constructor <;> linarith

lemma growLambda_add_mem_growLatticeL (G : GrowingRecData) (x : ℝ)
    {y : ℝ} (hy : y ∈ G.growLatticeL) :
    G.growLambda (x + y) = G.growLambda x := by
  obtain ⟨C, _, hdist⟩ := G.grow_dist_le_of_mem_growLatticeL hy
  have hdiff0 : Tendsto (fun j : ℕ => G.growSeq (x + y) j - G.growSeq x j) atTop (nhds 0) := by
    have hQ0 : Tendsto (fun j : ℕ => C / (G.Q j : ℝ)) atTop (nhds 0) :=
      G.grow_Q_tendsto_atTop.const_div_atTop C
    refine tendsto_zero_iff_abs_tendsto_zero.mpr ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ0
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    have hAp : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
    have hrec : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
      exact_mod_cast (G.grow_Q_succ_gt_A_mul hj).le
    have hQ0' : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
    have hQ1' : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    calc |G.growSeq (x + y) j - G.growSeq x j|
        ≤ |(G.A j : ℝ)| * distToNearestInt ((G.Q j : ℝ) * y) := G.abs_growSeq_add_sub_le x y j
      _ ≤ (G.A j : ℝ) * (C / (G.Q (j + 1) : ℝ)) := by
          rw [abs_of_pos hAp]
          exact mul_le_mul_of_nonneg_left (hdist j hj) hAp.le
      _ ≤ C / (G.Q j : ℝ) := by
          rw [mul_div_assoc', div_le_div_iff₀ hQ1' hQ0']
          nlinarith
  have hle_of : ∀ u v : ℝ, Tendsto (fun j : ℕ => G.growSeq u j - G.growSeq v j) atTop (nhds 0) →
      G.growLambda u ≤ G.growLambda v := by
    intro u v huv
    by_cases hv : G.growLambda v = ⊤
    · simp [hv]
    · have hbd : ∀ ε : ℝ, 0 < ε → G.growLambda u ≤ G.growLambda v + ENNReal.ofReal ε := by
        intro ε hε
        have hev := huv.eventually (Iio_mem_nhds hε)
        have hsup_le : limsup (fun j : ℕ => ENNReal.ofReal (G.growSeq u j)) atTop ≤
            limsup (fun j : ℕ => ENNReal.ofReal (G.growSeq v j) + ENNReal.ofReal ε) atTop := by
          refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
          filter_upwards [hev] with j hj
          exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le
        exact hsup_le.trans
          (limsup_add_const_le (fun j : ℕ => ENNReal.ofReal (G.growSeq v j)) ENNReal.ofReal_ne_top)
      have hlim : Tendsto (fun n : ℕ => G.growLambda v + ENNReal.ofReal (1 / (n + 1 : ℝ)))
          atTop (nhds (G.growLambda v)) := by
        have hinv : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
          simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using (tendsto_const_nhds (x := G.growLambda v)).add hinv
      exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hbd _ (by positivity))
  refine le_antisymm (hle_of (x + y) x hdiff0) ?_
  have hdiff_rev : Tendsto (fun j : ℕ => G.growSeq x j - G.growSeq (x + y) j) atTop (nhds 0) := by
    simpa using hdiff0.neg
  exact hle_of x (x + y) hdiff_rev

lemma growUnsignedExactLimit_add_growLatticeL (G : GrowingRecData) (t : ℝ)
    {y : ℝ} (hy : y ∈ G.growLatticeL) :
    (fun x : ℝ => x + y) ⁻¹' G.growUnsignedExactLimitSet t = G.growUnsignedExactLimitSet t := by
  obtain ⟨C, _, hdist⟩ := G.grow_dist_le_of_mem_growLatticeL hy
  have hdiff0 : ∀ z : ℝ,
      Tendsto (fun j : ℕ => G.growSeq (z + y) j - G.growSeq z j) atTop (nhds 0) := by
    intro z
    have hQ0 : Tendsto (fun j : ℕ => C / (G.Q j : ℝ)) atTop (nhds 0) :=
      G.grow_Q_tendsto_atTop.const_div_atTop C
    refine tendsto_zero_iff_abs_tendsto_zero.mpr ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ0
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
    filter_upwards [eventually_ge_atTop G.J₀] with j hj
    have hAp : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
    have hrec : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
      exact_mod_cast (G.grow_Q_succ_gt_A_mul hj).le
    have hQ0' : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
    have hQ1' : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
    calc |G.growSeq (z + y) j - G.growSeq z j|
        ≤ |(G.A j : ℝ)| * distToNearestInt ((G.Q j : ℝ) * y) := G.abs_growSeq_add_sub_le z y j
      _ ≤ (G.A j : ℝ) * (C / (G.Q (j + 1) : ℝ)) := by
          rw [abs_of_pos hAp]
          exact mul_le_mul_of_nonneg_left (hdist j hj) hAp.le
      _ ≤ C / (G.Q j : ℝ) := by
          rw [mul_div_assoc', div_le_div_iff₀ hQ1' hQ0']
          nlinarith
  ext x
  simp only [Set.mem_preimage, growUnsignedExactLimitSet, Set.mem_ofPred_eq]
  constructor
  · intro hx
    have hsub := hx.sub (hdiff0 x)
    simpa using hsub
  · intro hx
    have hadd := hx.add (hdiff0 x)
    simpa using hadd

theorem growSignedExactLimitSet_coset_collapse (G : GrowingRecData) :
    (G.growSignedExactLimitSet 0 = G.growLatticeL) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∃ xPlus : ℝ,
        G.growSignedExactLimitSet (k : ℝ) = (fun z : ℝ => xPlus + z) '' G.growLatticeL ∧
        G.growSignedExactLimitSet (-(k : ℝ)) = (fun z : ℝ => -xPlus + z) '' G.growLatticeL ∧
        (G.growSignedExactLimitSet (k : ℝ)).Countable ∧
        (G.growSignedExactLimitSet (-(k : ℝ))).Countable ∧
        dimH (G.growSignedExactLimitSet (k : ℝ)) = 0 ∧
        dimH (G.growSignedExactLimitSet (-(k : ℝ))) = 0) ∧
    (∀ {t : ℝ}, (∀ z : ℤ, t ≠ (z : ℝ)) → G.growSignedExactLimitSet t = ∅) := by
  have hzero : G.growSignedExactLimitSet 0 = G.growLatticeL := by
    ext x
    simp only [growSignedExactLimitSet, Set.mem_ofPred_eq, ← G.growLambda_eq_zero_iff]
    constructor
    · intro hx
      have hseq0 : Tendsto (G.growSeq x) atTop (nhds 0) := by
        have habs : Tendsto (fun j : ℕ => |(G.A j : ℝ) * G.growEps x j|) atTop (nhds 0) := by
          simpa using hx.abs
        refine habs.congr' ?_
        filter_upwards [eventually_ge_atTop G.J₀] with j hj
        rw [G.growSeq_eq_of_ge x hj, abs_mul, abs_of_pos (G.grow_A_pos hj)]
      exact (ENNReal.tendsto_ofReal hseq0).limsup_eq.trans (by simp)
    · intro hx0
      have hne : G.growLambda x ≠ ⊤ := by simp [hx0]
      have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top hne
      have hdef : ∀ᶠ j : ℕ in atTop, G.growDefect x j = 0 :=
        ((G.growLambda_eq_zero_tfae x).out 2 3).mp hx0
      have hs := G.grow_signed_defect_approx x hε
      have hd0 : Tendsto (fun j : ℕ => (G.growDefect x j : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.congr' (hdef.mono fun j hj => by simp [hj])
      have hsub := hd0.sub hs
      simpa using hsub
  have hsub_lattice : ∀ {x y : ℝ} {d₀ : ℤ},
      Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps x j) atTop (nhds (d₀ : ℝ)) →
      Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps y j) atTop (nhds (d₀ : ℝ)) →
      x - y ∈ G.growLatticeL := by
    intro x y d₀ hx hy
    have hεx : Tendsto (G.growEps x) atTop (nhds 0) := by
      have hinv : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
        G.hA_tendsto.const_div_atTop 1
      have hM : Tendsto (fun j : ℕ => ((G.A j : ℝ) * G.growEps x j) * (1 / (G.A j : ℝ)))
          atTop (nhds 0) := by simpa using hx.mul hinv
      refine hM.congr' ?_
      filter_upwards [eventually_ge_atTop G.J₀] with j hj
      have hAp : (G.A j : ℝ) ≠ 0 := (G.grow_A_pos hj).ne'
      field_simp [hAp]
    have hεy : Tendsto (G.growEps y) atTop (nhds 0) := by
      have hinv : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
        G.hA_tendsto.const_div_atTop 1
      have hM : Tendsto (fun j : ℕ => ((G.A j : ℝ) * G.growEps y j) * (1 / (G.A j : ℝ)))
          atTop (nhds 0) := by simpa using hy.mul hinv
      refine hM.congr' ?_
      filter_upwards [eventually_ge_atTop G.J₀] with j hj
      have hAp : (G.A j : ℝ) ≠ 0 := (G.grow_A_pos hj).ne'
      field_simp [hAp]
    have hdx : ∀ᶠ j : ℕ in atTop, G.growDefect x j = d₀ :=
      FullSpectrumDiscrete.eventually_eq_int_of_tendsto
        (G.grow_signed_defect_approx x hεx |>.congr fun j => by ring) d₀ hx
    have hdy : ∀ᶠ j : ℕ in atTop, G.growDefect y j = d₀ :=
      FullSpectrumDiscrete.eventually_eq_int_of_tendsto
        (G.grow_signed_defect_approx y hεy |>.congr fun j => by ring) d₀ hy
    have hε_small : ∀ᶠ j : ℕ in atTop, |G.growEps x j| < 1 / 4 ∧ |G.growEps y j| < 1 / 4 :=
      ((tendsto_zero_iff_abs_tendsto_zero.mp hεx).eventually (Iio_mem_nhds (by norm_num))).and
        ((tendsto_zero_iff_abs_tendsto_zero.mp hεy).eventually (Iio_mem_nhds (by norm_num)))
    have hM_sub : ∀ᶠ j : ℕ in atTop,
        round ((G.Q j : ℝ) * (x - y)) =
          round ((G.Q j : ℝ) * x) - round ((G.Q j : ℝ) * y) := by
      filter_upwards [hε_small] with j ⟨hxj, hyj⟩
      have hdiff_lt : |(G.Q j : ℝ) * (x - y) -
          ((round ((G.Q j : ℝ) * x) - round ((G.Q j : ℝ) * y) : ℤ) : ℝ)| < 1 / 2 := by
        have heq : (G.Q j : ℝ) * (x - y) -
            ((round ((G.Q j : ℝ) * x) - round ((G.Q j : ℝ) * y) : ℤ) : ℝ) =
            G.growEps x j - G.growEps y j := by
          simp only [growEps]; push_cast; ring
        rw [heq]
        exact (abs_sub _ _).trans_lt (by linarith)
      exact round_eq_of_abs_sub_lt_half_grow hdiff_lt
    apply G.grow_mem_latticeL_of_eventually_defect_zero
    obtain ⟨J0, hJ0⟩ := eventually_atTop.mp (hdx.and (hdy.and hM_sub))
    refine eventually_atTop.mpr ⟨J0 + 1, fun j hj => ?_⟩
    have h1 := hJ0 (j + 1) (by omega)
    have h2 := hJ0 j (by omega)
    have h3 := hJ0 (j - 1) (by omega)
    dsimp [growDefect]
    rw [h1.2.2, h2.2.2, h3.2.2]
    have hd1 : G.growDefect x j = d₀ := h2.1
    have hd2 : G.growDefect y j = d₀ := h2.2.1
    dsimp [growDefect] at hd1 hd2
    linarith
  have hadd_signed : ∀ {x : ℝ} {t z : ℝ},
      x ∈ G.growSignedExactLimitSet t → z ∈ G.growLatticeL →
      x + z ∈ G.growSignedExactLimitSet t := by
    intro x t z hx hz
    obtain ⟨C, _, hdist⟩ := G.grow_dist_le_of_mem_growLatticeL hz
    have heps_sum : ∀ᶠ j : ℕ in atTop,
        |(G.A j : ℝ) * G.growEps (x + z) j - (G.A j : ℝ) * G.growEps x j| ≤
          C / (G.Q j : ℝ) := by
      have hεx : Tendsto (G.growEps x) atTop (nhds 0) := by
        have hinv : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
          G.hA_tendsto.const_div_atTop 1
        have hM : Tendsto (fun j : ℕ => ((G.A j : ℝ) * G.growEps x j) * (1 / (G.A j : ℝ)))
            atTop (nhds 0) := by simpa using hx.mul hinv
        refine hM.congr' ?_
        filter_upwards [eventually_ge_atTop G.J₀] with j hj
        have hAp : (G.A j : ℝ) ≠ 0 := (G.grow_A_pos hj).ne'
        field_simp [hAp]
      have hεz : Tendsto (G.growEps z) atTop (nhds 0) := by
        have hQ0 : Tendsto (fun j : ℕ => C / (G.Q (j + 1) : ℝ)) atTop (nhds 0) :=
          (G.grow_Q_tendsto_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop C
        refine tendsto_zero_iff_abs_tendsto_zero.mpr
          (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ0
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (eventually_atTop.mpr ⟨G.J₀, fun j hj => by
              rw [abs_growEps_eq_dist]; exact hdist j hj⟩))
      have hsmall : ∀ᶠ j : ℕ in atTop, |G.growEps x j| < 1 / 4 ∧ |G.growEps z j| < 1 / 4 :=
        ((tendsto_zero_iff_abs_tendsto_zero.mp hεx).eventually (Iio_mem_nhds (by norm_num))).and
          ((tendsto_zero_iff_abs_tendsto_zero.mp hεz).eventually (Iio_mem_nhds (by norm_num)))
      filter_upwards [hsmall, eventually_ge_atTop G.J₀] with j ⟨hxj, hzj⟩ hj
      have hr : round ((G.Q j : ℝ) * (x + z)) =
          round ((G.Q j : ℝ) * x) + round ((G.Q j : ℝ) * z) := by
        apply round_eq_of_abs_sub_lt_half_grow
        have heq : (G.Q j : ℝ) * (x + z) -
            ((round ((G.Q j : ℝ) * x) + round ((G.Q j : ℝ) * z) : ℤ) : ℝ) =
            G.growEps x j + G.growEps z j := by
          simp only [growEps]; push_cast; ring
        rw [heq]
        exact (abs_add_le _ _).trans_lt (by linarith)
      have heq_eps : G.growEps (x + z) j - G.growEps x j = G.growEps z j := by
        simp only [growEps, hr]; push_cast; ring
      have hAp : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
      have hrec : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
        exact_mod_cast (G.grow_Q_succ_gt_A_mul hj).le
      have hQ0' : (0 : ℝ) < (G.Q j : ℝ) := by exact_mod_cast G.hQ_pos j
      have hQ1' : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
      rw [← mul_sub, heq_eps, abs_mul, abs_of_pos hAp, abs_growEps_eq_dist]
      calc (G.A j : ℝ) * distToNearestInt ((G.Q j : ℝ) * z)
          ≤ (G.A j : ℝ) * (C / (G.Q (j + 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hdist j hj) hAp.le
        _ ≤ C / (G.Q j : ℝ) := by
            rw [mul_div_assoc', div_le_div_iff₀ hQ1' hQ0']
            nlinarith
    have hdiff0 : Tendsto (fun j : ℕ =>
        (G.A j : ℝ) * G.growEps (x + z) j - (G.A j : ℝ) * G.growEps x j) atTop (nhds 0) := by
      have hQ0 : Tendsto (fun j : ℕ => C / (G.Q j : ℝ)) atTop (nhds 0) :=
        G.grow_Q_tendsto_atTop.const_div_atTop C
      exact tendsto_zero_iff_abs_tendsto_zero.mpr
        (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hQ0
          (Filter.Eventually.of_forall fun _ => abs_nonneg _) heps_sum)
    have hsum := hx.add hdiff0
    simpa [growSignedExactLimitSet] using hsum
  have hcoset : ∀ k : ℕ, 1 ≤ k → ∃ xPlus : ℝ,
      G.growSignedExactLimitSet (k : ℝ) = (fun z : ℝ => xPlus + z) '' G.growLatticeL ∧
      G.growSignedExactLimitSet (-(k : ℝ)) = (fun z : ℝ => -xPlus + z) '' G.growLatticeL ∧
      (G.growSignedExactLimitSet (k : ℝ)).Countable ∧
      (G.growSignedExactLimitSet (-(k : ℝ))).Countable ∧
      dimH (G.growSignedExactLimitSet (k : ℝ)) = 0 ∧
      dimH (G.growSignedExactLimitSet (-(k : ℝ))) = 0 := by
    intro k hk
    obtain ⟨xPlus, hxP, _, _⟩ := G.grow_telescoping_const_defect (k : ℤ)
    have hnegP : -xPlus ∈ G.growSignedExactLimitSet (-(k : ℝ)) := by
      have hε_x : Tendsto (G.growEps xPlus) atTop (nhds 0) := by
        have hinv : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
          G.hA_tendsto.const_div_atTop 1
        have hM : Tendsto (fun j : ℕ => ((G.A j : ℝ) * G.growEps xPlus j) * (1 / (G.A j : ℝ)))
            atTop (nhds 0) := by simpa using hxP.mul hinv
        refine hM.congr' ?_
        filter_upwards [eventually_ge_atTop G.J₀] with j hj
        have hAp : (G.A j : ℝ) ≠ 0 := (G.grow_A_pos hj).ne'
        field_simp [hAp]
      have hsmall : ∀ᶠ j : ℕ in atTop, |G.growEps xPlus j| < 1 / 2 :=
        (tendsto_zero_iff_abs_tendsto_zero.mp hε_x).eventually (Iio_mem_nhds (by norm_num))
      have hx_neg : Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps (-xPlus) j)
          atTop (nhds (-(k : ℝ))) := by
        refine hxP.neg.congr' ?_
        filter_upwards [hsmall] with j hj
        have hr : round ((G.Q j : ℝ) * (-xPlus)) = -round ((G.Q j : ℝ) * xPlus) := by
          apply round_eq_of_abs_sub_lt_half_grow
          have heq : (G.Q j : ℝ) * (-xPlus) - ((-round ((G.Q j : ℝ) * xPlus) : ℤ) : ℝ) =
              -G.growEps xPlus j := by
            simp only [growEps]; push_cast; ring
          rw [heq, abs_neg]; exact hj
        simp only [growEps, hr]; push_cast; ring
      exact hx_neg
    have hpos_eq : G.growSignedExactLimitSet (k : ℝ) =
        (fun z : ℝ => xPlus + z) '' G.growLatticeL := by
      ext y
      constructor
      · intro hy
        refine ⟨y - xPlus, hsub_lattice (d₀ := (k : ℤ)) hy hxP, by ring⟩
      · rintro ⟨z, hz, rfl⟩
        exact hadd_signed hxP hz
    have hneg_eq : G.growSignedExactLimitSet (-(k : ℝ)) =
        (fun z : ℝ => -xPlus + z) '' G.growLatticeL := by
      have hnegP' : Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps (-xPlus) j)
          atTop (nhds ((-(k : ℤ) : ℤ) : ℝ)) := by push_cast; exact hnegP
      ext y
      constructor
      · intro hy
        have hy' : Tendsto (fun j : ℕ => (G.A j : ℝ) * G.growEps y j)
            atTop (nhds ((-(k : ℤ) : ℤ) : ℝ)) := by push_cast; exact hy
        refine ⟨y - (-xPlus), hsub_lattice (d₀ := -(k : ℤ)) hy' hnegP', by ring⟩
      · rintro ⟨z, hz, rfl⟩
        exact hadd_signed hnegP hz
    have hc_pos : (G.growSignedExactLimitSet (k : ℝ)).Countable := by
      rw [hpos_eq]; exact G.growLatticeL_countable.image _
    have hc_neg : (G.growSignedExactLimitSet (-(k : ℝ))).Countable := by
      rw [hneg_eq]; exact G.growLatticeL_countable.image _
    exact ⟨xPlus, hpos_eq, hneg_eq, hc_pos, hc_neg, hc_pos.dimH_zero, hc_neg.dimH_zero⟩
  have hempty : ∀ {t : ℝ}, (∀ z : ℤ, t ≠ (z : ℝ)) → G.growSignedExactLimitSet t = ∅ := by
    intro t ht
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hε : Tendsto (G.growEps x) atTop (nhds 0) := by
      have hinv : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
        G.hA_tendsto.const_div_atTop 1
      have hM : Tendsto (fun j : ℕ => ((G.A j : ℝ) * G.growEps x j) * (1 / (G.A j : ℝ)))
          atTop (nhds 0) := by simpa using hx.mul hinv
      refine hM.congr' ?_
      filter_upwards [eventually_ge_atTop G.J₀] with j hj
      have hAp : (G.A j : ℝ) ≠ 0 := (G.grow_A_pos hj).ne'
      field_simp [hAp]
    have hdef : Tendsto (fun j : ℕ => (G.growDefect x j : ℝ)) atTop (nhds t) := by
      have h1 := hx.add (G.grow_signed_defect_approx x hε)
      simpa using h1
    let z : ℤ := round t
    have hlt_dist : |t - (z : ℝ)| ≤ 1 / 2 := abs_sub_round t
    by_cases hhalf : |t - (z : ℝ)| < 1 / 2
    · have ht_ne : t ≠ (z : ℝ) := ht z
      have hgap : 0 < |t - (z : ℝ)| := abs_sub_pos.mpr ht_ne
      have hev := hdef.eventually (Metric.ball_mem_nhds t hgap)
      obtain ⟨j, hj⟩ := hev.exists
      rw [Real.dist_eq] at hj
      have hround_eq : round t = G.growDefect x j :=
        round_eq_of_abs_sub_lt_half_grow (by
          calc |t - (G.growDefect x j : ℝ)| = |(G.growDefect x j : ℝ) - t| := abs_sub_comm _ _
            _ < |t - (z : ℝ)| := hj
            _ < 1 / 2 := hhalf)
      have hEq : z = G.growDefect x j := hround_eq
      rw [← hEq, abs_sub_comm] at hj
      exact lt_irrefl _ hj
    · have hhalf_eq : |t - (z : ℝ)| = 1 / 2 := le_antisymm hlt_dist (not_lt.mp hhalf)
      have hdelta : ∀ w : ℤ, (1 / 2 : ℝ) ≤ |t - (w : ℝ)| := fun w => by
        rcases eq_or_lt_of_le (abs_sub_round t) with h | h
        · calc (1 / 2 : ℝ) = |t - (round t : ℝ)| := h.symm
            _ ≤ |t - (w : ℝ)| := distToNearestInt_le t w
        · exfalso; linarith
      have hev := hdef.eventually (Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1 / 2))
      obtain ⟨j, hj⟩ := hev.exists
      rw [Real.dist_eq, abs_sub_comm] at hj
      exact (not_lt_of_ge (hdelta (G.growDefect x j))) hj
  exact ⟨hzero, hcoset, hempty⟩

/-! ### Part 6: Universal Critical Gauges, Cantor Trees, and 3-Way Splitting on `ℝ` and `𝕋` -/

lemma grow_Q_div_Q_succ_tendsto_zero (G : GrowingRecData) :
    Tendsto (fun j : ℕ => (G.Q j : ℝ) / (G.Q (j + 1) : ℝ)) atTop (nhds 0) := by
  have hlimA : Tendsto (fun j : ℕ => 1 / (G.A j : ℝ)) atTop (nhds 0) :=
    G.hA_tendsto.const_div_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimA
    (Filter.Eventually.of_forall fun j => by
      have h0 : (0 : ℝ) ≤ (G.Q j : ℝ) := by exact_mod_cast (G.hQ_pos j).le
      have h1 : (0 : ℝ) ≤ (G.Q (j + 1) : ℝ) := by exact_mod_cast (G.hQ_pos (j + 1)).le
      exact div_nonneg h0 h1) ?_
  filter_upwards [eventually_ge_atTop G.J₀] with j hj
  have hrec : (G.A j : ℝ) * (G.Q j : ℝ) ≤ (G.Q (j + 1) : ℝ) := by
    exact_mod_cast (G.grow_Q_succ_gt_A_mul hj).le
  have hA : (0 : ℝ) < (G.A j : ℝ) := G.grow_A_pos hj
  have hQ1 : (0 : ℝ) < (G.Q (j + 1) : ℝ) := by exact_mod_cast G.hQ_pos (j + 1)
  rw [div_le_div_iff₀ hQ1 hA]
  nlinarith

lemma grow_unsigned_exact_limit_iff_defect_binary (G : GrowingRecData) (x : ℝ) (k : ℕ) :
    x ∈ G.growUnsignedExactLimitSet (k : ℝ) ↔
      Tendsto (G.growEps x) atTop (nhds 0) ∧
      ∀ᶠ j : ℕ in atTop, G.growDefect x j = (k : ℤ) ∨ G.growDefect x j = -(k : ℤ) := by
  constructor
  · intro hx
    have hlam_eq : G.growLambda x = (k : ℝ≥0∞) := by
      have h1 := (ENNReal.tendsto_ofReal hx).limsup_eq
      rwa [ENNReal.ofReal_natCast] at h1
    have hne : G.growLambda x ≠ ⊤ := by simp [hlam_eq]
    have hε := G.grow_eps_tendsto_zero_of_lambda_ne_top hne
    refine ⟨hε, ?_⟩
    have happrox := G.grow_abs_defect_approx x hε
    have habs_lim : Tendsto (fun j : ℕ => |(G.growDefect x j : ℝ)|) atTop (nhds (k : ℝ)) := by
      have h1 := happrox.add hx
      simpa using h1
    have hball := habs_lim.eventually (Metric.ball_mem_nhds (k : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hball] with j hj
    rw [Real.dist_eq] at hj
    have hZ : abs (abs (G.growDefect x j) - (k : ℤ)) = 0 := by
      have hlt1 : ((abs (abs (G.growDefect x j) - (k : ℤ)) : ℤ) : ℝ) < (1 : ℤ) := by
        rw [Int.cast_abs, Int.cast_sub, Int.cast_abs, Int.cast_natCast, Int.cast_one]
        linarith [(abs_lt.mp hj).1, (abs_lt.mp hj).2]
      have hltZ := Int.cast_lt.mp hlt1
      have hnn : 0 ≤ abs (abs (G.growDefect x j) - (k : ℤ)) := abs_nonneg _
      omega
    have heq : |G.growDefect x j| = (k : ℤ) := sub_eq_zero.mp (abs_eq_zero.mp hZ)
    exact abs_eq (Int.natCast_nonneg k) |>.mp heq
  · rintro ⟨hε, hbin⟩
    have happrox := G.grow_abs_defect_approx x hε
    have habs_lim : Tendsto (fun j : ℕ => |(G.growDefect x j : ℝ)|) atTop (nhds (k : ℝ)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hbin] with j hj
      rcases hj with h | h <;> simp [h]
    have hsub := habs_lim.sub happrox
    simpa [growUnsignedExactLimitSet] using hsub

lemma growExactLevel_add_growLatticeL (G : GrowingRecData) (k : ℕ)
    {y : ℝ} (hy : y ∈ G.growLatticeL) :
    (fun x : ℝ => x + y) ⁻¹' G.growExactLevel k = G.growExactLevel k := by
  ext x
  simp only [Set.mem_preimage, growExactLevel, Set.mem_ofPred_eq,
    G.growLambda_add_mem_growLatticeL x hy]

lemma growLevelSet_add_growLatticeL (G : GrowingRecData) (t : ℝ≥0∞)
    {y : ℝ} (hy : y ∈ G.growLatticeL) :
    (fun x : ℝ => x + y) ⁻¹' G.growLevelSet t = G.growLevelSet t := by
  ext x
  simp only [Set.mem_preimage, growLevelSet, Set.mem_ofPred_eq,
    G.growLambda_add_mem_growLatticeL x hy]

/-! #### Part 6.1: Piecewise-linear Continuous Critical & Binary Gauges -/

def growInvQ (G : GrowingRecData) (n : ℕ) : ℝ := 1 / (G.Q n : ℝ)

lemma growInvQ_pos (G : GrowingRecData) (n : ℕ) : 0 < G.growInvQ n := by
  unfold growInvQ
  have hQ : (0 : ℝ) < (G.Q n : ℝ) := by exact_mod_cast G.hQ_pos n
  positivity

lemma growInvQ_succ_lt (G : GrowingRecData) {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growInvQ (n + 1) < G.growInvQ n := by
  unfold growInvQ
  have hQ : (0 : ℝ) < (G.Q n : ℝ) := by exact_mod_cast G.hQ_pos n
  have hlt : (G.Q n : ℝ) < (G.Q (n + 1) : ℝ) := by exact_mod_cast G.grow_Q_lt_succ hn
  exact one_div_lt_one_div_of_lt hQ hlt

lemma growInvQ_antitoneOn (G : GrowingRecData) :
    AntitoneOn G.growInvQ (Set.Ici G.J₀) := by
  intro m hm n hn hmn
  unfold growInvQ
  have hQpos : (0 : ℝ) < (G.Q m : ℝ) := by exact_mod_cast G.hQ_pos m
  have hQle : (G.Q m : ℝ) ≤ (G.Q n : ℝ) := by
    exact_mod_cast G.grow_Q_monoOn hm hmn
  exact one_div_le_one_div_of_le hQpos hQle

lemma growInvQ_le_J₀ (G : GrowingRecData) {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growInvQ n ≤ G.growInvQ G.J₀ :=
  G.growInvQ_antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hn) hn

lemma tendsto_growInvQ (G : GrowingRecData) : Tendsto G.growInvQ atTop (nhds 0) :=
  G.grow_Q_tendsto_atTop.const_div_atTop 1

def growSegVal (G : GrowingRecData) (b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  b ^ (-((n + 1 : ℕ) : ℤ)) +
    ((t - G.growInvQ (n + 1)) / (G.growInvQ n - G.growInvQ (n + 1))) *
      (b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)))

lemma growSegVal_at_left (G : GrowingRecData) (b : ℝ) (n : ℕ) :
    G.growSegVal b n (G.growInvQ (n + 1)) = b ^ (-((n + 1 : ℕ) : ℤ)) := by
  simp [growSegVal]

lemma growSegVal_at_right (G : GrowingRecData) (b : ℝ) {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growSegVal b n (G.growInvQ n) = b ^ (-(n : ℤ)) := by
  have hne : G.growInvQ n - G.growInvQ (n + 1) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (G.growInvQ_succ_lt hn))
  simp [growSegVal, hne]

lemma growSegVal_continuous (G : GrowingRecData) (b : ℝ) (n : ℕ) :
    Continuous (G.growSegVal b n) := by
  unfold growSegVal
  fun_prop

lemma growSegVal_mono (G : GrowingRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : G.J₀ ≤ n) :
    Monotone (G.growSegVal b n) := by
  intro s t hst
  have hq : 0 < G.growInvQ n - G.growInvQ (n + 1) := sub_pos.mpr (G.growInvQ_succ_lt hn)
  have hpow : b ^ (-((n + 1 : ℕ) : ℤ)) ≤ b ^ (-(n : ℤ)) := by
    rw [zpow_le_zpow_iff_right₀ hb]; omega
  have hdiff : 0 ≤ b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)) := sub_nonneg.mpr hpow
  unfold growSegVal
  gcongr

lemma growSegVal_nonneg (G : GrowingRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : G.J₀ ≤ n)
    {t : ℝ} (ht : G.growInvQ (n + 1) ≤ t) : 0 ≤ G.growSegVal b n t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have h1 : 0 ≤ b ^ (-((n + 1 : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb0) _
  have h2 := G.growSegVal_mono hb hn ht
  rw [G.growSegVal_at_left] at h2
  exact le_trans h1 h2

lemma growSegVal_le_right (G : GrowingRecData) {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : G.J₀ ≤ n)
    {t : ℝ} (ht : t ≤ G.growInvQ n) : G.growSegVal b n t ≤ b ^ (-(n : ℤ)) := by
  have h := G.growSegVal_mono hb hn ht
  rwa [G.growSegVal_at_right b hn] at h

def growInterpIdx (G : GrowingRecData) (t : ℝ) : ℕ :=
  if h : 0 < t ∧ t < G.growInvQ G.J₀ then
    Nat.find (show ∃ n : ℕ, G.J₀ ≤ n ∧ G.growInvQ (n + 1) ≤ t by
      have hev := G.tendsto_growInvQ.eventually (Iio_mem_nhds h.1)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine ⟨max G.J₀ N, le_max_left _ _, ?_⟩
      have h1 : G.growInvQ (max G.J₀ N + 1) ≤ G.growInvQ (max G.J₀ N) :=
        le_of_lt (G.growInvQ_succ_lt (le_max_left _ _))
      have h2 : G.growInvQ (max G.J₀ N) < t := hN (max G.J₀ N) (le_max_right _ _)
      exact le_trans h1 (le_of_lt h2))
  else G.J₀

lemma growInterpIdx_spec (G : GrowingRecData) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < G.growInvQ G.J₀) :
    G.J₀ ≤ G.growInterpIdx t ∧
    G.growInvQ (G.growInterpIdx t + 1) ≤ t ∧
    t < G.growInvQ (G.growInterpIdx t) := by
  have h : 0 < t ∧ t < G.growInvQ G.J₀ := ⟨ht0, ht1⟩
  have hex : ∃ n : ℕ, G.J₀ ≤ n ∧ G.growInvQ (n + 1) ≤ t := by
    have hev := G.tendsto_growInvQ.eventually (Iio_mem_nhds h.1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max G.J₀ N, le_max_left _ _, ?_⟩
    have h1 : G.growInvQ (max G.J₀ N + 1) ≤ G.growInvQ (max G.J₀ N) :=
      le_of_lt (G.growInvQ_succ_lt (le_max_left _ _))
    have h2 : G.growInvQ (max G.J₀ N) < t := hN (max G.J₀ N) (le_max_right _ _)
    exact le_trans h1 (le_of_lt h2)
  have hdef : G.growInterpIdx t = Nat.find hex := by simp [growInterpIdx, h]
  have hspec := Nat.find_spec hex
  rw [← hdef] at hspec
  refine ⟨hspec.1, hspec.2, ?_⟩
  by_cases hnJ : G.growInterpIdx t = G.J₀
  · rw [hnJ]; exact ht1
  · have hm1 : G.J₀ ≤ G.growInterpIdx t - 1 := by omega
    have hlt : G.growInterpIdx t - 1 < G.growInterpIdx t := by omega
    have hmin := Nat.find_min hex (by rw [← hdef]; exact hlt)
    push Not at hmin
    have hadd : G.growInterpIdx t - 1 + 1 = G.growInterpIdx t := by omega
    rw [hadd] at hmin
    exact hmin hm1

lemma growInterpIdx_eq_of_mem_Ico (G : GrowingRecData) {t : ℝ} {n : ℕ} (hn : G.J₀ ≤ n)
    (hlo : G.growInvQ (n + 1) ≤ t) (hhi : t < G.growInvQ n) :
    G.growInterpIdx t = n := by
  have ht0 : 0 < t := lt_of_lt_of_le (G.growInvQ_pos (n + 1)) hlo
  have ht1 : t < G.growInvQ G.J₀ := lt_of_lt_of_le hhi (G.growInvQ_le_J₀ hn)
  obtain ⟨hm1, hmlo, hmhi⟩ := G.growInterpIdx_spec ht0 ht1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : G.growInterpIdx t + 1 ≤ n := by omega
    have hq : G.growInvQ n ≤ G.growInvQ (G.growInterpIdx t + 1) :=
      G.growInvQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hn) hle
    linarith
  · have hle : n + 1 ≤ G.growInterpIdx t := by omega
    have hq : G.growInvQ (G.growInterpIdx t) ≤ G.growInvQ (n + 1) :=
      G.growInvQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hm1) hle
    linarith

lemma growInterpIdx_antitone (G : GrowingRecData) {s t : ℝ} (hs0 : 0 < s)
    (ht1 : t < G.growInvQ G.J₀) (hst : s ≤ t) :
    G.growInterpIdx t ≤ G.growInterpIdx s := by
  have hs1 : s < G.growInvQ G.J₀ := lt_of_le_of_lt hst ht1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  obtain ⟨_, hnlo, _⟩ := G.growInterpIdx_spec hs0 hs1
  obtain ⟨hm1, _, hmhi⟩ := G.growInterpIdx_spec ht0 ht1
  by_contra hlt
  push Not at hlt
  have hle : G.growInterpIdx s + 1 ≤ G.growInterpIdx t := by omega
  have hq : G.growInvQ (G.growInterpIdx t) ≤ G.growInvQ (G.growInterpIdx s + 1) :=
    G.growInvQ_antitoneOn
      (Set.mem_Ici.mpr (by have := (G.growInterpIdx_spec hs0 hs1).1; omega))
      (Set.mem_Ici.mpr hm1) hle
  linarith

def growInterpGaugeReal (G : GrowingRecData) (b : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if G.growInvQ G.J₀ ≤ t then b ^ (-(G.J₀ : ℤ))
  else G.growSegVal b (G.growInterpIdx t) t

lemma growInterpGaugeReal_le_zero (G : GrowingRecData) (b : ℝ) {t : ℝ} (ht : t ≤ 0) :
    G.growInterpGaugeReal b t = 0 := by simp [growInterpGaugeReal, ht]

lemma growInterpGaugeReal_zero (G : GrowingRecData) (b : ℝ) :
    G.growInterpGaugeReal b 0 = 0 := G.growInterpGaugeReal_le_zero b le_rfl

lemma growInterpGaugeReal_ge_J₀ (G : GrowingRecData) (b : ℝ) {t : ℝ}
    (ht : G.growInvQ G.J₀ ≤ t) :
    G.growInterpGaugeReal b t = b ^ (-(G.J₀ : ℤ)) := by
  have hnot : ¬ t ≤ 0 := not_le.mpr (lt_of_lt_of_le (G.growInvQ_pos G.J₀) ht)
  simp [growInterpGaugeReal, hnot, ht]

lemma growInterpGaugeReal_eq_segVal (G : GrowingRecData) {b : ℝ} (_hb : 1 < b)
    {n : ℕ} (hn : G.J₀ ≤ n) {t : ℝ} (hlo : G.growInvQ (n + 1) ≤ t)
    (hhi : t ≤ G.growInvQ n) :
    G.growInterpGaugeReal b t = G.growSegVal b n t := by
  have ht0 : 0 < t := lt_of_lt_of_le (G.growInvQ_pos (n + 1)) hlo
  have hnot0 : ¬ t ≤ 0 := not_le.mpr ht0
  rcases eq_or_lt_of_le hhi with rfl | ht_lt
  · rw [G.growSegVal_at_right b hn]
    by_cases hnJ : n = G.J₀
    · subst hnJ; exact G.growInterpGaugeReal_ge_J₀ b le_rfl
    · have hn' : G.J₀ ≤ n - 1 := by omega
      have hadd : n - 1 + 1 = n := by omega
      have hlo' : G.growInvQ (n - 1 + 1) ≤ G.growInvQ n := by rw [hadd]
      have hhi' : G.growInvQ n < G.growInvQ (n - 1) := by
        simpa [hadd] using G.growInvQ_succ_lt hn'
      have ht1 : ¬ G.growInvQ G.J₀ ≤ G.growInvQ n := by
        have := lt_of_lt_of_le hhi' (G.growInvQ_le_J₀ hn'); linarith
      simp only [growInterpGaugeReal, hnot0, ↓reduceIte, ht1]
      rw [G.growInterpIdx_eq_of_mem_Ico hn' hlo' hhi']
      conv_lhs => rhs; rw [← hadd]
      rw [G.growSegVal_at_left, hadd]
  · have ht1 : ¬ G.growInvQ G.J₀ ≤ t := by
      have := lt_of_lt_of_le ht_lt (G.growInvQ_le_J₀ hn); linarith
    simp only [growInterpGaugeReal, hnot0, ↓reduceIte, ht1]
    rw [G.growInterpIdx_eq_of_mem_Ico hn hlo ht_lt]

lemma growInterpGaugeReal_at_invQ (G : GrowingRecData) {b : ℝ} (hb : 1 < b)
    {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growInterpGaugeReal b (G.growInvQ n) = b ^ (-(n : ℤ)) := by
  rw [G.growInterpGaugeReal_eq_segVal hb hn (le_of_lt (G.growInvQ_succ_lt hn)) le_rfl,
    G.growSegVal_at_right b hn]

lemma growInterpGaugeReal_nonneg (G : GrowingRecData) {b : ℝ} (hb : 1 < b) (t : ℝ) :
    0 ≤ G.growInterpGaugeReal b t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  by_cases ht0 : t ≤ 0
  · rw [G.growInterpGaugeReal_le_zero b ht0]
  · by_cases ht1 : G.growInvQ G.J₀ ≤ t
    · rw [G.growInterpGaugeReal_ge_J₀ b ht1]; positivity
    · have ht0' : 0 < t := lt_of_not_ge ht0
      have ht1' : t < G.growInvQ G.J₀ := lt_of_not_ge ht1
      obtain ⟨hn1, hnlo, _⟩ := G.growInterpIdx_spec ht0' ht1'
      simp only [growInterpGaugeReal, ht0, ↓reduceIte, ht1]
      exact G.growSegVal_nonneg hb hn1 hnlo

lemma growInterpGaugeReal_mono (G : GrowingRecData) {b : ℝ} (hb : 1 < b) :
    Monotone (G.growInterpGaugeReal b) := by
  intro s t hst
  by_cases hs0 : s ≤ 0
  · rw [G.growInterpGaugeReal_le_zero b hs0]; exact G.growInterpGaugeReal_nonneg hb t
  · have hs0' : 0 < s := lt_of_not_ge hs0
    have ht0' : 0 < t := lt_of_lt_of_le hs0' hst
    have ht0 : ¬ t ≤ 0 := not_le.mpr ht0'
    by_cases ht1 : G.growInvQ G.J₀ ≤ t
    · rw [G.growInterpGaugeReal_ge_J₀ b ht1]
      by_cases hs1 : G.growInvQ G.J₀ ≤ s
      · rw [G.growInterpGaugeReal_ge_J₀ b hs1]
      · have hs1' : s < G.growInvQ G.J₀ := lt_of_not_ge hs1
        obtain ⟨hn1, _, hnhi⟩ := G.growInterpIdx_spec hs0' hs1'
        simp only [growInterpGaugeReal, hs0, ↓reduceIte, hs1]
        have h1 := G.growSegVal_le_right hb hn1 (le_of_lt hnhi)
        have h2 : b ^ (-(G.growInterpIdx s : ℤ)) ≤ b ^ (-(G.J₀ : ℤ)) := by
          rw [zpow_le_zpow_iff_right₀ hb]; omega
        exact le_trans h1 h2
    · have ht1' : t < G.growInvQ G.J₀ := lt_of_not_ge ht1
      have hs1' : s < G.growInvQ G.J₀ := lt_of_le_of_lt hst ht1'
      have hs1 : ¬ G.growInvQ G.J₀ ≤ s := not_le.mpr hs1'
      obtain ⟨hn1, _, hnhi⟩ := G.growInterpIdx_spec hs0' hs1'
      obtain ⟨hm1, hmlo, _⟩ := G.growInterpIdx_spec ht0' ht1'
      have hidx : G.growInterpIdx t ≤ G.growInterpIdx s := G.growInterpIdx_antitone hs0' ht1' hst
      simp only [growInterpGaugeReal, hs0, ht0, ↓reduceIte, hs1, ht1]
      rcases eq_or_lt_of_le hidx with heq | hlt
      · rw [heq]; exact G.growSegVal_mono hb hn1 hst
      · have h1 := G.growSegVal_le_right hb hn1 (le_of_lt hnhi)
        have h2 := G.growSegVal_mono hb hm1 hmlo
        rw [G.growSegVal_at_left] at h2
        have hpow : b ^ (-(G.growInterpIdx s : ℤ)) ≤
            b ^ (-((G.growInterpIdx t + 1 : ℕ) : ℤ)) := by
          rw [zpow_le_zpow_iff_right₀ hb]; omega
        exact le_trans h1 (le_trans hpow h2)

lemma growInterpGaugeReal_continuous (G : GrowingRecData) {b : ℝ} (hb : 1 < b) :
    Continuous (G.growInterpGaugeReal b) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · have hev : ∀ᶠ y in nhds t, (0 : ℝ) = G.growInterpGaugeReal b y := by
      filter_upwards [Iio_mem_nhds ht_neg] with y hy
      exact (G.growInterpGaugeReal_le_zero b (le_of_lt hy)).symm
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr hev
  · rw [Metric.continuousAt_iff]
    intro ε hε
    have hb_inv : 0 ≤ b⁻¹ := by positivity
    have hb_lt1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
    have hpow0 : Tendsto (fun n : ℕ => b⁻¹ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hb_inv hb_lt1
    obtain ⟨N, hN⟩ := (hpow0.eventually (Iio_mem_nhds hε)).exists
    set n := max G.J₀ N
    have hn1 : G.J₀ ≤ n := le_max_left _ _
    have hNle : N ≤ n := le_max_right _ _
    have hbn : b ^ (-(n : ℤ)) < ε := by
      have h1 : b ^ (-(n : ℤ)) = b⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
      have h2 : b⁻¹ ^ n ≤ b⁻¹ ^ N := pow_le_pow_of_le_one hb_inv (le_of_lt hb_lt1) hNle
      linarith
    refine ⟨G.growInvQ n, G.growInvQ_pos n, fun {y} hy => ?_⟩
    rw [G.growInterpGaugeReal_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg (G.growInterpGaugeReal_nonneg hb y)]
    have hy_lt : y < G.growInvQ n := by
      rw [Real.dist_eq, sub_zero] at hy; exact (abs_lt.mp hy).2
    calc G.growInterpGaugeReal b y
        ≤ G.growInterpGaugeReal b (G.growInvQ n) := G.growInterpGaugeReal_mono hb (le_of_lt hy_lt)
      _ = b ^ (-(n : ℤ)) := G.growInterpGaugeReal_at_invQ hb hn1
      _ < ε := hbn
  · rcases lt_trichotomy t (G.growInvQ G.J₀) with ht_lt1 | ht_eq | ht_gt1
    · set n := G.growInterpIdx t
      obtain ⟨hn1, hnlo, hnhi⟩ := G.growInterpIdx_spec ht_pos ht_lt1
      rcases eq_or_lt_of_le hnlo with h_eq | h_gt
      · have hleft : ContinuousWithinAt (G.growInterpGaugeReal b) (Iic t) t := by
          have hmem : Ioc (G.growInvQ (n + 2)) t ∈ nhdsWithin t (Iic t) := by
            rw [← Ioi_inter_Iic]
            exact Filter.inter_mem
              (nhdsWithin_le_nhds (Ioi_mem_nhds
                (by rw [← h_eq]; exact G.growInvQ_succ_lt (by omega))))
              self_mem_nhdsWithin
          have heq : ∀ᶠ y in nhdsWithin t (Iic t),
              G.growInterpGaugeReal b y = G.growSegVal b (n + 1) y := by
            filter_upwards [hmem] with y hy
            exact G.growInterpGaugeReal_eq_segVal hb (by omega) (le_of_lt hy.1)
              (by rw [h_eq]; exact hy.2)
          have hfx : G.growInterpGaugeReal b t = G.growSegVal b (n + 1) t :=
            G.growInterpGaugeReal_eq_segVal hb (by omega)
              (le_of_lt (by rw [← h_eq]; exact G.growInvQ_succ_lt (by omega))) (by rw [h_eq])
          exact (G.growSegVal_continuous b (n + 1)).continuousWithinAt.congr_of_eventuallyEq
            heq hfx
        have hright : ContinuousWithinAt (G.growInterpGaugeReal b) (Ici t) t := by
          have hmem : Ico t (G.growInvQ n) ∈ nhdsWithin t (Ici t) := by
            rw [← Ici_inter_Iio]
            exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hnhi))
          have heq : ∀ᶠ y in nhdsWithin t (Ici t),
              G.growInterpGaugeReal b y = G.growSegVal b n y := by
            filter_upwards [hmem] with y hy
            exact G.growInterpGaugeReal_eq_segVal hb hn1 (by rw [h_eq]; exact hy.1)
              (le_of_lt hy.2)
          have hfx : G.growInterpGaugeReal b t = G.growSegVal b n t :=
            G.growInterpGaugeReal_eq_segVal hb hn1 hnlo (le_of_lt hnhi)
          exact (G.growSegVal_continuous b n).continuousWithinAt.congr_of_eventuallyEq heq hfx
        have hunion := hleft.union hright
        rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
      · have hev : ∀ᶠ y in nhds t, G.growSegVal b n y = G.growInterpGaugeReal b y := by
          filter_upwards [Ioo_mem_nhds h_gt hnhi] with y hy
          exact (G.growInterpGaugeReal_eq_segVal hb hn1 (le_of_lt hy.1) (le_of_lt hy.2)).symm
        exact (G.growSegVal_continuous b n).continuousAt.congr hev
    · rw [ht_eq]
      have hleft : ContinuousWithinAt (G.growInterpGaugeReal b) (Iic (G.growInvQ G.J₀))
          (G.growInvQ G.J₀) := by
        have hmem : Ioc (G.growInvQ (G.J₀ + 1)) (G.growInvQ G.J₀) ∈
            nhdsWithin (G.growInvQ G.J₀) (Iic (G.growInvQ G.J₀)) := by
          rw [← Ioi_inter_Iic]
          exact Filter.inter_mem
            (nhdsWithin_le_nhds (Ioi_mem_nhds (G.growInvQ_succ_lt le_rfl)))
            self_mem_nhdsWithin
        have heq : ∀ᶠ y in nhdsWithin (G.growInvQ G.J₀) (Iic (G.growInvQ G.J₀)),
            G.growInterpGaugeReal b y = G.growSegVal b G.J₀ y := by
          filter_upwards [hmem] with y hy
          exact G.growInterpGaugeReal_eq_segVal hb le_rfl (le_of_lt hy.1) hy.2
        have hfx : G.growInterpGaugeReal b (G.growInvQ G.J₀) =
            G.growSegVal b G.J₀ (G.growInvQ G.J₀) :=
          G.growInterpGaugeReal_eq_segVal hb le_rfl
            (le_of_lt (G.growInvQ_succ_lt le_rfl)) le_rfl
        exact (G.growSegVal_continuous b G.J₀).continuousWithinAt.congr_of_eventuallyEq heq hfx
      have hright : ContinuousWithinAt (G.growInterpGaugeReal b) (Ici (G.growInvQ G.J₀))
          (G.growInvQ G.J₀) := by
        have heq : ∀ᶠ y in nhdsWithin (G.growInvQ G.J₀) (Ici (G.growInvQ G.J₀)),
            G.growInterpGaugeReal b y = b ^ (-(G.J₀ : ℤ)) := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact G.growInterpGaugeReal_ge_J₀ b hy
        exact continuousWithinAt_const.congr_of_eventuallyEq heq
          (G.growInterpGaugeReal_ge_J₀ b le_rfl)
      have hunion := hleft.union hright
      rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
    · have hev : ∀ᶠ y in nhds t, b ^ (-(G.J₀ : ℤ)) = G.growInterpGaugeReal b y := by
        filter_upwards [Ioi_mem_nhds ht_gt1] with y hy
        exact (G.growInterpGaugeReal_ge_J₀ b (le_of_lt hy)).symm
      exact (continuousAt_const : ContinuousAt (fun _ : ℝ => b ^ (-(G.J₀ : ℤ))) t).congr hev

def growInterpGauge (G : GrowingRecData) (b : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if ENNReal.ofReal (G.growInvQ G.J₀) ≤ x then ENNReal.ofReal (b ^ (-(G.J₀ : ℤ)))
  else ENNReal.ofReal (G.growInterpGaugeReal b x.toReal)

lemma growInterpGauge_eq_ofReal_toReal (G : GrowingRecData) {b : ℝ} (_hb : 1 < b)
    {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    G.growInterpGauge b x = ENNReal.ofReal (G.growInterpGaugeReal b x.toReal) := by
  by_cases hx1 : ENNReal.ofReal (G.growInvQ G.J₀) ≤ x
  · have hx1R : G.growInvQ G.J₀ ≤ x.toReal := by
      have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hx).mpr hx1
      rwa [ENNReal.toReal_ofReal (le_of_lt (G.growInvQ_pos G.J₀))] at h1
    simp [growInterpGauge, hx1, G.growInterpGaugeReal_ge_J₀ b hx1R]
  · simp [growInterpGauge, hx1]

lemma growInterpGauge_zero (G : GrowingRecData) (b : ℝ) : G.growInterpGauge b 0 = 0 := by
  have h0 : ¬ ENNReal.ofReal (G.growInvQ G.J₀) ≤ 0 := by
    rw [not_le]; exact ENNReal.ofReal_pos.mpr (G.growInvQ_pos G.J₀)
  simp [growInterpGauge, h0, G.growInterpGaugeReal_zero]

lemma growInterpGauge_at_inv_Q (G : GrowingRecData) {b : ℝ} (hb : 1 < b)
    {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growInterpGauge b (ENNReal.ofReal (1 / (G.Q n : ℝ))) = ENNReal.ofReal (b ^ (-(n : ℤ))) := by
  rw [G.growInterpGauge_eq_ofReal_toReal hb ENNReal.ofReal_ne_top]
  have hpos : 0 ≤ 1 / (G.Q n : ℝ) := le_of_lt (G.growInvQ_pos n)
  rw [ENNReal.toReal_ofReal hpos]
  change ENNReal.ofReal (G.growInterpGaugeReal b (G.growInvQ n)) = _
  rw [G.growInterpGaugeReal_at_invQ hb hn]

lemma growInterpGauge_mono (G : GrowingRecData) {b : ℝ} (hb : 1 < b) :
    Monotone (G.growInterpGauge b) := by
  intro x y hxy
  by_cases hy1 : ENNReal.ofReal (G.growInvQ G.J₀) ≤ y
  · by_cases hx1 : ENNReal.ofReal (G.growInvQ G.J₀) ≤ x
    · simp [growInterpGauge, hx1, hy1]
    · have hx_lt : x < ENNReal.ofReal (G.growInvQ G.J₀) := lt_of_not_ge hx1
      have hx_ne : x ≠ ⊤ := ne_of_lt (lt_trans hx_lt ENNReal.ofReal_lt_top)
      have hx1R : x.toReal ≤ G.growInvQ G.J₀ := by
        have h1 := (ENNReal.toReal_le_toReal hx_ne ENNReal.ofReal_ne_top).mpr hx_lt.le
        rwa [ENNReal.toReal_ofReal (le_of_lt (G.growInvQ_pos G.J₀))] at h1
      simp only [growInterpGauge, hx1, ↓reduceIte, hy1]
      apply ENNReal.ofReal_le_ofReal
      calc G.growInterpGaugeReal b x.toReal
          ≤ G.growInterpGaugeReal b (G.growInvQ G.J₀) := G.growInterpGaugeReal_mono hb hx1R
        _ = b ^ (-(G.J₀ : ℤ)) := G.growInterpGaugeReal_ge_J₀ b le_rfl
  · have hx1 : ¬ ENNReal.ofReal (G.growInvQ G.J₀) ≤ x := fun h => hy1 (le_trans h hxy)
    have hy_ne : y ≠ ⊤ := ne_of_lt (lt_trans (lt_of_not_ge hy1) ENNReal.ofReal_lt_top)
    rw [G.growInterpGauge_eq_ofReal_toReal hb (ne_top_of_le_ne_top hy_ne hxy),
      G.growInterpGauge_eq_ofReal_toReal hb hy_ne]
    exact ENNReal.ofReal_le_ofReal
      (G.growInterpGaugeReal_mono hb
        ((ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hy_ne hxy) hy_ne).mpr hxy))

lemma growInterpGauge_continuous (G : GrowingRecData) {b : ℝ} (hb : 1 < b) :
    Continuous (G.growInterpGauge b) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx1 : ENNReal.ofReal (G.growInvQ G.J₀) < x
  · have hev : ∀ᶠ y in nhds x, ENNReal.ofReal (b ^ (-(G.J₀ : ℤ))) = G.growInterpGauge b y := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      have hy1 : ENNReal.ofReal (G.growInvQ G.J₀) ≤ y := le_of_lt hy
      simp [growInterpGauge, hy1]
    exact (continuousAt_const :
      ContinuousAt (fun _ : ℝ≥0∞ => ENNReal.ofReal (b ^ (-(G.J₀ : ℤ)))) x).congr hev
  · have hx_le : x ≤ ENNReal.ofReal (G.growInvQ G.J₀) := le_of_not_gt hx1
    have hx_lt_top : x < ⊤ := lt_of_le_of_lt hx_le ENNReal.ofReal_lt_top
    have hx_ne : x ≠ ⊤ := ne_of_lt hx_lt_top
    have hev : ∀ᶠ y in nhds x,
        ENNReal.ofReal (G.growInterpGaugeReal b y.toReal) = G.growInterpGauge b y := by
      filter_upwards [Iio_mem_nhds hx_lt_top] with y hy
      exact (G.growInterpGauge_eq_ofReal_toReal hb (ne_of_lt hy)).symm
    have hcomp : ContinuousAt
        (fun y : ℝ≥0∞ => ENNReal.ofReal (G.growInterpGaugeReal b y.toReal)) x :=
      ENNReal.continuous_ofReal.continuousAt.comp
        ((G.growInterpGaugeReal_continuous hb).continuousAt.comp
          (ENNReal.continuousAt_toReal hx_ne))
    exact hcomp.congr hev

lemma growInterpGauge_ratio_tendsto_zero (G : GrowingRecData) {b₁ b₂ : ℝ}
    (hb₁ : 1 < b₁) (hb₂ : b₁ < b₂) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → G.growInterpGauge b₂ r ≤ (ε : ℝ≥0∞) * G.growInterpGauge b₁ r := by
  intro ε hε
  have hb₁_pos : 0 < b₁ := lt_trans zero_lt_one hb₁
  have hb₂_pos : 0 < b₂ := lt_trans hb₁_pos hb₂
  have hb₂_gt1 : 1 < b₂ := lt_trans hb₁ hb₂
  have hratio_nn : 0 ≤ b₁ / b₂ := div_nonneg (le_of_lt hb₁_pos) (le_of_lt hb₂_pos)
  have hratio_lt : b₁ / b₂ < 1 := (div_lt_one hb₂_pos).mpr hb₂
  have hpow0 : Tendsto (fun n : ℕ => b₁ * (b₁ / b₂) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt).const_mul b₁
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hpow0.eventually (Iio_mem_nhds hεR))
  set N := max G.J₀ N0
  have hNJ₀ : G.J₀ ≤ N := le_max_left _ _
  have hN_bound : b₁ * (b₁ / b₂) ^ N ≤ (ε : ℝ) := le_of_lt (hN0 N (le_max_right _ _))
  refine ⟨ENNReal.ofReal (G.growInvQ (N + 1)),
    ENNReal.ofReal_pos.mpr (G.growInvQ_pos (N + 1)), ?_⟩
  intro r hr
  by_cases hr0 : r = 0
  · subst hr0; simp [growInterpGauge_zero]
  · have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
    have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
    have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
    have hr_real_le : r.toReal ≤ G.growInvQ (N + 1) := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
      rwa [ENNReal.toReal_ofReal (le_of_lt (G.growInvQ_pos (N + 1)))] at h1
    have hr_lt_invQN : r.toReal < G.growInvQ N :=
      lt_of_le_of_lt hr_real_le (G.growInvQ_succ_lt hNJ₀)
    have hr_lt_J₀ : r.toReal < G.growInvQ G.J₀ :=
      lt_of_lt_of_le hr_lt_invQN (G.growInvQ_le_J₀ hNJ₀)
    set n := G.growInterpIdx r.toReal
    obtain ⟨hn1, hnlo, hnhi⟩ := G.growInterpIdx_spec hr_real_pos hr_lt_J₀
    have hN_le_n : N ≤ n := by
      by_contra hlt
      push Not at hlt
      have hle : n + 1 ≤ N := by omega
      have hq : G.growInvQ N ≤ G.growInvQ (n + 1) :=
        G.growInvQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
      linarith
    have hb₂_le : G.growInterpGaugeReal b₂ r.toReal ≤ b₂ ^ (-(n : ℤ)) := by
      calc G.growInterpGaugeReal b₂ r.toReal
          ≤ G.growInterpGaugeReal b₂ (G.growInvQ n) :=
            G.growInterpGaugeReal_mono hb₂_gt1 (le_of_lt hnhi)
        _ = b₂ ^ (-(n : ℤ)) := G.growInterpGaugeReal_at_invQ hb₂_gt1 hn1
    have hb₁_ge : b₁ ^ (-((n + 1 : ℕ) : ℤ)) ≤ G.growInterpGaugeReal b₁ r.toReal := by
      calc b₁ ^ (-((n + 1 : ℕ) : ℤ))
          = G.growInterpGaugeReal b₁ (G.growInvQ (n + 1)) :=
            (G.growInterpGaugeReal_at_invQ hb₁ (by omega)).symm
        _ ≤ G.growInterpGaugeReal b₁ r.toReal := G.growInterpGaugeReal_mono hb₁ hnlo
    have hpow_mono : b₁ * (b₁ / b₂) ^ n ≤ b₁ * (b₁ / b₂) ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hratio_nn (le_of_lt hratio_lt) hN_le_n) hb₁_pos.le
    have halg : b₂ ^ (-(n : ℤ)) = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, div_pow]
      have hb1n : b₁ ^ n ≠ 0 := pow_ne_zero n hb₁_pos.ne'
      have hb2n : b₂ ^ n ≠ 0 := pow_ne_zero n hb₂_pos.ne'
      have hb10 : b₁ ≠ 0 := hb₁_pos.ne'
      field_simp
    have hreal : G.growInterpGaugeReal b₂ r.toReal ≤
        (ε : ℝ) * G.growInterpGaugeReal b₁ r.toReal := by
      calc G.growInterpGaugeReal b₂ r.toReal
          ≤ b₂ ^ (-(n : ℤ)) := hb₂_le
        _ = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := halg
        _ ≤ (b₁ * (b₁ / b₂) ^ N) * G.growInterpGaugeReal b₁ r.toReal :=
            mul_le_mul hpow_mono hb₁_ge (zpow_nonneg hb₁_pos.le _) (by positivity)
        _ ≤ (ε : ℝ) * G.growInterpGaugeReal b₁ r.toReal := by
            gcongr; exact G.growInterpGaugeReal_nonneg hb₁ r.toReal
    rw [G.growInterpGauge_eq_ofReal_toReal hb₂_gt1 hr_ne_top,
      G.growInterpGauge_eq_ofReal_toReal hb₁ hr_ne_top]
    have hεE : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by simp
    rw [hεE, ← ENNReal.ofReal_mul (NNReal.coe_nonneg ε)]
    exact ENNReal.ofReal_le_ofReal hreal

def growCritGauge (G : GrowingRecData) (k : ℕ) : ℝ≥0∞ → ℝ≥0∞ :=
  G.growInterpGauge (2 * (k : ℝ) + 1)

def growBinaryGauge (G : GrowingRecData) : ℝ≥0∞ → ℝ≥0∞ :=
  G.growInterpGauge 2

lemma growCritGauge_zero (G : GrowingRecData) (k : ℕ) : G.growCritGauge k 0 = 0 :=
  G.growInterpGauge_zero _

lemma growCritGauge_mono (G : GrowingRecData) (k : ℕ) (hk : 1 ≤ k) :
    Monotone (G.growCritGauge k) :=
  G.growInterpGauge_mono (GaugeCircle.critGauge_base_gt_one k hk)

lemma growCritGauge_continuous (G : GrowingRecData) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (G.growCritGauge k) :=
  G.growInterpGauge_continuous (GaugeCircle.critGauge_base_gt_one k hk)

lemma growCritGauge_at_inv_Q (G : GrowingRecData) (k : ℕ) (hk : 1 ≤ k)
    {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growCritGauge k (ENNReal.ofReal (1 / (G.Q n : ℝ))) =
      ENNReal.ofReal ((2 * (k : ℝ) + 1) ^ (-(n : ℤ))) :=
  G.growInterpGauge_at_inv_Q (GaugeCircle.critGauge_base_gt_one k hk) hn

lemma growBinaryGauge_zero (G : GrowingRecData) : G.growBinaryGauge 0 = 0 :=
  G.growInterpGauge_zero 2

lemma growBinaryGauge_mono (G : GrowingRecData) : Monotone G.growBinaryGauge :=
  G.growInterpGauge_mono (by norm_num)

lemma growBinaryGauge_continuous (G : GrowingRecData) : Continuous G.growBinaryGauge :=
  G.growInterpGauge_continuous (by norm_num)

lemma growBinaryGauge_at_inv_Q (G : GrowingRecData) {n : ℕ} (hn : G.J₀ ≤ n) :
    G.growBinaryGauge (ENNReal.ofReal (1 / (G.Q n : ℝ))) = ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) :=
  G.growInterpGauge_at_inv_Q (by norm_num) hn

/-! #### Part 6.2: Universal `mkMetric` Upper Bounds, Nullity, and `σ`-Finiteness -/

def growNormalizedGaugeCost (G : GrowingRecData) (b : ℝ) (g : ℝ≥0∞ → ℝ≥0∞)
    (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (b ^ n) * g (ENNReal.ofReal (1 / (G.Q n : ℝ)))

theorem mkMetric_growAlphabetClass_le_liminf (G : GrowingRecData) (D : Finset ℤ)
    (hD : 1 ≤ D.card) (N : ℕ) (m₀ m₁ : ℤ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    Measure.mkMetric g (G.growAlphabetClass D N m₀ m₁) ≤
      liminf (G.growNormalizedGaugeCost (D.card : ℝ) g) atTop := by
  let ι : ℕ → Type := fun n => (G.growPairTreeA D N m₀ m₁ (n - N) : Set (ℤ × ℤ))
  have hr0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (G.Q n : ℝ))) atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => 1 / (G.Q n : ℝ)) atTop (nhds 0) :=
      G.grow_Q_tendsto_atTop.const_div_atTop 1
    simpa using ENNReal.tendsto_ofReal hreal
  have ht : ∀ᶠ n in atTop, ∀ i : ι n,
      Metric.ediam (G.growGaugeInterv n i.1.1) ≤ ENNReal.ofReal (1 / (G.Q n : ℝ)) :=
    Filter.Eventually.of_forall fun n i => G.ediam_growGaugeInterv_le n i.1.1
  have hst : ∀ᶠ n in atTop, G.growAlphabetClass D N m₀ m₁ ⊆
      ⋃ i : ι n, G.growGaugeInterv n i.1.1 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hadd : N + (n - N) = n := Nat.add_sub_of_le hn
    have hcov := G.growAlphabetClass_subset_cover D N m₀ m₁ (n - N)
    rwa [hadd] at hcov
  have hmain := PolyGaugeAndPhaseTransition.mkMetric_le_liminf_of_seq_cover
    (G.growAlphabetClass D N m₀ m₁)
    (fun n => ENNReal.ofReal (1 / (G.Q n : ℝ))) hr0
    (fun n (i : ι n) => G.growGaugeInterv n i.1.1) ht hst g hg
  have hcost_le : ∀ᶠ n in atTop,
      ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (G.Q n : ℝ))) ≤
        G.growNormalizedGaugeCost (D.card : ℝ) g n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcard : Fintype.card (ι n) = (G.growPairTreeA D N m₀ m₁ (n - N)).card := by simp [ι]
    have hpow_nat : (G.growPairTreeA D N m₀ m₁ (n - N)).card ≤ D.card ^ n :=
      le_trans (G.card_growPairTreeA_le D N m₀ m₁ (n - N))
        (Nat.pow_le_pow_right hD (Nat.sub_le n N))
    have hpow_enn : ((Fintype.card (ι n) : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((D.card : ℝ) ^ n) := by
      rw [hcard, ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast hpow_nat
    exact mul_le_mul_of_nonneg_right hpow_enn bot_le
  exact le_trans hmain
    (Filter.liminf_le_liminf hcost_le (by isBoundedDefault) (by isBoundedDefault))

lemma growStrictLevel_subset_iUnion_alphabet (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k) :
    G.growStrictLevel k ⊆
      ⋃ p : ℕ × ℤ × ℤ,
        G.growAlphabetClass (Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ))
          p.1 p.2.1 p.2.2 := by
  intro x hx
  have hle : G.growLambda x ≤ ((k - 1 : ℕ) : ℝ≥0∞) := by
    have hne : G.growLambda x ≠ ⊤ := ne_top_of_lt hx
    have hmem : G.growLambda x ∈ Set.range G.growLambda := ⟨x, rfl⟩
    rw [G.grow_range_lambda] at hmem
    rcases hmem with ⟨m, hm⟩ | htop
    · dsimp only at hm
      change G.growLambda x < (k : ℝ≥0∞) at hx
      rw [← hm] at hx ⊢
      have hmk : m < k := by exact_mod_cast hx
      exact_mod_cast (by omega : m ≤ k - 1)
    · exact absurd htop hne
  exact G.growLevelSet_nat_subset_iUnion_alphabet (k - 1) hle

lemma growUnsignedExactLimit_subset_iUnion_alphabet (G : GrowingRecData) (k : ℕ) :
    G.growUnsignedExactLimitSet (k : ℝ) ⊆
      ⋃ p : ℕ × ℤ × ℤ,
        G.growAlphabetClass {-(k : ℤ), (k : ℤ)} p.1 p.2.1 p.2.2 := by
  intro x hx
  have hbin := (G.grow_unsigned_exact_limit_iff_defect_binary x k |>.mp hx).2
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbin
  let N := max G.J₀ N0
  refine Set.mem_iUnion.mpr ⟨(N, round ((G.Q (N - 1) : ℝ) * x),
    round ((G.Q N : ℝ) * x)), le_max_left _ _, le_trans G.hJ₀ (le_max_left _ _), rfl, rfl,
    fun j hj => ?_⟩
  rcases hN0 j (le_trans (le_max_right _ _) hj) with hpos | hneg
  · simp [hpos]
  · simp [hneg]

lemma grow_liminf_normalizedGaugeCost_zero_of_smaller_base (G : GrowingRecData)
    {b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₁₂ : b₁ < b₂) (g : ℝ≥0∞ → ℝ≥0∞)
    (hfin : liminf (G.growNormalizedGaugeCost b₂ g) atTop < ⊤) :
    liminf (G.growNormalizedGaugeCost b₁ g) atTop = 0 := by
  have hb₂ : 0 < b₂ := lt_of_le_of_lt hb₁ hb₁₂
  have hratio_nn : 0 ≤ b₁ / b₂ := div_nonneg hb₁ hb₂.le
  have hratio_lt : b₁ / b₂ < 1 := (div_lt_one hb₂).mpr hb₁₂
  have hpow0 : Tendsto (fun n : ℕ => (b₁ / b₂) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt
  set L := liminf (G.growNormalizedGaugeCost b₂ g) atTop
  set C : ℝ := L.toReal + 1
  have hC_pos : 0 < C := by positivity
  have hL_lt : L < ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hC_pos).mpr (by linarith)
  have hfreq : ∃ᶠ n : ℕ in atTop,
      G.growNormalizedGaugeCost b₂ g n < ENNReal.ofReal C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hL_lt
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hev_pow : ∀ᶠ n : ℕ in atTop, (b₁ / b₂) ^ n < (ε : ℝ) / C :=
    hpow0.eventually (Iio_mem_nhds (div_pos hε_pos hC_pos))
  have hfreq_small : ∃ᶠ n : ℕ in atTop,
      G.growNormalizedGaugeCost b₁ g n ≤ (ε : ℝ≥0∞) := by
    refine (hfreq.and_eventually hev_pow).mono fun n ⟨hn_cost, hn_pow⟩ => ?_
    have hsplit : b₁ ^ n = (b₁ / b₂) ^ n * b₂ ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hb₂.ne')]
    calc G.growNormalizedGaugeCost b₁ g n
        = ENNReal.ofReal ((b₁ / b₂) ^ n) * G.growNormalizedGaugeCost b₂ g n := by
          unfold growNormalizedGaugeCost
          rw [hsplit, ENNReal.ofReal_mul (pow_nonneg hratio_nn n), mul_assoc]
      _ ≤ ENNReal.ofReal ((ε : ℝ) / C) * ENNReal.ofReal C := by gcongr
      _ = (ε : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_mul (div_pos hε_pos hC_pos).le,
            div_mul_cancel₀ _ hC_pos.ne', ENNReal.ofReal_coe_nnreal]
  exact Filter.liminf_le_of_frequently_le' hfreq_small

lemma grow_liminf_normalizedGaugeCost_interp_le_one (G : GrowingRecData)
    {b : ℝ} (hb : 1 < b) :
    liminf (G.growNormalizedGaugeCost b (G.growInterpGauge b)) atTop ≤ 1 := by
  have hev : ∀ᶠ n : ℕ in atTop,
      G.growNormalizedGaugeCost b (G.growInterpGauge b) n = 1 := by
    filter_upwards [eventually_ge_atTop G.J₀] with n hn
    unfold growNormalizedGaugeCost
    rw [G.growInterpGauge_at_inv_Q hb hn]
    have hb_pos : 0 < b := lt_trans zero_lt_one hb
    rw [← ENNReal.ofReal_mul (pow_nonneg hb_pos.le n), zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero n hb_pos.ne'), ENNReal.ofReal_one]
  exact le_of_eq ((Filter.liminf_congr hev).trans (Filter.liminf_const 1))

theorem mkMetric_growStrictLevel_null_of_liminf_lt_top (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hlim : liminf (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop < ⊤) :
    Measure.mkMetric g (G.growStrictLevel k) = 0 := by
  apply measure_mono_null (G.growStrictLevel_subset_iUnion_alphabet hk)
  apply measure_iUnion_null
  intro p
  set D := Finset.Icc (-((k - 1 : ℕ) : ℤ)) ((k - 1 : ℕ) : ℤ)
  have hD_card : D.card = 2 * (k - 1) + 1 := by rw [Int.card_Icc]; omega
  have hD_pos : 1 ≤ D.card := by omega
  have hD_lt : (D.card : ℝ) < 2 * (k : ℝ) + 1 := by
    rw [hD_card]
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by simpa using Nat.cast_sub hk
    push_cast; rw [hk1]; linarith
  have hle := G.mkMetric_growAlphabetClass_le_liminf D hD_pos p.1 p.2.1 p.2.2 g hg
  have hzero := G.grow_liminf_normalizedGaugeCost_zero_of_smaller_base
    (Nat.cast_nonneg D.card) hD_lt g hlim
  exact le_antisymm (hle.trans_eq hzero) bot_le

theorem mkMetric_growCritGauge_growStrictLevel_null (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growStrictLevel k) = 0 := by
  apply G.mkMetric_growStrictLevel_null_of_liminf_lt_top hk _ (G.growCritGauge_mono k hk)
  exact lt_of_le_of_lt
    (G.grow_liminf_normalizedGaugeCost_interp_le_one (GaugeCircle.critGauge_base_gt_one k hk))
    ENNReal.one_lt_top

theorem mkMetric_growLevelSet_null_of_liminf_zero (G : GrowingRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop = 0) :
    Measure.mkMetric g (G.growLevelSet (k : ℝ≥0∞)) = 0 := by
  apply measure_mono_null (G.growLevelSet_nat_subset_iUnion_alphabet k)
  apply measure_iUnion_null
  intro p
  set D := Finset.Icc (-(k : ℤ)) (k : ℤ)
  have hD_card : D.card = 2 * k + 1 := by rw [Int.card_Icc]; omega
  have hD_pos : 1 ≤ D.card := by omega
  have hD_eq : (D.card : ℝ) = 2 * (k : ℝ) + 1 := by rw [hD_card]; push_cast; ring
  have hle := G.mkMetric_growAlphabetClass_le_liminf D hD_pos p.1 p.2.1 p.2.2 g hg
  rw [hD_eq] at hle
  exact le_antisymm (hle.trans_eq hzero) bot_le

theorem growLevelSet_sigma_finite_of_liminf_lt_top (G : GrowingRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop < ⊤) :
    ∃ E : ℕ → Set ℝ, G.growLevelSet (k : ℝ≥0∞) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  classical
  let e : ℕ ≃ (ℕ × ℤ × ℤ) := (Denumerable.eqv _).symm
  refine ⟨fun i => G.growAlphabetClass (Finset.Icc (-(k : ℤ)) (k : ℤ))
      (e i).1 (e i).2.1 (e i).2.2, ?_, fun i => ?_⟩
  · intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (G.growLevelSet_nat_subset_iUnion_alphabet k hx)
    refine Set.mem_iUnion.mpr ⟨e.symm p, ?_⟩
    simpa [e.apply_symm_apply] using hp
  · set D := Finset.Icc (-(k : ℤ)) (k : ℤ)
    have hD_card : D.card = 2 * k + 1 := by rw [Int.card_Icc]; omega
    have hD_pos : 1 ≤ D.card := by omega
    have hD_eq : (D.card : ℝ) = 2 * (k : ℝ) + 1 := by rw [hD_card]; push_cast; ring
    have hle := G.mkMetric_growAlphabetClass_le_liminf D hD_pos (e i).1 (e i).2.1 (e i).2.2 g hg
    rw [hD_eq] at hle
    exact lt_of_le_of_lt hle hfin

theorem growExactLevel_critGauge_sigma_finite (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∃ E : ℕ → Set ℝ, G.growExactLevel k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (G.growCritGauge k) (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := G.growLevelSet_sigma_finite_of_liminf_lt_top k (G.growCritGauge k)
    (G.growCritGauge_mono k hk)
    (lt_of_le_of_lt
      (G.grow_liminf_normalizedGaugeCost_interp_le_one (GaugeCircle.critGauge_base_gt_one k hk))
      ENNReal.one_lt_top)
  exact ⟨E, Set.Subset.trans (fun _ hx => le_of_eq hx) hcov, hfin⟩

theorem mkMetric_growUnsignedExactLimit_null_of_liminf_zero (G : GrowingRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hzero : liminf (G.growNormalizedGaugeCost 2 g) atTop = 0) :
    Measure.mkMetric g (G.growUnsignedExactLimitSet (k : ℝ)) = 0 := by
  apply measure_mono_null (G.growUnsignedExactLimit_subset_iUnion_alphabet k)
  apply measure_iUnion_null
  intro p
  set D : Finset ℤ := {-(k : ℤ), (k : ℤ)}
  have hD_pos : 1 ≤ D.card := Finset.card_pos.mpr ⟨-(k : ℤ), by simp [D]⟩
  have hD_le2 : (D.card : ℝ) ≤ 2 := by
    have h1 : D.card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
    exact_mod_cast h1
  have hle := G.mkMetric_growAlphabetClass_le_liminf D hD_pos p.1 p.2.1 p.2.2 g hg
  have hcost_le : ∀ n : ℕ, G.growNormalizedGaugeCost (D.card : ℝ) g n ≤
      G.growNormalizedGaugeCost 2 g n := fun n => by
    unfold growNormalizedGaugeCost; gcongr
  have h0 : liminf (G.growNormalizedGaugeCost (D.card : ℝ) g) atTop = 0 := by
    refine le_antisymm ?_ bot_le
    calc liminf (G.growNormalizedGaugeCost (D.card : ℝ) g) atTop
        ≤ liminf (G.growNormalizedGaugeCost 2 g) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall hcost_le)
            (by isBoundedDefault) (by isBoundedDefault)
      _ = 0 := hzero
  exact le_antisymm (hle.trans_eq h0) bot_le

theorem mkMetric_growUnsignedExactLimit_null_of_critGauge (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growUnsignedExactLimitSet (k : ℝ)) = 0 := by
  apply G.mkMetric_growUnsignedExactLimit_null_of_liminf_zero k _ (G.growCritGauge_mono k hk)
  have h2lt : (2 : ℝ) < 2 * (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  apply G.grow_liminf_normalizedGaugeCost_zero_of_smaller_base (by norm_num) h2lt
    (G.growCritGauge k)
  exact lt_of_le_of_lt
    (G.grow_liminf_normalizedGaugeCost_interp_le_one (GaugeCircle.critGauge_base_gt_one k hk))
    ENNReal.one_lt_top

theorem growUnsignedExactLimit_sigma_finite_of_liminf_lt_top (G : GrowingRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfin : liminf (G.growNormalizedGaugeCost 2 g) atTop < ⊤) :
    ∃ E : ℕ → Set ℝ, G.growUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  classical
  let e : ℕ ≃ (ℕ × ℤ × ℤ) := (Denumerable.eqv _).symm
  refine ⟨fun i => G.growAlphabetClass {-(k : ℤ), (k : ℤ)} (e i).1 (e i).2.1 (e i).2.2,
    ?_, fun i => ?_⟩
  · intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (G.growUnsignedExactLimit_subset_iUnion_alphabet k hx)
    refine Set.mem_iUnion.mpr ⟨e.symm p, ?_⟩
    simpa [e.apply_symm_apply] using hp
  · set D : Finset ℤ := {-(k : ℤ), (k : ℤ)}
    have hD_pos : 1 ≤ D.card := Finset.card_pos.mpr ⟨-(k : ℤ), by simp [D]⟩
    have hD_le2 : (D.card : ℝ) ≤ 2 := by
      have h1 : D.card ≤ 2 := le_trans (Finset.card_insert_le _ _) (by simp)
      exact_mod_cast h1
    have hle := G.mkMetric_growAlphabetClass_le_liminf D hD_pos (e i).1 (e i).2.1 (e i).2.2 g hg
    have hcost_le : ∀ n : ℕ, G.growNormalizedGaugeCost (D.card : ℝ) g n ≤
        G.growNormalizedGaugeCost 2 g n := fun n => by
      unfold growNormalizedGaugeCost; gcongr
    have hlim_le := Filter.liminf_le_liminf (f := atTop) (Filter.Eventually.of_forall hcost_le)
      (by isBoundedDefault) (by isBoundedDefault)
    exact lt_of_le_of_lt (le_trans hle hlim_le) hfin

theorem growUnsignedExactLimit_binaryGauge_sigma_finite (G : GrowingRecData) (k : ℕ) :
    ∃ E : ℕ → Set ℝ, G.growUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric G.growBinaryGauge (E i) < ⊤ :=
  G.growUnsignedExactLimit_sigma_finite_of_liminf_lt_top k G.growBinaryGauge G.growBinaryGauge_mono
    (lt_of_le_of_lt (G.grow_liminf_normalizedGaugeCost_interp_le_one (by norm_num))
      ENNReal.one_lt_top)

lemma exists_growInterpGauge_le_mul_of_liminf_pos (G : GrowingRecData) {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hpos : 0 < liminf (G.growNormalizedGaugeCost b g) atTop) :
    ∃ (c : ℝ≥0) (δ : ℝ≥0∞), 0 < c ∧ 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → G.growInterpGauge b r ≤ (c : ℝ≥0∞) * g r := by
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  set L : ℝ≥0∞ := min 1 (liminf (G.growNormalizedGaugeCost b g) atTop) / 2
  have hL_pos : 0 < L := ENNReal.div_pos (lt_min one_pos hpos).ne' (by norm_num)
  have hL_lt : L < liminf (G.growNormalizedGaugeCost b g) atTop := by
    have h1 : min 1 (liminf (G.growNormalizedGaugeCost b g) atTop) ≤
        liminf (G.growNormalizedGaugeCost b g) atTop := min_le_right _ _
    have hhalf : min 1 (liminf (G.growNormalizedGaugeCost b g) atTop) / 2 <
        min 1 (liminf (G.growNormalizedGaugeCost b g) atTop) :=
      ENNReal.half_lt_self (lt_min one_pos hpos).ne'
        (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
    exact lt_of_lt_of_le hhalf h1
  have hL_ne_top : L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (ENNReal.div_le_of_le_mul (by exact le_mul_of_one_le_right bot_le (by norm_num)))
        (min_le_left _ _))
  have hev : ∀ᶠ n : ℕ in atTop, L < G.growNormalizedGaugeCost b g n :=
    Filter.eventually_lt_of_lt_liminf hL_lt
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max G.J₀ N0
  have hNJ₀ : G.J₀ ≤ N := le_max_left _ _
  have hNN0 : N0 ≤ N := le_max_right _ _
  set η : ℝ := L.toReal
  have hη_pos : 0 < η := ENNReal.toReal_pos hL_pos.ne' hL_ne_top
  have hη_le : ENNReal.ofReal η ≤ L := by rw [ENNReal.ofReal_toReal hL_ne_top]
  set c0 : ℝ≥0 := ⟨b / η, by positivity⟩
  have hc0_pos : 0 < c0 := by change 0 < b / η; positivity
  refine ⟨c0, ENNReal.ofReal (G.growInvQ (N + 1)), hc0_pos,
    ENNReal.ofReal_pos.mpr (G.growInvQ_pos (N + 1)), fun r hr => ?_⟩
  by_cases hr0 : r = 0
  · subst hr0; simp [growInterpGauge_zero]
  have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
  have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
  have hr_real_le : r.toReal ≤ G.growInvQ (N + 1) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    rwa [ENNReal.toReal_ofReal (le_of_lt (G.growInvQ_pos (N + 1)))] at h1
  have hr_lt_N : r.toReal < G.growInvQ N := lt_of_le_of_lt hr_real_le (G.growInvQ_succ_lt hNJ₀)
  have hr_lt_J₀ : r.toReal < G.growInvQ G.J₀ := lt_of_lt_of_le hr_lt_N (G.growInvQ_le_J₀ hNJ₀)
  set n := G.growInterpIdx r.toReal
  obtain ⟨hnJ₀, hnlo, hnhi⟩ := G.growInterpIdx_spec hr_real_pos hr_lt_J₀
  have hN_le_n : N ≤ n := by
    by_contra hlt; push Not at hlt
    have hle : n + 1 ≤ N := by omega
    have hq : G.growInvQ N ≤ G.growInvQ (n + 1) :=
      G.growInvQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
    linarith
  have hcost_n1 : ENNReal.ofReal η < G.growNormalizedGaugeCost b g (n + 1) :=
    lt_of_le_of_lt hη_le (hN0 (n + 1) (by omega))
  have hb_inv_le : ENNReal.ofReal (b ^ (-(n : ℤ))) ≤
      (c0 : ℝ≥0∞) * g (ENNReal.ofReal (G.growInvQ (n + 1))) := by
    have hc_eq : (c0 : ℝ≥0∞) * ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ)) * η) =
        ENNReal.ofReal (b ^ (-(n : ℤ))) := by
      have hc0R : (c0 : ℝ≥0∞) = ENNReal.ofReal (b / η) := by
        rw [← ENNReal.ofReal_coe_nnreal]; rfl
      rw [hc0R, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]; field_simp
    have hmult : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal η ≤
        g (ENNReal.ofReal (G.growInvQ (n + 1))) := by
      have hmul := mul_le_mul_of_nonneg_left hcost_n1.le
        (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))))
      unfold growNormalizedGaugeCost at hmul
      have hid : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal (b ^ (n + 1)) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), zpow_neg, zpow_natCast,
          inv_mul_cancel₀ (pow_ne_zero (n + 1) hb_pos.ne'), ENNReal.ofReal_one]
      rw [← mul_assoc, hid, one_mul] at hmul
      simpa [growInvQ] using hmul
    calc ENNReal.ofReal (b ^ (-(n : ℤ)))
        = (c0 : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal η) := by
          rw [← hc_eq, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ (c0 : ℝ≥0∞) * g (ENNReal.ofReal (G.growInvQ (n + 1))) := by gcongr
  have hr_eq : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hr_ne_top
  calc G.growInterpGauge b r
      = ENNReal.ofReal (G.growInterpGaugeReal b r.toReal) :=
        G.growInterpGauge_eq_ofReal_toReal hb hr_ne_top
    _ ≤ ENNReal.ofReal (b ^ (-(n : ℤ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc G.growInterpGaugeReal b r.toReal
            ≤ G.growInterpGaugeReal b (G.growInvQ n) := G.growInterpGaugeReal_mono hb hnhi.le
          _ = b ^ (-(n : ℤ)) := G.growInterpGaugeReal_at_invQ hb hnJ₀
    _ ≤ (c0 : ℝ≥0∞) * g (ENNReal.ofReal (G.growInvQ (n + 1))) := hb_inv_le
    _ ≤ (c0 : ℝ≥0∞) * g r := by
        gcongr; exact hg (by rw [← hr_eq]; exact ENNReal.ofReal_le_ofReal hnlo)

lemma growInterpGauge_ratio_tendsto_zero_of_liminf_top (G : GrowingRecData) {b : ℝ} (hb : 1 < b)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (htop : liminf (G.growNormalizedGaugeCost b g) atTop = ⊤) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → G.growInterpGauge b r ≤ (ε : ℝ≥0∞) * g r := by
  intro ε hε
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  set M : ℝ := b / (ε : ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal M < G.growNormalizedGaugeCost b g n :=
    Filter.eventually_lt_of_lt_liminf (by rw [htop]; exact ENNReal.ofReal_lt_top)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max G.J₀ N0
  have hNJ₀ : G.J₀ ≤ N := le_max_left _ _
  refine ⟨ENNReal.ofReal (G.growInvQ (N + 1)),
    ENNReal.ofReal_pos.mpr (G.growInvQ_pos (N + 1)), fun r hr => ?_⟩
  by_cases hr0 : r = 0
  · subst hr0; simp [growInterpGauge_zero]
  have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
  have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
  have hr_real_le : r.toReal ≤ G.growInvQ (N + 1) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
    rwa [ENNReal.toReal_ofReal (le_of_lt (G.growInvQ_pos (N + 1)))] at h1
  have hr_lt_N : r.toReal < G.growInvQ N := lt_of_le_of_lt hr_real_le (G.growInvQ_succ_lt hNJ₀)
  have hr_lt_J₀ : r.toReal < G.growInvQ G.J₀ := lt_of_lt_of_le hr_lt_N (G.growInvQ_le_J₀ hNJ₀)
  set n := G.growInterpIdx r.toReal
  obtain ⟨hnJ₀, hnlo, hnhi⟩ := G.growInterpIdx_spec hr_real_pos hr_lt_J₀
  have hN_le_n : N ≤ n := by
    by_contra hlt; push Not at hlt
    have hle : n + 1 ≤ N := by omega
    have hq : G.growInvQ N ≤ G.growInvQ (n + 1) :=
      G.growInvQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hNJ₀) hle
    linarith
  have hcost : ENNReal.ofReal M < G.growNormalizedGaugeCost b g (n + 1) := hN0 (n + 1) (by omega)
  have hmult : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M ≤
      g (ENNReal.ofReal (G.growInvQ (n + 1))) := by
    have hmul := mul_le_mul_of_nonneg_left hcost.le
      (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))))
    unfold growNormalizedGaugeCost at hmul
    have hid : ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal (b ^ (n + 1)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), zpow_neg, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero (n + 1) hb_pos.ne'), ENNReal.ofReal_one]
    rw [← mul_assoc, hid, one_mul] at hmul
    simpa [growInvQ] using hmul
  have hid2 : (ε : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M) =
      ENNReal.ofReal (b ^ (-(n : ℤ))) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; dsimp [M]; rw [zpow_neg, zpow_neg]; norm_cast; rw [pow_succ]; field_simp
  have hr_eq : ENNReal.ofReal r.toReal = r := ENNReal.ofReal_toReal hr_ne_top
  calc G.growInterpGauge b r
      = ENNReal.ofReal (G.growInterpGaugeReal b r.toReal) :=
        G.growInterpGauge_eq_ofReal_toReal hb hr_ne_top
    _ ≤ ENNReal.ofReal (b ^ (-(n : ℤ))) := by
        apply ENNReal.ofReal_le_ofReal
        calc G.growInterpGaugeReal b r.toReal
            ≤ G.growInterpGaugeReal b (G.growInvQ n) := G.growInterpGaugeReal_mono hb hnhi.le
          _ = b ^ (-(n : ℤ)) := G.growInterpGaugeReal_at_invQ hb hnJ₀
    _ = (ε : ℝ≥0∞) * (ENNReal.ofReal (b ^ (-((n + 1 : ℕ) : ℤ))) * ENNReal.ofReal M) := hid2.symm
    _ ≤ (ε : ℝ≥0∞) * g (ENNReal.ofReal (G.growInvQ (n + 1))) := by gcongr
    _ ≤ (ε : ℝ≥0∞) * g r := by
        gcongr; exact hg (by rw [← hr_eq]; exact ENNReal.ofReal_le_ofReal hnlo)

/-! #### Part 6.3: Compact Cantor Trees and Local Infinite `mkMetric` Lower Bounds -/

def growTreeJ (G : GrowingRecData) (k : ℕ) : ℕ :=
  max (G.J₀ + 1) (Nat.find (eventually_atTop.mp
    (G.hA_tendsto.eventually_ge_atTop ((8 * (k : ℤ) + 9 : ℤ) : ℝ))))

lemma growTreeJ_ge_J₀_succ (G : GrowingRecData) (k : ℕ) : G.J₀ + 1 ≤ G.growTreeJ k :=
  le_max_left _ _

lemma growA_ge_tree_bound (G : GrowingRecData) (k m : ℕ) (hm : G.growTreeJ k ≤ m) :
    8 * (k : ℤ) + 9 ≤ G.A m := by
  have hex := eventually_atTop.mp
    (G.hA_tendsto.eventually_ge_atTop ((8 * (k : ℤ) + 9 : ℤ) : ℝ))
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ m := le_trans (le_max_right _ _) hm
  exact Int.cast_le.mp (hspec m hle)

def growPairOfWord (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) :
    ∀ n : ℕ, (Fin n → Fin C.b) → ℤ × ℤ
  | 0, _ => (0, 0)
  | n + 1, w =>
      let p := growPairOfWord G C n (fun i => w i.castSucc)
      (p.2, G.A (G.growTreeJ k + n + 1) * p.2 + p.1 + C.digit (w (Fin.last n)))

def growCenterInt (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℤ :=
  (G.growPairOfWord C n w).2

lemma growPairOfWord_fst_succ (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    (G.growPairOfWord C (n + 1) w).1 =
      G.growCenterInt C n (fun i => w i.castSucc) := rfl

def growWOfWord (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℤ :=
  (G.growPairOfWord C n w).2 * G.Q (G.growTreeJ k + n) -
    (G.growPairOfWord C n w).1 * G.Q (G.growTreeJ k + n + 1)

lemma growWOfWord_zero (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (w : Fin 0 → Fin C.b) :
    G.growWOfWord C 0 w = 0 := by simp [growWOfWord, growPairOfWord]

lemma growWOfWord_succ (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    G.growWOfWord C (n + 1) w =
      -G.growWOfWord C n (fun i => w i.castSucc) +
        C.digit (w (Fin.last n)) * G.Q (G.growTreeJ k + n + 1) := by
  have hJ₀ : G.J₀ ≤ G.growTreeJ k + n + 1 := by
    have := G.growTreeJ_ge_J₀_succ k; omega
  have hQrec : G.Q (G.growTreeJ k + n + 2) =
      G.A (G.growTreeJ k + n + 1) * G.Q (G.growTreeJ k + n + 1) +
        G.Q (G.growTreeJ k + n) := by
    have h := G.hQ_rec (G.growTreeJ k + n + 1) hJ₀
    have hs1 : G.growTreeJ k + n + 1 + 1 = G.growTreeJ k + n + 2 := by omega
    have hs2 : G.growTreeJ k + n + 1 - 1 = G.growTreeJ k + n := by omega
    rw [hs1, hs2] at h
    exact h
  unfold growWOfWord
  dsimp [growPairOfWord]
  have hidx1 : G.growTreeJ k + (n + 1) = G.growTreeJ k + n + 1 := by omega
  have hidx3 : G.growTreeJ k + n + 1 + 1 = G.growTreeJ k + n + 2 := by omega
  rw [hidx1, hidx3, hQrec]
  ring

lemma abs_growWOfWord_le (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) :
    |G.growWOfWord C n w| ≤ ((k : ℤ) + 1) * G.Q (G.growTreeJ k + n) := by
  induction n with
  | zero =>
      rw [growWOfWord_zero, abs_zero]
      exact mul_nonneg (by positivity) (G.hQ_pos _).le
  | succ n ih =>
      rw [G.growWOfWord_succ]
      set p_w := fun i : Fin n => w i.castSucc
      have ih' := ih p_w
      have hd : |C.digit (w (Fin.last n))| ≤ (k : ℤ) := C.abs_le (w (Fin.last n))
      have hQ_pos : 0 ≤ G.Q (G.growTreeJ k + n + 1) := (G.hQ_pos _).le
      have hQ_J₀ : G.J₀ ≤ G.growTreeJ k + n := by
        have := G.growTreeJ_ge_J₀_succ k; omega
      have hQ_gt : G.A (G.growTreeJ k + n) * G.Q (G.growTreeJ k + n) <
          G.Q (G.growTreeJ k + n + 1) := G.grow_Q_succ_gt_A_mul hQ_J₀
      by_cases hn0 : n = 0
      · subst hn0
        rw [growWOfWord_zero, neg_zero, zero_add, abs_mul, abs_of_nonneg hQ_pos]
        have h1 : |C.digit (w (Fin.last 0))| * G.Q (G.growTreeJ k + 0 + 1) ≤
            (k : ℤ) * G.Q (G.growTreeJ k + 0 + 1) := mul_le_mul_of_nonneg_right hd hQ_pos
        nlinarith [hQ_pos]
      · have hm : G.growTreeJ k ≤ G.growTreeJ k + n := by omega
        have hA : 8 * (k : ℤ) + 9 ≤ G.A (G.growTreeJ k + n) :=
          G.growA_ge_tree_bound k (G.growTreeJ k + n) hm
        have hQ_prev_pos : 0 ≤ G.Q (G.growTreeJ k + n) := (G.hQ_pos _).le
        have hstep_prev : ((k : ℤ) + 1) * G.Q (G.growTreeJ k + n) ≤
            G.Q (G.growTreeJ k + n + 1) := by
          have h1 : ((k : ℤ) + 1) * G.Q (G.growTreeJ k + n) ≤
              G.A (G.growTreeJ k + n) * G.Q (G.growTreeJ k + n) :=
            mul_le_mul_of_nonneg_right (by omega) hQ_prev_pos
          exact le_trans h1 hQ_gt.le
        have htri : |-G.growWOfWord C n p_w +
            C.digit (w (Fin.last n)) * G.Q (G.growTreeJ k + n + 1)| ≤
            |G.growWOfWord C n p_w| + |C.digit (w (Fin.last n))| * G.Q (G.growTreeJ k + n + 1) := by
          calc |-G.growWOfWord C n p_w +
                  C.digit (w (Fin.last n)) * G.Q (G.growTreeJ k + n + 1)|
              ≤ |-G.growWOfWord C n p_w| +
                  |C.digit (w (Fin.last n)) * G.Q (G.growTreeJ k + n + 1)| := abs_add_le _ _
            _ = |G.growWOfWord C n p_w| +
                  |C.digit (w (Fin.last n))| * G.Q (G.growTreeJ k + n + 1) := by
                  rw [abs_neg, abs_mul, abs_of_nonneg hQ_pos]
        have hsum : |G.growWOfWord C n p_w| +
            |C.digit (w (Fin.last n))| * G.Q (G.growTreeJ k + n + 1) ≤
            ((k : ℤ) + 1) * G.Q (G.growTreeJ k + (n + 1)) := by
          have hidx : G.growTreeJ k + (n + 1) = G.growTreeJ k + n + 1 := by omega
          rw [hidx]
          calc |G.growWOfWord C n p_w| + |C.digit (w (Fin.last n))| * G.Q (G.growTreeJ k + n + 1)
              ≤ ((k : ℤ) + 1) * G.Q (G.growTreeJ k + n) +
                  (k : ℤ) * G.Q (G.growTreeJ k + n + 1) := by gcongr
            _ ≤ G.Q (G.growTreeJ k + n + 1) + (k : ℤ) * G.Q (G.growTreeJ k + n + 1) := by gcongr
            _ = ((k : ℤ) + 1) * G.Q (G.growTreeJ k + n + 1) := by ring
        exact le_trans htri hsum

def growCenter (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : ℝ :=
  (G.growCenterInt C n w : ℝ) / (G.Q (G.growTreeJ k + n + 1) : ℝ)

def growRadC (G : GrowingRecData) (k n : ℕ) : ℝ :=
  (2 * (k : ℝ) + 2) / (G.Q (G.growTreeJ k + n + 2) : ℝ)

lemma growRadC_pos (G : GrowingRecData) (k n : ℕ) : 0 < G.growRadC k n := by
  unfold growRadC
  have hQ : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 2) : ℝ) := by exact_mod_cast G.hQ_pos _
  positivity

lemma growRadC_twice_lt (G : GrowingRecData) (k n : ℕ) :
    2 * G.growRadC k n < (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + n + 1) : ℝ) := by
  unfold growRadC
  have hQ1 : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hQ2 : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 2) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hJ₀ : G.J₀ ≤ G.growTreeJ k + n + 1 := by
    have := G.growTreeJ_ge_J₀_succ k; omega
  have hgt : (G.A (G.growTreeJ k + n + 1) : ℝ) * (G.Q (G.growTreeJ k + n + 1) : ℝ) <
      (G.Q (G.growTreeJ k + n + 2) : ℝ) := by
    exact_mod_cast G.grow_Q_succ_gt_A_mul hJ₀
  have hA : (8 * (k : ℝ) + 9) ≤ (G.A (G.growTreeJ k + n + 1) : ℝ) := by
    exact_mod_cast G.growA_ge_tree_bound k (G.growTreeJ k + n + 1) (by omega)
  have h8k8_lt : (8 * (k : ℝ) + 8) * (G.Q (G.growTreeJ k + n + 1) : ℝ) <
      (G.Q (G.growTreeJ k + n + 2) : ℝ) := by nlinarith
  rw [show 2 * ((2 * (k : ℝ) + 2) / (G.Q (G.growTreeJ k + n + 2) : ℝ)) =
      (4 * (k : ℝ) + 4) / (G.Q (G.growTreeJ k + n + 2) : ℝ) by ring]
  rw [div_lt_div_iff₀ hQ2 hQ1]
  nlinarith

lemma growCenter_step_sub_abs_le (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    |G.growCenter C (n + 1) w - G.growCenter C n (fun i => w i.castSucc)| ≤
      ((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ) := by
  have hQ1 : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hQ2 : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 2) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hdiff : G.growCenter C (n + 1) w - G.growCenter C n (fun i => w i.castSucc) =
      (G.growWOfWord C (n + 1) w : ℝ) /
        ((G.Q (G.growTreeJ k + n + 1) : ℝ) * (G.Q (G.growTreeJ k + n + 2) : ℝ)) := by
    unfold growCenter growWOfWord growCenterInt
    rw [G.growPairOfWord_fst_succ]
    have hidx1 : G.growTreeJ k + (n + 1) + 1 = G.growTreeJ k + n + 2 := by omega
    have hidx2 : G.growTreeJ k + (n + 1) = G.growTreeJ k + n + 1 := by omega
    rw [hidx1, hidx2]
    push_cast [growCenterInt]
    field_simp
  rw [hdiff, abs_div, abs_of_pos (mul_pos hQ1 hQ2)]
  have hW : |(G.growWOfWord C (n + 1) w : ℝ)| ≤
      ((k : ℝ) + 1) * (G.Q (G.growTreeJ k + n + 1) : ℝ) := by
    have h := G.abs_growWOfWord_le C (n + 1) w
    have hidx : G.growTreeJ k + (n + 1) = G.growTreeJ k + n + 1 := by omega
    rw [hidx] at h
    exact_mod_cast h
  calc |(G.growWOfWord C (n + 1) w : ℝ)| /
        ((G.Q (G.growTreeJ k + n + 1) : ℝ) * (G.Q (G.growTreeJ k + n + 2) : ℝ))
      ≤ (((k : ℝ) + 1) * (G.Q (G.growTreeJ k + n + 1) : ℝ)) /
          ((G.Q (G.growTreeJ k + n + 1) : ℝ) * (G.Q (G.growTreeJ k + n + 2) : ℝ)) :=
        div_le_div_of_nonneg_right hW (mul_pos hQ1 hQ2).le
    _ = ((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ) := by field_simp

def growCInterv (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : Set ℝ :=
  Set.Icc (G.growCenter C n w - G.growRadC k n) (G.growCenter C n w + G.growRadC k n)

lemma growCInterv_nonempty (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : (G.growCInterv C n w).Nonempty :=
  ⟨G.growCenter C n w, by have hr := (G.growRadC_pos k n).le; exact ⟨by linarith, by linarith⟩⟩

lemma growCInterv_isClosed (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : IsClosed (G.growCInterv C n w) := isClosed_Icc

lemma growCInterv_isCompact (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin n → Fin C.b) : IsCompact (G.growCInterv C n w) := isCompact_Icc

lemma growCInterv_succ_subset (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    (w : Fin (n + 1) → Fin C.b) :
    G.growCInterv C (n + 1) w ⊆ G.growCInterv C n (fun i => w i.castSucc) := by
  intro x hx
  have hstep := G.growCenter_step_sub_abs_le C n w
  have hrad_succ : G.growRadC k (n + 1) ≤ ((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ) := by
    have hlt := G.growRadC_twice_lt k (n + 1)
    have hidx : G.growTreeJ k + (n + 1) + 1 = G.growTreeJ k + n + 2 := by omega
    rw [hidx] at hlt
    have hQ2 : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 2) : ℝ) := by exact_mod_cast G.hQ_pos _
    have h1 : (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + n + 2) : ℝ) ≤
        ((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hQ2.le
    have hrad_pos := G.growRadC_pos k (n + 1)
    linarith
  have hrad_sum : ((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ) + G.growRadC k (n + 1) ≤
      G.growRadC k n := by
    have hbase : G.growRadC k n = 2 * (((k : ℝ) + 1) / (G.Q (G.growTreeJ k + n + 2) : ℝ)) := by
      unfold growRadC; ring
    linarith
  rw [abs_le] at hstep
  exact ⟨by linarith [hx.1, hstep.1], by linarith [hx.2, hstep.2]⟩

def growPrefix (n : ℕ) {α : Type*} (w : ℕ → α) : Fin n → α := fun i => w i.1

def growCantorSet (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) : Set ℝ :=
  {x : ℝ | ∃ w : ℕ → Fin C.b, ∀ n : ℕ, x ∈ G.growCInterv C n (growPrefix n w)}

lemma growCenterInt_injective (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ) :
    Function.Injective (G.growCenterInt C n) := by
  intro w1 w2 heq
  by_contra hne
  have hex : ∃ i : Fin n, w1 i ≠ w2 i := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  let S : Finset ℕ := (Finset.univ : Finset (Fin n)).filter (fun i => w1 i ≠ w2 i)
    |>.image (fun i => i.1)
  have hS_ne : S.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i.1, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩⟩
  set i₀ := S.min' hS_ne
  have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨i₀Fin, hi₀Fin, hi₀_val⟩ := Finset.mem_image.mp hi₀_mem
  have hi₀_lt : i₀ < n := by rw [← hi₀_val]; exact i₀Fin.2
  have hi₀_ne : w1 ⟨i₀, hi₀_lt⟩ ≠ w2 ⟨i₀, hi₀_lt⟩ := by
    have h1 := (Finset.mem_filter.mp hi₀Fin).2
    have hfin : i₀Fin = ⟨i₀, hi₀_lt⟩ := Fin.ext hi₀_val
    rwa [hfin] at h1
  have hagree : ∀ t : ℕ, (ht : t ≤ i₀) →
      (fun j : Fin t => w1 ⟨j.1, by omega⟩) = (fun j : Fin t => w2 ⟨j.1, by omega⟩) := by
    intro t ht; funext j; by_contra hj
    have hj_mem : j.1 ∈ S := Finset.mem_image.mpr ⟨⟨j.1, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
    have := Finset.min'_le S j.1 hj_mem; omega
  let pref1 : ∀ t : ℕ, t ≤ n → Fin t → Fin C.b := fun t _ j => w1 ⟨j.1, by omega⟩
  let pref2 : ∀ t : ℕ, t ≤ n → Fin t → Fin C.b := fun t _ j => w2 ⟨j.1, by omega⟩
  have hagree_pref : ∀ (t : ℕ) (ht : t ≤ n), t ≤ i₀ → pref1 t ht = pref2 t ht := fun t ht hti =>
    funext fun j => congrFun (hagree t hti) j
  let Δ : ℕ → ℤ := fun t =>
    if ht : t ≤ n then G.growCenterInt C t (pref1 t ht) - G.growCenterInt C t (pref2 t ht) else 0
  have hΔ_zero : ∀ t : ℕ, t ≤ i₀ → Δ t = 0 := fun t ht => by
    have htn : t ≤ n := by omega
    dsimp [Δ]; simp only [htn, ↓reduceDIte]; rw [hagree_pref t htn ht, sub_self]
  have hΔ_i₀1 : 1 ≤ |Δ (i₀ + 1)| := by
    have htn : i₀ + 1 ≤ n := by omega
    have hi0n : i₀ ≤ n := by omega
    have h1 : pref1 (i₀ + 1) htn (Fin.last i₀) = w1 ⟨i₀, hi₀_lt⟩ := by simp [pref1, Fin.last]
    have h2 : pref2 (i₀ + 1) htn (Fin.last i₀) = w2 ⟨i₀, hi₀_lt⟩ := by simp [pref2, Fin.last]
    have hpre : (fun j : Fin i₀ => pref1 (i₀ + 1) htn j.castSucc) = pref1 i₀ hi0n := rfl
    have hpre2 : (fun j : Fin i₀ => pref2 (i₀ + 1) htn j.castSucc) = pref2 i₀ hi0n := rfl
    have hpeq : G.growPairOfWord C i₀ (pref1 i₀ hi0n) =
        G.growPairOfWord C i₀ (pref2 i₀ hi0n) := by
      rw [hagree_pref i₀ hi0n le_rfl]
    have hΔ_eq : Δ (i₀ + 1) = C.digit (w1 ⟨i₀, hi₀_lt⟩) - C.digit (w2 ⟨i₀, hi₀_lt⟩) := by
      dsimp [Δ, growCenterInt]; simp only [htn, ↓reduceDIte]; dsimp [growPairOfWord]
      rw [hpre, hpre2, hpeq, h1, h2]; ring
    rw [hΔ_eq]
    have hd_ne : C.digit (w1 ⟨i₀, hi₀_lt⟩) ≠ C.digit (w2 ⟨i₀, hi₀_lt⟩) :=
      fun h => hi₀_ne (C.inj h)
    exact Int.one_le_abs (sub_ne_zero.mpr hd_ne)
  have hΔ_growth : ∀ t : ℕ, i₀ + 1 ≤ t → t ≤ n →
      1 ≤ |Δ t| ∧ |Δ (t - 1)| < |Δ t| := by
    intro t ht_lo ht_hi
    induction t with
    | zero => omega
    | succ t ih =>
        by_cases hteq : t = i₀
        · subst hteq
          have h0 : Δ i₀ = 0 := hΔ_zero i₀ le_rfl
          simp only [Nat.add_sub_cancel]; rw [h0, abs_zero]; exact ⟨hΔ_i₀1, by omega⟩
        · have ht_lo' : i₀ + 1 ≤ t := by omega
          have ⟨ih1, ih2⟩ := ih ht_lo' (by omega)
          have htn : t ≤ n := by omega
          have ht1n : t + 1 ≤ n := ht_hi
          have htm1n : t - 1 ≤ n := by omega
          have hΔ_rec : Δ (t + 1) = G.A (G.growTreeJ k + t + 1) * Δ t + Δ (t - 1) +
              (C.digit (pref1 (t + 1) ht1n (Fin.last t)) -
                C.digit (pref2 (t + 1) ht1n (Fin.last t))) := by
            have hpre1 : (fun j : Fin t => pref1 (t + 1) ht1n j.castSucc) = pref1 t htn := rfl
            have hpre2 : (fun j : Fin t => pref2 (t + 1) ht1n j.castSucc) = pref2 t htn := rfl
            have hfst1 : (G.growPairOfWord C t (pref1 t htn)).1 =
                G.growCenterInt C (t - 1) (pref1 (t - 1) htm1n) := by
              obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
              subst hm; exact G.growPairOfWord_fst_succ C m _
            have hfst2 : (G.growPairOfWord C t (pref2 t htn)).1 =
                G.growCenterInt C (t - 1) (pref2 (t - 1) htm1n) := by
              obtain ⟨m, hm⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
              subst hm; exact G.growPairOfWord_fst_succ C m _
            dsimp [Δ, growCenterInt]; simp only [ht1n, htn, htm1n, ↓reduceDIte]
            dsimp [growPairOfWord]; rw [hpre1, hpre2, hfst1, hfst2]; dsimp [growCenterInt]; ring
          have hA := G.growA_ge_tree_bound k (G.growTreeJ k + t + 1) (by omega)
          have hd1 := C.abs_le (pref1 (t + 1) ht1n (Fin.last t))
          have hd2 := C.abs_le (pref2 (t + 1) ht1n (Fin.last t))
          set δ : ℤ := C.digit (pref1 (t + 1) ht1n (Fin.last t)) -
            C.digit (pref2 (t + 1) ht1n (Fin.last t))
          have hδ : |δ| ≤ 2 * (k : ℤ) := by
            calc |δ| ≤ |C.digit _| + |C.digit _| := abs_sub _ _
              _ ≤ (k : ℤ) + (k : ℤ) := add_le_add hd1 hd2
              _ = 2 * (k : ℤ) := by ring
          have hrev : G.A (G.growTreeJ k + t + 1) * |Δ t| - |Δ (t - 1)| - |δ| ≤ |Δ (t + 1)| := by
            have hA_nn : 0 ≤ G.A (G.growTreeJ k + t + 1) := by omega
            have hmul_eq : G.A (G.growTreeJ k + t + 1) * Δ t = Δ (t + 1) - (Δ (t - 1) + δ) := by
              linarith
            have htri1 : |G.A (G.growTreeJ k + t + 1) * Δ t| ≤ |Δ (t + 1)| + |Δ (t - 1) + δ| := by
              rw [hmul_eq]; exact abs_sub _ _
            rw [abs_mul, abs_of_nonneg hA_nn] at htri1
            have h2 := abs_add_le (Δ (t - 1)) δ
            linarith
          have hbig : 2 * |Δ t| ≤ |Δ (t + 1)| := by
            have h1 : (8 * (k : ℤ) + 9) * |Δ t| ≤ G.A (G.growTreeJ k + t + 1) * |Δ t| :=
              mul_le_mul_of_nonneg_right hA (abs_nonneg _)
            have h2 : 2 * (k : ℤ) ≤ 2 * (k : ℤ) * |Δ t| := by nlinarith
            nlinarith
          simp only [Nat.add_sub_cancel]
          exact ⟨by omega, by omega⟩
  have hΔ_ne : Δ n ≠ 0 := by
    have h1 := (hΔ_growth n (by omega) le_rfl).1
    intro h0; rw [h0, abs_zero] at h1; omega
  dsimp [Δ] at hΔ_ne
  simp only [le_rfl, ↓reduceDIte] at hΔ_ne
  have h1 : pref1 n le_rfl = w1 := rfl
  have h2 : pref2 n le_rfl = w2 := rfl
  rw [h1, h2, heq, sub_self] at hΔ_ne
  exact hΔ_ne rfl

lemma growCInterv_prefix_subset (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k)
    {m n : ℕ} (hmn : m ≤ n) (w : Fin n → Fin C.b) :
    G.growCInterv C n w ⊆ G.growCInterv C m (fun i => w ⟨i.1, by omega⟩) := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := by omega
      have hw : (fun i : Fin 0 => w ⟨i.1, by omega⟩) = w := funext fun i => Fin.elim0 i
      rw [hw]
  | succ n ih =>
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · exact subset_rfl
      · exact Set.Subset.trans (G.growCInterv_succ_subset C n w)
          (ih (Nat.lt_succ_iff.mp hlt) _)

lemma growCantorSet_inter_growCInterv_nonempty (G : GrowingRecData) {k : ℕ}
    (C : PolyDigitCode k) (n : ℕ) (u : Fin n → Fin C.b) :
    (G.growCantorSet C ∩ G.growCInterv C n u).Nonempty := by
  let w : ℕ → Fin C.b := fun m => if h : m < n then u ⟨m, h⟩ else ⟨0, C.hb⟩
  let F : ℕ → Set ℝ := fun m => G.growCInterv C (n + m) (growPrefix (n + m) w)
  have hanti : ∀ m : ℕ, F (m + 1) ⊆ F m := fun m => G.growCInterv_succ_subset C (n + m) _
  have hne : ∀ m : ℕ, (F m).Nonempty := fun m => G.growCInterv_nonempty C _ _
  have hcomp : IsCompact (F 0) := G.growCInterv_isCompact C _ _
  have hclosed : ∀ m : ℕ, IsClosed (F m) := fun m => G.growCInterv_isClosed C _ _
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hanti hne hcomp hclosed
  have hpre_u : growPrefix n w = u := by funext i; simp [growPrefix, w, i.2]
  have hx_all : ∀ m : ℕ, x ∈ G.growCInterv C m (growPrefix m w) := fun m => by
    rcases le_or_gt n m with hnm | hmn
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnm
      exact Set.mem_iInter.mp hx t
    · have h0 : x ∈ G.growCInterv C (n + 0) (growPrefix (n + 0) w) := Set.mem_iInter.mp hx 0
      have hsub := G.growCInterv_prefix_subset C (by omega : m ≤ n + 0) (growPrefix (n + 0) w) h0
      have heq_w : (fun i : Fin m => growPrefix (n + 0) w ⟨i.1, by omega⟩) = growPrefix m w :=
        funext fun _ => rfl
      rwa [heq_w] at hsub
  refine ⟨x, ⟨w, hx_all⟩, ?_⟩
  have h0 := hx_all n
  rwa [hpre_u] at h0

lemma growCInterv_disjoint_of_ne (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) (n : ℕ)
    {u₁ u₂ : Fin n → Fin C.b} (hne : u₁ ≠ u₂) :
    Disjoint (G.growCInterv C n u₁) (G.growCInterv C n u₂) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hIntNe : G.growCenterInt C n u₁ ≠ G.growCenterInt C n u₂ :=
    fun h => hne (G.growCenterInt_injective C n h)
  have hQ_pos : (0 : ℝ) < (G.Q (G.growTreeJ k + n + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  have hZ_ge1 : (1 : ℤ) ≤ |G.growCenterInt C n u₁ - G.growCenterInt C n u₂| :=
    Int.one_le_abs (sub_ne_zero.mpr hIntNe)
  have hR_ge1 : (1 : ℝ) ≤ |(G.growCenterInt C n u₁ : ℝ) - (G.growCenterInt C n u₂ : ℝ)| := by
    exact_mod_cast hZ_ge1
  have hcdiff : 1 / (G.Q (G.growTreeJ k + n + 1) : ℝ) ≤
      |G.growCenter C n u₁ - G.growCenter C n u₂| := by
    unfold growCenter; rw [← sub_div, abs_div, abs_of_pos hQ_pos]
    exact div_le_div_of_nonneg_right hR_ge1 hQ_pos.le
  have h1 : |x - G.growCenter C n u₁| ≤ G.growRadC k n :=
    abs_sub_le_iff.mpr ⟨by linarith [hx1.2], by linarith [hx1.1]⟩
  have h2 : |x - G.growCenter C n u₂| ≤ G.growRadC k n :=
    abs_sub_le_iff.mpr ⟨by linarith [hx2.2], by linarith [hx2.1]⟩
  have htri : |G.growCenter C n u₁ - G.growCenter C n u₂| ≤ 2 * G.growRadC k n := by
    calc |G.growCenter C n u₁ - G.growCenter C n u₂|
        = |(x - G.growCenter C n u₂) - (x - G.growCenter C n u₁)| := by ring_nf
      _ ≤ |x - G.growCenter C n u₂| + |x - G.growCenter C n u₁| := abs_sub _ _
      _ ≤ 2 * G.growRadC k n := by linarith
  have hlt := G.growRadC_twice_lt k n
  have hhalf : (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + n + 1) : ℝ) <
      1 / (G.Q (G.growTreeJ k + n + 1) : ℝ) := div_lt_div_of_pos_right (by norm_num) hQ_pos
  linarith

lemma growCantorSet_isCompact (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) :
    IsCompact (G.growCantorSet C) := by
  let U : ℕ → Set ℝ := fun n =>
    ⋃ u ∈ (Finset.univ : Finset (Fin n → Fin C.b)), G.growCInterv C n u
  have hEq : G.growCantorSet C = ⋂ n : ℕ, U n := by
    ext x; constructor
    · rintro ⟨w, hw⟩
      exact Set.mem_iInter.mpr fun n =>
        Set.mem_iUnion₂.mpr ⟨growPrefix n w, Finset.mem_univ _, hw n⟩
    · intro hx
      have huniq : ∀ n : ℕ, ∃! u : Fin n → Fin C.b, x ∈ G.growCInterv C n u := by
        intro n
        obtain ⟨u, _, hu⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hx n)
        refine ⟨u, hu, fun v hv => ?_⟩
        by_contra hne
        exact (Set.disjoint_left.mp (G.growCInterv_disjoint_of_ne C n hne)) hv hu
      choose u hu using fun n => (huniq n).exists
      have huniq_u : ∀ n v, x ∈ G.growCInterv C n v → v = u n := fun n v hv =>
        (huniq n).unique hv (hu n)
      have hcompat : ∀ n : ℕ, (fun i : Fin n => u (n + 1) i.castSucc) = u n := fun n =>
        huniq_u n _ (G.growCInterv_succ_subset C n (u (n + 1)) (hu (n + 1)))
      let w : ℕ → Fin C.b := fun n => u (n + 1) (Fin.last n)
      have hpref : ∀ n : ℕ, growPrefix n w = u n := fun n => by
        induction n with
        | zero => funext i; exact Fin.elim0 i
        | succ n ih =>
            funext i; refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [growPrefix, w]
            · change w j.1 = u (n + 1) j.castSucc
              exact (congrFun ih j).trans (congrFun (hcompat n) j).symm
      exact ⟨w, fun n => by rw [hpref n]; exact hu n⟩
  rw [hEq]
  have hclosed_U : ∀ n : ℕ, IsClosed (U n) := fun n =>
    isClosed_biUnion_finset fun u _ => G.growCInterv_isClosed C n u
  have hclosed : IsClosed (⋂ n : ℕ, U n) := isClosed_iInter hclosed_U
  have hsub0 : (⋂ n : ℕ, U n) ⊆ G.growCInterv C 0 ![] := by
    intro x hx
    obtain ⟨u, _, hu⟩ := Set.mem_iUnion₂.mp (Set.mem_iInter.mp hx 0)
    have heq : u = ![] := Subsingleton.elim _ _
    rwa [← heq]
  exact (G.growCInterv_isCompact C 0 ![]).of_isClosed_subset hclosed hsub0

lemma growCantorSet_isClosed (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) :
    IsClosed (G.growCantorSet C) :=
  (G.growCantorSet_isCompact C).isClosed

private lemma grow_fin_ext_card (b n N : ℕ) (h : n ≤ N) (v : Fin n → Fin b) :
    (Finset.univ.filter (fun w : Fin N → Fin b =>
      (fun t : Fin n => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v)).card ≤ b ^ (N - n) := by
  let proj : {w : Fin N → Fin b // (fun t : Fin n => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v} →
      (Fin (N - n) → Fin b) := fun ⟨w, _⟩ t => w ⟨n + t.1, by omega⟩
  have hinj : Function.Injective proj := by
    rintro ⟨w1, hw1⟩ ⟨w2, hw2⟩ heq; ext s
    by_cases hs : s.1 < n
    · exact congrArg Fin.val ((congrFun hw1 ⟨s.1, hs⟩).trans (congrFun hw2 ⟨s.1, hs⟩).symm)
    · have hid : n + (s.1 - n) = s.1 := by omega
      have hval := congrArg Fin.val (congrFun heq ⟨s.1 - n, by omega⟩)
      dsimp [proj] at hval; simpa [hid] using hval
  have hcard := Fintype.card_le_of_injective proj hinj
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_subtype] at hcard
  exact hcard

lemma grow_subtree_inv_pow_le_sum_of_cover (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k)
    (_hb2 : 2 ≤ C.b) (M : ℕ) (u₀ : Fin M → Fin C.b)
    {ι : Type*} (F : Finset ι) (V : ι → Set ℝ)
    (hcov : G.growCantorSet C ∩ G.growCInterv C M u₀ ⊆ ⋃ i ∈ F, V i)
    (hpos_diam : ∀ i ∈ F, 0 < Metric.ediam (V i))
    (hsmall_diam : ∀ i ∈ F,
      Metric.ediam (V i) < ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + M + 1) : ℝ))) :
    ((C.b : ℝ) ^ M)⁻¹ ≤ ∑ i ∈ F, (2 * (C.b : ℝ) ^ (G.growTreeJ k + 2)) *
      (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i))).toReal := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  have hex_lvl : ∀ i : ι, i ∈ F → ∃ n : ℕ, M ≤ n ∧
      ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + n + 2) : ℝ)) ≤ Metric.ediam (V i) ∧
      Metric.ediam (V i) < ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + n + 1) : ℝ)) := by
    intro i hi
    have h0 : 0 < Metric.ediam (V i) := hpos_diam i hi
    have hlt_top : Metric.ediam (V i) < ⊤ :=
      lt_of_lt_of_le (hsmall_diam i hi) (le_of_lt ENNReal.ofReal_lt_top)
    set r := (Metric.ediam (V i)).toReal
    have hr_pos : 0 < r := ENNReal.toReal_pos h0.ne' hlt_top.ne
    have hlt_invM : r < 1 / (G.Q (G.growTreeJ k + M + 1) : ℝ) := by
      have h1 := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top (hsmall_diam i hi)
      rwa [ENNReal.toReal_ofReal (by have := G.hQ_pos (G.growTreeJ k + M + 1); positivity)] at h1
    have ht0 : Tendsto (fun m : ℕ => 1 / (G.Q m : ℝ)) atTop (nhds 0) :=
      G.grow_Q_tendsto_atTop.const_div_atTop 1
    obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp (ht0.eventually (Iio_mem_nhds hr_pos))
    let S := (Finset.range (M + m0 + 2)).filter fun n =>
      M ≤ n ∧ r < 1 / (G.Q (G.growTreeJ k + n + 1) : ℝ)
    have hMS : M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl, hlt_invM⟩
    set n := S.max' ⟨M, hMS⟩
    have hn_mem := Finset.mem_filter.mp (S.max'_mem ⟨M, hMS⟩)
    have hnM : M ≤ n := hn_mem.2.1
    have hn_lt : r < 1 / (G.Q (G.growTreeJ k + n + 1) : ℝ) := hn_mem.2.2
    have hn_bound : n < M + m0 + 1 := by
      by_contra hge
      have hcontra := hm0 _ (by omega : m0 ≤ G.growTreeJ k + n + 1)
      linarith
    have hn1_ge : 1 / (G.Q (G.growTreeJ k + n + 2) : ℝ) ≤ r := by
      by_contra hlt_next; push Not at hlt_next
      have hn1_mem : n + 1 ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
        have hidx : G.growTreeJ k + (n + 1) + 1 = G.growTreeJ k + n + 2 := by omega
        rwa [hidx]
      have hle_max := S.le_max' (n + 1) hn1_mem; omega
    refine ⟨n, hnM, ?_, ?_⟩
    · rw [← ENNReal.ofReal_toReal hlt_top.ne]; exact ENNReal.ofReal_le_ofReal hn1_ge
    · rw [← ENNReal.ofReal_toReal hlt_top.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff
        (by have := G.hQ_pos (G.growTreeJ k + n + 1); positivity)).mpr hn_lt
  choose n_fun hnM hn_lo hn_hi using fun i (hi : i ∈ F) => hex_lvl i hi
  let ni : ι → ℕ := fun i => if hi : i ∈ F then n_fun i hi else M
  have hFne : F.Nonempty := by
    by_contra hFempty; rw [Finset.not_nonempty_iff_eq_empty] at hFempty
    obtain ⟨x, hx⟩ := G.growCantorSet_inter_growCInterv_nonempty C M u₀
    have hx_cov := hcov hx; simp [hFempty] at hx_cov
  set N : ℕ := F.sup' hFne ni
  have hN_ge_M : M ≤ N := by
    obtain ⟨i0, hi0⟩ := hFne
    exact le_trans (by dsimp [ni]; simp only [hi0, ↓reduceDIte]; exact hnM i0 hi0)
      (Finset.le_sup' ni hi0)
  have hni_le_N : ∀ i ∈ F, ni i ≤ N := fun i hi => Finset.le_sup' ni hi
  let ExtN : Finset (Fin N → Fin C.b) :=
    Finset.univ.filter fun w => ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j
  have hExtN_card : ExtN.card = C.b ^ (N - M) := by
    let e : {w : Fin N → Fin C.b // ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j} ≃
        (Fin (N - M) → Fin C.b) :=
      { toFun := fun ⟨w, _⟩ t => w ⟨M + t.1, by omega⟩
        invFun := fun tail =>
          ⟨fun i => if hi : i.1 < M then u₀ ⟨i.1, hi⟩ else tail ⟨i.1 - M, by omega⟩, fun j => by
            simp [j.2]⟩
        left_inv := fun ⟨w, hw⟩ => by
          ext i; dsimp
          by_cases hi : i.1 < M
          · simp only [hi, ↓reduceDIte]; exact (congrArg Fin.val (hw ⟨i.1, hi⟩)).symm
          · simp only [hi, ↓reduceDIte]; simp [show M + (i.1 - M) = i.1 by omega]
        right_inv := fun tail => by
          dsimp; funext t; have hnot : ¬ (M + t.1 < M) := by omega
          simp only [hnot, ↓reduceDIte]
          exact congrArg tail (Fin.ext (by dsimp only; omega)) }
    have hcard : ExtN.card =
        Fintype.card {w : Fin N → Fin C.b // ∀ j : Fin M, w ⟨j.1, by omega⟩ = u₀ j} :=
      (Fintype.card_subtype _).symm
    rw [hcard, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  let Act (i : ι) : Finset (Fin (ni i) → Fin C.b) :=
    Finset.univ.filter fun v => (V i ∩ G.growCInterv C (ni i) v).Nonempty
  have hactive_le_two : ∀ i ∈ F, (Act i).card ≤ 2 := by
    intro i hi; by_contra hgt2
    have h3 : 3 ≤ (Act i).card := by omega
    obtain ⟨v1, hv1, v2, hv2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (Act i).card)
    have hne12 : 2 ≤ ((Act i).erase v1).card := by rw [Finset.card_erase_of_mem hv1]; omega
    have hpos3 : 0 < (((Act i).erase v1).erase v2).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h12.symm, hv2⟩)]; omega
    obtain ⟨v3, hv3'⟩ := Finset.card_pos.mp hpos3
    have hv3 : v3 ∈ Act i := (Finset.mem_erase.mp (Finset.mem_erase.mp hv3').2).2
    have h13 : v1 ≠ v3 := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hv3').2).1 h.symm
    have h23 : v2 ≠ v3 := fun h => (Finset.mem_erase.mp hv3').1 h.symm
    let m1 := G.growCenterInt C (ni i) v1
    let m2 := G.growCenterInt C (ni i) v2
    let m3 := G.growCenterInt C (ni i) v3
    have hm12 : m1 ≠ m2 := fun h => h12 (G.growCenterInt_injective C (ni i) h)
    have hm13 : m1 ≠ m3 := fun h => h13 (G.growCenterInt_injective C (ni i) h)
    have hm23 : m2 ≠ m3 := fun h => h23 (G.growCenterInt_injective C (ni i) h)
    have hpair2 : ∃ va ∈ Act i, ∃ vb ∈ Act i,
        (2 : ℝ) ≤ |(G.growCenterInt C (ni i) va : ℝ) - (G.growCenterInt C (ni i) vb : ℝ)| := by
      have hZ : 2 ≤ |m1 - m2| ∨ 2 ≤ |m1 - m3| ∨ 2 ≤ |m2 - m3| := by
        by_contra hcon; push Not at hcon
        rcases hcon with ⟨h12_lt, h13_lt, h23_lt⟩
        have a12 := abs_lt.mp (by omega : |m1 - m2| < 2)
        have a13 := abs_lt.mp (by omega : |m1 - m3| < 2)
        have a23 := abs_lt.mp (by omega : |m2 - m3| < 2)
        omega
      rcases hZ with h | h | h
      · exact ⟨v1, hv1, v2, hv2, by exact_mod_cast h⟩
      · exact ⟨v1, hv1, v3, hv3, by exact_mod_cast h⟩
      · exact ⟨v2, hv2, v3, hv3, by exact_mod_cast h⟩
    rcases hpair2 with ⟨va, hva, vb, hvb, hmab⟩
    obtain ⟨xa, hxaV, hxaC⟩ := (Finset.mem_filter.mp hva).2
    obtain ⟨xb, hxbV, hxbC⟩ := (Finset.mem_filter.mp hvb).2
    have hQ_pos : (0 : ℝ) < (G.Q (G.growTreeJ k + ni i + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hcdiff : 2 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) ≤
        |G.growCenter C (ni i) va - G.growCenter C (ni i) vb| := by
      unfold growCenter; rw [← sub_div, abs_div, abs_of_pos hQ_pos]
      exact div_le_div_of_nonneg_right hmab hQ_pos.le
    have hxa_diff : |xa - G.growCenter C (ni i) va| ≤ G.growRadC k (ni i) :=
      abs_sub_le_iff.mpr ⟨by linarith [hxaC.2], by linarith [hxaC.1]⟩
    have hxb_diff : |xb - G.growCenter C (ni i) vb| ≤ G.growRadC k (ni i) :=
      abs_sub_le_iff.mpr ⟨by linarith [hxbC.2], by linarith [hxbC.1]⟩
    have hdist_lo : 2 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) - 2 * G.growRadC k (ni i) ≤
        |xa - xb| := by
      have htri : |G.growCenter C (ni i) va - G.growCenter C (ni i) vb| ≤
          |xa - xb| + |xa - G.growCenter C (ni i) va| +
            |xb - G.growCenter C (ni i) vb| := by
        calc |G.growCenter C (ni i) va - G.growCenter C (ni i) vb|
            = |((xa - xb) - (xa - G.growCenter C (ni i) va)) +
                (xb - G.growCenter C (ni i) vb)| := by congr 1; ring
          _ ≤ |(xa - xb) - (xa - G.growCenter C (ni i) va)| +
                |xb - G.growCenter C (ni i) vb| := abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_sub _ _
      linarith
    have h2rad := G.growRadC_twice_lt k (ni i)
    have hinv_lt : 1 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) < |xa - xb| := by
      have hhalf : 2 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) -
          (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) =
          (3 / 2 : ℝ) / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) := by ring
      have h1_lt : 1 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) <
          (3 / 2 : ℝ) / (G.Q (G.growTreeJ k + ni i + 1) : ℝ) :=
        div_lt_div_of_pos_right (by norm_num) hQ_pos
      linarith
    have hed_lt : ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + ni i + 1) : ℝ)) < edist xa xb := by
      rw [edist_dist, Real.dist_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (div_pos one_pos hQ_pos) hinv_lt)).mpr hinv_lt
    have hed_le : edist xa xb ≤ Metric.ediam (V i) := Metric.edist_le_ediam_of_mem hxaV hxbV
    have hni_eq : ni i = n_fun i hi := by dsimp [ni]; simp only [hi, ↓reduceDIte]
    have hhi := hn_hi i hi; rw [← hni_eq] at hhi
    exact (not_lt_of_ge (le_trans hed_lt.le hed_le) hhi).elim
  have hex_witness : ∀ w ∈ ExtN, ∃ i ∈ F, ∃ hle : ni i ≤ N,
      (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 hle⟩) ∈ Act i := by
    intro w hw
    have hw_ext := (Finset.mem_filter.mp hw).2
    obtain ⟨x, hxK, hxw⟩ := G.growCantorSet_inter_growCInterv_nonempty C N w
    have hxu₀ : x ∈ G.growCInterv C M u₀ := by
      have hsub := G.growCInterv_prefix_subset C hN_ge_M w hxw
      have heq : (fun j : Fin M => w ⟨j.1, by omega⟩) = u₀ := funext hw_ext
      rwa [heq] at hsub
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcov ⟨hxK, hxu₀⟩)
    refine ⟨i, hi, hni_le_N i hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨x, hxi, G.growCInterv_prefix_subset C (hni_le_N i hi) w hxw⟩
  let branchFin (i : ι) : Finset (Fin N → Fin C.b) :=
    if h : ni i ≤ N then
      (Act i).biUnion fun v => Finset.univ.filter fun w : Fin N → Fin C.b =>
        (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 h⟩) = v
    else ∅
  have hbranch_card : ∀ i ∈ F, (branchFin i).card ≤ 2 * C.b ^ (N - ni i) := fun i hi => by
    have hle := hni_le_N i hi
    dsimp [branchFin]; simp only [hle, ↓reduceDIte]
    calc ((Act i).biUnion _).card
        ≤ ∑ v ∈ Act i, (Finset.univ.filter fun w : Fin N → Fin C.b =>
            (fun t : Fin (ni i) => w ⟨t.1, Nat.lt_of_lt_of_le t.2 hle⟩) = v).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ Act i, C.b ^ (N - ni i) := by gcongr with v _; exact grow_fin_ext_card _ _ _ hle v
      _ = (Act i).card * C.b ^ (N - ni i) := by simp [Finset.sum_const]
      _ ≤ 2 * C.b ^ (N - ni i) := Nat.mul_le_mul_right _ (hactive_le_two i hi)
  have hExtN_sub_biUnion : ExtN ⊆ F.biUnion branchFin := fun w hw => by
    obtain ⟨i, hi, hle, hv⟩ := hex_witness w hw
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    dsimp [branchFin]; simp only [hle, ↓reduceDIte]
    exact Finset.mem_biUnion.mpr ⟨_, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hExtN_sub : ExtN.card ≤ ∑ i ∈ F, 2 * C.b ^ (N - ni i) :=
    (Finset.card_le_card hExtN_sub_biUnion).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum hbranch_card))
  rw [hExtN_card] at hExtN_sub
  have hR_le : ((C.b : ℝ) ^ (N - M)) ≤ ∑ i ∈ F, 2 * (C.b : ℝ) ^ (N - ni i) := by
    exact_mod_cast hExtN_sub
  have hbN_pos : 0 < (C.b : ℝ) ^ N := pow_pos hb_pos N
  have hdiv := div_le_div_of_nonneg_right hR_le hbN_pos.le
  have hlhs : ((C.b : ℝ) ^ (N - M)) / (C.b : ℝ) ^ N = ((C.b : ℝ) ^ M)⁻¹ := by
    rw [show (C.b : ℝ) ^ N = (C.b : ℝ) ^ M * (C.b : ℝ) ^ (N - M) by
      rw [← pow_add, Nat.add_sub_of_le hN_ge_M]]
    field_simp
  have hrhs_eq : (∑ i ∈ F, 2 * (C.b : ℝ) ^ (N - ni i)) / (C.b : ℝ) ^ N =
      ∑ i ∈ F, 2 * ((C.b : ℝ) ^ ni i)⁻¹ := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (C.b : ℝ) ^ N = (C.b : ℝ) ^ ni i * (C.b : ℝ) ^ (N - ni i) by
      rw [← pow_add, Nat.add_sub_of_le (hni_le_N i hi)]]
    field_simp
  rw [hlhs, hrhs_eq] at hdiv
  have hsum_term : ∀ i ∈ F, 2 * ((C.b : ℝ) ^ ni i)⁻¹ ≤
      (2 * (C.b : ℝ) ^ (G.growTreeJ k + 2)) *
        (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i))).toReal := fun i hi => by
    have hni_eq : ni i = n_fun i hi := by dsimp [ni]; simp only [hi, ↓reduceDIte]
    have hni_J₀ : G.J₀ ≤ G.growTreeJ k + ni i + 2 := by
      have := G.growTreeJ_ge_J₀_succ k; omega
    have hlo_i := hn_lo i hi; rw [← hni_eq] at hlo_i
    have hgauge_lo : ENNReal.ofReal ((C.b : ℝ) ^ (-((G.growTreeJ k + ni i + 2 : ℕ) : ℤ))) ≤
        G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i)) := by
      calc ENNReal.ofReal ((C.b : ℝ) ^ (-((G.growTreeJ k + ni i + 2 : ℕ) : ℤ)))
          = G.growInterpGauge (C.b : ℝ)
              (ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + ni i + 2) : ℝ))) :=
            (G.growInterpGauge_at_inv_Q hb1 hni_J₀).symm
        _ ≤ G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i)) :=
            G.growInterpGauge_mono hb1 hlo_i
    have hlt_top_V : Metric.ediam (V i) < ⊤ :=
      lt_of_lt_of_le (hsmall_diam i hi) (le_of_lt ENNReal.ofReal_lt_top)
    have hgauge_ne_top : G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i)) ≠ ⊤ := by
      rw [G.growInterpGauge_eq_ofReal_toReal hb1 hlt_top_V.ne]; exact ENNReal.ofReal_ne_top
    have hreal_lo : (C.b : ℝ) ^ (-((G.growTreeJ k + ni i + 2 : ℕ) : ℤ)) ≤
        (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V i))).toReal := by
      have h1 := ENNReal.toReal_mono hgauge_ne_top hgauge_lo
      rwa [ENNReal.toReal_ofReal (zpow_nonneg hb_pos.le _)] at h1
    have hid_pow : 2 * ((C.b : ℝ) ^ ni i)⁻¹ =
        (2 * (C.b : ℝ) ^ (G.growTreeJ k + 2)) *
          (C.b : ℝ) ^ (-((G.growTreeJ k + ni i + 2 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast]
      have hadd : (C.b : ℝ) ^ (G.growTreeJ k + ni i + 2) =
          (C.b : ℝ) ^ (G.growTreeJ k + 2) * (C.b : ℝ) ^ ni i := by
        rw [← pow_add, show G.growTreeJ k + 2 + ni i = G.growTreeJ k + ni i + 2 by omega]
      rw [hadd]; field_simp
    rw [hid_pow]
    exact mul_le_mul_of_nonneg_left hreal_lo (by positivity)
  exact le_trans hdiv (Finset.sum_le_sum hsum_term)

theorem mkMetric_growWordTree_subtree_pos (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k)
    (hb2 : 2 ≤ C.b) (M : ℕ) (u₀ : Fin M → Fin C.b) :
    ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / (2 * (C.b : ℝ) ^ (G.growTreeJ k + 2))) ≤
      Measure.mkMetric (G.growInterpGauge (C.b : ℝ))
        (G.growCantorSet C ∩ G.growCInterv C M u₀) := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  have hQ_pos : (0 : ℝ) < (G.Q (G.growTreeJ k + M + 1) : ℝ) := by exact_mod_cast G.hQ_pos _
  set Ctree : ℝ := 2 * (C.b : ℝ) ^ (G.growTreeJ k + 2)
  have hCtree_pos : 0 < Ctree := by positivity
  set r₀ : ℝ := (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ)
  have hr₀_pos : 0 < r₀ := by positivity
  rw [Measure.mkMetric_apply]
  refine le_iSup₂_of_le (ENNReal.ofReal r₀) (ENNReal.ofReal_pos.mpr hr₀_pos) ?_
  refine le_iInf fun t => le_iInf fun ht_cov => le_iInf fun ht_diam => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  by_cases htop : (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
      G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))) = ⊤
  · rw [htop]; exact le_trans le_top (le_add_right le_rfl)
  have hcont := G.growInterpGaugeReal_continuous hb1
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hη : ∀ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ y : ℝ, |y - (Metric.ediam (t n)).toReal| < η →
      |G.growInterpGaugeReal (C.b : ℝ) y -
        G.growInterpGaugeReal (C.b : ℝ) (Metric.ediam (t n)).toReal| <
        (ε : ℝ) / (2 ^ (n + 2) * Ctree) := fun n =>
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := (Metric.ediam (t n)).toReal)) _
      (by positivity)
  choose η_fun hη_pos hη_spec using hη
  let δ_fun : ℕ → ℝ := fun n =>
    min (η_fun n / 4) ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ))
  have hδ_pos : ∀ n : ℕ, 0 < δ_fun n := fun n => lt_min (by linarith [hη_pos n]) (by positivity)
  let V : ℕ → Set ℝ := fun n => if (t n).Nonempty then Metric.thickening (δ_fun n) (t n) else ∅
  have hV_open : ∀ n : ℕ, IsOpen (V n) := fun n => by
    dsimp [V]; split_ifs
    · exact Metric.isOpen_thickening
    · exact isOpen_empty
  have hV_cov : G.growCantorSet C ∩ G.growCInterv C M u₀ ⊆ ⋃ n : ℕ, V n := fun x hx => by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (ht_cov hx)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    have hne : (t n).Nonempty := ⟨x, hn⟩
    dsimp [V]; simp only [hne, ↓reduceIte]
    exact Metric.self_subset_thickening (hδ_pos n) _ hn
  have hK_comp : IsCompact (G.growCantorSet C ∩ G.growCInterv C M u₀) :=
    (G.growCantorSet_isCompact C).inter_right (G.growCInterv_isClosed C M u₀)
  obtain ⟨F₀, hF₀⟩ := hK_comp.elim_finite_subcover V hV_open hV_cov
  set F : Finset ℕ := F₀.filter fun n => (t n).Nonempty
  have hF_cov : G.growCantorSet C ∩ G.growCInterv C M u₀ ⊆ ⋃ n ∈ F, V n := fun x hx => by
    obtain ⟨n, hnF, hxn⟩ := Set.mem_iUnion₂.mp (hF₀ hx)
    have hne : (t n).Nonempty := by by_contra hempty; simp [V, hempty] at hxn
    exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_filter.mpr ⟨hnF, hne⟩, hxn⟩
  have hV_pos : ∀ n ∈ F, 0 < Metric.ediam (V n) := fun n hn => by
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hn).2
    have hne : (t n).Nonempty := ⟨x, hx⟩
    have h1 : x ∈ V n := by
      dsimp [V]; simp only [hne, ↓reduceIte]; exact Metric.self_subset_thickening (hδ_pos n) _ hx
    have h2 : x + δ_fun n / 2 ∈ V n := by
      dsimp [V]; simp only [hne, ↓reduceIte]; rw [Metric.mem_thickening_iff]
      refine ⟨x, hx, ?_⟩
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos (hδ_pos n))]
      linarith [hδ_pos n]
    have hed : edist x (x + δ_fun n / 2) = ENNReal.ofReal (δ_fun n / 2) := by
      rw [edist_dist, Real.dist_eq, sub_add_cancel_left, abs_neg,
        abs_of_pos (half_pos (hδ_pos n))]
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (half_pos (hδ_pos n)))
      (hed ▸ Metric.edist_le_ediam_of_mem h1 h2)
  have hV_small : ∀ n ∈ F, Metric.ediam (V n) <
      ENNReal.ofReal (1 / (G.Q (G.growTreeJ k + M + 1) : ℝ)) := fun n hn => by
    have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
    have hthick : Metric.ediam (V n) ≤ Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) := by
      dsimp [V]; simp only [hne, ↓reduceIte]
      exact WeightedExactDim.ediam_thickening_le (hδ_pos n).le
    have hbound_R : Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) ≤
        ENNReal.ofReal (r₀ + 2 * ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ))) := by
      have h1 := ht_diam n
      have h2 : δ_fun n ≤ (1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ) := min_le_right _ _
      calc Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n)
          ≤ ENNReal.ofReal r₀ +
              ENNReal.ofReal (2 * ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ))) := by
            gcongr; rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
            exact ENNReal.ofReal_le_ofReal (by linarith)
        _ = ENNReal.ofReal (r₀ + 2 * ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ))) :=
            (ENNReal.ofReal_add hr₀_pos.le (by positivity)).symm
    have hlt_R : r₀ + 2 * ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ)) <
        1 / (G.Q (G.growTreeJ k + M + 1) : ℝ) := by
      dsimp [r₀]
      have h1 : (1 / 2 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ) +
          2 * ((1 / 8 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ)) =
          (3 / 4 : ℝ) / (G.Q (G.growTreeJ k + M + 1) : ℝ) := by ring
      rw [h1]; exact div_lt_div_of_pos_right (by norm_num) hQ_pos
    exact lt_of_le_of_lt (le_trans hthick hbound_R)
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt_R)
  have hcov_low := G.grow_subtree_inv_pow_le_sum_of_cover C hb2 M u₀ F V hF_cov hV_pos hV_small
  have hterm_le : ∀ n ∈ F,
      Ctree * (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V n))).toReal ≤
        Ctree * (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal +
          (ε : ℝ) / 2 ^ (n + 2) := fun n hn => by
    have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
    have hV_ne_top : Metric.ediam (V n) ≠ ⊤ :=
      ne_of_lt (lt_of_lt_of_le (hV_small n hn) (le_of_lt ENNReal.ofReal_lt_top))
    have ht_ne_top : Metric.ediam (t n) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (ht_diam n) ENNReal.ofReal_lt_top)
    have hthick : Metric.ediam (V n) ≤ Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) := by
      dsimp [V]; simp only [hne, ↓reduceIte]
      exact WeightedExactDim.ediam_thickening_le (hδ_pos n).le
    have hdiff_R : |(Metric.ediam (V n)).toReal - (Metric.ediam (t n)).toReal| < η_fun n := by
      have hle_V : (Metric.ediam (V n)).toReal ≤ (Metric.ediam (t n)).toReal + 2 * δ_fun n := by
        have hnn : 0 ≤ 2 * δ_fun n := mul_nonneg (by norm_num) (hδ_pos n).le
        have hsum_eq : Metric.ediam (t n) + 2 * ENNReal.ofReal (δ_fun n) =
            ENNReal.ofReal ((Metric.ediam (t n)).toReal + 2 * δ_fun n) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hnn, ENNReal.ofReal_toReal ht_ne_top,
            ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        rw [hsum_eq] at hthick
        have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hthick
        rwa [ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg hnn)] at h1
      have hge_V : (Metric.ediam (t n)).toReal ≤ (Metric.ediam (V n)).toReal := by
        apply ENNReal.toReal_mono hV_ne_top
        dsimp [V]; simp only [hne, ↓reduceIte]
        exact Metric.ediam_mono (Metric.self_subset_thickening (hδ_pos n) _)
      rw [abs_of_nonneg (by linarith)]
      have hδ_eta : δ_fun n ≤ η_fun n / 4 := min_le_left _ _
      linarith [hη_pos n]
    have hη_s := hη_spec n (Metric.ediam (V n)).toReal hdiff_R
    have hgV : (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V n))).toReal =
        G.growInterpGaugeReal (C.b : ℝ) (Metric.ediam (V n)).toReal := by
      rw [G.growInterpGauge_eq_ofReal_toReal hb1 hV_ne_top,
        ENNReal.toReal_ofReal (G.growInterpGaugeReal_nonneg hb1 _)]
    have hgt : (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal =
        G.growInterpGaugeReal (C.b : ℝ) (Metric.ediam (t n)).toReal := by
      rw [G.growInterpGauge_eq_ofReal_toReal hb1 ht_ne_top,
        ENNReal.toReal_ofReal (G.growInterpGaugeReal_nonneg hb1 _)]
    rw [hgV, hgt]
    have h1 := (abs_lt.mp hη_s).2
    have h2 : Ctree * G.growInterpGaugeReal (C.b : ℝ) (Metric.ediam (V n)).toReal ≤
        Ctree * (G.growInterpGaugeReal (C.b : ℝ) (Metric.ediam (t n)).toReal +
          (ε : ℝ) / (2 ^ (n + 2) * Ctree)) := by gcongr; linarith
    have heq : Ctree * ((ε : ℝ) / (2 ^ (n + 2) * Ctree)) = (ε : ℝ) / 2 ^ (n + 2) := by
      field_simp
    linarith
  have hsum1 : ((C.b : ℝ) ^ M)⁻¹ ≤
      Ctree * (∑ n ∈ F, (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal) +
        (ε : ℝ) * (∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2))) := by
    have hε2 : ∀ n : ℕ, (ε : ℝ) / 2 ^ (n + 2) = (ε : ℝ) * ((1 / 2 : ℝ) ^ (n + 2)) :=
      fun n => by rw [one_div, inv_pow, div_eq_mul_inv]
    calc ((C.b : ℝ) ^ M)⁻¹
        ≤ ∑ n ∈ F, Ctree * (G.growInterpGauge (C.b : ℝ) (Metric.ediam (V n))).toReal := hcov_low
      _ ≤ ∑ n ∈ F, (Ctree * (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal +
            (ε : ℝ) / 2 ^ (n + 2)) := Finset.sum_le_sum hterm_le
      _ = Ctree * (∑ n ∈ F, (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal) +
            (ε : ℝ) * (∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2))) := by
          simp_rw [hε2]; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : ∑ n ∈ F, ((1 / 2 : ℝ) ^ (n + 2)) ≤ 1 / 2 := by
    have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
        (fun _ _ h => by omega)
    have hsum_val : (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 2)) = 1 / 2 := by
      have h0 : ∀ n : ℕ, (1 / 2 : ℝ) ^ (n + 2) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n :=
        fun n => by ring
      simp_rw [h0, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)]
      norm_num
    exact (hsumm.sum_le_tsum F (fun _ _ => by positivity)).trans_eq hsum_val
  have hsum_t_enn : ENNReal.ofReal
      (∑ n ∈ F, (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal) ≤
      ∑' n : ℕ, ⨆ _ : (t n).Nonempty, G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n)) := by
    have hFin : ENNReal.ofReal
        (∑ n ∈ F, (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal) =
        ∑ n ∈ F, ⨆ _ : (t n).Nonempty, G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
      have hne_top : G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n)) ≠ ⊤ := by
        have ht_ne : Metric.ediam (t n) ≠ ⊤ :=
          ne_of_lt (lt_of_le_of_lt (ht_diam n) ENNReal.ofReal_lt_top)
        rw [G.growInterpGauge_eq_ofReal_toReal hb1 ht_ne]; exact ENNReal.ofReal_ne_top
      rw [ciSup_pos hne, ENNReal.ofReal_toReal hne_top]
    rw [hFin]; exact ENNReal.sum_le_tsum F
  have hR_bound : ((C.b : ℝ) ^ M)⁻¹ / Ctree ≤
      (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
        G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal + (ε : ℝ) := by
    have hsum_t_real :
        ∑ n ∈ F, (G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal ≤
        (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
          G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal := by
      have h1 := ENNReal.toReal_mono htop hsum_t_enn
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)] at h1
    have hstep1 : ((C.b : ℝ) ^ M)⁻¹ ≤
        Ctree * (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
          G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal +
          (ε : ℝ) * (1 / 2) := by nlinarith
    have hC1 : 1 ≤ Ctree := by
      have h1 : (1 : ℝ) ≤ (C.b : ℝ) ^ (G.growTreeJ k + 2) := one_le_pow₀ hb1.le
      dsimp [Ctree]; linarith
    have hdiv := div_le_div_of_nonneg_right hstep1 hCtree_pos.le
    calc ((C.b : ℝ) ^ M)⁻¹ / Ctree
        ≤ (Ctree * (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
              G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal +
            (ε : ℝ) * (1 / 2)) / Ctree := hdiv
      _ = (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
              G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal +
            ((ε : ℝ) * (1 / 2)) / Ctree := by field_simp
      _ ≤ _ := by
          gcongr
          calc ((ε : ℝ) * (1 / 2)) / Ctree ≤ ((ε : ℝ) * (1 / 2)) / 1 :=
                div_le_div_of_nonneg_left (by positivity) one_pos hC1
            _ ≤ (ε : ℝ) := by linarith
  calc ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / Ctree)
      ≤ ENNReal.ofReal ((∑' n : ℕ, ⨆ _ : (t n).Nonempty,
            G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))).toReal + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal hR_bound
    _ = (∑' n : ℕ, ⨆ _ : (t n).Nonempty,
          G.growInterpGauge (C.b : ℝ) (Metric.ediam (t n))) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε_pos.le, ENNReal.ofReal_toReal htop,
            ENNReal.ofReal_coe_nnreal]

lemma growCantorSet_spec (G : GrowingRecData) {k : ℕ} (C : PolyDigitCode k) {x : ℝ}
    (hx : x ∈ G.growCantorSet C) :
    ∃ w : ℕ → Fin C.b,
      Tendsto (G.growEps x) atTop (nhds 0) ∧
      (∀ n : ℕ, round ((G.Q (G.growTreeJ k + n + 1) : ℝ) * x) =
        G.growCenterInt C n (growPrefix n w)) ∧
      (∀ n : ℕ, G.growDefect x (G.growTreeJ k + n + 2) = C.digit (w (n + 1))) := by
  obtain ⟨w, hw⟩ := hx
  have hQ_pos : ∀ j : ℕ, (0 : ℝ) < (G.Q j : ℝ) := fun j => by exact_mod_cast G.hQ_pos j
  have hrad_mul_lt : ∀ n : ℕ,
      (G.Q (G.growTreeJ k + n + 1) : ℝ) * G.growRadC k n < 1 / 4 := fun n => by
    have h2 := G.growRadC_twice_lt k n
    have hQ := hQ_pos (G.growTreeJ k + n + 1)
    have hmul := mul_lt_mul_of_pos_left h2 hQ
    have hlhs : (G.Q (G.growTreeJ k + n + 1) : ℝ) * (2 * G.growRadC k n) =
        2 * ((G.Q (G.growTreeJ k + n + 1) : ℝ) * G.growRadC k n) := by ring
    have hrhs : (G.Q (G.growTreeJ k + n + 1) : ℝ) *
        ((1 / 2 : ℝ) / (G.Q (G.growTreeJ k + n + 1) : ℝ)) = 1 / 2 := by field_simp
    linarith
  have hround : ∀ n : ℕ, round ((G.Q (G.growTreeJ k + n + 1) : ℝ) * x) =
      G.growCenterInt C n (growPrefix n w) := fun n => by
    have hxn := hw n
    have hdiff : |x - G.growCenter C n (growPrefix n w)| ≤ G.growRadC k n :=
      abs_sub_le_iff.mpr ⟨by linarith [hxn.2], by linarith [hxn.1]⟩
    have hQ := hQ_pos (G.growTreeJ k + n + 1)
    have hmul : |(G.Q (G.growTreeJ k + n + 1) : ℝ) * x -
        (G.growCenterInt C n (growPrefix n w) : ℝ)| ≤
        (G.Q (G.growTreeJ k + n + 1) : ℝ) * G.growRadC k n := by
      unfold growCenter at hdiff
      have heq : (G.Q (G.growTreeJ k + n + 1) : ℝ) * x -
          (G.growCenterInt C n (growPrefix n w) : ℝ) =
          (G.Q (G.growTreeJ k + n + 1) : ℝ) *
            (x - (G.growCenterInt C n (growPrefix n w) : ℝ) /
              (G.Q (G.growTreeJ k + n + 1) : ℝ)) := by field_simp
      rw [heq, abs_mul, abs_of_pos hQ]
      exact mul_le_mul_of_nonneg_left hdiff hQ.le
    exact round_eq_of_abs_sub_lt_half_grow
      (lt_of_le_of_lt hmul (lt_trans (hrad_mul_lt n) (by norm_num)))
  have hratio_zero : Tendsto (fun n : ℕ =>
      (G.Q (G.growTreeJ k + n + 1) : ℝ) / (G.Q (G.growTreeJ k + n + 2) : ℝ))
      atTop (nhds 0) :=
    G.grow_Q_div_Q_succ_tendsto_zero.comp
      ((tendsto_add_atTop_nat (G.growTreeJ k + 1)).congr (fun n => by omega))
  have heps : Tendsto (G.growEps x) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => G.growEps x (G.growTreeJ k + n + 1)) atTop (nhds 0) := by
      have hrad_zero : Tendsto (fun n : ℕ =>
          (2 * (k : ℝ) + 2) * ((G.Q (G.growTreeJ k + n + 1) : ℝ) /
            (G.Q (G.growTreeJ k + n + 2) : ℝ))) atTop (nhds 0) := by
        simpa using hratio_zero.const_mul (2 * (k : ℝ) + 2)
      have hnorm : Tendsto (fun n : ℕ => |G.growEps x (G.growTreeJ k + n + 1)|)
          atTop (nhds 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrad_zero
          (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (Filter.Eventually.of_forall fun n => ?_)
        have hxn := hw n
        have hdiff : |x - G.growCenter C n (growPrefix n w)| ≤ G.growRadC k n :=
          abs_sub_le_iff.mpr ⟨by linarith [hxn.2], by linarith [hxn.1]⟩
        have hQ := hQ_pos (G.growTreeJ k + n + 1)
        unfold growEps; rw [hround n]
        have heq : (G.Q (G.growTreeJ k + n + 1) : ℝ) * x -
            (G.growCenterInt C n (growPrefix n w) : ℝ) =
            (G.Q (G.growTreeJ k + n + 1) : ℝ) *
              (x - G.growCenter C n (growPrefix n w)) := by
          unfold growCenter; field_simp
        rw [heq, abs_mul, abs_of_pos hQ]
        calc (G.Q (G.growTreeJ k + n + 1) : ℝ) * |x - G.growCenter C n (growPrefix n w)|
            ≤ (G.Q (G.growTreeJ k + n + 1) : ℝ) * G.growRadC k n :=
              mul_le_mul_of_nonneg_left hdiff hQ.le
          _ = (2 * (k : ℝ) + 2) * ((G.Q (G.growTreeJ k + n + 1) : ℝ) /
                (G.Q (G.growTreeJ k + n + 2) : ℝ)) := by unfold growRadC; ring
      exact tendsto_zero_iff_abs_tendsto_zero.mpr hnorm
    have hid : (fun n : ℕ => G.growEps x (n + (G.growTreeJ k + 1))) =
        (fun n : ℕ => G.growEps x (G.growTreeJ k + n + 1)) := by
      ext n; congr 1; omega
    rw [← hid] at hshift
    exact (tendsto_add_atTop_iff_nat (G.growTreeJ k + 1)).mp hshift
  have hdef : ∀ n : ℕ, G.growDefect x (G.growTreeJ k + n + 2) = C.digit (w (n + 1)) := by
    intro n
    unfold growDefect
    have hidx1 : G.growTreeJ k + n + 2 + 1 = G.growTreeJ k + (n + 2) + 1 := by omega
    have hidx2 : G.growTreeJ k + n + 2 = G.growTreeJ k + (n + 1) + 1 := by omega
    have hidx0 : G.growTreeJ k + (n + 1) + 1 - 1 = G.growTreeJ k + n + 1 := by omega
    rw [hidx1, hidx2, hround (n + 2), hround (n + 1), hidx0, hround n]
    have hpre2 : (fun i : Fin (n + 1) => (growPrefix (n + 2) w) i.castSucc) =
        growPrefix (n + 1) w := rfl
    have hlast : growPrefix (n + 2) w (Fin.last (n + 1)) = w (n + 1) := rfl
    have hfst : (G.growPairOfWord C (n + 1) (growPrefix (n + 1) w)).1 =
        G.growCenterInt C n (growPrefix n w) :=
      G.growPairOfWord_fst_succ C n _
    change (G.growPairOfWord C (n + 2) (growPrefix (n + 2) w)).2 -
        G.A (G.growTreeJ k + (n + 1) + 1) *
          (G.growPairOfWord C (n + 1) (growPrefix (n + 1) w)).2 -
        (G.growPairOfWord C n (growPrefix n w)).2 = C.digit (w (n + 1))
    rw [show G.growPairOfWord C (n + 2) (growPrefix (n + 2) w) =
        let p := G.growPairOfWord C (n + 1)
          (fun i : Fin (n + 1) => (growPrefix (n + 2) w) i.castSucc)
        (p.2, G.A (G.growTreeJ k + (n + 1) + 1) * p.2 + p.1 +
          C.digit (growPrefix (n + 2) w (Fin.last (n + 1)))) from rfl, hpre2, hlast]
    dsimp only
    rw [show (G.growPairOfWord C (n + 1) (growPrefix (n + 1) w)).1 =
        (G.growPairOfWord C n (growPrefix n w)).2 from hfst]
    ring
  exact ⟨w, heps, hround, hdef⟩

lemma growCantorSet_exact_subset_levelSet (G : GrowingRecData) (k : ℕ) :
    G.growCantorSet (PolyDigitCode.exact k) ⊆ G.growLevelSet (k : ℝ≥0∞) := by
  intro x hx
  obtain ⟨w, heps, _, hdef⟩ := G.growCantorSet_spec (PolyDigitCode.exact k) hx
  have happrox := G.grow_abs_defect_approx x heps
  have hev_bound : ∀ᶠ j : ℕ in atTop,
      G.growSeq x j ≤ (k : ℝ) + abs (G.growSeq x j - abs (G.growDefect x j : ℝ)) := by
    filter_upwards [eventually_ge_atTop (G.growTreeJ k + 2)] with j hj
    obtain ⟨n, rfl⟩ : ∃ n, j = G.growTreeJ k + n + 2 := ⟨j - (G.growTreeJ k + 2), by omega⟩
    have hd : |(G.growDefect x (G.growTreeJ k + n + 2) : ℝ)| ≤ (k : ℝ) := by
      rw [hdef n]; exact_mod_cast (PolyDigitCode.exact k).abs_le (w (n + 1))
    linarith [le_abs_self (G.growSeq x (G.growTreeJ k + n + 2) -
      |(G.growDefect x (G.growTreeJ k + n + 2) : ℝ)|)]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε_pos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hev_err : ∀ᶠ j : ℕ in atTop,
      |(G.growDefect x j : ℝ)| - G.growSeq x j ∈ Metric.ball (0 : ℝ) (ε : ℝ) :=
    happrox.eventually (Metric.ball_mem_nhds 0 hε_pos)
  have hev_seq : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (G.growSeq x j) ≤ (k : ℝ≥0∞) + (ε : ℝ≥0∞) := by
    filter_upwards [hev_bound, hev_err] with j hbd herr
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_sub_comm] at herr
    have hdiv : G.growSeq x j ≤ (k : ℝ) + (ε : ℝ) := by linarith [herr.le]
    calc ENNReal.ofReal (G.growSeq x j)
        ≤ ENNReal.ofReal ((k : ℝ) + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hdiv
      _ = (k : ℝ≥0∞) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg k) hε_pos.le, ENNReal.ofReal_natCast,
            ENNReal.ofReal_coe_nnreal]
  exact limsup_le_of_le (by isBoundedDefault) hev_seq

lemma growCantorSet_binary_subset_unsignedExactLimit (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    G.growCantorSet (PolyDigitCode.binary k hk) ⊆
      G.growUnsignedExactLimitSet (k : ℝ) := by
  intro x hx
  obtain ⟨w, heps, _, hdef⟩ := G.growCantorSet_spec (PolyDigitCode.binary k hk) hx
  rw [G.grow_unsigned_exact_limit_iff_defect_binary]
  refine ⟨heps, ?_⟩
  filter_upwards [eventually_ge_atTop (G.growTreeJ k + 2)] with j hj
  obtain ⟨n, rfl⟩ : ∃ n, j = G.growTreeJ k + n + 2 := ⟨j - (G.growTreeJ k + 2), by omega⟩
  rw [hdef n]
  exact GaugeCircle.binDigitOf_mem_binary k (w (n + 1))

theorem mkMetric_grow_inter_Ioo_eq_top_of_compact_tree (G : GrowingRecData) {k : ℕ}
    (C : PolyDigitCode k) (hb2 : 2 ≤ C.b)
    {E : Set ℝ} (hKE : G.growCantorSet C ⊆ E)
    (hE_inv : ∀ {y : ℝ}, y ∈ G.growLatticeL → (fun x : ℝ => x + y) ⁻¹' E = E)
    {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (G.growInterpGauge (C.b : ℝ)) (E ∩ Set.Ioo a b) = ⊤ := by
  have hb_pos : (0 : ℝ) < (C.b : ℝ) := by exact_mod_cast C.hb
  have hb1 : (1 : ℝ) < (C.b : ℝ) := by exact_mod_cast (by omega : 1 < C.b)
  set h := G.growInterpGauge (C.b : ℝ)
  set Ctree : ℝ := 2 * (C.b : ℝ) ^ (G.growTreeJ k + 2)
  have hCtree_pos : 0 < Ctree := by positivity
  rw [eq_top_iff]
  refine le_of_forall_lt fun R hR => ?_
  have hR_ne_top : R ≠ ⊤ := hR.ne
  have hdiv0 : Tendsto (fun M : ℕ =>
      (C.b : ℝ) ^ M / (G.Q (G.growTreeJ k + M + 2) : ℝ)) atTop (nhds 0) := by
    have h0 := G.grow_pow_div_Q_tendsto_zero (C.b : ℝ)
    have h0' : Tendsto (fun M : ℕ =>
        (C.b : ℝ) ^ (M + (G.growTreeJ k + 2)) / (G.Q (M + (G.growTreeJ k + 2)) : ℝ))
        atTop (nhds 0) := h0.comp (tendsto_add_atTop_nat (G.growTreeJ k + 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0' ?_ ?_
    · intro M
      exact div_nonneg (pow_nonneg hb_pos.le _)
        (show (0 : ℝ) ≤ (G.Q (G.growTreeJ k + M + 2) : ℝ) by exact_mod_cast (G.hQ_pos _).le)
    · intro M
      have hidx : G.growTreeJ k + M + 2 = M + (G.growTreeJ k + 2) := by omega
      dsimp only; rw [hidx]
      have hQpos : (0 : ℝ) < (G.Q (M + (G.growTreeJ k + 2)) : ℝ) := by exact_mod_cast G.hQ_pos _
      exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hb1.le (by omega)) hQpos.le
  set goal_R : ℝ := max R.toReal 1
  have hgoal_pos : 0 < goal_R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set eps : ℝ := (b - a) / (12 * (2 * (k : ℝ) + 2) * Ctree * goal_R)
  have heps_pos : 0 < eps := by positivity
  obtain ⟨M, hM⟩ := (hdiv0.eventually (Iio_mem_nhds heps_pos)).exists
  let u₀ : Fin M → Fin C.b := fun _ => ⟨0, C.hb⟩
  have hsub_pos := G.mkMetric_growWordTree_subtree_pos C hb2 M u₀
  have hK_closed : IsClosed (G.growCantorSet C ∩ G.growCInterv C M u₀) :=
    (G.growCantorSet_isClosed C).inter (G.growCInterv_isClosed C M u₀)
  set N : ℕ := Nat.floor ((b - a) / (3 * G.growRadC k M))
  obtain ⟨tvec, htL, htI, hdisj⟩ := G.exists_disjoint_growLattice_translates_in_Ioo
    (c := G.growCenter C M u₀) (r := G.growRadC k M) hab (G.growRadC_pos k M)
  let piece : Fin N → Set ℝ := fun i =>
    (fun x : ℝ => x + tvec i) '' (G.growCantorSet C ∩ G.growCInterv C M u₀)
  have hpiece_meas : ∀ i : Fin N, MeasurableSet (piece i) := fun i => by
    have hcls : IsClosed (piece i) := by
      have himg : piece i =
          (fun y : ℝ => y - tvec i) ⁻¹' (G.growCantorSet C ∩ G.growCInterv C M u₀) := by
        ext y; simp [piece, sub_eq_add_neg]
      rw [himg]; exact hK_closed.preimage (continuous_id.sub continuous_const)
    exact hcls.measurableSet
  have hpiece_sub : ∀ i : Fin N, piece i ⊆ E ∩ Set.Ioo a b := by
    intro i y hy; rcases hy with ⟨x, hx, rfl⟩
    refine ⟨?_, htI i ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩⟩
    have hxE : x ∈ E := hKE hx.1
    rw [← hE_inv (htL i)] at hxE; exact hxE
  have hpiece_disj : Pairwise (fun i j => Disjoint (piece i) (piece j)) := fun i j hij =>
    Set.disjoint_left.mpr fun y hyi hyj => by
      rcases hyi with ⟨xi, hxi, rfl⟩; rcases hyj with ⟨xj, hxj, heq⟩
      have hmem_i : xi + tvec i ∈ Set.Icc (G.growCenter C M u₀ + tvec i - G.growRadC k M)
          (G.growCenter C M u₀ + tvec i + G.growRadC k M) :=
        ⟨by linarith [hxi.2.1], by linarith [hxi.2.2]⟩
      have hmem_j : xi + tvec i ∈ Set.Icc (G.growCenter C M u₀ + tvec j - G.growRadC k M)
          (G.growCenter C M u₀ + tvec j + G.growRadC k M) := by
        change xj + tvec j = xi + tvec i at heq; rw [← heq]
        exact ⟨by linarith [hxj.2.1], by linarith [hxj.2.2]⟩
      exact Set.disjoint_left.mp (hdisj hij) hmem_i hmem_j
  have hmeas_sum : (∑ i : Fin N, Measure.mkMetric h (piece i)) ≤
      Measure.mkMetric h (E ∩ Set.Ioo a b) := by
    calc (∑ i : Fin N, Measure.mkMetric h (piece i))
        = ∑' i : Fin N, Measure.mkMetric h (piece i) := (tsum_fintype _).symm
      _ = Measure.mkMetric h (⋃ i : Fin N, piece i) := (measure_iUnion hpiece_disj hpiece_meas).symm
      _ ≤ Measure.mkMetric h (E ∩ Set.Ioo a b) := measure_mono (Set.iUnion_subset hpiece_sub)
  have hpiece_eq : ∀ i : Fin N, Measure.mkMetric h (piece i) =
      Measure.mkMetric h (G.growCantorSet C ∩ G.growCInterv C M u₀) := fun i => by
    dsimp [piece]; simpa [add_comm] using GaugeExact.mkMetric_image_add h (tvec i)
      (G.growCantorSet C ∩ G.growCInterv C M u₀)
  have hN_ge : (N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) > goal_R := by
    have hQ2 : (0 : ℝ) < (G.Q (G.growTreeJ k + M + 2) : ℝ) := by exact_mod_cast G.hQ_pos _
    have hinv_gt : 1 / eps < (G.Q (G.growTreeJ k + M + 2) : ℝ) / (C.b : ℝ) ^ M := by
      have hpos : 0 < (C.b : ℝ) ^ M / (G.Q (G.growTreeJ k + M + 2) : ℝ) := by positivity
      have h1 := one_div_lt_one_div_of_lt hpos hM
      have hrhs : 1 / ((C.b : ℝ) ^ M / (G.Q (G.growTreeJ k + M + 2) : ℝ)) =
          (G.Q (G.growTreeJ k + M + 2) : ℝ) / (C.b : ℝ) ^ M := one_div_div _ _
      linarith [h1, hrhs]
    have hN_gt : (b - a) / (3 * G.growRadC k M) - 1 < (N : ℝ) := by
      dsimp [N]; linarith [Nat.lt_floor_add_one ((b - a) / (3 * G.growRadC k M))]
    have hratio_eq : ((b - a) / (3 * G.growRadC k M)) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) =
        ((b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree)) *
          ((G.Q (G.growTreeJ k + M + 2) : ℝ) / (C.b : ℝ) ^ M) := by
      unfold growRadC; field_simp
    have hbig : 4 * goal_R <
        ((b - a) / (3 * G.growRadC k M)) * (((C.b : ℝ) ^ M)⁻¹ / Ctree) := by
      rw [hratio_eq]
      have hmul := mul_lt_mul_of_pos_left hinv_gt
        (by positivity : 0 < (b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree))
      have heq4 : ((b - a) / (3 * (2 * (k : ℝ) + 2) * Ctree)) * (1 / eps) = 4 * goal_R := by
        dsimp [eps]; field_simp; ring
      linarith
    have h1 : (((C.b : ℝ) ^ M)⁻¹ / Ctree) ≤ 1 := by
      have hC1 : 1 ≤ Ctree := by
        have h1' : (1 : ℝ) ≤ (C.b : ℝ) ^ (G.growTreeJ k + 2) := one_le_pow₀ hb1.le
        dsimp [Ctree]; linarith
      calc (((C.b : ℝ) ^ M)⁻¹ / Ctree) ≤ 1 / 1 := by
            gcongr; exact inv_le_one_of_one_le₀ (one_le_pow₀ hb1.le)
        _ = 1 := by norm_num
    have hpos_m : 0 < ((C.b : ℝ) ^ M)⁻¹ / Ctree := by positivity
    have hgoal1 : 1 ≤ goal_R := le_max_right _ _
    have hNm := mul_lt_mul_of_pos_right hN_gt hpos_m
    linarith [mul_sub_right_distrib ((b - a) / (3 * G.growRadC k M)) 1 (((C.b : ℝ) ^ M)⁻¹ / Ctree),
      one_mul (((C.b : ℝ) ^ M)⁻¹ / Ctree)]
  have hR_lt_prod : R < ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) := by
    calc R ≤ ENNReal.ofReal goal_R := by
          rw [← ENNReal.ofReal_toReal hR_ne_top]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
      _ < ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) :=
          (ENNReal.ofReal_lt_ofReal_iff (lt_trans hgoal_pos hN_ge)).mpr hN_ge
  have hprod_le : ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree)) ≤
      Measure.mkMetric h (E ∩ Set.Ioo a b) := by
    calc ENNReal.ofReal ((N : ℝ) * (((C.b : ℝ) ^ M)⁻¹ / Ctree))
        = ((N : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((C.b : ℝ) ^ M)⁻¹ / Ctree) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      _ ≤ ((N : ℕ) : ℝ≥0∞) * Measure.mkMetric h (G.growCantorSet C ∩ G.growCInterv C M u₀) := by
          gcongr
      _ = ∑ i : Fin N, Measure.mkMetric h (piece i) := by simp [hpiece_eq, Finset.sum_const]
      _ ≤ Measure.mkMetric h (E ∩ Set.Ioo a b) := hmeas_sum
  exact lt_of_lt_of_le hR_lt_prod hprod_le

/-! #### Part 6.4: Main Universal 3-Way Splitting & Dichotomy Theorems on `ℝ` and `UnitAddCircle` -/

def growCircleStrictLevel (G : GrowingRecData) (k : ℕ) : Set UnitAddCircle :=
  GaugeCircle.circleProj '' G.growStrictLevel k

def growCircleLevelSet (G : GrowingRecData) (t : ℝ≥0∞) : Set UnitAddCircle :=
  GaugeCircle.circleProj '' G.growLevelSet t

def growCircleExactLevel (G : GrowingRecData) (k : ℕ) : Set UnitAddCircle :=
  GaugeCircle.circleProj '' G.growExactLevel k

def growCircleUnsignedExactLimitSet (G : GrowingRecData) (t : ℝ) : Set UnitAddCircle :=
  GaugeCircle.circleProj '' G.growUnsignedExactLimitSet t

theorem mkMetric_growCritGauge_growExactLevel_inter_Ioo_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k ∩ Set.Ioo a b) = ⊤ := by
  have hsub_eq_top : Measure.mkMetric (G.growCritGauge k)
      (G.growLevelSet (k : ℝ≥0∞) ∩ Set.Ioo a b) = ⊤ := by
    have hCode := G.mkMetric_grow_inter_Ioo_eq_top_of_compact_tree (PolyDigitCode.exact k)
      (by simp [PolyDigitCode.exact]; omega) (G.growCantorSet_exact_subset_levelSet k)
      (fun {y} hy => G.growLevelSet_add_growLatticeL (k : ℝ≥0∞) hy) hab
    simpa [growCritGauge, PolyDigitCode.exact] using hCode
  have hcov : G.growLevelSet (k : ℝ≥0∞) ∩ Set.Ioo a b ⊆
      (G.growExactLevel k ∩ Set.Ioo a b) ∪ G.growStrictLevel k := by
    rintro x ⟨hx_le, hxI⟩
    rcases eq_or_lt_of_le (show G.growLambda x ≤ (k : ℝ≥0∞) from hx_le) with h_eq | h_lt
    · exact Or.inl ⟨h_eq, hxI⟩
    · exact Or.inr h_lt
  have hle : Measure.mkMetric (G.growCritGauge k) (G.growLevelSet (k : ℝ≥0∞) ∩ Set.Ioo a b) ≤
      Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k ∩ Set.Ioo a b) +
        Measure.mkMetric (G.growCritGauge k) (G.growStrictLevel k) :=
    le_trans (measure_mono hcov) (measure_union_le _ _)
  rw [hsub_eq_top, G.mkMetric_growCritGauge_growStrictLevel_null hk, add_zero] at hle
  exact eq_top_iff.mpr hle

theorem mkMetric_growCritGauge_growExactLevel_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k) = ⊤ := by
  rw [eq_top_iff, ← G.mkMetric_growCritGauge_growExactLevel_inter_Ioo_eq_top hk zero_lt_one]
  exact measure_mono Set.inter_subset_left

theorem mkMetric_growCritGauge_growExactLevel_pos (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    0 < Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k) := by
  rw [G.mkMetric_growCritGauge_growExactLevel_eq_top hk]; exact ENNReal.zero_lt_top

theorem mkMetric_growCritGauge_growExactLevel_inter_open_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set ℝ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k ∩ U) = ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hU_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ U := fun y hy => by
    apply hball; rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  rw [eq_top_iff, ← G.mkMetric_growCritGauge_growExactLevel_inter_Ioo_eq_top hk
    (by linarith : x₀ - ε < x₀ + ε)]
  exact measure_mono (Set.inter_subset_inter_right _ hsub)

theorem mkMetric_growBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b) :
    Measure.mkMetric G.growBinaryGauge (G.growUnsignedExactLimitSet (k : ℝ) ∩ Set.Ioo a b) = ⊤ := by
  have hCode := G.mkMetric_grow_inter_Ioo_eq_top_of_compact_tree (PolyDigitCode.binary k hk)
    (by simp [PolyDigitCode.binary]) (G.growCantorSet_binary_subset_unsignedExactLimit hk)
    (fun {y} hy => G.growUnsignedExactLimit_add_growLatticeL _ hy) hab
  simpa [growBinaryGauge, PolyDigitCode.binary] using hCode

theorem mkMetric_growBinaryGauge_unsignedExactLimit_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric G.growBinaryGauge (G.growUnsignedExactLimitSet (k : ℝ)) = ⊤ := by
  rw [eq_top_iff, ← G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top hk zero_lt_one]
  exact measure_mono Set.inter_subset_left

theorem mkMetric_growBinaryGauge_unsignedExactLimit_pos (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    0 < Measure.mkMetric G.growBinaryGauge (G.growUnsignedExactLimitSet (k : ℝ)) := by
  rw [G.mkMetric_growBinaryGauge_unsignedExactLimit_eq_top hk]; exact ENNReal.zero_lt_top

theorem mkMetric_growBinaryGauge_unsignedExactLimit_inter_open_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set ℝ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric G.growBinaryGauge (G.growUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hU_ne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ U := fun y hy => by
    apply hball; rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  rw [eq_top_iff, ← G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top hk
    (by linarith : x₀ - ε < x₀ + ε)]
  exact measure_mono (Set.inter_subset_inter_right _ hsub)

theorem mkMetric_growCritGauge_growCircleStrictLevel_null (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growCircleStrictLevel k) = 0 :=
  le_antisymm
    ((GaugeCircle.mkMetric_circleProj_image_le (G.growCritGauge k)
      (G.growCritGauge_mono k hk) _).trans_eq
      (G.mkMetric_growCritGauge_growStrictLevel_null hk)) bot_le

theorem mkMetric_growCritGauge_growCircleExactLevel_inter_open_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (G.growCritGauge k) (G.growCircleExactLevel k ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ :=
    GaugeCircle.exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := G.growExactLevel k ∩ Set.Ioo a b
  have hA_img : GaugeCircle.circleProj '' A ⊆ G.growCircleExactLevel k ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩; exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle := le_trans
    (GaugeCircle.mkMetric_le_circleProj_image_of_subset_Ioo (G.growCritGauge k)
      (G.growCritGauge_mono k hk) hwidth Set.inter_subset_right)
    (measure_mono hA_img)
  rw [G.mkMetric_growCritGauge_growExactLevel_inter_Ioo_eq_top hk hab] at hle
  exact eq_top_iff.mpr hle

theorem mkMetric_growCritGauge_growCircleExactLevel_eq_top (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growCircleExactLevel k) = ⊤ := by
  simpa using G.mkMetric_growCritGauge_growCircleExactLevel_inter_open_eq_top hk isOpen_univ
    ⟨0, Set.mem_univ _⟩

theorem growCircleExactLevel_critGauge_sigma_finite (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k) :
    ∃ E : ℕ → Set UnitAddCircle, G.growCircleExactLevel k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (G.growCritGauge k) (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := G.growExactLevel_critGauge_sigma_finite hk
  refine ⟨fun i => GaugeCircle.circleProj '' (E i), ?_, fun i => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · exact lt_of_le_of_lt (GaugeCircle.mkMetric_circleProj_image_le (G.growCritGauge k)
      (G.growCritGauge_mono k hk) _) (hfin i)

theorem mkMetric_growCircleUnsignedExactLimit_null_of_critGauge (G : GrowingRecData)
    {k : ℕ} (hk : 1 ≤ k) :
    Measure.mkMetric (G.growCritGauge k) (G.growCircleUnsignedExactLimitSet (k : ℝ)) = 0 :=
  le_antisymm
    ((GaugeCircle.mkMetric_circleProj_image_le (G.growCritGauge k)
      (G.growCritGauge_mono k hk) _).trans_eq
      (G.mkMetric_growUnsignedExactLimit_null_of_critGauge hk)) bot_le

theorem mkMetric_growBinaryGauge_growCircleUnsignedExactLimit_inter_open_eq_top
    (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric G.growBinaryGauge (G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ :=
    GaugeCircle.exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := G.growUnsignedExactLimitSet (k : ℝ) ∩ Set.Ioo a b
  have hA_img : GaugeCircle.circleProj '' A ⊆ G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩; exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle := le_trans
    (GaugeCircle.mkMetric_le_circleProj_image_of_subset_Ioo G.growBinaryGauge
      G.growBinaryGauge_mono hwidth Set.inter_subset_right)
    (measure_mono hA_img)
  rw [G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_Ioo_eq_top hk hab] at hle
  exact eq_top_iff.mpr hle

theorem growCircleUnsignedExactLimit_binaryGauge_sigma_finite (G : GrowingRecData) (k : ℕ) :
    ∃ E : ℕ → Set UnitAddCircle, G.growCircleUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric G.growBinaryGauge (E i) < ⊤ := by
  obtain ⟨E, hcov, hfin⟩ := G.growUnsignedExactLimit_binaryGauge_sigma_finite k
  refine ⟨fun i => GaugeCircle.circleProj '' (E i), ?_, fun i => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · exact lt_of_le_of_lt (GaugeCircle.mkMetric_circleProj_image_le G.growBinaryGauge
      G.growBinaryGauge_mono _) (hfin i)

/-- Universal three-way critical gauge splitting on `ℝ` and `UnitAddCircle`. -/
theorem grow_three_way_gauge_splitting (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k) :
    (Measure.mkMetric (G.growCritGauge k) (G.growStrictLevel k) = 0 ∧
      Measure.mkMetric (G.growCritGauge k) (G.growUnsignedExactLimitSet (k : ℝ)) = 0 ∧
      Measure.mkMetric (G.growCritGauge k) (G.growCircleStrictLevel k) = 0 ∧
      Measure.mkMetric (G.growCritGauge k) (G.growCircleUnsignedExactLimitSet (k : ℝ)) = 0) ∧
    ((∃ E : ℕ → Set ℝ, G.growExactLevel k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric (G.growCritGauge k) (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle, G.growCircleExactLevel k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric (G.growCritGauge k) (E i) < ⊤) ∧
      (∃ E : ℕ → Set ℝ, G.growUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric G.growBinaryGauge (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle, G.growCircleUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric G.growBinaryGauge (E i) < ⊤)) ∧
    ((∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric (G.growCritGauge k) (G.growCircleExactLevel k ∩ U) = ⊤) ∧
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric G.growBinaryGauge (G.growUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric G.growBinaryGauge
          (G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤)) :=
  ⟨⟨G.mkMetric_growCritGauge_growStrictLevel_null hk,
    G.mkMetric_growUnsignedExactLimit_null_of_critGauge hk,
    G.mkMetric_growCritGauge_growCircleStrictLevel_null hk,
    G.mkMetric_growCircleUnsignedExactLimit_null_of_critGauge hk⟩,
   ⟨G.growExactLevel_critGauge_sigma_finite hk,
    G.growCircleExactLevel_critGauge_sigma_finite hk,
    G.growUnsignedExactLimit_binaryGauge_sigma_finite k,
    G.growCircleUnsignedExactLimit_binaryGauge_sigma_finite k⟩,
   ⟨fun hUo hUne => G.mkMetric_growCritGauge_growExactLevel_inter_open_eq_top hk hUo hUne,
    fun hUo hUne => G.mkMetric_growCritGauge_growCircleExactLevel_inter_open_eq_top hk hUo hUne,
    fun hUo hUne => G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_open_eq_top hk hUo hUne,
    fun hUo hUne =>
      G.mkMetric_growBinaryGauge_growCircleUnsignedExactLimit_inter_open_eq_top hk hUo hUne⟩⟩

theorem growExactLevel_slow_gauge_non_sigma_finite (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → G.growCritGauge k r ≤ (ε : ℝ≥0∞) * g r) :
    (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
      Measure.mkMetric g (G.growExactLevel k ∩ U) = ⊤ ∧
      ¬ ∃ E : ℕ → Set ℝ, G.growExactLevel k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
    (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
      Measure.mkMetric g (G.growCircleExactLevel k ∩ U) = ⊤ ∧
      ¬ ∃ E : ℕ → Set UnitAddCircle, G.growCircleExactLevel k ∩ U ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) := by
  refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
  · have hpos : 0 < Measure.mkMetric (G.growCritGauge k) (G.growExactLevel k ∩ U) := by
      rw [G.mkMetric_growCritGauge_growExactLevel_inter_open_eq_top hk hUo hUne]
      exact ENNReal.zero_lt_top
    exact GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero
      (G.growCritGauge k) g hratio hpos
  · have hpos : 0 < Measure.mkMetric (G.growCritGauge k) (G.growCircleExactLevel k ∩ U) := by
      rw [G.mkMetric_growCritGauge_growCircleExactLevel_inter_open_eq_top hk hUo hUne]
      exact ENNReal.zero_lt_top
    exact GaugeCircle.not_countable_union_finite_of_ratio_tendsto_zero_circle
      (G.growCritGauge k) g hratio hpos

theorem growExactLevel_fast_gauge_null (G : GrowingRecData) (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hfast : Tendsto (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop (nhds 0)) :
    Measure.mkMetric g (G.growExactLevel k) = 0 ∧
    Measure.mkMetric g (G.growCircleExactLevel k) = 0 := by
  have hlim0 : liminf (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop = 0 := hfast.liminf_eq
  have hℝ : Measure.mkMetric g (G.growExactLevel k) = 0 :=
    measure_mono_null (fun _ hx => le_of_eq hx)
      (G.mkMetric_growLevelSet_null_of_liminf_zero k g hg hlim0)
  have hT : Measure.mkMetric g (G.growCircleExactLevel k) = 0 :=
    le_antisymm ((GaugeCircle.mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le
  exact ⟨hℝ, hT⟩

theorem growExactLevel_power_gauge_dichotomy (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) :
    (β < 2 * (k : ℝ) + 1 →
      ∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric (G.growInterpGauge β) (G.growExactLevel k ∩ U) = ⊤ ∧
        ¬ ∃ E : ℕ → Set ℝ, G.growExactLevel k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric (G.growInterpGauge β) (E i) < ⊤) ∧
    (2 * (k : ℝ) + 1 < β →
      Measure.mkMetric (G.growInterpGauge β) (G.growExactLevel k) = 0 ∧
      Measure.mkMetric (G.growInterpGauge β) (G.growCircleExactLevel k) = 0) := by
  constructor
  · intro hlt U hUo hUne
    exact (G.growExactLevel_slow_gauge_non_sigma_finite hk
      (G.growInterpGauge β) (G.growInterpGauge_ratio_tendsto_zero hβ1 hlt)).1 hUo hUne
  · intro hgt
    apply G.growExactLevel_fast_gauge_null k (G.growInterpGauge β) (G.growInterpGauge_mono hβ1)
    have hpow0 : Tendsto (fun n : ℕ => ((2 * (k : ℝ) + 1) / β) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one (by linarith)).mpr hgt)
    have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 * (k : ℝ) + 1) / β) ^ n))
        atTop (nhds 0) := by simpa using ENNReal.tendsto_ofReal hpow0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof0
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop G.J₀] with n hn
    unfold growNormalizedGaugeCost
    rw [G.growInterpGauge_at_inv_Q hβ1 hn, ← ENNReal.ofReal_mul (pow_nonneg (by positivity) n)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_pow, zpow_neg, zpow_natCast]
    simp [div_eq_mul_inv]

/-- Universal Euclidean power-gauge dichotomy
(`r ↦ r^s` vanishes on `Λ_G < ⊤`, equals `⊤` on `Λ_G = ⊤`). -/
theorem grow_power_gauge_dichotomy (G : GrowingRecData) {s : ℝ} (_hs : 0 < s) :
    dimH G.growFiniteSet = 0 ∧
    (∀ {a b : ℝ}, a < b → dimH (G.growInfiniteSet ∩ Set.Ioo a b) = 1) := by
  refine ⟨G.dimH_growFiniteSet_eq_zero, fun {a b} hab => ?_⟩
  have hsub : G.growInfiniteSet ∩ Set.Icc a b ⊆ G.growInfiniteSet ∩ Set.Ioo a b ∪ {a, b} := by
    rintro x ⟨hx, hxab⟩
    rcases eq_or_lt_of_le hxab.1 with rfl | hlt
    · exact Or.inr (by simp)
    · rcases eq_or_lt_of_le hxab.2 with rfl | hrt
      · exact Or.inr (by simp)
      · exact Or.inl ⟨hx, hlt, hrt⟩
  have hle1 : dimH (G.growInfiniteSet ∩ Set.Ioo a b) ≤ 1 :=
    (dimH_mono (Set.inter_subset_left)).trans (GaugeExact.dimH_real_subset_le_one _)
  have hfin : dimH ({a, b} : Set ℝ) = 0 :=
    (Set.Finite.countable (by simp : ({a, b} : Set ℝ).Finite)).dimH_zero
  have hge1 : 1 ≤ dimH (G.growInfiniteSet ∩ Set.Ioo a b) := by
    have hm := dimH_mono hsub
    rw [G.dimH_growInfiniteSet_inter_Icc_eq_one hab, dimH_union, hfin] at hm
    simpa using hm
  exact le_antisymm hle1 hge1

theorem growExactLevel_liminf_four_way (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (G.growNormalizedGaugeCost (2 * (k : ℝ) + 1) g) atTop
    (ρ = 0 → Measure.mkMetric g (G.growExactLevel k) = 0 ∧
             Measure.mkMetric g (G.growCircleExactLevel k) = 0) ∧
    (ρ < ⊤ →
      (∃ E : ℕ → Set ℝ, G.growExactLevel k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle, G.growCircleExactLevel k ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤)) ∧
    (0 < ρ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (G.growExactLevel k ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (G.growCircleExactLevel k ∩ U) = ⊤)) ∧
    (ρ = ⊤ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set ℝ, G.growExactLevel k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set UnitAddCircle, G.growCircleExactLevel k ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  intro ρ; refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have hℝ : Measure.mkMetric g (G.growExactLevel k) = 0 :=
      measure_mono_null (fun _ hx => le_of_eq hx)
        (G.mkMetric_growLevelSet_null_of_liminf_zero k g hg h0)
    exact ⟨hℝ, le_antisymm ((GaugeCircle.mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le⟩
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := G.growLevelSet_sigma_finite_of_liminf_lt_top k g hg hfin
    refine ⟨⟨E, Set.Subset.trans (fun _ hx => le_of_eq hx) hcov, hE⟩,
      fun i => GaugeCircle.circleProj '' (E i), ?_, fun i => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (le_of_eq hx))
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
    · exact lt_of_le_of_lt (GaugeCircle.mkMetric_circleProj_image_le g hg _) (hE i)
  · intro hpos
    obtain ⟨c, δ, hc_pos, hδ_pos, hle⟩ := G.exists_growInterpGauge_le_mul_of_liminf_pos
      (GaugeCircle.critGauge_base_gt_one k hk) g hg hpos
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hcmp := GaugeExact.mkMetric_le_mul_of_eventually_le (G.growCritGauge k) g c hδ_pos hle
        (G.growExactLevel k ∩ U)
      rw [G.mkMetric_growCritGauge_growExactLevel_inter_open_eq_top hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g (G.growExactLevel k ∩ U) < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
    · have hcmp := GaugeCircle.mkMetric_le_mul_of_eventually_le_circle (G.growCritGauge k)
        g c hδ_pos hle (G.growCircleExactLevel k ∩ U)
      rw [G.mkMetric_growCritGauge_growCircleExactLevel_inter_open_eq_top hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g (G.growCircleExactLevel k ∩ U) < ⊤ :=
        lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
  · intro htop
    have hratio := G.growInterpGauge_ratio_tendsto_zero_of_liminf_top
      (GaugeCircle.critGauge_base_gt_one k hk) g hg htop
    exact ⟨fun hUo hUne =>
        (G.growExactLevel_slow_gauge_non_sigma_finite hk g hratio).1 hUo hUne |>.2,
      fun hUo hUne =>
        (G.growExactLevel_slow_gauge_non_sigma_finite hk g hratio).2 hUo hUne |>.2⟩

theorem growUnsignedExactLimit_liminf_four_way (G : GrowingRecData) {k : ℕ} (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g) :
    let ρ := liminf (G.growNormalizedGaugeCost 2 g) atTop
    (ρ = 0 → Measure.mkMetric g (G.growUnsignedExactLimitSet (k : ℝ)) = 0 ∧
             Measure.mkMetric g (G.growCircleUnsignedExactLimitSet (k : ℝ)) = 0) ∧
    (ρ < ⊤ →
      (∃ E : ℕ → Set ℝ, G.growUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∃ E : ℕ → Set UnitAddCircle, G.growCircleUnsignedExactLimitSet (k : ℝ) ⊆ ⋃ i, E i ∧
        ∀ i, Measure.mkMetric g (E i) < ⊤)) ∧
    (0 < ρ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (G.growUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        Measure.mkMetric g (G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U) = ⊤)) ∧
    (ρ = ⊤ →
      (∀ {U : Set ℝ}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set ℝ, G.growUnsignedExactLimitSet (k : ℝ) ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤) ∧
      (∀ {U : Set UnitAddCircle}, IsOpen U → U.Nonempty →
        ¬ ∃ E : ℕ → Set UnitAddCircle,
          G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U ⊆ ⋃ i, E i ∧
          ∀ i, Measure.mkMetric g (E i) < ⊤)) := by
  intro ρ; refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have hℝ := G.mkMetric_growUnsignedExactLimit_null_of_liminf_zero k g hg h0
    exact ⟨hℝ, le_antisymm ((GaugeCircle.mkMetric_circleProj_image_le g hg _).trans_eq hℝ) bot_le⟩
  · intro hfin
    obtain ⟨E, hcov, hE⟩ := G.growUnsignedExactLimit_sigma_finite_of_liminf_lt_top k g hg hfin
    refine ⟨⟨E, hcov, hE⟩, fun i => GaugeCircle.circleProj '' (E i), ?_, fun i => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
    · exact lt_of_le_of_lt (GaugeCircle.mkMetric_circleProj_image_le g hg _) (hE i)
  · intro hpos
    obtain ⟨c, δ, hc_pos, hδ_pos, hle⟩ := G.exists_growInterpGauge_le_mul_of_liminf_pos
      (by norm_num : (1 : ℝ) < 2) g hg hpos
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hcmp := GaugeExact.mkMetric_le_mul_of_eventually_le G.growBinaryGauge g c hδ_pos hle
        (G.growUnsignedExactLimitSet (k : ℝ) ∩ U)
      rw [G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_open_eq_top hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g _ < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
    · have hcmp := GaugeCircle.mkMetric_le_mul_of_eventually_le_circle G.growBinaryGauge
        g c hδ_pos hle (G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U)
      rw [G.mkMetric_growBinaryGauge_growCircleUnsignedExactLimit_inter_open_eq_top
        hk hUo hUne] at hcmp
      by_contra hlt_top
      have hfin : Measure.mkMetric g _ < ⊤ := lt_top_iff_ne_top.mpr hlt_top
      exact (ENNReal.mul_lt_top ENNReal.coe_lt_top hfin).ne (eq_top_iff.mpr hcmp)
  · intro htop
    have hratio := G.growInterpGauge_ratio_tendsto_zero_of_liminf_top
      (by norm_num : (1 : ℝ) < 2) g hg htop
    refine ⟨fun {U} hUo hUne => ?_, fun {U} hUo hUne => ?_⟩
    · have hpos : 0 < Measure.mkMetric G.growBinaryGauge
          (G.growUnsignedExactLimitSet (k : ℝ) ∩ U) := by
        rw [G.mkMetric_growBinaryGauge_unsignedExactLimit_inter_open_eq_top hk hUo hUne]
        exact ENNReal.zero_lt_top
      exact (GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero
        G.growBinaryGauge g hratio hpos).2
    · have hpos : 0 < Measure.mkMetric G.growBinaryGauge
          (G.growCircleUnsignedExactLimitSet (k : ℝ) ∩ U) := by
        rw [G.mkMetric_growBinaryGauge_growCircleUnsignedExactLimit_inter_open_eq_top
          hk hUo hUne]
        exact ENNReal.zero_lt_top
      exact (GaugeCircle.not_countable_union_finite_of_ratio_tendsto_zero_circle
        G.growBinaryGauge g hratio hpos).2

end GrowingRecData

end

end GeneralGrowingRec

