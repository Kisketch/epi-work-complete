import EpiFormal.TransferOperatorDim

/-!
# Resolvent Test Functions, Global Strict Separation (`∀ m ≥ 2`), and
# Reciprocal-Fibonacci Two-Term Asymptotics (`ResidueAsymptotic`)

Unconditionally proves:
1. **Exact Resolvent Functional Identity**: using metallic-mean convergent denominators
   `metalQ r n` (`metalQ 1 n = Nat.fib (n + 1)`), the infinite series
   `resolventV r s x = ∑' n, (metalQ r n + metalQPrev r n * x) ^ (-(2 * s))`
   satisfies the exact Gauss-branch identity
   `(r + x) ^ (-(2 * s)) * resolventV r s (1 / (r + x)) = resolventV r s x - 1`.
2. **Non-Asymptotic Resolvent Criteria**: explicit transfer-operator upper and lower
   dimension criteria `dimH_residueConstSet_le_of_resolvent` and
   `le_dimH_residueConstSet_of_resolvent` (and constant-`1` criteria for `F_{m,m}`),
   requiring no Bowen pressure formula.
3. **Global Strict Separation (`dimH_residueConstSet_mm_lt_m1`)**:
   `∀ m ≥ 2, dimH F_{m,m} < dimH F_{m,1} = dimH E_m` unconditionally for every integer
   modulus `m ≥ 2` (resolving all infinitely many moduli beyond `m ≤ 6`).
4. **Two-Term Reciprocal-Fibonacci & Metallic-Constant Asymptotics**:
   * `dimH F_{m,r} = 1/2 + C_r / (2m) - C_r^2 (log m) / (2m^2) + O_r(1/m^2)`,
     with `C_1 = ψ_Fib = ∑' n ≥ 1, 1 / F_n` for `F_{m,1}` and `E_m`;
   * `dimH F_{m,m} = 1/2 + 1 / (2m) - (log m) / (2m^2) + O(1/m^2)`;
   * Exact first-order constant ratios `(dimH F_{m,r} - 1/2) / (dimH F_{m,m} - 1/2) → C_r`
     (in particular `→ ψ_Fib` for `F_{m,1}` and `E_m`), yielding eventual strict
     monotonicity `dimH F_{m,r₂} < dimH F_{m,r₁}` whenever `1 ≤ r₁ < r₂`.
-/

namespace ResidueAsymptotic

open Set Filter ENNReal Metric Real MeasureTheory
open ResidueModGeneral TransferOperatorDim

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Metallic-mean convergent denominators and constants `C_r` -/

/-- Convergent-like denominators `q_n(r)` with `q_0 = 1`, `q_1 = r`, `q_{n+2} = r * q_{n+1} + q_n`. -/
def metalQ (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => r
  | n + 2 => r * metalQ r (n + 1) + metalQ r n

/-- Shifted predecessor denominator `q_{n-1}(r)` with `q_{-1} = 0`. -/
def metalQPrev (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => metalQ r n

@[simp] lemma metalQ_zero (r : ℕ) : metalQ r 0 = 1 := rfl
@[simp] lemma metalQ_one (r : ℕ) : metalQ r 1 = r := rfl
@[simp] lemma metalQ_succ_succ (r n : ℕ) :
    metalQ r (n + 2) = r * metalQ r (n + 1) + metalQ r n := rfl
@[simp] lemma metalQPrev_zero (r : ℕ) : metalQPrev r 0 = 0 := rfl
@[simp] lemma metalQPrev_succ (r n : ℕ) : metalQPrev r (n + 1) = metalQ r n := rfl

lemma metalQ_one_eq_fib (n : ℕ) : metalQ 1 n = Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [Nat.fib_one]
    | 1 => simp [Nat.fib_two]
    | k + 2 =>
      rw [metalQ_succ_succ, one_mul, ih (k + 1) (by omega), ih k (by omega), add_comm]
      exact (Nat.fib_add_two).symm

lemma metalQ_pos {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 0 < metalQ r n := by
  match n with
  | 0 => simp
  | 1 => simp only [metalQ]; omega
  | k + 2 =>
    have h1 := metalQ_pos hr (k + 1)
    have h0 := metalQ_pos hr k
    rw [metalQ_succ_succ]
    nlinarith

lemma metalQPrev_le_metalQ {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : metalQPrev r n ≤ metalQ r n := by
  match n with
  | 0 => simp
  | 1 => simp only [metalQ, metalQPrev]; omega
  | k + 2 =>
    rw [metalQPrev_succ, metalQ_succ_succ]
    have h0 : metalQ r (k + 1) ≤ r * metalQ r (k + 1) := Nat.le_mul_of_pos_left _ hr
    omega

lemma metalQ_two_step_ge {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 2 * metalQ r n ≤ metalQ r (n + 2) := by
  match n with
  | 0 =>
    rw [metalQ_zero, metalQ_succ_succ, metalQ_one, metalQ_zero]
    nlinarith
  | k + 1 =>
    have hk : metalQ r (k + 1) ≤ metalQ r (k + 2) := by
      simpa [metalQPrev_succ] using metalQPrev_le_metalQ hr (k + 2)
    rw [metalQ_succ_succ]
    have hmul : metalQ r (k + 2) ≤ r * metalQ r (k + 2) := Nat.le_mul_of_pos_left _ hr
    linarith

lemma metalQ_pow_two_le {r : ℕ} (hr : 1 ≤ r) (n : ℕ) : 2 ^ (n / 2) ≤ metalQ r n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp
    | 1 => simp only [metalQ]; omega
    | k + 2 =>
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [hdiv, pow_succ']
      exact le_trans (Nat.mul_le_mul_left 2 (ih k (by omega))) (metalQ_two_step_ge hr k)

lemma metalQ_le_of_le {r₁ r₂ : ℕ} (h : r₁ ≤ r₂) (n : ℕ) : metalQ r₁ n ≤ metalQ r₂ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp
    | 1 => simpa using h
    | k + 2 =>
      rw [metalQ_succ_succ, metalQ_succ_succ]
      exact add_le_add (Nat.mul_le_mul h (ih (k + 1) (by omega))) (ih k (by omega))

lemma metalQ_lt_of_lt {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (h : r₁ < r₂) {n : ℕ} (hn : 1 ≤ n) :
    metalQ r₁ n < metalQ r₂ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => omega
    | 1 => simpa using h
    | k + 2 =>
      rw [metalQ_succ_succ, metalQ_succ_succ]
      have h1 := metalQ_pos hr₁ (k + 1)
      have hmul : r₁ * metalQ r₁ (k + 1) < r₂ * metalQ r₂ (k + 1) :=
        mul_lt_mul' (le_of_lt h) (by
          rcases eq_or_lt_of_le (show 0 ≤ k by omega) with rfl | hk
          · simpa using h
          · exact ih (k + 1) (by omega) (by omega)) (by omega) (by omega)
      have hm2 := metalQ_le_of_le (le_of_lt h) k
      have hk0 : r₁ * metalQ r₁ (k + 1) < r₂ * metalQ r₁ (k + 1) :=
        Nat.mul_lt_mul_of_pos_right h h1
      have hk1 : r₂ * metalQ r₁ (k + 1) ≤ r₂ * metalQ r₂ (k + 1) :=
        Nat.mul_le_mul_left r₂ (metalQ_le_of_le (le_of_lt h) (k + 1))
      omega

lemma metalQ_ge_half_geom {r : ℕ} (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ((metalQ r n : ℝ) ^ (-p)) ≤ ((2 : ℝ) ^ (-(p / 2))) ^ n * (2 : ℝ) ^ (p / 2) := by
  have hQ_pos : (0 : ℝ) < (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
  have hpow : (2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2) ≤ (metalQ r n : ℝ) := by
    have hnat : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have hrem : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      have hm : n % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt n (by norm_num))
      have hnat' : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by exact_mod_cast hrem
      have hm' : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hm
      linarith
    have h2 : (2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2) ≤ (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hnat
    have hcast : ((2 : ℝ) ^ ((n / 2 : ℕ) : ℝ)) = ((2 ^ (n / 2) : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; norm_cast
    have hq : ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (metalQ r n : ℝ) := by
      exact_mod_cast metalQ_pow_two_le hr n
    exact h2.trans (hcast.symm ▸ hq)
  have hpos2 : 0 < (2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 := Real.rpow_le_rpow_of_nonpos hpos2 hpow (by linarith : -p ≤ 0)
  have h2 : ((2 : ℝ) ^ ((n : ℝ) / 2 - 1 / 2)) ^ (-p) =
      ((2 : ℝ) ^ (-(p / 2))) ^ n * (2 : ℝ) ^ (p / 2) := by
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-(p / 2))) n,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  exact h1.trans_eq h2

lemma summable_metalQ_rpow {r : ℕ} (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) :
    Summable fun n : ℕ => ((metalQ r n : ℝ)) ^ (-p) := by
  have hgeom : Summable fun n : ℕ => ((2 : ℝ) ^ (-(p / 2))) ^ n * (2 : ℝ) ^ (p / 2) := by
    refine Summable.mul_right _ (summable_geometric_of_lt_one ?_ ?_)
    · positivity
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact Summable.of_nonneg_of_le (fun n => by positivity) (metalQ_ge_half_geom hr hp) hgeom

/-- Generalized reciprocal metallic-mean series `C_r(p) = ∑' n, q_n(r)^(-p)`. -/
def metalC (r : ℕ) (p : ℝ) : ℝ := ∑' n : ℕ, ((metalQ r n : ℝ)) ^ (-p)

/-- The reciprocal Fibonacci constant `ψ = ∑_{k ≥ 1} 1 / F_k`. -/
def psiFib : ℝ := metalC 1 1

lemma metalC_one_eq_psiFib : psiFib = ∑' n : ℕ, (1 : ℝ) / (Nat.fib (n + 1) : ℝ) := by
  unfold psiFib metalC
  refine tsum_congr fun n => ?_
  rw [metalQ_one_eq_fib, Real.rpow_neg_one, one_div]

lemma one_le_metalC {r : ℕ} (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) : 1 ≤ metalC r p := by
  unfold metalC
  have h0 : ((metalQ r 0 : ℝ)) ^ (-p) = 1 := by simp
  have hsum := summable_metalQ_rpow hr hp
  have hle : ((metalQ r 0 : ℝ)) ^ (-p) ≤ ∑' n : ℕ, ((metalQ r n : ℝ)) ^ (-p) :=
    hsum.le_tsum 0 (fun n _ => by positivity)
  linarith [h0, hle]

lemma one_add_inv_le_psiFib : 1 + (1 : ℝ) ≤ psiFib := by
  unfold psiFib metalC
  have hsum := summable_metalQ_rpow (by decide : 1 ≤ 1) (by norm_num : (0 : ℝ) < 1)
  have hfin : (∑ n ∈ Finset.range 2, ((metalQ 1 n : ℝ)) ^ (-(1 : ℝ))) ≤
      ∑' n : ℕ, ((metalQ 1 n : ℝ)) ^ (-(1 : ℝ)) :=
    hsum.sum_le_tsum (Finset.range 2) (fun n _ => by positivity)
  have hcalc : (∑ n ∈ Finset.range 2, ((metalQ 1 n : ℝ)) ^ (-(1 : ℝ))) = 2 := by
    simp [Finset.sum_range_succ, metalQ]; norm_num
  linarith

lemma metalC_pos {r : ℕ} (hr : 1 ≤ r) {p : ℝ} (hp : 0 < p) : 0 < metalC r p :=
  lt_of_lt_of_le zero_lt_one (one_le_metalC hr hp)

lemma metalC_antitone_p {r : ℕ} (hr : 1 ≤ r) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) (hle : p₁ ≤ p₂) :
    metalC r p₂ ≤ metalC r p₁ := by
  unfold metalC
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_metalQ_rpow hr (lt_of_lt_of_le hp₁ hle))
    (summable_metalQ_rpow hr hp₁)
  have h1 : (1 : ℝ) ≤ (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

lemma metalC_strictAnti_r {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hlt : r₁ < r₂) {p : ℝ} (hp : 0 < p) :
    metalC r₂ p < metalC r₁ p := by
  have hr₂ : 1 ≤ r₂ := le_trans hr₁ hlt.le
  unfold metalC
  refine Summable.tsum_lt_tsum (i := 1) (fun n => ?_) ?_
    (summable_metalQ_rpow hr₂ hp) (summable_metalQ_rpow hr₁ hp)
  · have hpos1 : (0 : ℝ) < (metalQ r₁ n : ℝ) := by exact_mod_cast metalQ_pos hr₁ n
    have hle : (metalQ r₁ n : ℝ) ≤ (metalQ r₂ n : ℝ) := by
      exact_mod_cast metalQ_le_of_le hlt.le n
    exact Real.rpow_le_rpow_of_nonpos hpos1 hle (by linarith)
  · have hpos1 : (0 : ℝ) < (metalQ r₁ 1 : ℝ) := by exact_mod_cast metalQ_pos hr₁ 1
    have hlt' : (metalQ r₁ 1 : ℝ) < (metalQ r₂ 1 : ℝ) := by
      exact_mod_cast metalQ_lt_of_lt hr₁ hlt (by decide : 1 ≤ 1)
    exact Real.rpow_lt_rpow_of_neg hpos1 hlt' (by linarith)

lemma summable_log_metalQ_div {r : ℕ} (hr : 1 ≤ r) :
    Summable fun n : ℕ => Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ) := by
  have hterm : ∀ n : ℕ, 0 ≤ Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ) := fun n =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast metalQ_pos hr n)) (Nat.cast_nonneg _)
  have hbd : ∀ n : ℕ, Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ) ≤
      2 * ((metalQ r n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    intro n
    have hq_pos : (0 : ℝ) < (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
    have hq_half : 0 < ((metalQ r n : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hq_pos _
    have hlog : Real.log (((metalQ r n : ℝ)) ^ (1 / 2 : ℝ)) ≤ ((metalQ r n : ℝ)) ^ (1 / 2 : ℝ) :=
      Real.log_le_sub_one_of_pos hq_half |>.trans (by linarith)
    have hlog2 : Real.log (metalQ r n : ℝ) = 2 * Real.log (((metalQ r n : ℝ)) ^ (1 / 2 : ℝ)) := by
      rw [Real.log_rpow hq_pos]; ring
    have hmul_pow : ((metalQ r n : ℝ)) ^ (1 / 2 : ℝ) / (metalQ r n : ℝ) =
        ((metalQ r n : ℝ)) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (metalQ r n : ℝ), ← Real.rpow_add hq_pos]
      congr 1; norm_num
    calc Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ)
        = 2 * (Real.log (((metalQ r n : ℝ)) ^ (1 / 2 : ℝ)) / (metalQ r n : ℝ)) := by
          rw [hlog2]; ring
      _ ≤ 2 * (((metalQ r n : ℝ)) ^ (1 / 2 : ℝ) / (metalQ r n : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hq_pos.le) (by norm_num)
      _ = 2 * ((metalQ r n : ℝ)) ^ (-(1 / 2 : ℝ)) := by rw [hmul_pow]
  exact Summable.of_nonneg_of_le hterm hbd
    ((summable_metalQ_rpow hr (by norm_num : (0 : ℝ) < 1 / 2)).mul_left 2)

/-- Lipschitz-in-exponent stability of `metalC r p` at `p = 1`:
    `0 ≤ metalC r 1 - metalC r (1 + δ) ≤ D_r * δ` for all `δ ≥ 0`. -/
lemma metalC_sub_le_of_nonneg {r : ℕ} (hr : 1 ≤ r) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ metalC r 1 - metalC r (1 + δ) ∧
      metalC r 1 - metalC r (1 + δ) ≤
        (∑' n : ℕ, Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ)) * δ := by
  have h1 : metalC r (1 + δ) ≤ metalC r 1 :=
    metalC_antitone_p hr zero_lt_one (by linarith)
  refine ⟨sub_nonneg.mpr h1, ?_⟩
  unfold metalC
  rw [← (summable_metalQ_rpow hr zero_lt_one).tsum_sub
    (summable_metalQ_rpow hr (by linarith : (0 : ℝ) < 1 + δ)), ← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((summable_metalQ_rpow hr zero_lt_one).sub
      (summable_metalQ_rpow hr (by linarith : (0 : ℝ) < 1 + δ)))
    ((summable_log_metalQ_div hr).mul_right δ)
  have hq1 : (1 : ℝ) ≤ (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
  have hq_pos : 0 < (metalQ r n : ℝ) := by linarith
  have hpow1 : (metalQ r n : ℝ) ^ (-(1 : ℝ)) = 1 / (metalQ r n : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  have hpow2 : (metalQ r n : ℝ) ^ (-(1 + δ)) =
      (1 / (metalQ r n : ℝ)) * (metalQ r n : ℝ) ^ (-δ) := by
    rw [show -(1 + δ) = -(1 : ℝ) + (-δ) by ring, Real.rpow_add hq_pos, Real.rpow_neg_one, one_div]
  have hsub_exp : 1 - (metalQ r n : ℝ) ^ (-δ) ≤ δ * Real.log (metalQ r n : ℝ) := by
    have hlog_nn : 0 ≤ δ * Real.log (metalQ r n : ℝ) :=
      mul_nonneg hδ (Real.log_nonneg hq1)
    have hexp := Real.add_one_le_exp (- (δ * Real.log (metalQ r n : ℝ)))
    have hrpow : (metalQ r n : ℝ) ^ (-δ) = Real.exp (-(δ * Real.log (metalQ r n : ℝ))) := by
      rw [Real.rpow_def_of_pos hq_pos]; congr 1; ring
    linarith
  rw [hpow1, hpow2, ← mul_one_sub]
  calc (1 / (metalQ r n : ℝ)) * (1 - (metalQ r n : ℝ) ^ (-δ))
      ≤ (1 / (metalQ r n : ℝ)) * (δ * Real.log (metalQ r n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsub_exp (by positivity)
    _ = (Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ)) * δ := by ring

/-! ### Part 2: Exact Resolvent Function `resolventV` and Branch Functional Identity -/

/-- Exact resolvent test function `v_r^{(s)}(x) = ∑' n, (q_n(r) + q_{n-1}(r) x)^(-2s)`. -/
def resolventV (r : ℕ) (s x : ℝ) : ℝ :=
  ∑' n : ℕ, ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x) ^ (-(2 * s))

lemma resolventV_term_le {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (n : ℕ) :
    ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x) ^ (-(2 * s)) ≤
      ((metalQ r n : ℝ)) ^ (-(2 * s)) := by
  have hq_pos : (0 : ℝ) < (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
  have hmul : 0 ≤ (metalQPrev r n : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  exact Real.rpow_le_rpow_of_nonpos hq_pos (by linarith) (by linarith)

lemma summable_resolventV {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    Summable fun n : ℕ => ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x) ^ (-(2 * s)) :=
  Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _)
    (resolventV_term_le hr hs hx) (summable_metalQ_rpow hr (by linarith : 0 < 2 * s))

lemma resolventV_zero (r : ℕ) (s : ℝ) : resolventV r s 0 = metalC r (2 * s) := by
  simp [resolventV, metalC]

lemma resolventV_le_metalC {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    resolventV r s x ≤ metalC r (2 * s) :=
  Summable.tsum_le_tsum (resolventV_term_le hr hs hx)
    (summable_resolventV hr hs hx) (summable_metalQ_rpow hr (by linarith : 0 < 2 * s))

lemma one_le_resolventV {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    1 ≤ resolventV r s x := by
  unfold resolventV
  have h0 : ((metalQ r 0 : ℝ) + (metalQPrev r 0 : ℝ) * x) ^ (-(2 * s)) = 1 := by simp
  have hle := (summable_resolventV hr hs hx).le_tsum 0 (fun _ _ => Real.rpow_nonneg (by positivity) _)
  linarith [h0, hle]

lemma finset_sum_le_resolventV {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (K : ℕ) :
    (∑ n ∈ Finset.range K, ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x) ^ (-(2 * s))) ≤
      resolventV r s x :=
  (summable_resolventV hr hs hx).sum_le_tsum (Finset.range K)
    (fun _ _ => Real.rpow_nonneg (by positivity) _)

lemma resolventV_antitone {r : ℕ} (hr : 1 ≤ r) {s : ℝ} (hs : 0 < s) {x₁ x₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hle : x₁ ≤ x₂) :
    resolventV r s x₂ ≤ resolventV r s x₁ := by
  unfold resolventV
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_resolventV hr hs (le_trans hx₁ hle)) (summable_resolventV hr hs hx₁)
  have hq_pos : (0 : ℝ) < (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x₁ := by
    have : (0 : ℝ) < (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
    have : 0 ≤ (metalQPrev r n : ℝ) * x₁ := mul_nonneg (Nat.cast_nonneg _) hx₁
    linarith
  have hbase : (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x₁ ≤
      (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * x₂ :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (metalQPrev r n)))
  exact Real.rpow_le_rpow_of_nonpos hq_pos hbase (by linarith)

lemma resolventV_term_shift (r : ℕ) (x : ℝ) (n : ℕ) :
    (metalQ r n : ℝ) * ((r : ℝ) + x) + (metalQPrev r n : ℝ) =
      (metalQ r (n + 1) : ℝ) + (metalQPrev r (n + 1) : ℝ) * x := by
  match n with
  | 0 => simp [metalQ, metalQPrev]
  | k + 1 =>
    simp only [metalQ_succ_succ, metalQPrev_succ, Nat.cast_add, Nat.cast_mul]
    ring

/-- **Exact Resolvent Functional Identity**:
    `(r + x) ^ (-2s) * v_r^{(s)}(1 / (r + x)) = v_r^{(s)}(x) - 1`. -/
theorem resolventV_branch_eq {r : ℕ} (hr : 1 ≤ r) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    ((r : ℝ) + x) ^ (-(2 * s)) * resolventV r s (1 / ((r : ℝ) + x)) =
      resolventV r s x - 1 := by
  have hrx_pos : (0 : ℝ) < (r : ℝ) + x := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hy_nn : 0 ≤ 1 / ((r : ℝ) + x) := by positivity
  unfold resolventV
  rw [← tsum_mul_left]
  have hterm : ∀ n : ℕ,
      ((r : ℝ) + x) ^ (-(2 * s)) *
        ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * (1 / ((r : ℝ) + x))) ^ (-(2 * s)) =
        ((metalQ r (n + 1) : ℝ) + (metalQPrev r (n + 1) : ℝ) * x) ^ (-(2 * s)) := by
    intro n
    have hq_nn : 0 ≤ (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * (1 / ((r : ℝ) + x)) := by positivity
    rw [← Real.mul_rpow hrx_pos.le hq_nn]
    congr 1
    calc ((r : ℝ) + x) * ((metalQ r n : ℝ) + (metalQPrev r n : ℝ) * (1 / ((r : ℝ) + x)))
        = (metalQ r n : ℝ) * ((r : ℝ) + x) + (metalQPrev r n : ℝ) := by
          field_simp [hrx_pos.ne']
      _ = (metalQ r (n + 1) : ℝ) + (metalQPrev r (n + 1) : ℝ) * x := resolventV_term_shift r x n
  simp_rw [hterm]
  have hsum := (summable_resolventV hr hs hx).tsum_eq_zero_add
  have h0 : ((metalQ r 0 : ℝ) + (metalQPrev r 0 : ℝ) * x) ^ (-(2 * s)) = 1 := by simp
  linarith

/-! ### Part 3: Non-Asymptotic Resolvent & Constant Criteria for `dimH F_{m,r}` -/

private lemma arithSet_bij (m r : ℕ) (hm : 1 ≤ m) :
    ∀ x : ℝ, ∀ f : ℕ → ℝ≥0∞,
      (∑' a : {a : ℕ // a ∈ {a : ℕ | r ≤ a ∧ a % m = r % m}}, f a.1) =
        ∑' k : ℕ, f (m * k + r) := by
  intro _ f
  let e : ℕ ≃ {a : ℕ // a ∈ {a : ℕ | r ≤ a ∧ a % m = r % m}} :=
    { toFun := fun k => ⟨m * k + r, ⟨Nat.le_add_left r (m * k), by simp [Nat.add_mod]⟩⟩
      invFun := fun a => (a.1 - r) / m
      left_inv := fun k => by
        dsimp
        rw [Nat.add_sub_cancel, Nat.mul_div_right k (by omega)]
      right_inv := fun a => Subtype.ext (by
        dsimp
        have hle : r ≤ a.1 := a.2.1
        have hmod : a.1 % m = r % m := a.2.2
        have hdvd : m ∣ (a.1 - r) :=
          (Nat.modEq_iff_dvd' hle).mp (by simpa [Nat.ModEq] using hmod.symm)
        rw [Nat.mul_div_cancel' hdvd]; omega) }
  exact (Equiv.tsum_eq e (fun a => f a.1)).symm

private lemma transferOp_eq_tsum_subtype (A : Set ℕ) (s : ℝ) (v : ℝ → ℝ≥0∞) (x : ℝ) :
    transferOp A s v x =
      ∑' a : {a : ℕ // a ∈ A},
        v (1 / ((a.1 : ℝ) + x)) * ENNReal.ofReal (((a.1 : ℝ) + x) ^ (-(2 * s))) := by
  unfold transferOp
  refine (tsum_congr fun a => ?_).trans
    (tsum_subtype A fun a : ℕ =>
      v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))).symm
  simp only [Set.indicator_apply]

/-- **Upper Resolvent Criterion**:
    If `C_r(2s) * ((r + m)^(-2s) + (r + m)^(1 - 2s) / (m (2s - 1))) ≤ 1`,
    then `dimH F_{m,r} ≤ s`. -/
theorem dimH_residueConstSet_le_of_resolvent {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r)
    {s : ℝ} (hs : 1 / 2 < s)
    (hcond : metalC r (2 * s) *
      ((((r + m : ℕ) : ℝ) ^ (-(2 * s))) +
        ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) ≤ 1) :
    dimH (residueConstSet m r) ≤ ENNReal.ofReal s := by
  have hs0 : 0 < s := by linarith
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (resolventV r s x)
  have hC_pos : 0 < metalC r (2 * s) := metalC_pos hr (by linarith)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal (metalC r (2 * s)) := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (one_le_resolventV hr hs0 hx.1),
      ENNReal.ofReal_le_ofReal (resolventV_le_metalC hr hs0 hx.1)⟩
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp {a : ℕ | r ≤ a ∧ a % m = r % m} s v x ≤ v x := by
    intro x hx
    rw [transferOp_eq_tsum_subtype, arithSet_bij m r hm x
      (fun a : ℕ => v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))]
    let g : ℕ → ℝ≥0∞ := fun k =>
      v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
        ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s)))
    change (∑' k : ℕ, g k) ≤ v x
    have hden_pos : ∀ k : ℕ, 0 < ((m * k + r : ℕ) : ℝ) + x := fun k =>
      add_pos_of_pos_of_nonneg (by exact_mod_cast (by omega : 0 < m * k + r)) hx.1
    have hsplit : (∑' k : ℕ, g k) = g 0 + (g 1 + ∑' k : ℕ, if 2 ≤ k then g k else 0) := by
      rw [ENNReal.tsum_eq_add_tsum_ite (0 : ℕ) (f := g)]
      congr 1
      let f1 : ℕ → ℝ≥0∞ := fun k => if k = 0 then 0 else g k
      have h1 := ENNReal.tsum_eq_add_tsum_ite (1 : ℕ) (f := f1)
      simp only [f1, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte] at h1
      refine (tsum_congr fun k => ?_).trans (h1.trans ?_)
      · by_cases hk0 : k = 0 <;> simp [hk0]
      · congr 1
        refine tsum_congr fun k => ?_
        by_cases h0k : k = 0 <;> by_cases h1k : k = 1
        · omega
        · simp [h0k, h1k]
        · simp [h0k, h1k]
        · have h2k : 2 ≤ k := by omega
          simp [h0k, h1k, h2k]
    have hrx_pos : 0 < (r : ℝ) + x :=
      add_pos_of_pos_of_nonneg (by exact_mod_cast hr) hx.1
    have hg0 : g 0 = ENNReal.ofReal (resolventV r s x - 1) := by
      dsimp only [g, v]
      have hz : ((m * 0 + r : ℕ) : ℝ) + x = (r : ℝ) + x := by simp
      rw [hz, mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hrx_pos.le _),
        resolventV_branch_eq hr hs0 hx.1]
    have hg1 : g 1 ≤ ENNReal.ofReal (metalC r (2 * s) * (((r + m : ℕ) : ℝ) ^ (-(2 * s)))) := by
      dsimp only [g, v]
      have hx1_nn : 0 ≤ 1 / (((m * 1 + r : ℕ) : ℝ) + x) := div_nonneg zero_le_one (hden_pos 1).le
      have hax_eq : ((m * 1 + r : ℕ) : ℝ) + x = ((r + m : ℕ) : ℝ) + x := by
        push_cast; ring
      have hv1 : resolventV r s (1 / (((m * 1 + r : ℕ) : ℝ) + x)) ≤ metalC r (2 * s) :=
        resolventV_le_metalC hr hs0 hx1_nn
      have hpow : (((m * 1 + r : ℕ) : ℝ) + x) ^ (-(2 * s)) ≤ ((r + m : ℕ) : ℝ) ^ (-(2 * s)) := by
        rw [hax_eq]
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < r + m))
          (by linarith [hx.1]) (by linarith)
      rw [← ENNReal.ofReal_mul (le_trans zero_le_one (one_le_resolventV hr hs0 hx1_nn))]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul hv1 hpow (Real.rpow_nonneg (hden_pos 1).le _) hC_pos.le)
    have htail : (∑' k : ℕ, if 2 ≤ k then g k else 0) ≤
        ENNReal.ofReal (metalC r (2 * s) *
          ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) := by
      have hk_le : ∀ k : ℕ, (if 2 ≤ k then g k else 0) ≤
          ENNReal.ofReal (metalC r (2 * s)) *
            (if 2 ≤ k then ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) := by
        intro k
        split_ifs with hk
        · dsimp only [g, v]
          have hxk_nn : 0 ≤ 1 / (((m * k + r : ℕ) : ℝ) + x) :=
            div_nonneg zero_le_one (hden_pos k).le
          exact mul_le_mul_of_nonneg_right
            (ENNReal.ofReal_le_ofReal (resolventV_le_metalC hr hs0 hxk_nn)) bot_le
        · simp
      have hsum_le : (∑' k : ℕ, if 2 ≤ k then g k else 0) ≤
          ENNReal.ofReal (metalC r (2 * s)) *
            ∑' k : ℕ, if 2 ≤ k then ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0 := by
        rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum hk_le
      have htail_r := tsum_arith_tail_le hm hr (by decide : 1 ≤ 2) hs hx
      have hm_eq : m * (2 - 1) + r = r + m := by omega
      rw [hm_eq] at htail_r
      calc (∑' k : ℕ, if 2 ≤ k then g k else 0)
          ≤ ENNReal.ofReal (metalC r (2 * s)) *
              (∑' k : ℕ, if 2 ≤ k then
                ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) else 0) := hsum_le
        _ ≤ ENNReal.ofReal (metalC r (2 * s)) *
              ENNReal.ofReal ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) :=
            mul_le_mul_of_nonneg_left htail_r bot_le
        _ = ENNReal.ofReal (metalC r (2 * s) *
              ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) :=
            (ENNReal.ofReal_mul hC_pos.le).symm
    have hvx_ge1 : 1 ≤ resolventV r s x := one_le_resolventV hr hs0 hx.1
    rw [hsplit, hg0]
    have hsum_tail_le : g 1 + (∑' k : ℕ, if 2 ≤ k then g k else 0) ≤ ENNReal.ofReal 1 := by
      have ha1 : 0 ≤ metalC r (2 * s) * (((r + m : ℕ) : ℝ) ^ (-(2 * s))) := by positivity
      have ha2 : 0 ≤ metalC r (2 * s) *
          ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
        have : 0 < 2 * s - 1 := by linarith
        positivity
      calc g 1 + (∑' k : ℕ, if 2 ≤ k then g k else 0)
          ≤ ENNReal.ofReal (metalC r (2 * s) * (((r + m : ℕ) : ℝ) ^ (-(2 * s)))) +
              ENNReal.ofReal (metalC r (2 * s) *
                ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) :=
            add_le_add hg1 htail
        _ = ENNReal.ofReal (metalC r (2 * s) *
              ((((r + m : ℕ) : ℝ) ^ (-(2 * s))) +
                ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))))) := by
            rw [← ENNReal.ofReal_add ha1 ha2, mul_add]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hcond
    calc ENNReal.ofReal (resolventV r s x - 1) + (g 1 + (∑' k : ℕ, if 2 ≤ k then g k else 0))
        ≤ ENNReal.ofReal (resolventV r s x - 1) + ENNReal.ofReal 1 := add_le_add le_rfl hsum_tail_le
      _ = ENNReal.ofReal ((resolventV r s x - 1) + 1) :=
          (ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) zero_le_one).symm
      _ = v x := by simp [v]
  rw [← cfAlphabetSet_eq_residueConstSet]
  exact dimH_le_of_transferOp_le (fun a ha => le_trans hr ha.1) hs0
    (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub

/-- **Lower Resolvent Criterion**:
    If `1 < v_r^{(s)}(1 / (r + m)) * ((r + m + 1)^(1 - 2s) / (m (2s - 1)))`,
    then `s ≤ dimH F_{m,r}`. -/
theorem le_dimH_residueConstSet_of_resolvent {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r)
    {s : ℝ} (hs : 1 / 2 < s)
    (hcond : 1 < resolventV r s (1 / ((r + m : ℕ) : ℝ)) *
      ((((r + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) :
    ENNReal.ofReal s ≤ dimH (residueConstSet m r) := by
  have hs0 : 0 < s := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2s1 : 0 < 2 * s - 1 := by linarith
  let vloc : ℝ := resolventV r s (1 / ((r + m : ℕ) : ℝ))
  have hvloc_pos : 0 < vloc := lt_of_lt_of_le zero_lt_one (one_le_resolventV hr hs0 (by positivity))
  have hden_pos : 0 < (m : ℝ) * (2 * s - 1) := mul_pos hmR h2s1
  set gap : ℝ :=
    vloc * ((((r + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) - 1
  have hgap : 0 < gap := sub_pos.mpr hcond
  have htend : Tendsto (fun K : ℕ =>
      vloc * ((((m * K + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))))
      atTop (nhds 0) := by
    have hrp : Tendsto (fun t : ℝ => t ^ (-(2 * s - 1))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop h2s1
    have hlin : Tendsto (fun K : ℕ => ((m * K + r + 1 : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun B => ⟨Nat.ceil (max B 0), fun K hK => ?_⟩
      have hK' : (Nat.ceil (max B 0) : ℝ) ≤ K := by exact_mod_cast hK
      have hB : B ≤ K := (le_max_left B 0).trans ((Nat.le_ceil _).trans hK')
      have hKm : (K : ℝ) ≤ (m : ℝ) * (K : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _)
        (by exact_mod_cast hm)
      push_cast; linarith
    have h0 := (hrp.comp hlin).div_const ((m : ℝ) * (2 * s - 1)) |>.const_mul vloc
    simpa [Function.comp_def, show -(2 * s - 1) = 1 - 2 * s by ring, zero_div, mul_zero] using h0
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hgap))
  let Kmax := max K0 2
  have hKmax1 : 1 ≤ Kmax := le_trans (by decide : 1 ≤ 2) (le_max_right _ _)
  have htail_lt : vloc * ((((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) /
      ((m : ℝ) * (2 * s - 1))) < gap := hK0 Kmax (le_max_left _ _)
  have hfinite_cond : 1 ≤ vloc *
      (((((m * 1 + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
          (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))) := by
    have h_eq : m * 1 + r + 1 = r + m + 1 := by omega
    rw [h_eq, sub_div, mul_sub]
    dsimp only [gap] at htail_lt
    linarith
  let A_fin : Finset ℕ := (Finset.range Kmax).image (fun k => m * k + r)
  have hAne : A_fin.Nonempty :=
    ⟨r, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩⟩
  have ha1 : ∀ a ∈ A_fin, 1 ≤ a := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    omega
  have hinj : Function.Injective (fun k => m * k + r) := fun a b hab =>
    Nat.mul_left_cancel hm (Nat.add_right_cancel hab)
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (resolventV r s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal (metalC r (2 * s)) := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (one_le_resolventV hr hs0 hx.1),
      ENNReal.ofReal_le_ofReal (resolventV_le_metalC hr hs0 hx.1)⟩
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      v x ≤ transferOp (A_fin : Set ℕ) s v x := by
    intro x hx
    have h_im : A_fin.sum (fun a : ℕ =>
        v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
        ∑ k ∈ Finset.range Kmax,
          v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) :=
      Finset.sum_image (fun a _ b _ hab => hinj hab)
    have hsum_tsum : A_fin.sum (fun a : ℕ =>
        v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) ≤
        transferOp (A_fin : Set ℕ) s v x := by
      unfold transferOp
      refine le_trans ?_ (ENNReal.sum_le_tsum A_fin)
      refine Finset.sum_le_sum fun a ha => ?_
      simp [ha]
    have hsplit : ∑ k ∈ Finset.range Kmax,
        v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
          ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) =
        (v (1 / (((m * 0 + r : ℕ) : ℝ) + x)) *
          ENNReal.ofReal ((((m * 0 + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) +
        ∑ k ∈ Finset.Ico 1 Kmax,
          v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot hKmax1]
    have h0 : v (1 / (((m * 0 + r : ℕ) : ℝ) + x)) *
        ENNReal.ofReal ((((m * 0 + r : ℕ) : ℝ) + x) ^ (-(2 * s))) =
        ENNReal.ofReal (resolventV r s x - 1) := by
      dsimp only [v]
      have hz : ((m * 0 + r : ℕ) : ℝ) + x = (r : ℝ) + x := by simp
      have hrp_nn : 0 ≤ ((r : ℝ) + x) ^ (-(2 * s)) :=
        Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg r) hx.1) _
      rw [hz, mul_comm, ← ENNReal.ofReal_mul hrp_nn, resolventV_branch_eq hr hs0 hx.1]
    have htail : ENNReal.ofReal 1 ≤
        ∑ k ∈ Finset.Ico 1 Kmax,
          v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have hv_ge : ∀ k ∈ Finset.Ico 1 Kmax, ENNReal.ofReal vloc ≤
          v (1 / (((m * k + r : ℕ) : ℝ) + x)) := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hden : ((r + m : ℕ) : ℝ) ≤ ((m * k + r : ℕ) : ℝ) + x := by
          have : r + m ≤ m * k + r := by nlinarith
          have : ((r + m : ℕ) : ℝ) ≤ ((m * k + r : ℕ) : ℝ) := by exact_mod_cast this
          linarith [hx.1]
        have hdiv : 1 / (((m * k + r : ℕ) : ℝ) + x) ≤ 1 / ((r + m : ℕ) : ℝ) :=
          one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < r + m)) hden
        have hdiv_nn : 0 ≤ 1 / (((m * k + r : ℕ) : ℝ) + x) :=
          one_div_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) hx.1)
        exact ENNReal.ofReal_le_ofReal (resolventV_antitone hr hs0 hdiv_nn hdiv)
      have h1 : ENNReal.ofReal vloc *
          ∑ k ∈ Finset.Ico 1 Kmax, ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) ≤
          ∑ k ∈ Finset.Ico 1 Kmax,
            v (1 / (((m * k + r : ℕ) : ℝ) + x)) *
              ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hv_ge k hk) bot_le
      have hlow := sum_arith_lower_ge hm hr hKmax1 hs hx
      calc ENNReal.ofReal 1
          ≤ ENNReal.ofReal (vloc *
              (((((m * 1 + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
                (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1)))) :=
            ENNReal.ofReal_le_ofReal hfinite_cond
        _ = ENNReal.ofReal vloc *
              ENNReal.ofReal (((((m * 1 + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
                (((m * Kmax + r + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))) :=
            ENNReal.ofReal_mul hvloc_pos.le
        _ ≤ ENNReal.ofReal vloc *
              ∑ k ∈ Finset.Ico 1 Kmax, ENNReal.ofReal ((((m * k + r : ℕ) : ℝ) + x) ^ (-(2 * s))) :=
            mul_le_mul_of_nonneg_left hlow bot_le
        _ ≤ _ := h1
    have hvx_ge1 : 1 ≤ resolventV r s x := one_le_resolventV hr hs0 hx.1
    calc v x = ENNReal.ofReal ((resolventV r s x - 1) + 1) := by
          dsimp only [v]; congr 1; ring
      _ = ENNReal.ofReal (resolventV r s x - 1) + ENNReal.ofReal 1 :=
          ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) zero_le_one
      _ ≤ _ := add_le_add h0.ge htail
      _ = _ := (h_im.trans hsplit).symm
      _ ≤ transferOp (A_fin : Set ℕ) s v x := hsum_tsum
  have hdim_sub := le_dimH_of_transferOp_ge hAne ha1 hs0
    (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsuper
  have hsub_F : cfAlphabetSet (A_fin : Set ℕ) ⊆ residueConstSet m r := by
    rintro x ⟨hx01, hirr, hadm⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hadm i))
    rw [← hk_eq]
    exact ⟨Nat.le_add_left _ _, by simp [Nat.add_mod]⟩
  exact hdim_sub.trans (dimH_mono hsub_F)

/-- Constant-`1` upper criterion for `F_{m,m}` with `K ≥ 1` exact leading terms and MVT integral tail. -/
theorem dimH_residueConstSet_mm_le {m K : ℕ} (hm : 1 ≤ m) (hK : 1 ≤ K)
    {s : ℝ} (hs : 1 / 2 < s)
    (hcond : (∑ k ∈ Finset.range K, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s))) +
      ((((K * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) ≤ 1) :
    dimH (residueConstSet m m) ≤ ENNReal.ofReal s := by
  have hs0 : 0 < s := by linarith
  let v : ℝ → ℝ≥0∞ := fun _ => 1
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞) ≤ v x ∧ v x ≤ 1 := fun _ _ => ⟨le_rfl, le_rfl⟩
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp {a : ℕ | m ≤ a ∧ a % m = m % m} s v x ≤ v x := by
    intro x hx
    rw [transferOp_eq_tsum_subtype, arithSet_bij m m hm x
      (fun a : ℕ => v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))]
    simp only [v, one_mul]
    let g : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((((m * k + m : ℕ) : ℝ) + x) ^ (-(2 * s)))
    change (∑' k : ℕ, g k) ≤ 1
    have hsplit : (∑' k : ℕ, g k) =
        (∑ k ∈ Finset.range K, g k) + (∑' k : ℕ, if K ≤ k then g k else 0) := by
      have hg_all : (∑' k : ℕ, g k) =
          (∑' k : ℕ, if k < K then g k else 0) + (∑' k : ℕ, if K ≤ k then g k else 0) := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun k => ?_
        by_cases hk : k < K
        · have hn : ¬ K ≤ k := by omega
          simp [hk, hn]
        · have hn : K ≤ k := by omega
          simp [hk, hn]
      rw [hg_all]
      congr 1
      rw [tsum_eq_sum (s := Finset.range K) (fun k hk => by
        have : ¬ k < K := by simpa [Finset.mem_range] using hk
        simp [this])]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp [Finset.mem_range.mp hk]
    have hhead : (∑ k ∈ Finset.range K, g k) ≤
        ENNReal.ofReal (∑ k ∈ Finset.range K, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s))) := by
      have hnn1 : ∀ k ∈ Finset.range K, 0 ≤ (((m * k + m : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun k _ =>
        Real.rpow_nonneg (add_nonneg (Nat.cast_nonneg _) hx.1) _
      dsimp only [g]
      rw [← ENNReal.ofReal_sum_of_nonneg hnn1]
      refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun k _ => ?_)
      have heq : (k + 1) * m = m * k + m := by ring
      rw [heq]
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < m * k + m))
        (by linarith [hx.1]) (by linarith)
    have htail : (∑' k : ℕ, if K ≤ k then g k else 0) ≤
        ENNReal.ofReal ((((K * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
      have ht := tsum_arith_tail_le hm hm hK hs hx
      have heq : m * (K - 1) + m = K * m := by
        calc m * (K - 1) + m = m * (K - 1 + 1) := by ring
          _ = m * K := by rw [Nat.sub_add_cancel hK]
          _ = K * m := by ring
      rwa [heq] at ht
    have hnnA : 0 ≤ ∑ k ∈ Finset.range K, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _
    have hnnB : 0 ≤ (((K * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)) := by
      have : 0 < 2 * s - 1 := by linarith
      positivity
    rw [hsplit]
    calc (∑ k ∈ Finset.range K, g k) + (∑' k : ℕ, if K ≤ k then g k else 0)
        ≤ ENNReal.ofReal (∑ k ∈ Finset.range K, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s))) +
            ENNReal.ofReal ((((K * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) :=
          add_le_add hhead htail
      _ = ENNReal.ofReal ((∑ k ∈ Finset.range K, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s))) +
            ((((K * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) :=
          (ENNReal.ofReal_add hnnA hnnB).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hcond
      _ = 1 := by simp
  rw [← cfAlphabetSet_eq_residueConstSet]
  exact dimH_le_of_transferOp_le (fun a ha => le_trans hm ha.1) hs0
    zero_lt_one ENNReal.one_lt_top hv_bd hsub

lemma dimH_residueConstSet_mm_le_one {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 1 / 2 < s)
    (hcond : ((m : ℝ) ^ (-(2 * s))) * (1 + 1 / (2 * s - 1)) ≤ 1) :
    dimH (residueConstSet m m) ≤ ENNReal.ofReal s := by
  refine dimH_residueConstSet_mm_le hm le_rfl hs ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs' : 2 * s - 1 ≠ 0 := by linarith
  have heq : (∑ k ∈ Finset.range 1, (((k + 1) * m : ℕ) : ℝ) ^ (-(2 * s))) +
      ((((1 * m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) =
      ((m : ℝ) ^ (-(2 * s))) * (1 + 1 / (2 * s - 1)) := by
    simp only [Finset.sum_range_one, zero_add, one_mul]
    rw [show (1 - 2 * s : ℝ) = 1 + -(2 * s) by ring, Real.rpow_add hmR, Real.rpow_one]
    field_simp [hmR.ne', hs']
  rwa [heq]

/-- Constant-`1` lower criterion for `F_{m,m}`. -/
theorem le_dimH_residueConstSet_mm {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs : 1 / 2 < s)
    (hcond : 1 < (((m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) :
    ENNReal.ofReal s ≤ dimH (residueConstSet m m) := by
  have hs0 : 0 < s := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h2s1 : 0 < 2 * s - 1 := by linarith
  set gap : ℝ := (((m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)) - 1
  have hgap : 0 < gap := sub_pos.mpr hcond
  have htend : Tendsto (fun K : ℕ =>
      (((m * K + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) atTop (nhds 0) := by
    have hrp : Tendsto (fun t : ℝ => t ^ (-(2 * s - 1))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop h2s1
    have hlin : Tendsto (fun K : ℕ => ((m * K + m + 1 : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun B => ⟨Nat.ceil (max B 0), fun K hK => ?_⟩
      have hB : B ≤ (K : ℝ) :=
        (le_max_left B 0).trans ((Nat.le_ceil _).trans (by exact_mod_cast hK))
      have hKm : (K : ℝ) ≤ (m : ℝ) * (K : ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _)
        (by exact_mod_cast hm)
      push_cast; linarith
    simpa [Function.comp_def, show -(2 * s - 1) = 1 - 2 * s by ring, zero_div] using
      (hrp.comp hlin).div_const ((m : ℝ) * (2 * s - 1))
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds hgap))
  let Kmax := max K0 1
  have htail_lt : (((m * Kmax + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)) < gap :=
    hK0 Kmax (le_max_left _ _)
  have hfinite : 1 ≤ (((((m * 0 + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) -
      (((m * Kmax + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s))) / ((m : ℝ) * (2 * s - 1))) := by
    have hz : m * 0 + m + 1 = m + 1 := by omega
    rw [hz, sub_div]
    dsimp only [gap] at htail_lt
    linarith
  let A_fin : Finset ℕ := (Finset.range Kmax).image (fun k => m * k + m)
  have hAne : A_fin.Nonempty :=
    ⟨m, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), by simp⟩⟩
  have ha1 : ∀ a ∈ A_fin, 1 ≤ a := fun a ha => by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha; omega
  have hinj : Function.Injective (fun k => m * k + m) := fun a b hab =>
    Nat.mul_left_cancel hm (Nat.add_right_cancel hab)
  let v : ℝ → ℝ≥0∞ := fun _ => 1
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1, v x ≤ transferOp (A_fin : Set ℕ) s v x := fun x hx => by
    have h_im : A_fin.sum (fun a : ℕ =>
        v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) =
        ∑ k ∈ Finset.range Kmax,
          ENNReal.ofReal ((((m * k + m : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      simpa [v] using Finset.sum_image (f := fun a : ℕ =>
        ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)))) (fun a _ b _ hab => hinj hab)
    have hlow := sum_arith_lower_ge hm hm (show 0 ≤ Kmax by omega) hs hx
    rw [Nat.Ico_zero_eq_range] at hlow
    have h1 : (1 : ℝ≥0∞) ≤
        ∑ k ∈ Finset.range Kmax, ENNReal.ofReal ((((m * k + m : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      simpa using (ENNReal.ofReal_le_ofReal hfinite).trans hlow
    unfold transferOp
    refine h1.trans (le_trans (le_of_eq h_im.symm) (ENNReal.sum_le_tsum A_fin |>.trans_eq' ?_))
    refine Finset.sum_congr rfl fun a ha => ?_
    simp [ha]
  have hdim_sub := le_dimH_of_transferOp_ge hAne ha1 hs0
    zero_lt_one ENNReal.one_lt_top (fun _ _ => ⟨le_rfl, le_rfl⟩) hsuper
  have hsub_F : cfAlphabetSet (A_fin : Set ℕ) ⊆ residueConstSet m m := by
    rintro x ⟨hx01, hirr, hadm⟩
    refine ⟨hx01, hirr, fun i => ?_⟩
    obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp (hadm i))
    rw [← hk_eq]
    exact ⟨Nat.le_add_left _ _, by simp⟩
  exact hdim_sub.trans (dimH_mono hsub_F)

/-! ### Part 4: Global Strict Separation `dimH F_{m,m} < dimH F_{m,1}` for EVERY `m ≥ 2` -/

private lemma rpow_neg_div_le {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b) {R : ℝ}
    (hR : 0 ≤ R) (h : 1 ≤ x ^ a * R ^ b) :
    x ^ (-((a : ℝ) / (b : ℝ))) ≤ R := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hp : (x ^ (-((a : ℝ) / (b : ℝ)))) ^ b ≤ R ^ b := by
    rw [← Real.rpow_natCast _ b, ← Real.rpow_mul hx.le]
    have hba : (-((a : ℝ) / (b : ℝ))) * (b : ℝ) = -((a : ℕ) : ℝ) := by
      field_simp [hb0]
    rw [hba, Real.rpow_neg hx.le, Real.rpow_natCast]
    exact (inv_le_iff_one_le_mul₀ (pow_pos hx a)).mpr (by linarith [mul_comm (x ^ a) (R ^ b)])
  exact le_of_pow_le_pow_left₀ hb.ne' hR hp

private lemma le_rpow_neg_div {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b) {L : ℝ}
    (h : x ^ a * L ^ b ≤ 1) :
    L ≤ x ^ (-((a : ℝ) / (b : ℝ))) := by
  by_cases hL : L ≤ 0
  · exact hL.trans (Real.rpow_nonneg hx.le _)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hp : L ^ b ≤ (x ^ (-((a : ℝ) / (b : ℝ)))) ^ b := by
    conv_rhs => rw [← Real.rpow_natCast _ b, ← Real.rpow_mul hx.le]
    have hba : (-((a : ℝ) / (b : ℝ))) * (b : ℝ) = -((a : ℕ) : ℝ) := by
      field_simp [hb0]
    rw [hba, Real.rpow_neg hx.le, Real.rpow_natCast, ← one_div, le_div_iff₀ (pow_pos hx a)]
    linarith [mul_comm (x ^ a) (L ^ b)]
  exact le_of_pow_le_pow_left₀ hb.ne' (Real.rpow_nonneg hx.le _) hp

private lemma poly5_le_pow7 : ∀ m : ℕ, 5 ≤ m → ((m : ℝ) + 2) ^ 5 ≤ (7 : ℝ) ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : ((m : ℝ) + 3) ^ 5 ≤ 7 * ((m : ℝ) + 2) ^ 5 := by
      have h8 : 8 * ((m : ℝ) + 2) ≥ 7 * ((m : ℝ) + 3) := by
        have : (5 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have hp5 : (7 : ℝ) ^ 5 * ((m : ℝ) + 3) ^ 5 ≤ (8 : ℝ) ^ 5 * ((m : ℝ) + 2) ^ 5 := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) 5
      nlinarith [show (0 : ℝ) < ((m : ℝ) + 3) ^ 5 by positivity,
        show (0 : ℝ) < ((m : ℝ) + 2) ^ 5 by positivity]
    calc ((m + 1 : ℕ) + 2 : ℝ) ^ 5 = ((m : ℝ) + 3) ^ 5 := by push_cast; ring
      _ ≤ 7 * ((m : ℝ) + 2) ^ 5 := hstep
      _ ≤ 7 * (7 : ℝ) ^ m := by linarith
      _ = (7 : ℝ) ^ (m + 1) := by rw [pow_succ']

/-- **Global Strict Separation Theorem**:
    For EVERY modulus `m ≥ 2`, `dimH F_{m,m} < dimH F_{m,1}`. -/
theorem dimH_residueConstSet_mm_lt_m1 (m : ℕ) (hm : 2 ≤ m) :
    dimH (residueConstSet m m) < dimH (residueConstSet m 1) := by
  rcases eq_or_lt_of_le hm with rfl | hm3
  · -- Case `m = 2`: `dimH F_{2,2} ≤ 37/50 < 3/4 ≤ dimH F_{2,1}`
    have hup : dimH (residueConstSet 2 2) ≤ ENNReal.ofReal (37 / 50) := by
      refine dimH_residueConstSet_mm_le (K := 4) (by decide) (by decide) (by norm_num) ?_
      have h2 : (2 : ℝ) ^ (-((37 : ℝ) / 25)) ≤ 36 / 100 :=
        rpow_neg_div_le (a := 37) (b := 25) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have h4 : (4 : ℝ) ^ (-((37 : ℝ) / 25)) ≤ 13 / 100 :=
        rpow_neg_div_le (a := 37) (b := 25) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have h6 : (6 : ℝ) ^ (-((37 : ℝ) / 25)) ≤ 71 / 1000 :=
        rpow_neg_div_le (a := 37) (b := 25) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have h8 : (8 : ℝ) ^ (-((37 : ℝ) / 25)) ≤ 47 / 1000 :=
        rpow_neg_div_le (a := 37) (b := 25) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have h8t : (8 : ℝ) ^ (-((12 : ℝ) / 25)) ≤ 37 / 100 :=
        rpow_neg_div_le (a := 12) (b := 25) (by norm_num) (by decide) (by norm_num) (by norm_num)
      calc (∑ k ∈ Finset.range 4, (((k + 1) * 2 : ℕ) : ℝ) ^ (-(2 * (37 / 50 : ℝ)))) +
            ((((4 * 2 : ℕ) : ℝ) ^ (1 - 2 * (37 / 50 : ℝ))) /
              (((2 : ℕ) : ℝ) * (2 * (37 / 50 : ℝ) - 1)))
          = (2 : ℝ) ^ (-((37 : ℝ) / 25)) + (4 : ℝ) ^ (-((37 : ℝ) / 25)) +
              (6 : ℝ) ^ (-((37 : ℝ) / 25)) + (8 : ℝ) ^ (-((37 : ℝ) / 25)) +
              (25 / 24 : ℝ) * (8 : ℝ) ^ (-((12 : ℝ) / 25)) := by
            simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
            norm_num
            ring
        _ ≤ 36 / 100 + 13 / 100 + 71 / 1000 + 47 / 1000 + (25 / 24 : ℝ) * (37 / 100) := by
            linarith only [h2, h4, h6, h8, h8t]
        _ ≤ 1 := by norm_num
    have hlo : ENNReal.ofReal (3 / 4) ≤ dimH (residueConstSet 2 1) := by
      refine le_dimH_residueConstSet_of_resolvent (by decide) (by decide) (by norm_num) ?_
      have hsub := finset_sum_le_resolventV (r := 1) (by decide) (s := 3 / 4) (x := 1 / ((1 + 2 : ℕ) : ℝ))
        (by norm_num) (by norm_num) 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        metalQ, metalQPrev] at hsub
      norm_num at hsub
      have ha1 : 64 / 100 ≤ ((4 / 3 : ℝ)) ^ (-((3 : ℝ) / 2)) :=
        le_rpow_neg_div (a := 3) (b := 2) (by norm_num) (by decide) (by norm_num)
      have ha2 : 28 / 100 ≤ ((7 / 3 : ℝ)) ^ (-((3 : ℝ) / 2)) :=
        le_rpow_neg_div (a := 3) (b := 2) (by norm_num) (by decide) (by norm_num)
      have ha3 : 14 / 100 ≤ ((11 / 3 : ℝ)) ^ (-((3 : ℝ) / 2)) :=
        le_rpow_neg_div (a := 3) (b := 2) (by norm_num) (by decide) (by norm_num)
      norm_num at ha1 ha2 ha3
      have hv_ge : (206 / 100 : ℝ) ≤ resolventV 1 (3 / 4) (1 / ((1 + 2 : ℕ) : ℝ)) := by
        linarith only [hsub, ha1, ha2, ha3]
      have ht_ge : (1 / 2 : ℝ) ≤ ((1 + 2 + 1 : ℕ) : ℝ) ^ (1 - 2 * (3 / 4 : ℝ)) := by
        norm_num
      have hden : ((2 : ℝ) * (2 * (3 / 4 : ℝ) - 1)) = 1 := by norm_num
      have hprod : 1 < (206 / 100 : ℝ) * ((1 / 2 : ℝ) / 1) := by norm_num
      calc (1 : ℝ) < (206 / 100 : ℝ) * ((1 / 2 : ℝ) / 1) := hprod
        _ ≤ resolventV 1 (3 / 4) (1 / ((1 + 2 : ℕ) : ℝ)) *
              (((1 + 2 + 1 : ℕ) : ℝ) ^ (1 - 2 * (3 / 4 : ℝ)) /
                ((2 : ℝ) * (2 * (3 / 4 : ℝ) - 1))) := by
            rw [hden]
            exact mul_le_mul hv_ge (div_le_div_of_nonneg_right ht_ge (by norm_num))
              (by norm_num) (by linarith only [hv_ge])
    exact lt_of_le_of_lt hup
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hlo)
  rcases eq_or_lt_of_le (show 3 ≤ m by omega) with rfl | hm4
  · -- Case `m = 3`: `dimH F_{3,3} ≤ 2/3 < 17/25 ≤ dimH F_{3,1}`
    have hup : dimH (residueConstSet 3 3) ≤ ENNReal.ofReal (2 / 3) := by
      refine dimH_residueConstSet_mm_le_one (by decide) (by norm_num) ?_
      have hs3 : (3 : ℝ) ^ (-(2 * (2 / 3 : ℝ))) ≤ 1 / 4 := by
        rw [show -(2 * (2 / 3 : ℝ)) = -((4 : ℝ) / 3) by norm_num]
        exact rpow_neg_div_le (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have hfac : (1 : ℝ) + 1 / (2 * (2 / 3 : ℝ) - 1) = 4 := by norm_num
      rw [hfac]; linarith only [hs3]
    have hlo : ENNReal.ofReal (17 / 25) ≤ dimH (residueConstSet 3 1) := by
      refine le_dimH_residueConstSet_of_resolvent (by decide) (by decide) (by norm_num) ?_
      have hsub := finset_sum_le_resolventV (r := 1) (by decide) (s := 17 / 25)
        (x := 1 / ((1 + 3 : ℕ) : ℝ)) (by norm_num) (by norm_num) 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        metalQ, metalQPrev] at hsub
      norm_num at hsub
      have ha1 : 73 / 100 ≤ ((5 / 4 : ℝ)) ^ (-((34 : ℝ) / 25)) :=
        le_rpow_neg_div (a := 34) (b := 25) (by norm_num) (by decide) (by norm_num)
      have ha2 : 30 / 100 ≤ ((9 / 4 : ℝ)) ^ (-((34 : ℝ) / 25)) :=
        le_rpow_neg_div (a := 34) (b := 25) (by norm_num) (by decide) (by norm_num)
      have ha3 : 16 / 100 ≤ ((7 / 2 : ℝ)) ^ (-((34 : ℝ) / 25)) :=
        le_rpow_neg_div (a := 34) (b := 25) (by norm_num) (by decide) (by norm_num)
      norm_num at ha1 ha2 ha3
      have hv_ge : (219 / 100 : ℝ) ≤ resolventV 1 (17 / 25) (1 / ((1 + 3 : ℕ) : ℝ)) := by
        linarith only [hsub, ha1, ha2, ha3]
      have ht_ge : (55 / 100 : ℝ) ≤ ((1 + 3 + 1 : ℕ) : ℝ) ^ (1 - 2 * (17 / 25 : ℝ)) := by
        have h9 : (55 / 100 : ℝ) ≤ (5 : ℝ) ^ (-((9 : ℝ) / 25)) :=
          le_rpow_neg_div (a := 9) (b := 25) (by norm_num) (by decide) (by norm_num)
        norm_num at h9 ⊢
        exact h9
      have hden : ((3 : ℝ) * (2 * (17 / 25 : ℝ) - 1)) = 27 / 25 := by norm_num
      have hprod : 1 < (219 / 100 : ℝ) * ((55 / 100 : ℝ) / (27 / 25)) := by norm_num
      calc (1 : ℝ) < (219 / 100 : ℝ) * ((55 / 100 : ℝ) / (27 / 25)) := hprod
        _ ≤ resolventV 1 (17 / 25) (1 / ((1 + 3 : ℕ) : ℝ)) *
              (((1 + 3 + 1 : ℕ) : ℝ) ^ (1 - 2 * (17 / 25 : ℝ)) /
                ((3 : ℝ) * (2 * (17 / 25 : ℝ) - 1))) := by
            rw [hden]
            exact mul_le_mul hv_ge (div_le_div_of_nonneg_right ht_ge (by norm_num))
              (by norm_num) (by linarith only [hv_ge])
    exact lt_of_le_of_lt hup
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hlo)
  rcases eq_or_lt_of_le (show 4 ≤ m by omega) with rfl | hm5_lt
  · -- Case `m = 4`: `dimH F_{4,4} ≤ 21/32 < 2/3 ≤ dimH F_{4,1}`
    have hup : dimH (residueConstSet 4 4) ≤ ENNReal.ofReal (21 / 32) := by
      refine dimH_residueConstSet_mm_le_one (by decide) (by norm_num) ?_
      have hpow : (4 : ℝ) ^ (-(2 * (21 / 32 : ℝ))) ≤ (1 / 5 : ℝ) := by
        rw [show -(2 * (21 / 32 : ℝ)) = -((21 : ℝ) / 16) by norm_num]
        exact rpow_neg_div_le (a := 21) (b := 16) (by norm_num) (by decide) (by norm_num) (by norm_num)
      have hfac : (1 : ℝ) + 1 / (2 * (21 / 32 : ℝ) - 1) = 21 / 5 := by norm_num
      calc (4 : ℝ) ^ (-(2 * (21 / 32 : ℝ))) * (1 + 1 / (2 * (21 / 32 : ℝ) - 1))
          ≤ (1 / 5) * (21 / 5) := by rw [hfac]; exact mul_le_mul_of_nonneg_right hpow (by norm_num)
        _ ≤ 1 := by norm_num
    have hlo : ENNReal.ofReal (2 / 3) ≤ dimH (residueConstSet 4 1) := by
      refine le_dimH_residueConstSet_of_resolvent (by decide) (by decide) (by norm_num) ?_
      have hsub := finset_sum_le_resolventV (r := 1) (by decide) (s := 2 / 3)
        (x := 1 / ((1 + 4 : ℕ) : ℝ)) (by norm_num) (by norm_num) 6
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        metalQ, metalQPrev] at hsub
      norm_num at hsub
      have ha1 : 78 / 100 ≤ ((6 / 5 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha2 : 34 / 100 ≤ ((11 / 5 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha3 : 19 / 100 ≤ ((17 / 5 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha4 : 10 / 100 ≤ ((28 / 5 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha5 : 5 / 100 ≤ ((9 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      norm_num at ha1 ha2 ha3 ha4 ha5
      have hv_ge : (246 / 100 : ℝ) ≤ resolventV 1 (2 / 3) (1 / ((1 + 4 : ℕ) : ℝ)) := by
        linarith only [hsub, ha1, ha2, ha3, ha4, ha5]
      have ht_ge : (55 / 100 : ℝ) ≤ ((1 + 4 + 1 : ℕ) : ℝ) ^ (1 - 2 * (2 / 3 : ℝ)) := by
        have h6 := le_rpow_neg_div (x := (6 : ℝ)) (a := 1) (b := 3) (L := 55 / 100)
          (by norm_num) (by decide) (by norm_num)
        norm_num at h6 ⊢
        exact h6
      have hden : ((4 : ℝ) * (2 * (2 / 3 : ℝ) - 1)) = 4 / 3 := by norm_num
      have hprod : 1 < (246 / 100 : ℝ) * ((55 / 100 : ℝ) / (4 / 3)) := by norm_num
      calc (1 : ℝ) < (246 / 100 : ℝ) * ((55 / 100 : ℝ) / (4 / 3)) := hprod
        _ ≤ resolventV 1 (2 / 3) (1 / ((1 + 4 : ℕ) : ℝ)) *
              (((1 + 4 + 1 : ℕ) : ℝ) ^ (1 - 2 * (2 / 3 : ℝ)) /
                ((4 : ℝ) * (2 * (2 / 3 : ℝ) - 1))) := by
            rw [hden]
            exact mul_le_mul hv_ge (div_le_div_of_nonneg_right ht_ge (by norm_num))
              (by norm_num) (by linarith only [hv_ge])
    exact lt_of_le_of_lt hup
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)) hlo)
  · -- Uniform Case `m ≥ 5`: `s_hi(m) = 1/2 + 5/(8m) < 1/2 + 2/(3m) = s_lo(m)`
    have hm5 : 5 ≤ m := by omega
    have hmR : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm5
    have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith only [hmR]
    have hm1 : 1 ≤ m := by omega
    let s_hi : ℝ := 1 / 2 + 5 / (8 * (m : ℝ))
    let s_lo : ℝ := 1 / 2 + 2 / (3 * (m : ℝ))
    have hs_hi_gt : 1 / 2 < s_hi := by
      dsimp only [s_hi]
      linarith only [div_pos (by norm_num : (0 : ℝ) < 5) (mul_pos (by norm_num : (0 : ℝ) < 8) hm_pos)]
    have hs_lo_gt : 1 / 2 < s_lo := by
      dsimp only [s_lo]
      linarith only [div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos (by norm_num : (0 : ℝ) < 3) hm_pos)]
    have hs_lo_pos : 0 < s_lo := by linarith only [hs_lo_gt]
    have hup : dimH (residueConstSet m m) ≤ ENNReal.ofReal s_hi := by
      refine dimH_residueConstSet_mm_le_one hm1 hs_hi_gt ?_
      have h2s_sub : 2 * s_hi - 1 = 5 / (4 * (m : ℝ)) := by dsimp [s_hi]; field_simp; ring
      have hmul_eq : (m : ℝ) ^ (-(2 * s_hi)) * (1 + 1 / (2 * s_hi - 1)) =
          ((m : ℝ) ^ (-(5 / (4 * (m : ℝ))))) * (4 / 5 + 1 / (m : ℝ)) := by
        rw [h2s_sub, show -(2 * s_hi) = -1 + -(5 / (4 * (m : ℝ))) by dsimp [s_hi]; ring,
          Real.rpow_add hm_pos, Real.rpow_neg_one]
        field_simp
        ring
      rw [hmul_eq]
      rcases eq_or_lt_of_le hm5 with rfl | hm6_lt
      · have h5 := rpow_neg_div_le (x := (5 : ℝ)) (a := 1) (b := 4) (R := 4 / 5)
          (by norm_num) (by decide) (by norm_num) (by norm_num)
        norm_num at h5 ⊢
        exact h5.trans (by norm_num)
      · have hm6 : 6 ≤ m := by omega
        have hm6R : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm6
        have hpow_le : (m : ℝ) ^ (-(5 / (4 * (m : ℝ)))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hm6R])
            (by linarith only [div_pos (by norm_num : (0 : ℝ) < 5) (mul_pos (by norm_num : (0 : ℝ) < 4) hm_pos)])
        have hfac : (4 / 5 : ℝ) + 1 / (m : ℝ) ≤ 1 := by
          have : 1 / (m : ℝ) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) hm6R
          linarith only [this]
        calc (m : ℝ) ^ (-(5 / (4 * (m : ℝ)))) * (4 / 5 + 1 / (m : ℝ))
            ≤ 1 * 1 := mul_le_mul hpow_le hfac (by positivity) zero_le_one
          _ = 1 := one_mul 1
    have hlo : ENNReal.ofReal s_lo ≤ dimH (residueConstSet m 1) := by
      refine le_dimH_residueConstSet_of_resolvent hm1 (by decide) hs_lo_gt ?_
      have hx_le : 1 / ((1 + m : ℕ) : ℝ) ≤ (1 / 6 : ℝ) := by
        have : (6 : ℝ) ≤ ((1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 6 ≤ 1 + m)
        exact one_div_le_one_div_of_le (by norm_num) this
      have h2s_le : 2 * s_lo ≤ 4 / 3 := by
        have h2s : 2 * s_lo = 1 + 4 / (3 * (m : ℝ)) := by dsimp [s_lo]; ring
        have h415 : 4 / (3 * (m : ℝ)) ≤ 4 / 15 := div_le_div_of_nonneg_left (by norm_num)
          (by norm_num) (by linarith only [hmR])
        linarith only [h2s, h415]
      have hv1 : resolventV 1 (2 / 3) (1 / 6 : ℝ) ≤ resolventV 1 s_lo (1 / ((1 + m : ℕ) : ℝ)) := by
        have h_ant := resolventV_antitone (r := 1) (by decide) (s := s_lo)
          hs_lo_pos (by positivity) hx_le
        refine le_trans ?_ h_ant
        unfold resolventV
        refine Summable.tsum_le_tsum (fun n => ?_)
          (summable_resolventV (by decide) (by norm_num) (by norm_num))
          (summable_resolventV (by decide) hs_lo_pos (by norm_num))
        have hq1 : (1 : ℝ) ≤ (metalQ 1 n : ℝ) + (metalQPrev 1 n : ℝ) * (1 / 6) := by
          have : (1 : ℝ) ≤ (metalQ 1 n : ℝ) := by exact_mod_cast metalQ_pos (by decide) n
          have : 0 ≤ (metalQPrev 1 n : ℝ) * (1 / 6 : ℝ) := by positivity
          linarith
        exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith only [h2s_le])
      have hsub := finset_sum_le_resolventV (r := 1) (by decide) (s := 2 / 3) (x := 1 / 6)
        (by norm_num) (by norm_num) 4
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        metalQ, metalQPrev] at hsub
      norm_num at hsub
      have ha1 : 81 / 100 ≤ ((7 / 6 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha2 : 35 / 100 ≤ ((13 / 6 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      have ha3 : 19 / 100 ≤ ((10 / 3 : ℝ)) ^ (-((4 : ℝ) / 3)) :=
        le_rpow_neg_div (a := 4) (b := 3) (by norm_num) (by decide) (by norm_num)
      norm_num at ha1 ha2 ha3
      have hv_ge : (235 / 100 : ℝ) ≤ resolventV 1 s_lo (1 / ((1 + m : ℕ) : ℝ)) := by
        have hv0 : (235 / 100 : ℝ) ≤ resolventV 1 (2 / 3) (1 / 6) := by
          linarith only [hsub, ha1, ha2, ha3]
        exact hv0.trans hv1
      have htail_ge : (59 / 100 : ℝ) ≤ ((1 + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s_lo) := by
        have h7p := poly5_le_pow7 m hm5
        have hm2_pos : 0 < (m : ℝ) + 2 := by positivity
        have hlog5 : 5 * Real.log ((m : ℝ) + 2) ≤ (m : ℝ) * Real.log 7 := by
          have hl := Real.log_le_log (pow_pos hm2_pos 5) h7p
          simpa [Real.log_pow] using hl
        have hexp_le : -((4 / 15 : ℝ)) * Real.log 7 ≤ (1 - 2 * s_lo) * Real.log ((m : ℝ) + 2) := by
          have h12 : 1 - 2 * s_lo = -(4 / (3 * (m : ℝ))) := by dsimp [s_lo]; ring
          rw [h12]
          have : 4 / (3 * (m : ℝ)) * Real.log ((m : ℝ) + 2) ≤ 4 / 15 * Real.log 7 := by
            have hdiv : Real.log ((m : ℝ) + 2) / (m : ℝ) ≤ Real.log 7 / 5 := by
              rw [div_le_div_iff₀ hm_pos (by norm_num)]
              linarith only [hlog5]
            calc 4 / (3 * (m : ℝ)) * Real.log ((m : ℝ) + 2)
                = (4 / 3) * (Real.log ((m : ℝ) + 2) / (m : ℝ)) := by ring
              _ ≤ (4 / 3) * (Real.log 7 / 5) :=
                  mul_le_mul_of_nonneg_left hdiv (by norm_num)
              _ = 4 / 15 * Real.log 7 := by ring
          linarith only [this]
        have hrpow7 : (7 : ℝ) ^ (-(4 / 15 : ℝ)) ≤ ((m : ℝ) + 2) ^ (1 - 2 * s_lo) := by
          rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hm2_pos, Real.exp_le_exp]
          have h7l : Real.log 7 * (-(4 / 15 : ℝ)) = -(4 / 15 : ℝ) * Real.log 7 := by ring
          have hml : Real.log ((m : ℝ) + 2) * (1 - 2 * s_lo) =
              (1 - 2 * s_lo) * Real.log ((m : ℝ) + 2) := by ring
          linarith only [hexp_le, h7l, hml]
        have hnum7 : (59 / 100 : ℝ) ≤ (7 : ℝ) ^ (-(4 / 15 : ℝ)) := by
          have h7' := le_rpow_neg_div (x := (7 : ℝ)) (a := 4) (b := 15) (L := 59 / 100)
            (by norm_num) (by decide) (by norm_num)
          norm_num at h7' ⊢
          exact h7'
        have hcast : ((1 + m + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        exact hnum7.trans hrpow7
      have hden : (m : ℝ) * (2 * s_lo - 1) = 4 / 3 := by dsimp [s_lo]; field_simp; ring
      have hprod : 1 < (235 / 100 : ℝ) * ((59 / 100 : ℝ) / (4 / 3)) := by norm_num
      calc (1 : ℝ) < (235 / 100 : ℝ) * ((59 / 100 : ℝ) / (4 / 3)) := hprod
        _ ≤ resolventV 1 s_lo (1 / ((1 + m : ℕ) : ℝ)) *
              (((1 + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s_lo) / ((m : ℝ) * (2 * s_lo - 1))) := by
            rw [hden]
            exact mul_le_mul hv_ge (div_le_div_of_nonneg_right htail_ge (by norm_num))
              (by norm_num) (by linarith only [hv_ge])
    have hlt_s : s_hi < s_lo := by
      dsimp only [s_hi, s_lo]
      have : 5 / (8 * (m : ℝ)) < 2 / (3 * (m : ℝ)) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [hm_pos]
      linarith only [this]
    exact lt_of_le_of_lt hup
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hs_lo_pos).mpr hlt_s) hlo)

/-- Global separation against the eventually periodic residue set `E_m` (`m ≥ 2`). -/
theorem dimH_residueConstSet_mm_lt_eventuallyPeriodic (m : ℕ) (hm : 2 ≤ m) :
    dimH (residueConstSet m m) < dimH (eventuallyPeriodicResidueSet m) := by
  rw [dimH_eventuallyPeriodicResidueSet_eq hm]
  exact dimH_residueConstSet_mm_lt_m1 m hm

/-! ### Part 5: Exact Two-Term Asymptotics and First-Order Ratios (`m → ∞`) -/

private lemma exp_neg_le_one_sub_add_sq {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 := by
  have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hpos : 0 < 1 + t := by linarith
  have h2 : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos h1
  have h3 : 1 / (1 + t) ≤ 1 - t + t ^ 2 := by
    rw [div_le_iff₀ hpos]
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
    linarith
  exact h2.trans h3

private lemma log_add_le_log_add_div {m a : ℕ} (hm : 2 ≤ m) :
    Real.log ((m + a : ℕ) : ℝ) ≤ Real.log (m : ℝ) + (a : ℝ) / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hma : ((m + a : ℕ) : ℝ) = (m : ℝ) * (1 + (a : ℝ) / (m : ℝ)) := by
    push_cast; field_simp [hm_pos.ne']
  rw [hma, Real.log_mul hm_pos.ne' (by positivity)]
  have hlog : Real.log (1 + (a : ℝ) / (m : ℝ)) ≤ (a : ℝ) / (m : ℝ) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  linarith

private lemma tendsto_log_div_nat :
    Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (nhds 0) := by
  have h0 : Tendsto (fun m : ℕ => 2 * ((m : ℝ) ^ (-(1 / 2 : ℝ)))) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hlog : Real.log ((m : ℝ) ^ (1 / 2 : ℝ)) ≤ (m : ℝ) ^ (1 / 2 : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hm_pos (1 / 2 : ℝ))]
    have hlog2 : Real.log (m : ℝ) = 2 * Real.log ((m : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.log_rpow hm_pos]; ring
    have hmul : (m : ℝ) ^ (1 / 2 : ℝ) / (m : ℝ) = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (m : ℝ), ← Real.rpow_add hm_pos]
      congr 1; norm_num
    calc Real.log (m : ℝ) / (m : ℝ)
        = 2 * (Real.log ((m : ℝ) ^ (1 / 2 : ℝ)) / (m : ℝ)) := by rw [hlog2]; ring
      _ ≤ 2 * ((m : ℝ) ^ (1 / 2 : ℝ) / (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hm_pos.le) (by norm_num)
      _ = 2 * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hmul]

private lemma tendsto_log_sq_div_nat :
    Tendsto (fun m : ℕ => (Real.log (m : ℝ)) ^ 2 / (m : ℝ)) atTop (nhds 0) := by
  have h0 : Tendsto (fun m : ℕ => 16 * ((m : ℝ) ^ (-(1 / 2 : ℝ)))) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop).const_mul (16 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m _
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hlog4 : Real.log ((m : ℝ) ^ (1 / 4 : ℝ)) ≤ (m : ℝ) ^ (1 / 4 : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hm_pos (1 / 4 : ℝ))]
    have hlog_eq : Real.log (m : ℝ) = 4 * Real.log ((m : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [Real.log_rpow hm_pos]; ring
    have hlog_le : Real.log (m : ℝ) ≤ 4 * (m : ℝ) ^ (1 / 4 : ℝ) := by linarith
    have hsq : (Real.log (m : ℝ)) ^ 2 ≤ 16 * (m : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 := pow_le_pow_left₀ hlogm_nn hlog_le 2
      have h2 : (4 * (m : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = 16 * (m : ℝ) ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hm_pos.le]
        norm_num
      linarith
    have hmul : (m : ℝ) ^ (1 / 2 : ℝ) / (m : ℝ) = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one (m : ℝ), ← Real.rpow_add hm_pos]
      congr 1; norm_num
    calc (Real.log (m : ℝ)) ^ 2 / (m : ℝ)
        ≤ 16 * ((m : ℝ) ^ (1 / 2 : ℝ) / (m : ℝ)) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hsq hm_pos.le
      _ = 16 * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hmul]

private lemma asymp_upper_m_step {r : ℕ} (hr : 1 ≤ r) :
    ∃ B₁ > 0, ∀ᶠ m : ℕ in atTop,
      dimH (residueConstSet m r) ≤
        ENNReal.ofReal (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
          (metalC r 1) ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) + B₁ / (m : ℝ) ^ 2) := by
  let C : ℝ := metalC r 1
  have hC1 : 1 ≤ C := one_le_metalC hr zero_lt_one
  let B₁ : ℝ := C ^ 2 + 1
  have hB₁_pos : 0 < B₁ := by positivity
  refine ⟨B₁, hB₁_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (Nat.ceil (4 * B₁ / C) + 1)),
    tendsto_log_div_nat.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * C))),
    tendsto_log_sq_div_nat.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (5 * C ^ 3 + 1)))]
    with m hm0 h1 h2
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm0
  have hm_ceil : 4 * B₁ / C ≤ (m : ℝ) := by
    have : (Nat.ceil (4 * B₁ / C) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast le_trans (le_trans (Nat.le_succ _) (le_max_right _ _)) hm0
    exact (Nat.le_ceil _).trans this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : 1 ≤ m := by omega
  have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  let α : ℝ := C - C ^ 2 * Real.log m / (m : ℝ) + 2 * B₁ / (m : ℝ)
  let s : ℝ := 1 / 2 + α / (2 * (m : ℝ))
  have hs_eq : s = 1 / 2 + C / (2 * (m : ℝ)) - C ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) +
      B₁ / (m : ℝ) ^ 2 := by
    dsimp only [s, α]
    field_simp [hm_pos.ne']
    ring
  have hC_log : C ^ 2 * Real.log m / (m : ℝ) < C / 4 := by
    have : C ^ 2 * (Real.log m / (m : ℝ)) < C ^ 2 * (1 / (4 * C)) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have heq : C ^ 2 * (1 / (4 * C)) = C / 4 := by field_simp
    linarith [show C ^ 2 * Real.log m / (m : ℝ) = C ^ 2 * (Real.log m / (m : ℝ)) by ring]
  have hα_pos : C / 2 < α := by
    dsimp only [α]
    have : 0 ≤ 2 * B₁ / (m : ℝ) := by positivity
    linarith
  have hα_le : α ≤ 2 * C := by
    dsimp only [α]
    have hB_le : 2 * B₁ / (m : ℝ) ≤ C := by
      rw [div_le_iff₀ hm_pos]
      have h_mul : 4 * B₁ ≤ (m : ℝ) * C := (div_le_iff₀ (by positivity : 0 < C)).mp hm_ceil
      linarith
    have hnn : 0 ≤ C ^ 2 * Real.log m / (m : ℝ) := by positivity
    linarith
  have hs_gt : 1 / 2 < s := by
    dsimp only [s]
    have : 0 < α / (2 * (m : ℝ)) := div_pos (by linarith) (by positivity)
    linarith
  have h2s_sub : 2 * s - 1 = α / (m : ℝ) := by dsimp only [s]; field_simp; ring
  have hm_den : (m : ℝ) * (2 * s - 1) = α := by rw [h2s_sub]; field_simp [hm_pos.ne']
  have h_le_C : metalC r (2 * s) ≤ C :=
    metalC_antitone_p hr zero_lt_one (by linarith : (1 : ℝ) ≤ 2 * s)
  have ht_nn : 0 ≤ (α / (m : ℝ)) * Real.log (m : ℝ) :=
    mul_nonneg (div_nonneg (by linarith only [hC1, hα_pos]) hm_pos.le) hlogm_nn
  have ht_le : (α / (m : ℝ)) * Real.log (m : ℝ) ≤ 2 * C * Real.log (m : ℝ) / (m : ℝ) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hα_le hlogm_nn) hm_pos.le
  have ht_sq : ((α / (m : ℝ)) * Real.log (m : ℝ)) ^ 2 ≤
      4 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
    have hsq := pow_le_pow_left₀ ht_nn ht_le 2
    calc ((α / (m : ℝ)) * Real.log (m : ℝ)) ^ 2
        ≤ (2 * C * Real.log (m : ℝ) / (m : ℝ)) ^ 2 := hsq
      _ = 4 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by ring
  have hm_rpow : ((r + m : ℕ) : ℝ) ^ (1 - 2 * s) ≤
      1 - C * Real.log (m : ℝ) / (m : ℝ) +
        5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
    have hrm_ge : (m : ℝ) ≤ ((r + m : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ r + m)
    have hrm_pow : ((r + m : ℕ) : ℝ) ^ (1 - 2 * s) ≤ (m : ℝ) ^ (-(α / (m : ℝ))) := by
      have h1' : 1 - 2 * s = -(α / (m : ℝ)) := by linarith [h2s_sub]
      rw [h1']
      exact Real.rpow_le_rpow_of_nonpos hm_pos hrm_ge
        (by linarith only [div_pos (by linarith only [hC1, hα_pos] : 0 < α) hm_pos])
    have hexp_eq : (m : ℝ) ^ (-(α / (m : ℝ))) = Real.exp (-((α / (m : ℝ)) * Real.log (m : ℝ))) := by
      rw [Real.rpow_def_of_pos hm_pos]; congr 1; ring
    refine hrm_pow.trans (hexp_eq.symm ▸ (exp_neg_le_one_sub_add_sq ht_nn).trans ?_)
    have ht_sub : (α / (m : ℝ)) * Real.log (m : ℝ) =
        C * Real.log (m : ℝ) / (m : ℝ) -
          (C ^ 2 * (Real.log (m : ℝ)) ^ 2 - 2 * B₁ * Real.log (m : ℝ)) / (m : ℝ) ^ 2 := by
      dsimp only [α]
      field_simp [hm_pos.ne']
      ring
    have h2B_nn : 0 ≤ 2 * B₁ * Real.log (m : ℝ) / (m : ℝ) ^ 2 := by positivity
    calc 1 - (α / (m : ℝ)) * Real.log (m : ℝ) + ((α / (m : ℝ)) * Real.log (m : ℝ)) ^ 2
        = 1 - C * Real.log (m : ℝ) / (m : ℝ) +
            C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 -
            2 * B₁ * Real.log (m : ℝ) / (m : ℝ) ^ 2 +
            ((α / (m : ℝ)) * Real.log (m : ℝ)) ^ 2 := by rw [ht_sub]; ring
      _ ≤ 1 - C * Real.log (m : ℝ) / (m : ℝ) +
            C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 +
            4 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by linarith [h2B_nn, ht_sq]
      _ = 1 - C * Real.log (m : ℝ) / (m : ℝ) +
            5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by ring
  have h_inv_le : ((r + m : ℕ) : ℝ) ^ (-(2 * s)) ≤ 1 / (m : ℝ) := by
    have hrm1 : (m : ℝ) ≤ ((r + m : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ r + m)
    have h1' : ((r + m : ℕ) : ℝ) ^ (-(2 * s)) ≤ (m : ℝ) ^ (-(2 * s)) :=
      Real.rpow_le_rpow_of_nonpos hm_pos hrm1 (by linarith)
    have h2' : (m : ℝ) ^ (-(2 * s)) ≤ (m : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm1) (by linarith)
    rw [Real.rpow_neg_one, ← one_div] at h2'
    exact h1'.trans h2'
  have hcond : metalC r (2 * s) *
      ((((r + m : ℕ) : ℝ) ^ (-(2 * s))) +
        ((((r + m : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1)))) ≤ 1 := by
    rw [hm_den]
    have hα0 : 0 < α := by linarith
    have h_inner : (((r + m : ℕ) : ℝ) ^ (-(2 * s))) + ((r + m : ℕ) : ℝ) ^ (1 - 2 * s) / α ≤
        1 / (m : ℝ) + (1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) / α :=
      add_le_add h_inv_le (div_le_div_of_nonneg_right hm_rpow hα0.le)
    have hC_pos : 0 ≤ metalC r (2 * s) := (metalC_pos hr (by linarith)).le
    have hstep1 := mul_le_mul_of_nonneg_left h_inner hC_pos
    have hsubC : metalC r (2 * s) * (1 / (m : ℝ) +
        (1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) / α) ≤
        C * (1 / (m : ℝ) +
          (1 - C * Real.log (m : ℝ) / (m : ℝ) +
            5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) / α) := by
      refine mul_le_mul_of_nonneg_right h_le_C ?_
      have hpos_num : 0 ≤ 1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
        have : C * Real.log (m : ℝ) / (m : ℝ) < 1 / 4 := by
          have := mul_lt_mul_of_pos_left h1 (by positivity : 0 < C)
          have he : C * (1 / (4 * C)) = 1 / 4 := by field_simp
          linarith [show C * Real.log (m : ℝ) / (m : ℝ) = C * (Real.log (m : ℝ) / (m : ℝ)) by ring]
        have : 0 ≤ 5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by positivity
        linarith
      exact add_nonneg (by positivity) (div_nonneg hpos_num hα0.le)
    have hC_step : C * (1 / (m : ℝ) +
        (1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) / α) ≤ 1 := by
      have hrew : C * (1 / (m : ℝ) + (1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) / α) =
          (C * (1 / (m : ℝ)) * α + C * (1 - C * Real.log (m : ℝ) / (m : ℝ) +
            5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2)) / α := by
        field_simp [hα0.ne']
      rw [hrew, div_le_one hα0]
      have hlog2_mul : 5 * C ^ 3 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ)) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h2.le (by positivity : 0 ≤ 5 * C ^ 3)
        calc 5 * C ^ 3 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))
            ≤ 5 * C ^ 3 * (1 / (5 * C ^ 3 + 1)) := this
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
      have h1_α : C * (1 / (m : ℝ)) * α ≤ 2 * C ^ 2 / (m : ℝ) := by
        calc C * (1 / (m : ℝ)) * α ≤ C * (1 / (m : ℝ)) * (2 * C) :=
              mul_le_mul_of_nonneg_left hα_le (by positivity)
          _ = 2 * C ^ 2 / (m : ℝ) := by ring
      have hexp : C * (1 - C * Real.log (m : ℝ) / (m : ℝ) +
          5 * C ^ 2 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2) =
          C - C ^ 2 * Real.log (m : ℝ) / (m : ℝ) +
            (5 * C ^ 3 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))) / (m : ℝ) := by ring
      have h5_div : (5 * C ^ 3 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))) / (m : ℝ) ≤ 1 / (m : ℝ) :=
        div_le_div_of_nonneg_right hlog2_mul hm_pos.le
      have hB_cmp : (2 * C ^ 2 + 1) / (m : ℝ) < 2 * B₁ / (m : ℝ) := by
        refine div_lt_div_of_pos_right ?_ hm_pos
        dsimp only [B₁]
        linarith
      have hadd : (2 * C ^ 2 + 1) / (m : ℝ) = 2 * C ^ 2 / (m : ℝ) + 1 / (m : ℝ) :=
        add_div _ _ _
      dsimp only [α] at *
      linarith only [h1_α, hexp, h5_div, hadd, hB_cmp]
    exact hstep1.trans (hsubC.trans hC_step)
  rw [← hs_eq]
  exact dimH_residueConstSet_le_of_resolvent hm1 hr hs_gt hcond

private lemma resolventV_inv_factor_lower {r : ℕ} (hr : 1 ≤ r) {s y : ℝ}
    (hs : 0 < s) (hy0 : 0 ≤ y) :
    (1 + y) ^ (-(2 * s)) * metalC r (2 * s) ≤ resolventV r s y := by
  unfold metalC resolventV
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_)
    ((summable_metalQ_rpow hr (by linarith)).mul_left _)
    (summable_resolventV hr hs hy0)
  have hqp : (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * y ≤ (metalQ r n : ℝ) * (1 + y) := by
    have hprev : (metalQPrev r n : ℝ) ≤ (metalQ r n : ℝ) := by
      exact_mod_cast metalQPrev_le_metalQ hr n
    nlinarith only [hprev, hy0]
  have hpos1 : (0 : ℝ) < (metalQ r n : ℝ) + (metalQPrev r n : ℝ) * y := by
    have hq : (0 : ℝ) < (metalQ r n : ℝ) := by exact_mod_cast metalQ_pos hr n
    have hp : 0 ≤ (metalQPrev r n : ℝ) * y := mul_nonneg (Nat.cast_nonneg _) hy0
    linarith only [hq, hp]
  have hmul := Real.rpow_le_rpow_of_nonpos hpos1 hqp (by linarith only [hs] : -(2 * s) ≤ 0)
  have hpow_mul : ((metalQ r n : ℝ) * (1 + y)) ^ (-(2 * s)) =
      (1 + y) ^ (-(2 * s)) * ((metalQ r n : ℝ)) ^ (-(2 * s)) := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (by linarith only [hy0]), mul_comm]
  linarith only [hmul, hpow_mul]

private lemma one_add_rpow_neg_two_ge {y p : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hp : p ≤ 2) :
    1 - 2 * y ≤ (1 + y) ^ (-p) := by
  have h1y_pos : 0 < 1 + y := by linarith only [hy0]
  have h_exp : (1 + y) ^ (-2 : ℝ) ≤ (1 + y) ^ (-p) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hy0]) (by linarith only [hp])
  have h_alg : (1 + y) ^ (-2 : ℝ) = (1 / (1 + y)) ^ 2 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1y_pos.le,
      Real.rpow_natCast, one_div, inv_pow]
  have hinv : 1 - y ≤ 1 / (1 + y) := by
    rw [le_div_iff₀ h1y_pos]
    nlinarith only [sq_nonneg y]
  have hsq1 : (1 - y) ^ 2 ≤ (1 / (1 + y)) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hy1]) hinv 2
  have h_lin : 1 - 2 * y ≤ (1 - y) ^ 2 := by nlinarith only [sq_nonneg y]
  exact h_lin.trans (hsq1.trans (h_alg ▸ h_exp))

private lemma asymp_lower_m_step {r : ℕ} (hr : 1 ≤ r) :
    ∃ B₂ > 0, ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
        (metalC r 1) ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) - B₂ / (m : ℝ) ^ 2) ≤
        dimH (residueConstSet m r) := by
  let C : ℝ := metalC r 1
  let D : ℝ := ∑' n : ℕ, Real.log (metalQ r n : ℝ) / (metalQ r n : ℝ)
  have hC1 : 1 ≤ C := one_le_metalC hr zero_lt_one
  have hD_nn : 0 ≤ D := tsum_nonneg fun n =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast metalQ_pos hr n)) (Nat.cast_nonneg _)
  let B₂ : ℝ := C + D * C + C ^ 2 * (r + 1 : ℝ) + 1
  have hB₂_pos : 0 < B₂ := by positivity
  refine ⟨B₂, hB₂_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (max 4 (Nat.ceil (8 * B₂ / C) + 1)),
    tendsto_log_div_nat.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * C))),
    tendsto_log_div_nat.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((2 * C + D * C) * C + 1)))]
    with m hm0 h1 hlog_small
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm0
  have hm_ceil : 8 * B₂ / C ≤ (m : ℝ) := by
    have : (Nat.ceil (8 * B₂ / C) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast le_trans (le_trans (Nat.le_succ _) (le_max_right _ _)) hm0
    exact (Nat.le_ceil _).trans this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : 1 ≤ m := by omega
  have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  let α : ℝ := C - C ^ 2 * Real.log m / (m : ℝ) - 2 * B₂ / (m : ℝ)
  let s : ℝ := 1 / 2 + α / (2 * (m : ℝ))
  have hs_eq : s = 1 / 2 + C / (2 * (m : ℝ)) - C ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) -
      B₂ / (m : ℝ) ^ 2 := by
    dsimp only [s, α]; field_simp [hm_pos.ne']; ring
  have hC_log : C ^ 2 * Real.log m / (m : ℝ) < C / 4 := by
    have : C ^ 2 * (Real.log m / (m : ℝ)) < C ^ 2 * (1 / (4 * C)) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have heq : C ^ 2 * (1 / (4 * C)) = C / 4 := by field_simp
    linarith only [this, heq,
      show C ^ 2 * Real.log m / (m : ℝ) = C ^ 2 * (Real.log m / (m : ℝ)) by ring]
  have hB_le : 2 * B₂ / (m : ℝ) ≤ C / 4 := by
    rw [div_le_iff₀ hm_pos]
    have h_mul : 8 * B₂ ≤ (m : ℝ) * C := (div_le_iff₀ (by positivity : 0 < C)).mp hm_ceil
    linarith only [h_mul]
  have hα_pos : C / 2 < α := by dsimp only [α]; linarith only [hC_log, hB_le]
  have hα_le : α ≤ C := by
    dsimp only [α]
    have h1' : 0 ≤ C ^ 2 * Real.log m / (m : ℝ) := by positivity
    have h2' : 0 ≤ 2 * B₂ / (m : ℝ) := by positivity
    linarith only [h1', h2']
  have hs_gt : 1 / 2 < s := by
    dsimp only [s]
    have : 0 < α / (2 * (m : ℝ)) := div_pos (by linarith only [hC1, hα_pos]) (by positivity)
    linarith only [this]
  have h2s_le2 : 2 * s ≤ 2 := by
    have h2s : 2 * s = 1 + α / (m : ℝ) := by dsimp only [s]; ring
    have hαm : α / (m : ℝ) ≤ C / (m : ℝ) := div_le_div_of_nonneg_right hα_le hm_pos.le
    have hCm : C / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm_pos]
      have h_mul : 8 * B₂ ≤ (m : ℝ) * C := (div_le_iff₀ (by positivity : 0 < C)).mp hm_ceil
      have hC_le_B : C ≤ 8 * B₂ / C := by
        rw [le_div_iff₀ (by positivity : 0 < C)]
        dsimp only [B₂]; nlinarith only [hC1, hD_nn]
      exact hC_le_B.trans hm_ceil
    linarith only [h2s, hαm, hCm]
  have h2s_sub : 2 * s - 1 = α / (m : ℝ) := by dsimp only [s]; field_simp; ring
  have hm_den : (m : ℝ) * (2 * s - 1) = α := by rw [h2s_sub]; field_simp [hm_pos.ne']
  let y : ℝ := 1 / ((r + m : ℕ) : ℝ)
  have hy_nn : 0 ≤ y := by positivity
  have hy_le : y ≤ 1 / (m : ℝ) :=
    one_div_le_one_div_of_le hm_pos (by exact_mod_cast (by omega : m ≤ r + m))
  have hm4R : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
  have hy_le1 : y ≤ 1 :=
    hy_le.trans (div_le_one hm_pos |>.mpr (by linarith only [hm4R]))
  have hv_fac := resolventV_inv_factor_lower hr (by linarith only [hs_gt] : 0 < s) hy_nn
  have h1y_ge : 1 - 2 / (m : ℝ) ≤ (1 + y) ^ (-(2 * s)) := by
    have h2y : 2 * y ≤ 2 / (m : ℝ) := by
      rw [show (2 : ℝ) / (m : ℝ) = 2 * (1 / (m : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left hy_le (by norm_num)
    exact (by linarith only [h2y] : 1 - 2 / (m : ℝ) ≤ 1 - 2 * y).trans
      (one_add_rpow_neg_two_ge hy_nn hy_le1 h2s_le2)
  have hC_diff : C - D * C / (m : ℝ) ≤ metalC r (2 * s) := by
    have h2s_eq : 2 * s = 1 + α / (m : ℝ) := by dsimp only [s]; ring
    rw [h2s_eq]
    have hα_nn : 0 ≤ α / (m : ℝ) := div_nonneg (by linarith only [hC1, hα_pos]) hm_pos.le
    have hlip := (metalC_sub_le_of_nonneg hr hα_nn).2
    have hDα : D * (α / (m : ℝ)) ≤ D * C / (m : ℝ) := by
      calc D * (α / (m : ℝ)) ≤ D * (C / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hα_le hm_pos.le) hD_nn
        _ = D * C / (m : ℝ) := by ring
    dsimp only [C, D] at *; linarith only [hlip, hDα]
  have hv_ge : C - (2 * C + D * C) / (m : ℝ) ≤ resolventV r s y := by
    have h1y_nn : 0 ≤ 1 - 2 / (m : ℝ) := by rw [sub_nonneg, div_le_one hm_pos]; linarith only [hm4R]
    have hCm_nn : 0 ≤ C - D * C / (m : ℝ) := by
      have hdc : D * C / (m : ℝ) ≤ B₂ / (m : ℝ) :=
        div_le_div_of_nonneg_right (by dsimp only [B₂]; nlinarith only [hC1, hD_nn]) hm_pos.le
      have h2B : 2 * (B₂ / (m : ℝ)) = 2 * B₂ / (m : ℝ) := by ring
      linarith only [hB_le, hdc, h2B, hC1]
    have hmul_ge : (1 - 2 / (m : ℝ)) * (C - D * C / (m : ℝ)) ≤
        (1 + y) ^ (-(2 * s)) * metalC r (2 * s) :=
      mul_le_mul h1y_ge hC_diff hCm_nn (h1y_nn.trans h1y_ge)
    have h_rem : 0 ≤ 2 * D * C / (m : ℝ) ^ 2 := by positivity
    have h_alg : C - (2 * C + D * C) / (m : ℝ) =
        (1 - 2 / (m : ℝ)) * (C - D * C / (m : ℝ)) - 2 * D * C / (m : ℝ) ^ 2 := by ring
    linarith only [h_alg, h_rem, hmul_ge, hv_fac]
  have htail_ge : 1 - C * Real.log (m : ℝ) / (m : ℝ) - C * (r + 1 : ℝ) / (m : ℝ) ^ 2 ≤
      ((r + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s) := by
    have hrm1_pos : (0 : ℝ) < ((r + m + 1 : ℕ) : ℝ) := by positivity
    have h12 : 1 - 2 * s = -(α / (m : ℝ)) := by linarith only [h2s_sub]
    rw [h12, Real.rpow_def_of_pos hrm1_pos]
    have hexp := Real.add_one_le_exp (-(Real.log ((r + m + 1 : ℕ) : ℝ) * (α / (m : ℝ))))
    have hlog_bd : Real.log ((r + m + 1 : ℕ) : ℝ) ≤
        Real.log (m : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ) := by
      have hm2 : 2 ≤ m := by omega
      have h_eq : r + m + 1 = m + (r + 1) := by omega
      rw [h_eq]; exact log_add_le_log_add_div hm2
    have hlog_sum_nn : 0 ≤ Real.log (m : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ) :=
      add_nonneg (Real.log_nonneg (by exact_mod_cast hm1)) (by positivity)
    have hαm_nn : 0 ≤ α / (m : ℝ) := div_nonneg (by linarith only [hC1, hα_pos]) hm_pos.le
    have hprod_bd : Real.log ((r + m + 1 : ℕ) : ℝ) * (α / (m : ℝ)) ≤
        C * Real.log (m : ℝ) / (m : ℝ) + C * (r + 1 : ℝ) / (m : ℝ) ^ 2 := by
      have h1' := mul_le_mul_of_nonneg_right hlog_bd hαm_nn
      have h2' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hα_le hm_pos.le) hlog_sum_nn
      have h3' : (Real.log (m : ℝ) + ((r + 1 : ℕ) : ℝ) / (m : ℝ)) * (C / (m : ℝ)) =
          C * Real.log (m : ℝ) / (m : ℝ) + C * (r + 1 : ℝ) / (m : ℝ) ^ 2 := by
        push_cast; ring
      linarith only [h1', h2', h3']
    have h_arg : -(Real.log ((r + m + 1 : ℕ) : ℝ) * (α / (m : ℝ))) =
        Real.log ((r + m + 1 : ℕ) : ℝ) * -(α / (m : ℝ)) := by ring
    rw [h_arg] at hexp
    linarith only [hexp, hprod_bd]
  have hcond : 1 < resolventV r s (1 / ((r + m : ℕ) : ℝ)) *
      ((((r + m + 1 : ℕ) : ℝ) ^ (1 - 2 * s)) / ((m : ℝ) * (2 * s - 1))) := by
    rw [hm_den, mul_div_assoc', lt_div_iff₀ (by linarith only [hC1, hα_pos] : 0 < α), one_mul]
    have ht_nn : 0 ≤ 1 - C * Real.log (m : ℝ) / (m : ℝ) - C * (r + 1 : ℝ) / (m : ℝ) ^ 2 := by
      have hCr_le : C * (r + 1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 4 := by
        have hBm : C * (r + 1 : ℝ) ≤ (m : ℝ) := by
          have : C * (r + 1 : ℝ) ≤ 8 * B₂ / C := by
            rw [le_div_iff₀ (by positivity : 0 < C)]
            dsimp only [B₂]; nlinarith only [hC1, hD_nn]
          exact this.trans hm_ceil
        rw [div_le_iff₀ (by positivity)]
        nlinarith only [hBm, hm4R]
      have hC_log1 : C * Real.log (m : ℝ) / (m : ℝ) < 1 / 4 := by
        have hm1' := mul_lt_mul_of_pos_left h1 (by positivity : 0 < C)
        have heq : C * (1 / (4 * C)) = 1 / 4 := by field_simp
        linarith only [hm1', heq,
          show C * Real.log (m : ℝ) / (m : ℝ) = C * (Real.log (m : ℝ) / (m : ℝ)) by ring]
      linarith only [hC_log1, hCr_le]
    have hv_nn : 0 ≤ C - (2 * C + D * C) / (m : ℝ) := by
      have h2B_le : (2 * C + D * C) / (m : ℝ) ≤ 2 * B₂ / (m : ℝ) :=
        div_le_div_of_nonneg_right (by dsimp only [B₂]; nlinarith only [hC1, hD_nn]) hm_pos.le
      linarith only [h2B_le, hB_le, hC1]
    have hmul := mul_le_mul hv_ge htail_ge ht_nn (hv_nn.trans hv_ge)
    have hcross : (2 * C + D * C) * (C * Real.log (m : ℝ) / (m : ℝ)) ≤ 1 := by
      have h_le := mul_le_mul_of_nonneg_left hlog_small.le (by positivity : 0 ≤ (2 * C + D * C) * C)
      calc (2 * C + D * C) * (C * Real.log (m : ℝ) / (m : ℝ))
          = ((2 * C + D * C) * C) * (Real.log (m : ℝ) / (m : ℝ)) := by ring
        _ ≤ ((2 * C + D * C) * C) * (1 / ((2 * C + D * C) * C + 1)) := h_le
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith only [hC1, hD_nn]
    have hrem_nn : 0 ≤ (2 * C + D * C) * C * (r + 1 : ℝ) / (m : ℝ) ^ 3 := by positivity
    have h_alg : (C - (2 * C + D * C) / (m : ℝ)) *
          (1 - C * Real.log (m : ℝ) / (m : ℝ) - C * (r + 1 : ℝ) / (m : ℝ) ^ 2)
        = C - C ^ 2 * Real.log (m : ℝ) / (m : ℝ) - (2 * C + D * C) / (m : ℝ) -
            C ^ 2 * (r + 1 : ℝ) / (m : ℝ) ^ 2 +
            ((2 * C + D * C) * (C * Real.log (m : ℝ) / (m : ℝ))) / (m : ℝ) +
            (2 * C + D * C) * C * (r + 1 : ℝ) / (m : ℝ) ^ 3 := by ring
    have h_r1 : C ^ 2 * (r + 1 : ℝ) / (m : ℝ) ^ 2 ≤ C ^ 2 * (r + 1 : ℝ) / (m : ℝ) := by
      refine div_le_div_of_nonneg_left (by positivity) hm_pos ?_
      nlinarith only [hm4R]
    have h_b2 : (2 * C + D * C + C ^ 2 * (r + 1 : ℝ)) / (m : ℝ) < 2 * B₂ / (m : ℝ) := by
      refine div_lt_div_of_pos_right ?_ hm_pos
      dsimp only [B₂]; nlinarith only [hC1, hD_nn]
    have h_pos_cross : 0 ≤ ((2 * C + D * C) * (C * Real.log (m : ℝ) / (m : ℝ))) / (m : ℝ) := by
      have : 0 ≤ (2 * C + D * C) * (C * Real.log (m : ℝ) / (m : ℝ)) := by positivity
      positivity
    have h_div_add : (2 * C + D * C + C ^ 2 * (r + 1 : ℝ)) / (m : ℝ) =
        (2 * C + D * C) / (m : ℝ) + C ^ 2 * (r + 1 : ℝ) / (m : ℝ) := by ring
    have h_cmp : α < (C - (2 * C + D * C) / (m : ℝ)) *
        (1 - C * Real.log (m : ℝ) / (m : ℝ) - C * (r + 1 : ℝ) / (m : ℝ) ^ 2) := by
      dsimp only [α]
      linarith only [h_alg, hrem_nn, h_r1, h_b2, h_pos_cross, h_div_add]
    exact h_cmp.trans_le hmul
  rw [← hs_eq]
  exact le_dimH_residueConstSet_of_resolvent hm1 hr hs_gt hcond

/-- **Exact Two-Term Asymptotic Expansion for `dimH F_{m,r}` (`m → ∞`)**:
    For every fixed shift `r ≥ 1`,
    `dimH F_{m,r} = 1/2 + C_r / (2m) - C_r^2 log m / (2m^2) + O_r(1/m^2)`,
    where `C_1 = ψ_Fib = ∑_{n≥1} 1 / F_n`. -/
theorem dimH_residueConstSet_asymp_two_term (r : ℕ) (hr : 1 ≤ r) :
    ∃ B > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (residueConstSet m r)).toReal -
        (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
          (metalC r 1) ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2))| ≤ B / (m : ℝ) ^ 2 := by
  obtain ⟨B₁, hB₁, hup⟩ := asymp_upper_m_step hr
  obtain ⟨B₂, hB₂, hlo⟩ := asymp_lower_m_step hr
  let B := max B₁ B₂
  have hB : 0 < B := lt_max_of_lt_left hB₁
  refine ⟨B, hB, ?_⟩
  let C : ℝ := metalC r 1
  have hC1 : 1 ≤ C := one_le_metalC hr zero_lt_one
  filter_upwards [hup, hlo, eventually_ge_atTop (max 4 (Nat.ceil (8 * B / C) + 1)),
    tendsto_log_div_nat.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * C ^ 2)))]
    with m hum hlm hm0 hlogC2
  have hm4 : 4 ≤ m := le_trans (le_max_left _ _) hm0
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have h_mid_nonneg : 0 ≤ 1 / 2 + C / (2 * (m : ℝ)) -
      C ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) + B₁ / (m : ℝ) ^ 2 := by
    have h1' : C ^ 2 * Real.log (m : ℝ) / (m : ℝ) < 1 / 2 := by
      have hm1' := mul_lt_mul_of_pos_left hlogC2 (by positivity : 0 < C ^ 2)
      have heq : C ^ 2 * (1 / (2 * C ^ 2)) = 1 / 2 := by field_simp
      linarith only [hm1', heq, show C ^ 2 * Real.log (m : ℝ) / (m : ℝ) =
        C ^ 2 * (Real.log (m : ℝ) / (m : ℝ)) by ring]
    have h2' : C ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) ≤ (1 / 2) / (2 * (m : ℝ)) := by
      have : C ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) =
          (C ^ 2 * Real.log (m : ℝ) / (m : ℝ)) / (2 * (m : ℝ)) := by ring
      rw [this]
      exact div_le_div_of_nonneg_right h1'.le (by positivity)
    have h3' : (1 / 2 : ℝ) / (2 * (m : ℝ)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm4
      linarith only [this]
    have h4' : 0 ≤ C / (2 * (m : ℝ)) := by positivity
    have h5' : 0 ≤ B₁ / (m : ℝ) ^ 2 := by positivity
    linarith only [h2', h3', h4', h5']
  have hne_top : dimH (residueConstSet m r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hum
  have h_toReal_le : (dimH (residueConstSet m r)).toReal ≤
      1 / 2 + C / (2 * (m : ℝ)) - C ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) + B₁ / (m : ℝ) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal h_mid_nonneg hum
  have h_le_toReal : 1 / 2 + C / (2 * (m : ℝ)) - C ^ 2 * Real.log m / (2 * (m : ℝ) ^ 2) -
      B₂ / (m : ℝ) ^ 2 ≤ (dimH (residueConstSet m r)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hlm
  rw [abs_le]
  have hB1_le : B₁ / (m : ℝ) ^ 2 ≤ B / (m : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_max_left B₁ B₂) (by positivity)
  have hB2_le : B₂ / (m : ℝ) ^ 2 ≤ B / (m : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_max_right B₁ B₂) (by positivity)
  constructor <;> dsimp only [C] at h_toReal_le h_le_toReal <;> linarith

/-- **Exact Two-Term Asymptotic Expansion for `dimH F_{m,m}` (`m → ∞`)**:
    `dimH F_{m,m} = 1/2 + 1/(2m) - (log m)/(2m^2) + O(1/m^2)`. -/
theorem dimH_residueConstSet_mm_asymp_two_term :
    ∃ B > 0, ∀ᶠ m : ℕ in atTop,
      |(dimH (residueConstSet m m)).toReal -
        (1 / 2 + 1 / (2 * (m : ℝ)) - Real.log m / (2 * (m : ℝ) ^ 2))| ≤ B / (m : ℝ) ^ 2 := by
  let B : ℝ := 2
  have hB : 0 < B := by norm_num
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop 20,
    tendsto_log_div_nat.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    tendsto_log_sq_div_nat.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))]
    with m hm20 h1 h2
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : 1 ≤ m := by omega
  have hm20R : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm20
  have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
  have hlm_div_nn : 0 ≤ Real.log (m : ℝ) / (m : ℝ) := div_nonneg hlogm_nn hm_pos.le
  let α_u : ℝ := 1 - Real.log m / (m : ℝ) + 2 * B / (m : ℝ)
  let s_u : ℝ := 1 / 2 + α_u / (2 * (m : ℝ))
  let α_l : ℝ := 1 - Real.log m / (m : ℝ) - 2 * B / (m : ℝ)
  let s_l : ℝ := 1 / 2 + α_l / (2 * (m : ℝ))
  have hsu_eq : s_u = 1 / 2 + 1 / (2 * (m : ℝ)) - Real.log m / (2 * (m : ℝ) ^ 2) + B / (m : ℝ) ^ 2 := by
    dsimp only [s_u, α_u]; field_simp [hm_pos.ne']; ring
  have hsl_eq : s_l = 1 / 2 + 1 / (2 * (m : ℝ)) - Real.log m / (2 * (m : ℝ) ^ 2) - B / (m : ℝ) ^ 2 := by
    dsimp only [s_l, α_l]; field_simp [hm_pos.ne']; ring
  have h4m : 4 / (m : ℝ) ≤ 1 / 5 := (div_le_iff₀ hm_pos).mpr (by linarith only [hm20R])
  have hαu_pos : 0 < α_u := by
    dsimp only [α_u, B]; linarith only [h1, show 0 ≤ 4 / (m : ℝ) from by positivity]
  have hαu_le : α_u ≤ 3 / 2 := by dsimp only [α_u, B]; linarith only [hlm_div_nn, h4m]
  have hαl_pos : 1 / 2 < α_l := by dsimp only [α_l, B]; linarith only [h1, h4m]
  have hαl_le : α_l ≤ 1 := by
    dsimp only [α_l, B]; linarith only [hlm_div_nn, show 0 ≤ 4 / (m : ℝ) from by positivity]
  have hs_u_gt : 1 / 2 < s_u := by
    dsimp only [s_u]; linarith only [div_pos hαu_pos (by positivity : 0 < 2 * (m : ℝ))]
  have hs_l_gt : 1 / 2 < s_l := by
    dsimp only [s_l]
    linarith only [div_pos (by linarith only [hαl_pos] : 0 < α_l) (by positivity : 0 < 2 * (m : ℝ))]
  have hum : dimH (residueConstSet m m) ≤ ENNReal.ofReal s_u := by
    refine dimH_residueConstSet_mm_le_one hm1 hs_u_gt ?_
    have h2su : 2 * s_u - 1 = α_u / (m : ℝ) := by dsimp only [s_u]; field_simp; ring
    have hfac : (m : ℝ) ^ (-(2 * s_u)) * (1 + 1 / (2 * s_u - 1)) =
        (m : ℝ) ^ (-(α_u / (m : ℝ))) * (1 / (m : ℝ) + 1 / α_u) := by
      rw [h2su, show -(2 * s_u) = -1 + -(α_u / (m : ℝ)) by dsimp only [s_u]; ring,
        Real.rpow_add hm_pos, Real.rpow_neg_one]
      field_simp [hm_pos.ne', hαu_pos.ne']
    rw [hfac]
    have hrew : (m : ℝ) ^ (-(α_u / (m : ℝ))) * (1 / (m : ℝ) + 1 / α_u) =
        ((m : ℝ) ^ (-(α_u / (m : ℝ))) * (1 / (m : ℝ)) * α_u +
          (m : ℝ) ^ (-(α_u / (m : ℝ)))) / α_u := by
      field_simp [hαu_pos.ne']
    rw [hrew, div_le_one hαu_pos]
    have ht_nn : 0 ≤ (α_u / (m : ℝ)) * Real.log (m : ℝ) :=
      mul_nonneg (div_nonneg hαu_pos.le hm_pos.le) hlogm_nn
    have hm_exp : (m : ℝ) ^ (-(α_u / (m : ℝ))) =
        Real.exp (-((α_u / (m : ℝ)) * Real.log (m : ℝ))) := by
      rw [Real.rpow_def_of_pos hm_pos]; congr 1; ring
    have hm_le1 : (m : ℝ) ^ (-(α_u / (m : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm1)
        (by linarith only [div_nonneg hαu_pos.le hm_pos.le])
    have ht_le : (α_u / (m : ℝ)) * Real.log (m : ℝ) ≤ 3 / 2 * Real.log (m : ℝ) / (m : ℝ) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hαu_le hlogm_nn) hm_pos.le
    have ht_sq : ((α_u / (m : ℝ)) * Real.log (m : ℝ)) ^ 2 ≤
        9 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
      have hsq := pow_le_pow_left₀ ht_nn ht_le 2
      calc ((α_u / (m : ℝ)) * Real.log (m : ℝ)) ^ 2
          ≤ (3 / 2 * Real.log (m : ℝ) / (m : ℝ)) ^ 2 := hsq
        _ = 9 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by ring
    have hexp_bd : (m : ℝ) ^ (-(α_u / (m : ℝ))) ≤
        1 - Real.log (m : ℝ) / (m : ℝ) + 13 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
      rw [hm_exp]
      refine (exp_neg_le_one_sub_add_sq ht_nn).trans ?_
      have htsub : (α_u / (m : ℝ)) * Real.log (m : ℝ) =
          Real.log (m : ℝ) / (m : ℝ) -
            ((Real.log (m : ℝ)) ^ 2 - 2 * B * Real.log (m : ℝ)) / (m : ℝ) ^ 2 := by
        dsimp only [α_u]; field_simp [hm_pos.ne']; ring
      have hBnn : 0 ≤ 2 * B * Real.log (m : ℝ) / (m : ℝ) ^ 2 := by positivity
      calc 1 - (α_u / (m : ℝ)) * Real.log (m : ℝ) + ((α_u / (m : ℝ)) * Real.log (m : ℝ)) ^ 2
          = 1 - Real.log (m : ℝ) / (m : ℝ) + (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 -
              2 * B * Real.log (m : ℝ) / (m : ℝ) ^ 2 + ((α_u / (m : ℝ)) * Real.log (m : ℝ)) ^ 2 := by
            rw [htsub]; ring
        _ ≤ 1 - Real.log (m : ℝ) / (m : ℝ) + (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 +
              9 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by linarith only [hBnn, ht_sq]
        _ = 1 - Real.log (m : ℝ) / (m : ℝ) + 13 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 := by
            ring
    have hmul_part1 : (m : ℝ) ^ (-(α_u / (m : ℝ))) * (1 / (m : ℝ)) * α_u ≤ 3 / (2 * (m : ℝ)) := by
      have h1' : (m : ℝ) ^ (-(α_u / (m : ℝ))) * (1 / (m : ℝ)) * α_u ≤ 1 * (1 / (m : ℝ)) * (3 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hm_le1 (by positivity)) hαu_le hαu_pos.le
          (by positivity)
      linarith only [h1', show 1 * (1 / (m : ℝ)) * (3 / 2) = 3 / (2 * (m : ℝ)) by ring]
    have h13 : 13 / 4 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ)) < 1 / 2 := by linarith only [h2]
    have h_13m : 13 / 4 * (Real.log (m : ℝ)) ^ 2 / (m : ℝ) ^ 2 =
        (13 / 4 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))) / (m : ℝ) := by ring
    have h_div_lt : (13 / 4 * ((Real.log (m : ℝ)) ^ 2 / (m : ℝ))) / (m : ℝ) ≤ (1 / 2) / (m : ℝ) :=
      div_le_div_of_nonneg_right h13.le hm_pos.le
    have h_two : 3 / (2 * (m : ℝ)) + (1 / 2 : ℝ) / (m : ℝ) ≤ 2 * B / (m : ℝ) := by
      dsimp only [B]
      rw [show (3 : ℝ) / (2 * (m : ℝ)) + (1 / 2 : ℝ) / (m : ℝ) = 2 / (m : ℝ) by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hm_pos.le
    dsimp only [α_u, B] at hmul_part1 hexp_bd h_two ⊢
    linarith only [hmul_part1, hexp_bd, h_13m, h_div_lt, h_two]
  have hlm : ENNReal.ofReal s_l ≤ dimH (residueConstSet m m) := by
    refine le_dimH_residueConstSet_mm hm1 hs_l_gt ?_
    have h2sl : (m : ℝ) * (2 * s_l - 1) = α_l := by dsimp only [s_l]; field_simp; ring
    have h12 : 1 - 2 * s_l = -(α_l / (m : ℝ)) := by dsimp only [s_l]; ring
    rw [h2sl, h12, lt_div_iff₀ (by linarith only [hαl_pos] : 0 < α_l), one_mul,
      Real.rpow_def_of_pos (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ))]
    have hlog_bd := log_add_le_log_add_div (a := 1) (by omega : 2 ≤ m)
    have h_mul : Real.log ((m + 1 : ℕ) : ℝ) * (α_l / (m : ℝ)) ≤
        Real.log (m : ℝ) / (m : ℝ) + 1 / (m : ℝ) ^ 2 := by
      have hαlm_nn : 0 ≤ α_l / (m : ℝ) := div_nonneg (by linarith only [hαl_pos]) hm_pos.le
      have h1' := mul_le_mul_of_nonneg_right hlog_bd hαlm_nn
      have hsum_nn : 0 ≤ Real.log (m : ℝ) + ((1 : ℕ) : ℝ) / (m : ℝ) :=
        add_nonneg hlogm_nn (by positivity)
      have h2' := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαl_le hm_pos.le) hsum_nn
      have h3' : (Real.log (m : ℝ) + ((1 : ℕ) : ℝ) / (m : ℝ)) * (1 / (m : ℝ)) =
          Real.log (m : ℝ) / (m : ℝ) + 1 / (m : ℝ) ^ 2 := by push_cast; ring
      linarith only [h1', h2', h3']
    have hexp := Real.add_one_le_exp (-(Real.log ((m + 1 : ℕ) : ℝ) * (α_l / (m : ℝ))))
    have h1m : 1 / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) :=
      div_le_div_of_nonneg_left zero_le_one hm_pos (by nlinarith only [hm20R])
    have h_mul_neg : Real.log ((m + 1 : ℕ) : ℝ) * -(α_l / (m : ℝ)) =
        -(Real.log ((m + 1 : ℕ) : ℝ) * (α_l / (m : ℝ))) := by ring
    have hαl_val : 1 - Real.log (m : ℝ) / (m : ℝ) - 4 / (m : ℝ) = α_l := by
      dsimp only [α_l, B]; ring
    have h41 : (4 : ℝ) / (m : ℝ) = 4 * (1 / (m : ℝ)) := by ring
    calc α_l
        < 1 - Real.log (m : ℝ) / (m : ℝ) - 1 / (m : ℝ) ^ 2 := by
          rw [← hαl_val]; linarith only [h1m, h41, one_div_pos.mpr hm_pos]
      _ ≤ -(Real.log ((m + 1 : ℕ) : ℝ) * (α_l / (m : ℝ))) + 1 := by linarith only [h_mul]
      _ ≤ Real.exp (Real.log ((m + 1 : ℕ) : ℝ) * -(α_l / (m : ℝ))) := by
          rw [h_mul_neg]; exact hexp
  have hne_top : dimH (residueConstSet m m) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hum
  have h_toReal_le := ENNReal.toReal_le_of_le_ofReal (by linarith only [hs_u_gt]) hum
  have h_le_toReal := (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hlm
  rw [abs_le]
  rw [hsu_eq] at h_toReal_le
  rw [hsl_eq] at h_le_toReal
  constructor <;> linarith only [h_toReal_le, h_le_toReal]

/-- First-order scaling constant `m * (dimH F_{m,r} - 1/2) → C_r / 2`. -/
theorem tendsto_mul_dimH_residueConstSet_sub_half (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun m : ℕ => (m : ℝ) * ((dimH (residueConstSet m r)).toReal - 1 / 2))
      atTop (nhds (metalC r 1 / 2)) := by
  obtain ⟨B, hB, h_ev⟩ := dimH_residueConstSet_asymp_two_term r hr
  have hinv : Tendsto (fun m : ℕ => B / (m : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h_err : Tendsto (fun m : ℕ =>
      ((metalC r 1) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ)) atTop (nhds 0) := by
    simpa using (tendsto_log_div_nat.const_mul ((metalC r 1) ^ 2 / 2)).add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := metalC r 1 / 2)).sub h_err)
    (by simpa using (tendsto_const_nhds (x := metalC r 1 / 2)).add h_err) ?_ ?_
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.1 hm_pos.le
    have hl1 : (m : ℝ) * (-(B / (m : ℝ) ^ 2) +
        (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
          (metalC r 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) - 1 / 2)) =
        metalC r 1 / 2 - (((metalC r 1) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ)) := by
      field_simp [hm_pos.ne']; ring
    linarith only [hmul, hl1]
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.2 hm_pos.le
    have hlog_nn : 0 ≤ ((metalC r 1) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ)) := by
      have : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm1)
      positivity
    have hl2 : (m : ℝ) * (B / (m : ℝ) ^ 2 +
        (1 / 2 + metalC r 1 / (2 * (m : ℝ)) -
          (metalC r 1) ^ 2 * Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) - 1 / 2)) =
        metalC r 1 / 2 - ((metalC r 1) ^ 2 / 2) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ) := by
      field_simp [hm_pos.ne']; ring
    linarith only [hmul, hl2, hlog_nn]

lemma tendsto_mul_dimH_residueConstSet_mm_sub_half :
    Tendsto (fun m : ℕ => (m : ℝ) * ((dimH (residueConstSet m m)).toReal - 1 / 2))
      atTop (nhds (1 / 2)) := by
  obtain ⟨B, _, h_ev⟩ := dimH_residueConstSet_mm_asymp_two_term
  have hinv : Tendsto (fun m : ℕ => B / (m : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h_err : Tendsto (fun m : ℕ =>
      (1 / 2 : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ)) atTop (nhds 0) := by
    simpa using (tendsto_log_div_nat.const_mul (1 / 2 : ℝ)).add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h_err)
    (by simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add h_err) ?_ ?_
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.1 hm_pos.le
    have hl1 : (m : ℝ) * (-(B / (m : ℝ) ^ 2) +
        (1 / 2 + 1 / (2 * (m : ℝ)) - Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) - 1 / 2)) =
        1 / 2 - ((1 / 2 : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ)) := by
      field_simp [hm_pos.ne']; ring
    linarith only [hmul, hl1]
  · filter_upwards [h_ev, eventually_ge_atTop 1] with m hm hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h_abs := abs_le.mp hm
    have hmul := mul_le_mul_of_nonneg_left h_abs.2 hm_pos.le
    have hlog_nn : 0 ≤ (1 / 2 : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) :=
      mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg (by exact_mod_cast hm1)) hm_pos.le)
    have hl2 : (m : ℝ) * (B / (m : ℝ) ^ 2 +
        (1 / 2 + 1 / (2 * (m : ℝ)) - Real.log (m : ℝ) / (2 * (m : ℝ) ^ 2) - 1 / 2)) =
        1 / 2 - (1 / 2 : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) + B / (m : ℝ) := by
      field_simp [hm_pos.ne']; ring
    linarith only [hmul, hl2, hlog_nn]

/-- **Exact Dimension-Excess Ratio**:
    `((dimH F_{m,r}).toReal - 1/2) / ((dimH F_{m,m}).toReal - 1/2) → C_r` as `m → ∞`
    (in particular `→ ψ_Fib` for `F_{m,1}` and `eventuallyPeriodicResidueSet m`). -/
theorem tendsto_dimH_residue_ratio_eq_metalC (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun m : ℕ =>
      ((dimH (residueConstSet m r)).toReal - 1 / 2) /
        ((dimH (residueConstSet m m)).toReal - 1 / 2))
      atTop (nhds (metalC r 1)) := by
  have hnum := tendsto_mul_dimH_residueConstSet_sub_half r hr
  have hden := tendsto_mul_dimH_residueConstSet_mm_sub_half
  have hdiv : Tendsto (fun m : ℕ =>
      ((m : ℝ) * ((dimH (residueConstSet m r)).toReal - 1 / 2)) /
        ((m : ℝ) * ((dimH (residueConstSet m m)).toReal - 1 / 2)))
      atTop (nhds ((metalC r 1 / 2) / (1 / 2))) :=
    hnum.div hden (by norm_num)
  rw [show (metalC r 1 / 2) / (1 / 2) = metalC r 1 by ring] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm1
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp [hm_ne]

theorem tendsto_dimH_eventuallyPeriodic_ratio_eq_psiFib :
    Tendsto (fun m : ℕ =>
      ((dimH (eventuallyPeriodicResidueSet m)).toReal - 1 / 2) /
        ((dimH (residueConstSet m m)).toReal - 1 / 2))
      atTop (nhds psiFib) := by
  have h := tendsto_dimH_residue_ratio_eq_metalC 1 le_rfl
  rw [show metalC 1 1 = psiFib from rfl] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with m hm2
  rw [dimH_eventuallyPeriodicResidueSet_eq hm2]

/-- **Eventual Strict Monotonicity Across Fixed Residues**:
    whenever `1 ≤ r₁ < r₂`, `dimH F_{m,r₂} < dimH F_{m,r₁}` for all sufficiently large `m`. -/
theorem eventually_dimH_residueConstSet_strictAnti {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hlt : r₁ < r₂) :
    ∀ᶠ m : ℕ in atTop, dimH (residueConstSet m r₂) < dimH (residueConstSet m r₁) := by
  have hr₂ : 1 ≤ r₂ := le_trans hr₁ hlt.le
  have hC_lt : metalC r₂ 1 < metalC r₁ 1 := metalC_strictAnti_r hr₁ hlt zero_lt_one
  have ht1 := tendsto_mul_dimH_residueConstSet_sub_half r₁ hr₁
  have ht2 := tendsto_mul_dimH_residueConstSet_sub_half r₂ hr₂
  obtain ⟨_, _, h1up⟩ := asymp_upper_m_step hr₁
  obtain ⟨_, _, h2up⟩ := asymp_upper_m_step hr₂
  have hsub := ht1.sub ht2
  have hpos : 0 < metalC r₁ 1 / 2 - metalC r₂ 1 / 2 := by linarith only [hC_lt]
  filter_upwards [hsub.eventually (lt_mem_nhds hpos), h1up, h2up, eventually_ge_atTop 1]
    with m hm_diff h1u h2u hm1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hlt_real : (dimH (residueConstSet m r₂)).toReal < (dimH (residueConstSet m r₁)).toReal := by
    nlinarith only [hm_pos, hm_diff]
  have hne1 : dimH (residueConstSet m r₁) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1u
  have hne2 : dimH (residueConstSet m r₂) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2u
  exact (ENNReal.toReal_lt_toReal hne2 hne1).mp hlt_real

end

end ResidueAsymptotic

