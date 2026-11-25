import EpiFormal.ResidueMultiAsymptotic
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Exact Supercritical Leading Constant for Multi-Residue Continued-Fraction Cantor Sets

Resolves Paper 2 Open Problem §五.2(c) conditionally on the explicit simple-pole residue
parameter `hPole` (passed as an explicit theorem hypothesis, with ZERO global axioms and
ZERO `sorry`):

For any finite `S, B : Finset ℕ` (`∀ a ∈ S, 1 ≤ a`) in the supercritical regime
`s₀ := poincareAbscissa S > 1 / 2`, if the continuant Poincaré series `multiC S p`
has a simple pole at `p = 2 s₀` with positive residue `κ > 0`:
  `(p - 2 s₀) * multiC S p → κ` as `p → (2 s₀)⁺`,
then the Hausdorff dimension of `multiResidueSet m S B` obeys the exact power-law limit
  `m^(2 s₀) * ((dimH (multiResidueSet m S B)).toReal - s₀) → d * κ * ζ(2 s₀) / 2`
as `m → ∞`, where `d = S.card + B.card` and
`ζ(2 s₀) = ∑' k : ℕ, ((k + 1 : ℕ) : ℝ)^(-(2 s₀)) = (riemannZeta (2 * s₀ : ℂ)).re`.

## Proof method (completely Bowen-free & spectral-gap-free)
Both the upper bound (`limsup ≤ L*`) and the lower bound (`liminf ≥ L*`) use the exact
multi-branch resolvent `multiResolventV S s` evaluated at `s(m) = s₀ + c * m^(-2 s₀) > s₀`
(where the resolvent series converges!), together with the elementary uniform two-sided
comparison
  `(1 + y)^(-2 s) * multiC S (2 s) ≤ multiResolventV S s y ≤ multiC S (2 s)` (`y ≥ 0`).
- For any `c > L*`, the full tail `multiResidueTailReal m S B (s(m)) x` converges uniformly
  on `[0, 1]` to `L* / c < 1`, giving `dimH ≤ s(m)` via `dimH_le_of_transferOp_le`.
- For any `0 < c < L*`, fixing `K` large enough that the `K`-truncated zeta sum satisfies
  `d * κ * Z_K / (2 c) > 1`, the truncated tail on `truncMultiAlphabet m K S B` exceeds `1`
  uniformly on `[0, 1]` for all large `m`, giving `s(m) ≤ dimH` via `le_dimH_of_transferOp_ge`.
-/

namespace SupercriticalConstant

open Set Filter Finset ENNReal Real MeasureTheory Topology
open TransferOperatorDim ResidueMultiAsymptotic

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part 1: Elementary Resolvent & Nonemptiness Helpers -/

lemma nonempty_of_half_lt_poincareAbscissa {S : Finset ℕ}
    (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) : S.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  subst h
  have hle : poincareAbscissa (∅ : Finset ℕ) ≤ 1 / 4 := by
    refine csInf_le ⟨0, fun _ hs => hs.1.le⟩ ⟨by norm_num, ?_⟩
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) fun n hn => ?_
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by simpa using hn)
    exact wordSum_empty hn1
  linarith

/-- Uniform lower comparison for the multi-branch resolvent near `0`:
    `(1 + y)^(-2s) * multiC S (2s) ≤ multiResolventV S s y` for all `y ≥ 0`, `s > 0`. -/
lemma multiResolventV_ge_mul_multiC {S : Finset ℕ} (hS1 : ∀ a ∈ S, 1 ≤ a)
    {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) (hsum : Summable (wordSum S (2 * s))) :
    (1 + y) ^ (-(2 * s)) * multiC S (2 * s) ≤ multiResolventV S s y := by
  unfold multiResolventV multiC
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (hsum.mul_left _)
    (summable_multiResolventV hS1 hs hy hsum)
  unfold wordSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  have hpd := posDigits_subWord (fun a ha => hS1 a ha) n w
  have hq_pos : 0 < denQ (subWord n w) := denQ_pos hpd
  have hp_le : denP (subWord n w) ≤ denQ (subWord n w) := denP_le_denQ hpd
  have hpos_sum : 0 < denQ (subWord n w) + denP (subWord n w) * y :=
    add_pos_of_pos_of_nonneg hq_pos (mul_nonneg (denP_nonneg _) hy)
  have hle_base : denQ (subWord n w) + denP (subWord n w) * y ≤
      denQ (subWord n w) * (1 + y) := by
    have : denP (subWord n w) * y ≤ denQ (subWord n w) * y :=
      mul_le_mul_of_nonneg_right hp_le hy
    linarith
  have hrpow := Real.rpow_le_rpow_of_nonpos hpos_sum hle_base (by linarith : -(2 * s) ≤ 0)
  rw [Real.mul_rpow hq_pos.le (by linarith : 0 ≤ 1 + y), mul_comm] at hrpow
  exact hrpow

/-- Finite `K`-branch real tail sum corresponding to `truncMultiAlphabet m K S B`. -/
def truncMultiResidueTailReal (m K : ℕ) (S B : Finset ℕ) (s x : ℝ) : ℝ :=
  (∑ r ∈ S, ∑ k ∈ Finset.range K,
    multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
      ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) +
  (∑ b ∈ B, ∑ k ∈ Finset.range K,
    multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
      ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))

/-! ### Part 2: Resolvent Dimension Bridges (Upper & Truncated Lower) -/

/-- Resolvent upper dimension bridge: if `multiResidueTailReal m S B s x ≤ 1` for all
    `x ∈ [0, 1]`, then `dimH (multiResidueSet m S B) ≤ ENNReal.ofReal s`. -/
lemma dimH_multiResidue_upper_of_tail_le_one {m : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm_sep : S.sup id + B.sup id + 1 ≤ m)
    (hm_2M0 : 2 * ((S.sup id + B.sup id + 1 : ℕ) : ℝ) ≤ (m : ℝ))
    {s : ℝ} (hs_lo : 1 / 2 < s) (hsum_s : Summable (wordSum S (2 * s)))
    (htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B s x ≤ 1) :
    dimH (multiResidueSet m S B) ≤ ENNReal.ofReal s := by
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀1 : 1 ≤ M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 1 ≤ S.sup id + B.sup id + 1)
  have hs_pos : 0 < s := by linarith
  let C : ℝ := multiC S (2 * s)
  have hC1 : 1 ≤ C := one_le_multiC hsum_s
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by dsimp only [M₀] at hM₀1; linarith only [hm_2M0, hM₀1]
  have hV_ge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ multiResolventV S s y :=
    fun y hy => one_le_multiResolventV hS1 hs_pos hy hsum_s
  have hV_leC : ∀ y : ℝ, 0 ≤ y → multiResolventV S s y ≤ C :=
    fun y hy => multiResolventV_le_multiC hS1 hs_pos hy hsum_s
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (hV_ge1 x hx.1), ENNReal.ofReal_le_ofReal (hV_leC x hx.1)⟩
  have hterm_sum : ∀ γ : ℝ, |γ| ≤ M₀ →
      Summable fun k : ℕ =>
        multiResolventV S s (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) *
          ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s))) := fun γ hγ => by
    have hζ : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-(2 * s)))) := by
      have h := (summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s))
      refine h.congr fun k => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg _)]
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      (hζ.mul_left (C * ((m : ℝ) / 2) ^ (-(2 * s))))
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by
        have := (abs_le.mp hγ).1; nlinarith [hk1, hm_2M0, hM₀1]
      exact mul_nonneg (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one h_pos.le)))
        (Real.rpow_nonneg h_pos.le _)
    · have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      have hk_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by
        have := (abs_le.mp hγ).1; nlinarith [hk1, hm_2M0]
      have h_half_pos : 0 < (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 := by nlinarith [hk1, hm_ge2]
      have h_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by linarith only [h_half_pos, hk_ge]
      have hV_le := hV_leC (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ))
        (div_nonneg zero_le_one h_pos.le)
      have hpow := Real.rpow_le_rpow_of_nonpos (z := -(2 * s)) h_half_pos hk_ge
        (by linarith only [hs_pos])
      have hsplit : ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) =
          ((m : ℝ) / 2) ^ (-(2 * s)) * (((k + 1 : ℕ) : ℝ) ^ (-(2 * s))) := by
        rw [show (((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2 = ((m : ℝ) / 2) * ((k + 1 : ℕ) : ℝ) by ring,
          Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
      calc _ ≤ C * ((((k + 1 : ℕ) : ℝ) * (m : ℝ)) / 2) ^ (-(2 * s)) :=
            mul_le_mul hV_le hpow (Real.rpow_nonneg h_pos.le _) (zero_le_one.trans hC1)
        _ = _ := by rw [hsplit]; ring
  have hsub : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      transferOp (multiResidueAlphabet m S B) s v x ≤ v x := by
    intro x hx
    rw [transferOp_multiResidueAlphabet_eq hS1 hm_sep s v x]
    have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
      rw [transferOp_finset_eq]
      have hbr := multiResolventV_branch_eq hS1 hs_pos hx.1 hsum_s
      have hnonneg : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _)
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]))))
      calc (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))
          = ∑ a ∈ S, ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha_nn : 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) :=
                Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _
              dsimp only [v]; rw [mul_comm, ← ENNReal.ofReal_mul ha_nn]
        _ = ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) :=
              (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
        _ = ENNReal.ofReal (multiResolventV S s x - 1) := by rw [hbr]
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hS_tsum :
        (∑ r ∈ S, ∑' k : ℕ, v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ r ∈ S, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_r : ∀ r ∈ S, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun r _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_r]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by
        exact_mod_cast Finset.le_sup (f := id) hr
      have hγ : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id)]
      have hsum_r' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum ((r : ℝ) + x) hγ).congr fun k => ?_
        congr 2 <;> push_cast <;> ring
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _))
        hsum_r']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))]
    have hB_tsum :
        (∑ b ∈ B, ∑' k : ℕ, v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ b ∈ B, ∑' k : ℕ,
            multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have h_nn_b : ∀ b ∈ B, 0 ≤ ∑' k : ℕ,
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun b _ =>
        tsum_nonneg fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg h_nn_b]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hγ : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id)]
      have hsum_b' : Summable fun k : ℕ =>
          multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := by
        refine (hterm_sum (-(b : ℝ) + x) hγ).congr fun k => ?_
        have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _))
        hsum_b']
      refine tsum_congr fun k => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))]
    have hvx_ge1 : 1 ≤ multiResolventV S s x := hV_ge1 x hx.1
    have h_S_nn : 0 ≤ ∑ r ∈ S, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun r _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
    have h_B_nn : 0 ≤ ∑ b ∈ B, ∑' k : ℕ,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun b _ => tsum_nonneg fun k => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
    have htail_nn : 0 ≤ multiResidueTailReal m S B s x := add_nonneg h_S_nn h_B_nn
    rw [hS_part, hS_tsum, hB_tsum, add_assoc, ← ENNReal.ofReal_add h_S_nn h_B_nn]
    change ENNReal.ofReal (multiResolventV S s x - 1) +
      ENNReal.ofReal (multiResidueTailReal m S B s x) ≤ v x
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) htail_nn]
    exact ENNReal.ofReal_le_ofReal (by linarith [htail x hx])
  exact dimH_le_of_transferOp_le (multiResidueAlphabet_ge_one hS1) hs_pos
    (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsub

/-- Resolvent truncated lower dimension bridge: if `1 ≤ truncMultiResidueTailReal m K S B s x`
    for all `x ∈ [0, 1]`, then `ENNReal.ofReal s ≤ dimH (multiResidueSet m S B)`. -/
lemma dimH_multiResidue_lower_of_truncTail_ge_one {m K : ℕ} {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hm_sep : S.sup id + B.sup id + 1 ≤ m)
    (hd : 1 ≤ S.card + B.card) (hK : 1 ≤ K)
    {s : ℝ} (hs_pos : 0 < s) (hsum_s : Summable (wordSum S (2 * s)))
    (htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ truncMultiResidueTailReal m K S B s x) :
    ENNReal.ofReal s ≤ dimH (multiResidueSet m S B) := by
  let C : ℝ := multiC S (2 * s)
  have hV_ge1 : ∀ y : ℝ, 0 ≤ y → 1 ≤ multiResolventV S s y :=
    fun y hy => one_le_multiResolventV hS1 hs_pos hy hsum_s
  have hV_leC : ∀ y : ℝ, 0 ≤ y → multiResolventV S s y ≤ C :=
    fun y hy => multiResolventV_le_multiC hS1 hs_pos hy hsum_s
  let v : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (multiResolventV S s x)
  have hv_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal 1 ≤ v x ∧ v x ≤ ENNReal.ofReal C := fun x hx =>
    ⟨ENNReal.ofReal_le_ofReal (hV_ge1 x hx.1), ENNReal.ofReal_le_ofReal (hV_leC x hx.1)⟩
  have hsuper : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      v x ≤ transferOp (truncMultiAlphabet m K S B : Set ℕ) s v x := by
    intro x hx
    rw [transferOp_truncMultiAlphabet_eq hS1 hm_sep s v x]
    have hS_part : transferOp (S : Set ℕ) s v x = ENNReal.ofReal (multiResolventV S s x - 1) := by
      rw [transferOp_finset_eq]
      have hbr := multiResolventV_branch_eq hS1 hs_pos hx.1 hsum_s
      have hnonneg : ∀ a ∈ S, 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) *
          multiResolventV S s (1 / ((a : ℝ) + x)) := fun a _ =>
        mul_nonneg (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _)
          (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]))))
      calc (∑ a ∈ S, v (1 / ((a : ℝ) + x)) * ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s))))
          = ∑ a ∈ S, ENNReal.ofReal (((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              have ha_nn : 0 ≤ ((a : ℝ) + x) ^ (-(2 * s)) :=
                Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) a]) _
              dsimp only [v]; rw [mul_comm, ← ENNReal.ofReal_mul ha_nn]
        _ = ENNReal.ofReal (∑ a ∈ S, ((a : ℝ) + x) ^ (-(2 * s)) *
              multiResolventV S s (1 / ((a : ℝ) + x))) :=
              (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
        _ = ENNReal.ofReal (multiResolventV S s x - 1) := by rw [hbr]
    have hS_fin :
        (∑ r ∈ S, ∑ k ∈ Finset.range K,
          v (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ r ∈ S, ∑ k ∈ Finset.range K,
            multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have hnn_term : ∀ r ∈ S, ∀ k ∈ Finset.range K,
          0 ≤ multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun r _ k _ =>
        mul_nonneg (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg (fun r hr => Finset.sum_nonneg (hnn_term r hr))]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (hnn_term r hr)]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))]
    have hB_fin :
        (∑ b ∈ B, ∑ k ∈ Finset.range K,
          v (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ENNReal.ofReal (((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)))) =
          ENNReal.ofReal (∑ b ∈ B, ∑ k ∈ Finset.range K,
            multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s))) := by
      have hnn_term : ∀ b ∈ B, ∀ k ∈ Finset.range K,
          0 ≤ multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) := fun b _ k _ =>
        mul_nonneg (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
            (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
          (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
      rw [ENNReal.ofReal_sum_of_nonneg (fun b hb => Finset.sum_nonneg (hnn_term b hb))]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [ENNReal.ofReal_sum_of_nonneg (hnn_term b hb)]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp only [v]
      rw [ENNReal.ofReal_mul (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
        (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))]
    have hS_nn : 0 ≤ ∑ r ∈ S, ∑ k ∈ Finset.range K,
        multiResolventV S s (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m + r)]) _)
    have hB_nn : 0 ≤ ∑ b ∈ B, ∑ k ∈ Finset.range K,
        multiResolventV S s (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s)) :=
      Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ => mul_nonneg
        (zero_le_one.trans (hV_ge1 _ (div_nonneg zero_le_one
          (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]))))
        (Real.rpow_nonneg (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) ((k + 1) * m - b)]) _)
    have hvx_ge1 : 1 ≤ multiResolventV S s x := hV_ge1 x hx.1
    have htail_nn : 0 ≤ truncMultiResidueTailReal m K S B s x := add_nonneg hS_nn hB_nn
    rw [hS_part, hS_fin, hB_fin, add_assoc, ← ENNReal.ofReal_add hS_nn hB_nn]
    change v x ≤ ENNReal.ofReal (multiResolventV S s x - 1) +
      ENNReal.ofReal (truncMultiResidueTailReal m K S B s x)
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hvx_ge1) htail_nn]
    exact ENNReal.ofReal_le_ofReal (by linarith [htail x hx])
  have hsub_dim : ENNReal.ofReal s ≤ dimH (cfAlphabetSet (truncMultiAlphabet m K S B : Set ℕ)) :=
    le_dimH_of_transferOp_ge (truncMultiAlphabet_nonempty hm_sep hd hK)
      (truncMultiAlphabet_ge_one hS1 hm_sep) hs_pos
      (by simp : (0 : ℝ≥0∞) < ENNReal.ofReal 1) ENNReal.ofReal_lt_top hv_bd hsuper
  have hset_mono : cfAlphabetSet (truncMultiAlphabet m K S B : Set ℕ) ⊆ multiResidueSet m S B := by
    rintro x ⟨hx01, hirr, hadm⟩
    exact ⟨hx01, hirr, fun i => truncMultiAlphabet_subset hm_sep (hadm i)⟩
  exact hsub_dim.trans (dimH_mono hset_mono)

/-! ### Part 3: Asymptotic Helpers Along `s(m) = s₀ + c * m^(-2 s₀)` -/

lemma tendsto_multiC_mul_rpow {S : Finset ℕ}
    (hsuper : (1 / 2 : ℝ) < poincareAbscissa S) {κ c : ℝ} (hc : 0 < c)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ)) :
    Tendsto (fun m : ℕ =>
        multiC S (2 * (poincareAbscissa S + c * (m : ℝ) ^ (-(2 * poincareAbscissa S)))) *
          (m : ℝ) ^ (-(2 * poincareAbscissa S)))
      atTop (𝓝 (κ / (2 * c))) := by
  let s₀ : ℝ := poincareAbscissa S
  have ht_pow0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * s₀))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s₀)).comp tendsto_natCast_atTop_atTop
  have ht_2s : Tendsto (fun m : ℕ => 2 * (s₀ + c * (m : ℝ) ^ (-(2 * s₀))))
      atTop (𝓝[>] (2 * s₀)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 := (ht_pow0.const_mul c).const_add s₀
      have h2 := h1.const_mul (2 : ℝ)
      simpa only [mul_zero, add_zero] using h2
    · filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hδ_pos : 0 < c * (m : ℝ) ^ (-(2 * s₀)) := mul_pos hc (Real.rpow_pos_of_pos hm_pos _)
      change 2 * s₀ < 2 * (s₀ + c * (m : ℝ) ^ (-(2 * s₀)))
      linarith
  have ht_pole := hPole.comp ht_2s
  have ht_div := ht_pole.div_const (2 * c)
  refine ht_div.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m _
  change ((2 * (s₀ + c * (m : ℝ) ^ (-(2 * s₀))) - 2 * s₀) *
      multiC S (2 * (s₀ + c * (m : ℝ) ^ (-(2 * s₀))))) / (2 * c) = _
  field_simp [hc.ne']
  ring

lemma tendsto_log_div_nat : Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h1.comp tendsto_natCast_atTop_atTop

lemma tendsto_m_rpow_neg_two_delta {s₀ c : ℝ} (hs₀ : 1 / 2 < s₀) (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀)))))) atTop (𝓝 1) := by
  have hexp0 : Tendsto (fun m : ℕ => -(2 * (c * (m : ℝ) ^ (-(2 * s₀)))) * Real.log (m : ℝ))
      atTop (𝓝 0) := by
    have hhi : Tendsto (fun m : ℕ => (2 * c) * (Real.log (m : ℝ) / (m : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_log_div_nat.const_mul (2 * c)
    have hlo : Tendsto (fun m : ℕ => -((2 * c) * (Real.log (m : ℝ) / (m : ℝ)))) atTop (𝓝 0) := by
      simpa only [neg_zero] using hhi.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlog_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm_ge1
      have hpow_le : (m : ℝ) ^ (-(2 * s₀)) ≤ (m : ℝ)⁻¹ := by
        calc (m : ℝ) ^ (-(2 * s₀))
            ≤ (m : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm_ge1 (by linarith)
          _ = (m : ℝ)⁻¹ := Real.rpow_neg_one (m : ℝ)
      have hpos_le : 2 * (c * (m : ℝ) ^ (-(2 * s₀))) * Real.log (m : ℝ) ≤
          (2 * c) * (Real.log (m : ℝ) / (m : ℝ)) := by
        rw [div_eq_mul_inv]
        have h1 : 2 * (c * (m : ℝ) ^ (-(2 * s₀))) * Real.log (m : ℝ) ≤
            2 * (c * (m : ℝ)⁻¹) * Real.log (m : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le hc.le) zero_le_two)
            hlog_nn
        linarith
      linarith
    · filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
      have hlog_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm_ge1
      have hδ_nn : 0 ≤ c * (m : ℝ) ^ (-(2 * s₀)) :=
        mul_nonneg hc.le (Real.rpow_nonneg hm_pos.le _)
      nlinarith
  have hrexp : Tendsto (fun m : ℕ =>
      Real.exp (-(2 * (c * (m : ℝ) ^ (-(2 * s₀)))) * Real.log (m : ℝ))) atTop (𝓝 1) := by
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hexp0
  refine hrexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  conv_rhs => rw [Real.rpow_def_of_pos hm_pos]
  rw [mul_comm]

/-! ### Part 4: Exact Upper & Lower Bounds for Arbitrary `c > L*` and `0 < c < L*` -/

lemma supercritical_eventually_le_ennreal {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S)
    {κ : ℝ} (hκ : 0 < κ)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ))
    {c : ℝ}
    (hc_gt : ((S.card + B.card : ℕ) : ℝ) * κ *
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) / 2 < c) :
    ∀ᶠ m : ℕ in atTop,
      dimH (multiResidueSet m S B) ≤
        ENNReal.ofReal (poincareAbscissa S + c * (m : ℝ) ^ (-(2 * poincareAbscissa S))) := by
  let s₀ : ℝ := poincareAbscissa S
  let d : ℝ := ((S.card + B.card : ℕ) : ℝ)
  let Z : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))
  have hSne : S.Nonempty := nonempty_of_half_lt_poincareAbscissa hsuper
  have hd_pos : 0 < d := by
    dsimp only [d]; exact_mod_cast (Nat.add_pos_left hSne.card_pos B.card)
  have hZ_sum : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s₀))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hZ_pos : 0 < Z := by
    have h0 := hZ_sum.le_tsum 0 (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h1 : (((0 + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) = 1 := by simp
    dsimp only [Z]; linarith
  have hc_pos : 0 < c := lt_trans (by positivity) hc_gt
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀_pos : 0 < M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 0 < S.sup id + B.sup id + 1)
  let s : ℕ → ℝ := fun m => s₀ + c * (m : ℝ) ^ (-(2 * s₀))
  have ht_s : Tendsto s atTop (𝓝 s₀) := by
    have ht0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * s₀))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s₀)).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, add_zero] using (ht0.const_mul c).const_add s₀
  have ht_fac : Tendsto (fun m : ℕ => (1 - M₀ / (m : ℝ)) ^ (-(2 * s m))) atTop (𝓝 1) := by
    have hbase : Tendsto (fun m : ℕ => 1 - M₀ / (m : ℝ)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun m : ℕ => M₀ / (m : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [sub_zero] using tendsto_const_nhds.sub hdiv
    have hexp : Tendsto (fun m : ℕ => -(2 * s m)) atTop (𝓝 (-(2 * s₀))) :=
      (ht_s.const_mul 2).neg
    simpa only [Real.one_rpow] using hbase.rpow hexp (Or.inl one_ne_zero)
  have ht_Cm := tendsto_multiC_mul_rpow hsuper hc_pos hPole
  have ht_rhs : Tendsto (fun m : ℕ =>
      d * (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) *
        (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * Z)
      atTop (𝓝 (d * κ * Z / (2 * c))) := by
    have h := (((ht_fac.const_mul d).mul ht_Cm).mul_const Z)
    have hval : d * 1 * (κ / (2 * c)) * Z = d * κ * Z / (2 * c) := by ring
    rwa [hval] at h
  have hlim_lt1 : d * κ * Z / (2 * c) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [hc_gt]
  filter_upwards [eventually_ge_atTop (2 * (S.sup id + B.sup id + 1) + 4),
    ht_rhs.eventually (gt_mem_nhds hlim_lt1)] with m hm_big hrhs_lt1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm_sep : S.sup id + B.sup id + 1 ≤ m := by omega
  have hm_2M0 : 2 * M₀ ≤ (m : ℝ) := by
    dsimp [M₀]; exact_mod_cast (by omega : 2 * (S.sup id + B.sup id + 1) ≤ m)
  have h1sub_pos : 0 < 1 - M₀ / (m : ℝ) := by
    have : M₀ / (m : ℝ) ≤ 1 / 2 := (div_le_iff₀ hm_pos).mpr (by linarith)
    linarith
  have hδ_pos : 0 < c * (m : ℝ) ^ (-(2 * s₀)) := mul_pos hc_pos (Real.rpow_pos_of_pos hm_pos _)
  have hs_lo : 1 / 2 < s m := by dsimp [s]; linarith
  have hs_pos : 0 < s m := by linarith
  have hsum_s : Summable (wordSum S (2 * s m)) :=
    summable_wordSum_of_poincareAbscissa_lt hS1 (by dsimp [s, s₀]; linarith)
  have hC_nn : 0 ≤ multiC S (2 * s m) := zero_le_one.trans (one_le_multiC hsum_s)
  have htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, multiResidueTailReal m S B (s m) x ≤ 1 := fun x hx => by
    have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
      dsimp [M₀]; push_cast; ring
    have hbr_bd : ∀ γ : ℝ, |γ| ≤ M₀ →
        (∑' k : ℕ, multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s m)))) ≤
          (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) *
            (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * Z := fun γ hγ => by
      let maj : ℕ → ℝ := fun k =>
        ((1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) * (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀)))) *
          ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))
      have hmaj_sum : Summable maj := hZ_sum.mul_left _
      have hpt : ∀ k : ℕ,
          multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) *
              ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s m))) ≤ maj k := fun k => by
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have hlo_base : ((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ)) ≤
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by
          have hγ1 := (abs_le.mp hγ).1
          have hmul : ((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ)) =
              ((k + 1 : ℕ) : ℝ) * (m : ℝ) - ((k + 1 : ℕ) : ℝ) * M₀ := by
            field_simp [hm_pos.ne']
          rw [hmul]
          nlinarith [hk1, hM₀_pos]
        have hlo_pos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ)) := by positivity
        have hpos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := lt_of_lt_of_le hlo_pos hlo_base
        have hV_le := multiResolventV_le_multiC hS1 hs_pos (div_nonneg zero_le_one hpos.le) hsum_s
        have hpow1 := Real.rpow_le_rpow_of_nonpos hlo_pos hlo_base (by linarith : -(2 * s m) ≤ 0)
        have hpow_split : (((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ))) ^ (-(2 * s m)) =
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * s m)) * (m : ℝ) ^ (-(2 * s m)) *
              (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) := by
          rw [Real.mul_rpow (by positivity) h1sub_pos.le, Real.mul_rpow (by positivity) hm_pos.le]
        have hk_le : ((k + 1 : ℕ) : ℝ) ^ (-(2 * s m)) ≤ ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)) :=
          Real.rpow_le_rpow_of_exponent_le hk1 (by dsimp [s]; linarith)
        have hm_le : (m : ℝ) ^ (-(2 * s m)) ≤ (m : ℝ) ^ (-(2 * s₀)) :=
          Real.rpow_le_rpow_of_exponent_le hm_ge1 (by dsimp [s]; linarith)
        have hpow2 : (((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ))) ^ (-(2 * s m)) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)) * (m : ℝ) ^ (-(2 * s₀)) *
              (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) := by
          rw [hpow_split]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hk_le hm_le (Real.rpow_nonneg hm_pos.le _)
              (Real.rpow_nonneg (by positivity) _))
            (Real.rpow_nonneg h1sub_pos.le _)
        calc _ ≤ multiC S (2 * s m) *
              (((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 - M₀ / (m : ℝ))) ^ (-(2 * s m)) :=
              mul_le_mul hV_le hpow1 (Real.rpow_nonneg hpos.le _) hC_nn
          _ ≤ multiC S (2 * s m) *
              (((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)) * (m : ℝ) ^ (-(2 * s₀)) *
                (1 - M₀ / (m : ℝ)) ^ (-(2 * s m))) :=
              mul_le_mul_of_nonneg_left hpow2 hC_nn
          _ = maj k := by dsimp [maj]; ring
      have hterm_sum : Summable fun k : ℕ =>
          multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s m))) := by
        refine Summable.of_nonneg_of_le (fun k => ?_) hpt hmaj_sum
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have hpos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by
          have := (abs_le.mp hγ).1; nlinarith [hk1, hm_2M0, hM₀_pos]
        exact mul_nonneg (zero_le_one.trans (one_le_multiResolventV hS1 hs_pos
          (div_nonneg zero_le_one hpos.le) hsum_s)) (Real.rpow_nonneg hpos.le _)
      have htsum_le := hterm_sum.tsum_le_tsum hpt hmaj_sum
      have hmaj_eval : (∑' k : ℕ, maj k) =
          (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) * (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * Z := by
        dsimp only [maj, Z]; rw [tsum_mul_left]
      exact htsum_le.trans_eq hmaj_eval
    let Bval : ℝ := (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) *
      (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * Z
    have hS_br : (∑ r ∈ S, ∑' k : ℕ,
        multiResolventV S (s m) (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s m))) ≤ (S.card : ℝ) * Bval := by
      rw [show (S.card : ℝ) * Bval = ∑ _r ∈ S, Bval by rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun r hr => ?_
      have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by exact_mod_cast Finset.le_sup (f := id) hr
      have hγ : |(r : ℝ) + x| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (B.sup id), hM0_eq]
      have hcongr : (∑' k : ℕ, multiResolventV S (s m) (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
          ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s m))) =
          ∑' k : ℕ, multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x))) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x)) ^ (-(2 * s m))) := by
        refine tsum_congr fun k => ?_
        congr 2 <;> push_cast <;> ring
      rw [hcongr]
      exact hbr_bd ((r : ℝ) + x) hγ
    have hB_br : (∑ b ∈ B, ∑' k : ℕ,
        multiResolventV S (s m) (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s m))) ≤ (B.card : ℝ) * Bval := by
      rw [show (B.card : ℝ) * Bval = ∑ _b ∈ B, Bval by rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun b hb => ?_
      have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
      have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
      have hbm : b ≤ m := le_trans hb_nat (by omega)
      have hγ : |(-(b : ℝ) + x)| ≤ M₀ := by
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
          Nat.cast_nonneg (α := ℝ) (S.sup id), hM0_eq]
      have hcongr : (∑' k : ℕ, multiResolventV S (s m) (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
          ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s m))) =
          ∑' k : ℕ, multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x))) *
            ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x)) ^ (-(2 * s m))) := by
        refine tsum_congr fun k => ?_
        have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
        have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
          rw [Nat.cast_sub hk1m]; push_cast; ring
        rw [hcast]
      rw [hcongr]
      exact hbr_bd (-(b : ℝ) + x) hγ
    calc multiResidueTailReal m S B (s m) x
        ≤ (S.card : ℝ) * Bval + (B.card : ℝ) * Bval := add_le_add hS_br hB_br
      _ = d * (1 - M₀ / (m : ℝ)) ^ (-(2 * s m)) *
            (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * Z := by
          dsimp only [d, Bval]; push_cast; ring
      _ ≤ 1 := hrhs_lt1.le
  exact dimH_multiResidue_upper_of_tail_le_one hS1 hm_sep hm_2M0 hs_lo hsum_s htail

lemma supercritical_eventually_le {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S)
    {κ : ℝ} (hκ : 0 < κ)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ))
    {c : ℝ}
    (hc_gt : ((S.card + B.card : ℕ) : ℝ) * κ *
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) / 2 < c) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ (2 * poincareAbscissa S) *
        ((dimH (multiResidueSet m S B)).toReal - poincareAbscissa S) ≤ c := by
  let s₀ : ℝ := poincareAbscissa S
  have hZ_sum : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s₀))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hZ_pos : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)) := by
    have h0 := hZ_sum.le_tsum 0 (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h1 : (((0 + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) = 1 := by simp
    linarith
  have hd_pos : (0 : ℝ) < ((S.card + B.card : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_pos_left (nonempty_of_half_lt_poincareAbscissa hsuper).card_pos B.card)
  have hc_pos : 0 < c := lt_trans (by positivity) hc_gt
  filter_upwards [eventually_ge_atTop 1,
    supercritical_eventually_le_ennreal hS1 hsuper hκ hPole hc_gt] with m hm1 hdim_enn
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hs_nn : 0 ≤ s₀ + c * (m : ℝ) ^ (-(2 * s₀)) := by
    have : 0 ≤ s₀ := poincareAbscissa_nonneg S
    positivity
  have hdim_real : (dimH (multiResidueSet m S B)).toReal ≤ s₀ + c * (m : ℝ) ^ (-(2 * s₀)) :=
    ENNReal.toReal_le_of_le_ofReal hs_nn hdim_enn
  have hdiff : (dimH (multiResidueSet m S B)).toReal - s₀ ≤ c * (m : ℝ) ^ (-(2 * s₀)) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff (Real.rpow_nonneg hm_pos.le (2 * s₀))
  have hcancel : (m : ℝ) ^ (2 * s₀) * (c * (m : ℝ) ^ (-(2 * s₀))) = c := by
    rw [mul_left_comm, ← Real.rpow_add hm_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  exact hmul.trans_eq hcancel

lemma supercritical_eventually_ge {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S)
    {κ : ℝ} (hκ : 0 < κ)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ))
    {c : ℝ} (hc_pos : 0 < c)
    (hc_lt : c < ((S.card + B.card : ℕ) : ℝ) * κ *
      (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) / 2) :
    ∀ᶠ m : ℕ in atTop,
      c ≤ (m : ℝ) ^ (2 * poincareAbscissa S) *
        ((dimH (multiResidueSet m S B)).toReal - poincareAbscissa S) := by
  let s₀ : ℝ := poincareAbscissa S
  let d : ℝ := ((S.card + B.card : ℕ) : ℝ)
  let Z : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))
  have hSne : S.Nonempty := nonempty_of_half_lt_poincareAbscissa hsuper
  have hd_nat : 1 ≤ S.card + B.card := Nat.add_pos_left hSne.card_pos B.card
  have hd_pos : 0 < d := by dsimp only [d]; exact_mod_cast hd_nat
  have hZ_sum : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * s₀))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hZ_lim : Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀)))
      atTop (𝓝 Z) := hZ_sum.hasSum.tendsto_sum_nat
  have htarget_gt1 : 1 < d * κ * Z / (2 * c) := by
    rw [one_lt_div (by positivity)]
    linarith [hc_lt]
  have ht_trunc_lim : Tendsto
      (fun K : ℕ => d * κ * (∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) ^ (-(2 * s₀))) / (2 * c))
      atTop (𝓝 (d * κ * Z / (2 * c))) :=
    (hZ_lim.const_mul (d * κ)).div_const (2 * c)
  obtain ⟨K, hK_gt1, hK1⟩ :=
    ((ht_trunc_lim.eventually (lt_mem_nhds htarget_gt1)).and (eventually_ge_atTop 1)).exists
  let ZK : ℝ → ℝ := fun t => ∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) ^ (-(2 * t))
  let M₀ : ℝ := ((S.sup id + B.sup id + 1 : ℕ) : ℝ)
  have hM₀_pos : 0 < M₀ := by dsimp [M₀]; exact_mod_cast (by omega : 0 < S.sup id + B.sup id + 1)
  let s : ℕ → ℝ := fun m => s₀ + c * (m : ℝ) ^ (-(2 * s₀))
  have ht_s : Tendsto s atTop (𝓝 s₀) := by
    have ht0 : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(2 * s₀))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * s₀)).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, add_zero] using (ht0.const_mul c).const_add s₀
  have hZK_cont : Continuous ZK := by
    unfold ZK
    refine continuous_finsetSum _ fun k _ => ?_
    have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
    exact Continuous.rpow continuous_const (continuous_const.mul continuous_id).neg
      (fun _ => Or.inl hk_pos.ne')
  have ht_ZK : Tendsto (fun m : ℕ => ZK (s m)) atTop (𝓝 (ZK s₀)) :=
    (hZK_cont.tendsto s₀).comp ht_s
  have ht_fac1 : Tendsto (fun m : ℕ => (1 + 2 / (m : ℝ)) ^ (-(2 * s m))) atTop (𝓝 1) := by
    have hbase : Tendsto (fun m : ℕ => 1 + 2 / (m : ℝ)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun m : ℕ => (2 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [add_zero] using tendsto_const_nhds.add hdiv
    have hexp : Tendsto (fun m : ℕ => -(2 * s m)) atTop (𝓝 (-(2 * s₀))) :=
      (ht_s.const_mul 2).neg
    simpa only [Real.one_rpow] using hbase.rpow hexp (Or.inl one_ne_zero)
  have ht_fac2 : Tendsto (fun m : ℕ => (1 + M₀ / (m : ℝ)) ^ (-(2 * s m))) atTop (𝓝 1) := by
    have hbase : Tendsto (fun m : ℕ => 1 + M₀ / (m : ℝ)) atTop (𝓝 1) := by
      have hdiv : Tendsto (fun m : ℕ => M₀ / (m : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [add_zero] using tendsto_const_nhds.add hdiv
    have hexp : Tendsto (fun m : ℕ => -(2 * s m)) atTop (𝓝 (-(2 * s₀))) :=
      (ht_s.const_mul 2).neg
    simpa only [Real.one_rpow] using hbase.rpow hexp (Or.inl one_ne_zero)
  have ht_m2δ := tendsto_m_rpow_neg_two_delta hsuper hc_pos
  have ht_Cm := tendsto_multiC_mul_rpow hsuper hc_pos hPole
  have ht_lhs : Tendsto (fun m : ℕ =>
      d * (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * (1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
        (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
        (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * ZK (s m))
      atTop (𝓝 (d * κ * ZK s₀ / (2 * c))) := by
    have h := ((((ht_fac1.const_mul d).mul ht_fac2).mul ht_m2δ).mul ht_Cm).mul ht_ZK
    have hval : d * 1 * 1 * 1 * (κ / (2 * c)) * ZK s₀ = d * κ * ZK s₀ / (2 * c) := by ring
    rwa [hval] at h
  have hup_fin : ∀ᶠ m : ℕ in atTop, dimH (multiResidueSet m S B) ≠ ⊤ := by
    have h_ev := supercritical_eventually_le_ennreal hS1 hsuper hκ hPole (c := d * κ * Z / 2 + 1)
      (by dsimp only [d, Z, s₀]; linarith)
    filter_upwards [h_ev] with m hm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  filter_upwards [eventually_ge_atTop (2 * (S.sup id + B.sup id + 1) + 4),
    ht_lhs.eventually (lt_mem_nhds hK_gt1), hup_fin] with m hm_big hlhs_gt1 hne_top
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_sep : S.sup id + B.sup id + 1 ≤ m := by omega
  have hm_2M0 : 2 * M₀ ≤ (m : ℝ) := by
    dsimp [M₀]; exact_mod_cast (by omega : 2 * (S.sup id + B.sup id + 1) ≤ m)
  have hδ_pos : 0 < c * (m : ℝ) ^ (-(2 * s₀)) := mul_pos hc_pos (Real.rpow_pos_of_pos hm_pos _)
  have hs_pos : 0 < s m := by dsimp [s]; linarith
  have hsum_s : Summable (wordSum S (2 * s m)) :=
    summable_wordSum_of_poincareAbscissa_lt hS1 (by dsimp [s, s₀]; linarith)
  have hC_nn : 0 ≤ multiC S (2 * s m) := zero_le_one.trans (one_le_multiC hsum_s)
  have htail : ∀ x ∈ Set.Icc (0 : ℝ) 1, 1 ≤ truncMultiResidueTailReal m K S B (s m) x :=
    fun x hx => by
      have hM0_eq : M₀ = ((S.sup id : ℕ) : ℝ) + ((B.sup id : ℕ) : ℝ) + 1 := by
        dsimp [M₀]; push_cast; ring
      let Bval : ℝ := (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * (1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
        (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
        (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * ZK (s m)
      have hbr_ge : ∀ γ : ℝ, |γ| ≤ M₀ →
          Bval ≤ ∑ k ∈ Finset.range K,
            multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) *
              ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s m))) := fun γ hγ => by
        dsimp only [Bval, ZK]
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        have hlo : (m : ℝ) / 2 ≤ ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := by
          have := (abs_le.mp hγ).1; nlinarith [hk1, hm_2M0, hM₀_pos]
        have hpos : 0 < ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ := lt_of_lt_of_le (by positivity) hlo
        have hy_le : 1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ≤ 2 / (m : ℝ) := by
          rw [show (2 : ℝ) / (m : ℝ) = 1 / ((m : ℝ) / 2) by field_simp [hm_pos.ne']]
          exact one_div_le_one_div_of_le (by positivity) hlo
        have hV_ge : (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * multiC S (2 * s m) ≤
            multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) := by
          have h1 := multiResolventV_ge_mul_multiC hS1 hs_pos
            (div_nonneg zero_le_one hpos.le) hsum_s
          have h2 : (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) ≤
              (1 + 1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ)) ^ (-(2 * s m)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
          exact (mul_le_mul_of_nonneg_right h2 hC_nn).trans h1
        have hhi_base : ((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ ≤
            ((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 + M₀ / (m : ℝ)) := by
          have hγ2 := (abs_le.mp hγ).2
          have hmul : ((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 + M₀ / (m : ℝ)) =
              ((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((k + 1 : ℕ) : ℝ) * M₀ := by
            field_simp [hm_pos.ne']
          rw [hmul]
          nlinarith [hk1, hM₀_pos]
        have hpow_ge : (((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 + M₀ / (m : ℝ))) ^ (-(2 * s m)) ≤
            (((k + 1 : ℕ) : ℝ) * (m : ℝ) + γ) ^ (-(2 * s m)) :=
          Real.rpow_le_rpow_of_nonpos hpos hhi_base (by linarith)
        have hpow_split : (((k + 1 : ℕ) : ℝ) * (m : ℝ) * (1 + M₀ / (m : ℝ))) ^ (-(2 * s m)) =
            (1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
              (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
              (m : ℝ) ^ (-(2 * s₀)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * s m)) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) hm_pos.le,
            show -(2 * s m) = -(2 * s₀) + -(2 * (c * (m : ℝ) ^ (-(2 * s₀)))) by dsimp [s]; ring,
            Real.rpow_add hm_pos]
          ring
        have hmul := mul_le_mul hV_ge (hpow_split ▸ hpow_ge)
          (by positivity)
          (zero_le_one.trans (one_le_multiResolventV hS1 hs_pos
            (div_nonneg zero_le_one hpos.le) hsum_s))
        have hmul_eq :
            (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * (1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
              (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
              (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) *
              ((k + 1 : ℕ) : ℝ) ^ (-(2 * s m)) =
            ((1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * multiC S (2 * s m)) *
              ((1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
                (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
                (m : ℝ) ^ (-(2 * s₀)) * ((k + 1 : ℕ) : ℝ) ^ (-(2 * s m))) := by
          ring
        rw [hmul_eq]
        exact hmul
      have hS_br : (S.card : ℝ) * Bval ≤ ∑ r ∈ S, ∑ k ∈ Finset.range K,
          multiResolventV S (s m) (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
            ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s m)) := by
        rw [show (S.card : ℝ) * Bval = ∑ _r ∈ S, Bval by rw [Finset.sum_const, nsmul_eq_mul]]
        refine Finset.sum_le_sum fun r hr => ?_
        have hr_le : (r : ℝ) ≤ ((S.sup id : ℕ) : ℝ) := by
          exact_mod_cast Finset.le_sup (f := id) hr
        have hγ : |(r : ℝ) + x| ≤ M₀ := by
          rw [abs_le]
          constructor <;> linarith [Nat.cast_nonneg (α := ℝ) r, hx.1, hx.2,
            Nat.cast_nonneg (α := ℝ) (B.sup id), hM0_eq]
        have hcongr : (∑ k ∈ Finset.range K,
            multiResolventV S (s m) (1 / ((((k + 1) * m + r : ℕ) : ℝ) + x)) *
              ((((k + 1) * m + r : ℕ) : ℝ) + x) ^ (-(2 * s m))) =
            ∑ k ∈ Finset.range K,
              multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x))) *
                ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + ((r : ℝ) + x)) ^ (-(2 * s m))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 2 <;> push_cast <;> ring
        rw [hcongr]
        exact hbr_ge ((r : ℝ) + x) hγ
      have hB_br : (B.card : ℝ) * Bval ≤ ∑ b ∈ B, ∑ k ∈ Finset.range K,
          multiResolventV S (s m) (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
            ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s m)) := by
        rw [show (B.card : ℝ) * Bval = ∑ _b ∈ B, Bval by rw [Finset.sum_const, nsmul_eq_mul]]
        refine Finset.sum_le_sum fun b hb => ?_
        have hb_nat : b ≤ B.sup id := Finset.le_sup (f := id) hb
        have hb_le : (b : ℝ) ≤ ((B.sup id : ℕ) : ℝ) := by exact_mod_cast hb_nat
        have hbm : b ≤ m := le_trans hb_nat (by omega)
        have hγ : |(-(b : ℝ) + x)| ≤ M₀ := by
          rw [abs_le]
          constructor <;> linarith [Nat.cast_nonneg (α := ℝ) b, hx.1, hx.2,
            Nat.cast_nonneg (α := ℝ) (S.sup id), hM0_eq]
        have hcongr : (∑ k ∈ Finset.range K,
            multiResolventV S (s m) (1 / ((((k + 1) * m - b : ℕ) : ℝ) + x)) *
              ((((k + 1) * m - b : ℕ) : ℝ) + x) ^ (-(2 * s m))) =
            ∑ k ∈ Finset.range K,
              multiResolventV S (s m) (1 / (((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x))) *
                ((((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x)) ^ (-(2 * s m))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hk1m : b ≤ (k + 1) * m := le_trans hbm (Nat.le_mul_of_pos_left m (by omega))
          have hcast : ((((k + 1) * m - b : ℕ) : ℝ) + x) =
              ((k + 1 : ℕ) : ℝ) * (m : ℝ) + (-(b : ℝ) + x) := by
            rw [Nat.cast_sub hk1m]; push_cast; ring
          rw [hcast]
        rw [hcongr]
        exact hbr_ge (-(b : ℝ) + x) hγ
      calc (1 : ℝ) ≤ d * Bval := by
            have heq : d * Bval =
                d * (1 + 2 / (m : ℝ)) ^ (-(2 * s m)) * (1 + M₀ / (m : ℝ)) ^ (-(2 * s m)) *
                  (m : ℝ) ^ (-(2 * (c * (m : ℝ) ^ (-(2 * s₀))))) *
                  (multiC S (2 * s m) * (m : ℝ) ^ (-(2 * s₀))) * ZK (s m) := by
              dsimp only [Bval]; ring
            rw [heq]; exact hlhs_gt1.le
        _ = (S.card : ℝ) * Bval + (B.card : ℝ) * Bval := by dsimp only [d]; push_cast; ring
        _ ≤ truncMultiResidueTailReal m K S B (s m) x := add_le_add hS_br hB_br
  have hdim_enn := dimH_multiResidue_lower_of_truncTail_ge_one hS1 hm_sep hd_nat hK1 hs_pos
    hsum_s htail
  have hdim_real : s m ≤ (dimH (multiResidueSet m S B)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hne_top).mp hdim_enn
  have hdiff : c * (m : ℝ) ^ (-(2 * s₀)) ≤ (dimH (multiResidueSet m S B)).toReal - s₀ := by
    dsimp [s] at hdim_real; linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff (Real.rpow_nonneg hm_pos.le (2 * s₀))
  have hcancel : (m : ℝ) ^ (2 * s₀) * (c * (m : ℝ) ^ (-(2 * s₀))) = c := by
    rw [mul_left_comm, ← Real.rpow_add hm_pos, add_neg_cancel, Real.rpow_zero, mul_one]
  exact hcancel ▸ hmul

/-! ### Part 5: Main Theorems (Real Zeta Series & `riemannZeta` Forms) -/

/-- **Exact Supercritical Leading Constant (Real Zeta Series Form)**:
    Under the explicit simple-pole hypothesis `hPole` on `multiC S` at `2 * poincareAbscissa S`,
    `m^(2 s₀) * (dimH (multiResidueSet m S B) - s₀) → (S.card + B.card) * κ * ζ(2 s₀) / 2`. -/
theorem tendsto_supercritical_leading_constant {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S)
    {κ : ℝ} (hκ : 0 < κ)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ)) :
    Tendsto (fun m : ℕ =>
        (m : ℝ) ^ (2 * poincareAbscissa S) *
          ((dimH (multiResidueSet m S B)).toReal - poincareAbscissa S))
      atTop (𝓝 (((S.card + B.card : ℕ) : ℝ) * κ *
        (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) / 2)) := by
  let L : ℝ := ((S.card + B.card : ℕ) : ℝ) * κ *
    (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) / 2
  have hSne : S.Nonempty := nonempty_of_half_lt_poincareAbscissa hsuper
  have hd_pos : (0 : ℝ) < ((S.card + B.card : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_pos_left hSne.card_pos B.card)
  have hZ_sum : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 2 * poincareAbscissa S))
    refine h.congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have hZ_pos : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S)) := by
    have h0 := hZ_sum.le_tsum 0 (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h1 : (((0 + 1 : ℕ) : ℝ) ^ (-(2 * poincareAbscissa S))) = 1 := by simp
    linarith
  have hL_pos : 0 < L := by dsimp [L]; positivity
  refine tendsto_order.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have haL : a < L := ha
    let c : ℝ := max (L / 2) ((a + L) / 2)
    have hc_pos : 0 < c := lt_of_lt_of_le (half_pos hL_pos) (le_max_left _ _)
    have hc_lt : c < L := max_lt (by linarith) (by linarith)
    have ha_lt_c : a < c := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    filter_upwards [supercritical_eventually_ge hS1 hsuper hκ hPole hc_pos hc_lt] with m hm
    exact lt_of_lt_of_le ha_lt_c hm
  · have hLb : L < b := hb
    let c : ℝ := (L + b) / 2
    have hL_lt_c : L < c := by dsimp [c]; linarith
    have hc_lt_b : c < b := by dsimp [c]; linarith
    filter_upwards [supercritical_eventually_le hS1 hsuper hκ hPole hL_lt_c] with m hm
    exact lt_of_le_of_lt hm hc_lt_b

/-- Identification of `(riemannZeta (p : ℂ)).re` with the real Dirichlet series for `1 < p`. -/
lemma riemannZeta_re_eq_tsum {p : ℝ} (hp : 1 < p) :
    (riemannZeta (p : ℂ)).re = ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-p) := by
  have hre : 1 < (p : ℂ).re := by simpa using hp
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have hterm : ∀ k : ℕ, (1 : ℂ) / ((k : ℂ) + 1) ^ (p : ℂ) =
      ((((k + 1 : ℕ) : ℝ) ^ (-p) : ℝ) : ℂ) := fun k => by
    have hk_nn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk_cast : ((k : ℂ) + 1) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [hk_cast, ← Complex.ofReal_cpow hk_nn p, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Real.rpow_neg hk_nn, one_div]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **Exact Supercritical Leading Constant (`riemannZeta` Form)**:
    `m^(2 s₀) * (dimH (multiResidueSet m S B) - s₀) →`
    `(S.card + B.card) * κ * (riemannZeta (2 s₀)).re / 2`. -/
theorem tendsto_supercritical_leading_constant_zeta {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hsuper : (1 / 2 : ℝ) < poincareAbscissa S)
    {κ : ℝ} (hκ : 0 < κ)
    (hPole : Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
      (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ)) :
    Tendsto (fun m : ℕ =>
        (m : ℝ) ^ (2 * poincareAbscissa S) *
          ((dimH (multiResidueSet m S B)).toReal - poincareAbscissa S))
      atTop (𝓝 (((S.card + B.card : ℕ) : ℝ) * κ *
        (riemannZeta ((2 * poincareAbscissa S : ℝ) : ℂ)).re / 2)) := by
  rw [riemannZeta_re_eq_tsum (by linarith : (1 : ℝ) < 2 * poincareAbscissa S)]
  exact tendsto_supercritical_leading_constant hS1 hsuper hκ hPole

end

end SupercriticalConstant
