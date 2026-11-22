import Mathlib
import EpiFormal.WeightedFinal
import EpiFormal.WeightedPhase
import EpiFormal.DimHCore

open Real Filter Topology Set Finset MeasureTheory DimHCore WeightedFiber WeightedUpper WeightedFinal SpectralGap
open scoped ENNReal NNReal

namespace WeightedExactDim

noncomputable section

/-! ## 1. 精确极限集定义与基础性质 -/

/-- 精确加权极限集：`{x ∈ [0,1] | j^α ‖Q_j x‖ → c}`。 -/
def exactLimitSetα (α c : ℝ) : Set ℝ :=
  {x ∈ Set.Icc (0 : ℝ) 1 | Tendsto (apprSeqα α x) atTop (nhds c)}

/-- 精确极限集包含于加权子水平集。 -/
lemma exactLimitSetα_subset_levelSetα (α c : ℝ) :
    exactLimitSetα α c ⊆ levelSetα α (ENNReal.ofReal c) := by
  intro x hx
  have htend : Tendsto (apprSeqαE α x) atTop (nhds (ENNReal.ofReal c)) :=
    ENNReal.tendsto_ofReal hx.2
  show apprExponentα α x ≤ ENNReal.ofReal c
  unfold apprExponentα
  rw [htend.limsup_eq]

/-- `Qsel j ≤ 7^j * j!`（j ≥ 1）。 -/
lemma Qsel_le_seven_pow_mul_fact (j : ℕ) (hj : 1 ≤ j) :
    (Qsel j : ℝ) ≤ (7 : ℝ) ^ j * (Nat.factorial j : ℝ) := by
  induction j, hj using Nat.le_induction with
  | base =>
      simp only [Qsel_one, pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
      norm_num
  | succ j hj ih =>
      have hrec : (Qsel (j + 1) : ℝ) ≤ (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := by
        have hZ := DimHCore.Qsel_succ_le j hj
        have hR : (Qsel (j + 1) : ℝ) ≤ ((4 * (j : ℤ) + 3) * Qsel j : ℝ) := by exact_mod_cast hZ
        push_cast at hR
        linarith
      have h4j3 : 4 * (j : ℝ) + 3 ≤ 7 * ((j + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      have hQjnn : 0 ≤ (Qsel j : ℝ) := by exact_mod_cast le_of_lt (Qsel_pos j hj)
      have hfact : (Nat.factorial (j + 1) : ℝ) = ((j + 1 : ℕ) : ℝ) * (Nat.factorial j : ℝ) := by
        push_cast [Nat.factorial_succ]; ring
      calc (Qsel (j + 1) : ℝ)
          ≤ (4 * (j : ℝ) + 3) * (Qsel j : ℝ) := hrec
        _ ≤ (7 * ((j + 1 : ℕ) : ℝ)) * ((7 : ℝ) ^ j * (Nat.factorial j : ℝ)) := by
            apply mul_le_mul h4j3 ih hQjnn (by positivity)
        _ = (7 : ℝ) ^ (j + 1) * (Nat.factorial (j + 1) : ℝ) := by
            rw [hfact, pow_succ]; ring

/-- `4 * j * Q_j ≤ Q_{j+1}`（j ≥ 1）。 -/
lemma four_mul_Qsel_le_succ (j : ℕ) (hj : 1 ≤ j) :
    4 * (j : ℝ) * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
  have hrec := DimHCore.Qsel_rec1 j hj
  have hQprev0 : 0 ≤ Qsel (j - 1) := by
    by_cases hj1 : j = 1
    · subst hj1; simp [Qsel_zero]
    · exact le_of_lt (Qsel_pos (j - 1) (by omega))
  have hQj0 : 0 ≤ Qsel j := le_of_lt (Qsel_pos j hj)
  have hZ : 4 * (j : ℤ) * Qsel j ≤ Qsel (j + 1) := by nlinarith
  exact_mod_cast hZ

/-- 若 `k ≤ y ≤ k + 1/2`（`k : ℤ`），则 `distToNearestInt y = y - k`。 -/
lemma distToNearestInt_eq_sub_of_mem_Icc (k : ℤ) (y : ℝ)
    (hlo : (k : ℝ) ≤ y) (hhi : y ≤ (k : ℝ) + 1 / 2) :
    distToNearestInt y = y - (k : ℝ) := by
  unfold distToNearestInt
  apply le_antisymm
  · calc |y - (round y : ℝ)| ≤ |y - (k : ℝ)| := round_le y k
      _ = y - (k : ℝ) := abs_of_nonneg (by linarith)
  · by_cases hm : round y ≤ k
    · have hmR : (round y : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm
      have : y - (k : ℝ) ≤ y - (round y : ℝ) := by linarith
      exact le_trans this (le_abs_self _)
    · have hm1 : k + 1 ≤ round y := by omega
      have hm1R : (k : ℝ) + 1 ≤ (round y : ℝ) := by exact_mod_cast hm1
      have : y - (k : ℝ) ≤ (round y : ℝ) - y := by linarith
      calc y - (k : ℝ) ≤ (round y : ℝ) - y := this
        _ = -(y - (round y : ℝ)) := by ring
        _ ≤ |y - (round y : ℝ)| := neg_le_abs _

/-- `0 < s ≤ 1` 时次可加性：`(a + b)^s ≤ a^s + b^s`。 -/
lemma rpow_add_le_add_rpow {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    (a + b) ^ s ≤ a ^ s + b ^ s := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0, add_zero, Real.zero_rpow (ne_of_gt hs0), add_zero]
  · have hpos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
    have hp : 0 < (a + b) ^ s := Real.rpow_pos_of_pos hpos s
    have ha_le : a / (a + b) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hb_le : b / (a + b) ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have ha_nn : 0 ≤ a / (a + b) := div_nonneg ha (le_of_lt hpos)
    have hb_nn : 0 ≤ b / (a + b) := div_nonneg hb (le_of_lt hpos)
    have h1 : a / (a + b) ≤ (a / (a + b)) ^ s := by
      by_cases ha0 : a = 0
      · simp [ha0, Real.zero_rpow (ne_of_gt hs0)]
      · calc a / (a + b) = (a / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (a / (a + b)) ^ s := Real.rpow_le_rpow_of_exponent_ge (div_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hpos) ha_le hs1
    have h2 : b / (a + b) ≤ (b / (a + b)) ^ s := by
      by_cases hb0 : b = 0
      · simp [hb0, Real.zero_rpow (ne_of_gt hs0)]
      · calc b / (a + b) = (b / (a + b)) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (b / (a + b)) ^ s := Real.rpow_le_rpow_of_exponent_ge (div_pos (lt_of_le_of_ne hb (Ne.symm hb0)) hpos) hb_le hs1
    have hsum : (1 : ℝ) ≤ (a / (a + b)) ^ s + (b / (a + b)) ^ s := by
      have hdiv : a / (a + b) + b / (a + b) = 1 := by field_simp
      linarith
    have hmul := mul_le_mul_of_nonneg_right hsum (le_of_lt hp)
    rw [one_mul, add_mul, Real.div_rpow ha (le_of_lt hpos) s, Real.div_rpow hb (le_of_lt hpos) s,
      div_mul_cancel₀ _ (ne_of_gt hp), div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
    exact hmul

/-! ## 2. 均匀嵌套 Cantor 树构造（固定 `α, c, s`） -/

section CantorConstruction

variable (α c β : ℝ)

/-- 第 `j` 层偏移宽 `w_j = j^{-β}`。 -/
def wWidth (j : ℕ) : ℝ := (j : ℝ) ^ (-β)

/-- 第 `j` 层区间半径 `r_j = w_j / Q_j`。 -/
def cRad (j : ℕ) : ℝ := wWidth β j / (Qsel j : ℝ)

/-- 第 `j` 层钳位偏移 `θ_j = max(w_j, min(c j^{-α}, 1/2 - w_j))`。 -/
def cTheta (j : ℕ) : ℝ := max (wWidth β j) (min (c * (j : ℝ) ^ (-α)) (1 / 2 - wWidth β j))

/-- 第 `j` 层第 `k` 块区间中心 `(k + θ_j) / Q_j`。 -/
def cCenter (j : ℕ) (k : ℤ) : ℝ := ((k : ℝ) + cTheta α c β j) / (Qsel j : ℝ)

/-- 第 `j` 层第 `k` 块闭区间。 -/
def cInterv (j : ℕ) (k : ℤ) : Set ℝ :=
  Set.Icc (cCenter α c β j k - cRad β j) (cCenter α c β j k + cRad β j)

/-- 第 `j` 层均匀分支数 `b_j = ⌊6 j^{1-β}⌋₊`。 -/
def branchNum (j : ℕ) : ℕ := Nat.floor (6 * (j : ℝ) ^ (1 - β))

lemma wWidth_pos (j : ℕ) (hj : 1 ≤ j) : 0 < wWidth β j :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < j)) (-β)

lemma cRad_pos (j : ℕ) (hj : 1 ≤ j) : 0 < cRad β j :=
  div_pos (wWidth_pos β j hj) (by exact_mod_cast Qsel_pos j hj)

lemma wWidth_antitone (hβ : 0 < β) {j₁ j₂ : ℕ} (hj₁ : 1 ≤ j₁) (h : j₁ ≤ j₂) :
    wWidth β j₂ ≤ wWidth β j₁ := by
  unfold wWidth
  have hj1pos : (0 : ℝ) < (j₁ : ℝ) := by exact_mod_cast (by omega : 0 < j₁)
  have hle : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h
  exact Real.rpow_le_rpow_of_nonpos hj1pos hle (by linarith)

lemma cRad_succ_le_quarter (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) :
    cRad β (j + 1) ≤ (1 / 4) * cRad β j := by
  unfold cRad
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hfour : 4 * (Qsel j : ℝ) ≤ (Qsel (j + 1) : ℝ) := by
    have h1 := four_mul_Qsel_le_succ j hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  have hw : wWidth β (j + 1) ≤ wWidth β j := wWidth_antitone β hβ hj (by omega)
  have hw0 : 0 ≤ wWidth β (j + 1) := le_of_lt (wWidth_pos β (j + 1) (by omega))
  calc wWidth β (j + 1) / (Qsel (j + 1) : ℝ)
      ≤ wWidth β (j + 1) / (4 * (Qsel j : ℝ)) :=
        div_le_div_of_nonneg_left hw0 (by positivity) hfour
    _ ≤ wWidth β j / (4 * (Qsel j : ℝ)) :=
        div_le_div_of_nonneg_right hw (by positivity)
    _ = (1 / 4) * (wWidth β j / (Qsel j : ℝ)) := by ring

lemma branchNum_ge_five (hβ1 : β < 1) (j : ℕ) (hj : 1 ≤ j) :
    5 * (j : ℝ) ^ (1 - β) ≤ (branchNum β j : ℝ) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpow : (1 : ℝ) ≤ (j : ℝ) ^ (1 - β) := Real.one_le_rpow hj1 (by linarith)
  have hlt := Nat.lt_floor_add_one (6 * (j : ℝ) ^ (1 - β))
  change 6 * (j : ℝ) ^ (1 - β) < (branchNum β j : ℝ) + 1 at hlt
  linarith

lemma branchNum_pos (hβ1 : β < 1) (j : ℕ) (hj : 1 ≤ j) : 0 < branchNum β j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpow : (1 : ℝ) ≤ (j : ℝ) ^ (1 - β) := Real.one_le_rpow hj1 (by linarith)
  have h5 := branchNum_ge_five β hβ1 j hj
  have hpos : (0 : ℝ) < (branchNum β j : ℝ) := by linarith
  exact_mod_cast hpos

/-- 嵌套子中心左端点。 -/
def childLeft (j : ℕ) (k : ℤ) : ℝ :=
  (Qsel (j + 1) : ℝ) * (cCenter α c β j k - (cRad β j - cRad β (j + 1))) - cTheta α c β (j + 1)

/-- 嵌套子中心右端点。 -/
def childRight (j : ℕ) (k : ℤ) : ℝ :=
  (Qsel (j + 1) : ℝ) * (cCenter α c β j k + (cRad β j - cRad β (j + 1))) - cTheta α c β (j + 1)

lemma childRight_sub_childLeft_ge (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) (k : ℤ) :
    6 * (j : ℝ) ^ (1 - β) ≤ childRight α c β j k - childLeft α c β j k := by
  have hdiff : childRight α c β j k - childLeft α c β j k =
      2 * (cRad β j - cRad β (j + 1)) * (Qsel (j + 1) : ℝ) := by
    unfold childRight childLeft; ring
  rw [hdiff]
  have hr := cRad_succ_le_quarter β hβ j hj
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hQj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hfour := four_mul_Qsel_le_succ j hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hrad_nn : 0 ≤ cRad β j := le_of_lt (cRad_pos β j hj)
  have hstep1 : 2 * ((3 / 4) * cRad β j) * (Qsel (j + 1) : ℝ) ≤
      2 * (cRad β j - cRad β (j + 1)) * (Qsel (j + 1) : ℝ) := by
    nlinarith
  have hstep2 : 2 * ((3 / 4) * cRad β j) * (4 * (j : ℝ) * (Qsel j : ℝ)) ≤
      2 * ((3 / 4) * cRad β j) * (Qsel (j + 1) : ℝ) := by
    gcongr
  have hcalc : 2 * ((3 / 4) * cRad β j) * (4 * (j : ℝ) * (Qsel j : ℝ)) = 6 * (j : ℝ) ^ (1 - β) := by
    unfold cRad wWidth
    have hmul : (j : ℝ) ^ (-β) * (j : ℝ) = (j : ℝ) ^ (1 - β) := by
      calc (j : ℝ) ^ (-β) * (j : ℝ)
          = (j : ℝ) ^ (-β) * (j : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (j : ℝ) ^ (-β + 1) := (Real.rpow_add hjpos (-β) 1).symm
        _ = (j : ℝ) ^ (1 - β) := by ring_nf
    have hQj_ne : (Qsel j : ℝ) ≠ 0 := ne_of_gt hQj
    field_simp
    nlinarith [hmul]
  linarith

/-- 第 `j` 层父节点 `k` 的第 `m` 个嵌套子节点整数索引。 -/
def childInt (j : ℕ) (k : ℤ) (m : ℕ) : ℤ :=
  Int.ceil (childLeft α c β j k) + (m : ℤ)

lemma childInt_mem_bounds (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) (k : ℤ) (m : ℕ)
    (hm : m < branchNum β j) :
    childLeft α c β j k ≤ (childInt α c β j k m : ℝ) ∧
      (childInt α c β j k m : ℝ) ≤ childRight α c β j k := by
  set A := childLeft α c β j k
  set B := childRight α c β j k
  have hceil_le : A ≤ (Int.ceil A : ℝ) := Int.le_ceil A
  have hceil_lt : (Int.ceil A : ℝ) < A + 1 := Int.ceil_lt_add_one A
  have hwidth := childRight_sub_childLeft_ge α c β hβ j hj k
  have hfloor_le : (branchNum β j : ℝ) ≤ 6 * (j : ℝ) ^ (1 - β) :=
    Nat.floor_le (by positivity)
  have hm1 : (m : ℝ) + 1 ≤ (branchNum β j : ℝ) := by
    have : m + 1 ≤ branchNum β j := by omega
    exact_mod_cast this
  constructor
  · unfold childInt
    push_cast
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  · unfold childInt
    push_cast
    linarith

/-- 严格嵌套：`cInterv (j+1) (childInt j k m) ⊆ cInterv j k`。 -/
lemma cInterv_child_subset (hβ : 0 < β) (j : ℕ) (hj : 1 ≤ j) (k : ℤ) (m : ℕ)
    (hm : m < branchNum β j) :
    cInterv α c β (j + 1) (childInt α c β j k m) ⊆ cInterv α c β j k := by
  have hb := childInt_mem_bounds α c β hβ j hj k m hm
  have hQj1 : 0 < (Qsel (j + 1) : ℝ) := by exact_mod_cast Qsel_pos (j + 1) (by omega)
  have hlo : cCenter α c β j k - (cRad β j - cRad β (j + 1)) ≤
      cCenter α c β (j + 1) (childInt α c β j k m) := by
    change cCenter α c β j k - (cRad β j - cRad β (j + 1)) ≤
      ((childInt α c β j k m : ℝ) + cTheta α c β (j + 1)) / (Qsel (j + 1) : ℝ)
    rw [le_div_iff₀ hQj1]
    have h1 := hb.1
    unfold childLeft at h1
    linarith
  have hhi : cCenter α c β (j + 1) (childInt α c β j k m) ≤
      cCenter α c β j k + (cRad β j - cRad β (j + 1)) := by
    change ((childInt α c β j k m : ℝ) + cTheta α c β (j + 1)) / (Qsel (j + 1) : ℝ) ≤
      cCenter α c β j k + (cRad β j - cRad β (j + 1))
    rw [div_le_iff₀ hQj1]
    have h2 := hb.2
    unfold childRight at h2
    linarith
  intro x hx
  simp only [cInterv, Set.mem_Icc] at hx ⊢
  constructor <;> linarith

/-- 同级区间不交（需 `w_j ≤ 1/8`）。 -/
lemma cInterv_disjoint (j : ℕ) (hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    {k₁ k₂ : ℤ} (hne : k₁ ≠ k₂) :
    Disjoint (cInterv α c β j k₁) (cInterv α c β j k₂) := by
  rw [Set.disjoint_iff]
  intro x hx
  have h1 := hx.1
  have h2 := hx.2
  simp only [cInterv, Set.mem_Icc] at h1 h2
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hdist : |cCenter α c β j k₁ - cCenter α c β j k₂| ≤ 2 * cRad β j := by
    rw [abs_le]; constructor <;> linarith
  have hdiff : cCenter α c β j k₁ - cCenter α c β j k₂ = ((k₁ : ℝ) - (k₂ : ℝ)) / (Qsel j : ℝ) := by
    unfold cCenter; ring
  rw [hdiff, abs_div, abs_of_pos hQj] at hdist
  have h1le : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
    have : 1 ≤ |k₁ - k₂| := Int.one_le_abs (sub_ne_zero.mpr hne)
    exact_mod_cast this
  have hmul := (div_le_iff₀ hQj).mp hdist
  unfold cRad at hmul
  have hsimp : 2 * (wWidth β j / (Qsel j : ℝ)) * (Qsel j : ℝ) = 2 * wWidth β j := by
    field_simp
  rw [hsimp] at hmul
  linarith

/-- 若 `x ∈ cInterv j k` 且 `w_j ≤ 1/8`，则 `|distToNearestInt (Q_j x) - θ_j| ≤ w_j`。 -/
lemma distToNearestInt_cInterv_bound (j : ℕ) (hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    (k : ℤ) {x : ℝ} (hx : x ∈ cInterv α c β j k) :
    |distToNearestInt ((Qsel j : ℝ) * x) - cTheta α c β j| ≤ wWidth β j := by
  simp only [cInterv, Set.mem_Icc] at hx
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have hθ_lo : wWidth β j ≤ cTheta α c β j := le_max_left _ _
  have hθ_hi : cTheta α c β j ≤ 1 / 2 - wWidth β j :=
    max_le (by linarith) (min_le_right _ _)
  have hQx_lo : (k : ℝ) + cTheta α c β j - wWidth β j ≤ (Qsel j : ℝ) * x := by
    have h1 := mul_le_mul_of_nonneg_left hx.1 (le_of_lt hQj)
    have h2 : (Qsel j : ℝ) * (cCenter α c β j k - cRad β j) =
        (k : ℝ) + cTheta α c β j - wWidth β j := by
      unfold cCenter cRad; field_simp
    linarith
  have hQx_hi : (Qsel j : ℝ) * x ≤ (k : ℝ) + cTheta α c β j + wWidth β j := by
    have h1 := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hQj)
    have h2 : (Qsel j : ℝ) * (cCenter α c β j k + cRad β j) =
        (k : ℝ) + cTheta α c β j + wWidth β j := by
      unfold cCenter cRad; field_simp
    linarith
  have hd := distToNearestInt_eq_sub_of_mem_Icc k ((Qsel j : ℝ) * x)
    (by linarith) (by linarith)
  rw [hd, abs_le]
  constructor <;> linarith

/-- 钳位偏移与目标 `c j^{-α}` 的距离至多 `w_j`。 -/
lemma abs_cTheta_sub_le (j : ℕ) (hw : wWidth β j ≤ 1 / 8)
    (htarget0 : 0 ≤ c * (j : ℝ) ^ (-α)) (htarget_hi : c * (j : ℝ) ^ (-α) ≤ 1 / 2) :
    |cTheta α c β j - c * (j : ℝ) ^ (-α)| ≤ wWidth β j := by
  unfold cTheta
  set t := c * (j : ℝ) ^ (-α)
  set w := wWidth β j
  have hw0 : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg j) (-β)
  rw [abs_le]
  constructor
  · -- -w ≤ max w (min t (1/2 - w)) - t
    by_cases ht : t ≤ 1 / 2 - w
    · have : min t (1 / 2 - w) = t := min_eq_left ht
      have hle : t ≤ max w (min t (1 / 2 - w)) := by rw [this]; exact le_max_right _ _
      linarith
    · have : min t (1 / 2 - w) = 1 / 2 - w := min_eq_right (le_of_not_ge ht)
      have hle : 1 / 2 - w ≤ max w (min t (1 / 2 - w)) := by rw [this]; exact le_max_right _ _
      linarith
  · -- max w (min t (1/2 - w)) - t ≤ w
    have hmax : max w (min t (1 / 2 - w)) ≤ t + w := by
      apply max_le
      · linarith
      · exact le_trans (min_le_left _ _) (by linarith)
    linarith

/-- 若集合 `V` 的直径 `≤ 1 / Q_j` 且 `w_j ≤ 1/8`，则与 `V` 相交的所有 `k : ℤ` 之间相差至多 1。 -/
lemma intersect_cInterv_abs_sub_le_one (j : ℕ) (hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    {V : Set ℝ} (hbd : Bornology.IsBounded V) (hdiam : Metric.diam V ≤ 1 / (Qsel j : ℝ))
    {k₁ k₂ : ℤ} {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ V ∩ cInterv α c β j k₁) (hx₂ : x₂ ∈ V ∩ cInterv α c β j k₂) :
    |k₁ - k₂| ≤ 1 := by
  have hQj : 0 < (Qsel j : ℝ) := by exact_mod_cast Qsel_pos j hj
  have h1 := hx₁.2
  have h2 := hx₂.2
  simp only [cInterv, Set.mem_Icc] at h1 h2
  have hdx : |x₁ - x₂| ≤ 1 / (Qsel j : ℝ) := by
    have := Metric.dist_le_diam_of_mem hbd hx₁.1 hx₂.1
    rw [Real.dist_eq] at this
    exact le_trans this hdiam
  have hdx' := abs_le.mp hdx
  have hcdiff : |cCenter α c β j k₁ - cCenter α c β j k₂| ≤ 2 * cRad β j + 1 / (Qsel j : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hdiff : cCenter α c β j k₁ - cCenter α c β j k₂ = ((k₁ : ℝ) - (k₂ : ℝ)) / (Qsel j : ℝ) := by
    unfold cCenter; ring
  rw [hdiff, abs_div, abs_of_pos hQj] at hcdiff
  have hmul := (div_le_iff₀ hQj).mp hcdiff
  have hsimp : (2 * cRad β j + 1 / (Qsel j : ℝ)) * (Qsel j : ℝ) = 2 * wWidth β j + 1 := by
    unfold cRad; field_simp
  rw [hsimp] at hmul
  have hlt2 : |(k₁ : ℝ) - (k₂ : ℝ)| < 2 := by linarith
  have hlt2Z : |k₁ - k₂| < 2 := by exact_mod_cast hlt2
  omega

/-- 由 `|k₁ - k₂| ≤ 1` 得满足条件的整数集合基数至多为 2。 -/
lemma card_le_two_of_abs_sub_le_one {ι : Type*} (f : ι → ℤ)
    (hinj : Function.Injective f) (S : Finset ι)
    (hclose : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ 1) :
    S.card ≤ 2 := by
  by_cases hS : S.Nonempty
  · obtain ⟨a0, ha0⟩ := hS
    have hsub : S.image f ⊆ {f a0 - 1, f a0, f a0 + 1} := by
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      have h := abs_le.mp (hclose a ha a0 ha0)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    -- 更强：S.image f 不能同时含 f a0 - 1 和 f a0 + 1
    by_cases hm : f a0 - 1 ∈ S.image f
    · have hp : f a0 + 1 ∉ S.image f := by
        intro hp
        obtain ⟨a1, ha1, hfa1⟩ := Finset.mem_image.mp hm
        obtain ⟨a2, ha2, hfa2⟩ := Finset.mem_image.mp hp
        have h := abs_le.mp (hclose a1 ha1 a2 ha2)
        omega
      have hsub2 : S.image f ⊆ {f a0 - 1, f a0} := by
        intro z hz
        have h3 := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at h3 ⊢
        rcases h3 with rfl | rfl | rfl
        · left; rfl
        · right; rfl
        · exact absurd hz hp
      have hcard : (S.image f).card ≤ 2 := by
        calc (S.image f).card ≤ ({f a0 - 1, f a0} : Finset ℤ).card := Finset.card_le_card hsub2
          _ ≤ 2 := Finset.card_le_two
      rwa [Finset.card_image_of_injective S hinj] at hcard
    · have hsub2 : S.image f ⊆ {f a0, f a0 + 1} := by
        intro z hz
        have h3 := hsub hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at h3 ⊢
        rcases h3 with rfl | rfl | rfl
        · exact absurd hz hm
        · left; rfl
        · right; rfl
      have hcard : (S.image f).card ≤ 2 := by
        calc (S.image f).card ≤ ({f a0, f a0 + 1} : Finset ℤ).card := Finset.card_le_card hsub2
          _ ≤ 2 := Finset.card_le_two
      rwa [Finset.card_image_of_injective S hinj] at hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]; simp

/-! ## 3. Cantor 树词、投影与纤维计数 -/

variable (J : ℕ)

/-- 第 `n` 层词类型。 -/
abbrev CWord (n : ℕ) : Type := ∀ i : Fin n, Fin (branchNum β (J + i.1))

/-- 第 `n` 层词总数 `M_n = ∏_{i=0}^{n-1} b_{J+i}`。 -/
def wordCount (n : ℕ) : ℕ := ∏ i : Fin n, branchNum β (J + i.1)

lemma card_CWord (n : ℕ) : Fintype.card (CWord β J n) = wordCount β J n := by
  unfold CWord wordCount
  simp [Fintype.card_pi]

lemma wordCount_pos (hβ1 : β < 1) (hJ : 1 ≤ J) (n : ℕ) : 0 < wordCount β J n := by
  unfold wordCount
  exact Finset.prod_pos (fun i _ => branchNum_pos β hβ1 (J + i.1) (by omega))

lemma wordCount_succ (n : ℕ) :
    wordCount β J (n + 1) = wordCount β J n * branchNum β (J + n) := by
  unfold wordCount
  rw [Fin.prod_univ_castSucc]
  rfl

/-- 第 `n` 层词对应的整数中心（根为 `0`）。 -/
def centerInt : ∀ n, CWord β J n → ℤ
  | 0, _ => 0
  | n + 1, w => childInt α c β (J + n) (centerInt n (fun i => w i.castSucc)) (w (Fin.last n)).1

/-- 前缀投影 `Word N → Word n`（`n ≤ N`）。 -/
def prefixWord {n N : ℕ} (h : n ≤ N) (w : CWord β J N) : CWord β J n :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

lemma prefixWord_self (n : ℕ) (w : CWord β J n) : prefixWord β J (le_refl n) w = w := by
  funext i; rfl

lemma prefixWord_succ {n N : ℕ} (h : n ≤ N) (w : CWord β J (N + 1)) :
    prefixWord β J (Nat.le_succ_of_le h) w = prefixWord β J h (fun i => w i.castSucc) := by
  funext i; rfl

/-- 子区间嵌套到祖先区间。 -/
lemma cInterv_prefix_subset (hβ : 0 < β) (hJ : 1 ≤ J) {n N : ℕ} (h : n ≤ N) (w : CWord β J N) :
    cInterv α c β (J + N) (centerInt α c β J N w) ⊆
      cInterv α c β (J + n) (centerInt α c β J n (prefixWord β J h w)) := by
  induction N, h using Nat.le_induction with
  | base =>
      rw [prefixWord_self]
  | succ N h ih =>
      have hstep : cInterv α c β (J + (N + 1)) (centerInt α c β J (N + 1) w) ⊆
          cInterv α c β (J + N) (centerInt α c β J N (fun i => w i.castSucc)) := by
        have heq : J + (N + 1) = (J + N) + 1 := by omega
        rw [heq]
        exact cInterv_child_subset α c β hβ (J + N) (by omega)
          (centerInt α c β J N (fun i => w i.castSucc)) (w (Fin.last N)).1 (w (Fin.last N)).2
      rw [prefixWord_succ β J h w]
      exact Set.Subset.trans hstep (ih (fun i => w i.castSucc))

/-- `centerInt n` 单射（需对一切 `m ≥ J` 有 `w_m ≤ 1/8`）。 -/
lemma centerInt_injective (hβ : 0 < β) (hJ : 1 ≤ J)
    (hwJ : wWidth β J ≤ 1 / 8) (n : ℕ) :
    Function.Injective (centerInt α c β J n) := by
  induction n with
  | zero =>
      intro w₁ w₂ _
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro w₁ w₂ heq
      set p₁ : CWord β J n := fun i => w₁ i.castSucc
      set p₂ : CWord β J n := fun i => w₂ i.castSucc
      have hp : p₁ = p₂ := by
        by_contra hne
        have hkne : centerInt α c β J n p₁ ≠ centerInt α c β J n p₂ :=
          fun hc => hne (ih hc)
        have hwn : wWidth β (J + n) ≤ 1 / 8 :=
          le_trans (wWidth_antitone β hβ hJ (by omega)) hwJ
        have hdisj := cInterv_disjoint α c β (J + n) (by omega) hwn hkne
        have hsub1 : cInterv α c β (J + (n + 1)) (centerInt α c β J (n + 1) w₁) ⊆
            cInterv α c β (J + n) (centerInt α c β J n p₁) := by
          have heq1 : J + (n + 1) = (J + n) + 1 := by omega
          rw [heq1]
          exact cInterv_child_subset α c β hβ (J + n) (by omega) _ _ (w₁ (Fin.last n)).2
        have hsub2 : cInterv α c β (J + (n + 1)) (centerInt α c β J (n + 1) w₂) ⊆
            cInterv α c β (J + n) (centerInt α c β J n p₂) := by
          have heq1 : J + (n + 1) = (J + n) + 1 := by omega
          rw [heq1]
          exact cInterv_child_subset α c β hβ (J + n) (by omega) _ _ (w₂ (Fin.last n)).2
        rw [heq] at hsub1
        have hmem : cCenter α c β (J + (n + 1)) (centerInt α c β J (n + 1) w₂) ∈
            cInterv α c β (J + (n + 1)) (centerInt α c β J (n + 1) w₂) := by
          have hr := le_of_lt (cRad_pos β (J + (n + 1)) (by omega))
          simp only [cInterv, Set.mem_Icc]
          constructor <;> linarith
        exact Set.disjoint_left.mp hdisj (hsub1 hmem) (hsub2 hmem)
      have hlast : w₁ (Fin.last n) = w₂ (Fin.last n) := by
        have hci : childInt α c β (J + n) (centerInt α c β J n p₁) (w₁ (Fin.last n)).1 =
            childInt α c β (J + n) (centerInt α c β J n p₁) (w₂ (Fin.last n)).1 := by
          have := heq
          simp only [centerInt] at this
          change childInt α c β (J + n) (centerInt α c β J n p₁) (w₁ (Fin.last n)).1 =
            childInt α c β (J + n) (centerInt α c β J n p₂) (w₂ (Fin.last n)).1 at this
          rw [hp] at this ⊢
          exact this
        unfold childInt at hci
        have hmZ : ((w₁ (Fin.last n)).1 : ℤ) = ((w₂ (Fin.last n)).1 : ℤ) := add_left_cancel hci
        have hmN : (w₁ (Fin.last n)).1 = (w₂ (Fin.last n)).1 := by exact_mod_cast hmZ
        exact Fin.ext hmN
      funext i
      refine Fin.lastCases hlast (fun j => ?_) i
      exact congrFun hp j

/-- 抽象分支序列的纤维计数引理（避免 `isDefEq` 展开 `branchNum`）。 -/
private lemma card_prefix_fiber_mul_aux (b : ℕ → ℕ) (n N : ℕ) (h : n ≤ N)
    (u : ∀ i : Fin n, Fin (b i.1)) :
    (Finset.univ.filter (fun w : (∀ i : Fin N, Fin (b i.1)) =>
      (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)).card * (∏ i : Fin n, b i.1) =
      ∏ i : Fin N, b i.1 := by
  induction N, h using Nat.le_induction with
  | base =>
      have hfilt : (Finset.univ.filter (fun w : (∀ i : Fin n, Fin (b i.1)) =>
          (fun i : Fin n => w ⟨i.1, i.2⟩) = u)) = {u} := by
        ext w; simp
      rw [hfilt, Finset.card_singleton, one_mul]
  | succ N h ih =>
      let e : (∀ i : Fin (N + 1), Fin (b i.1)) ≃
          (∀ i : Fin N, Fin (b i.1)) × Fin (b N) :=
        { toFun := fun w => (fun i => w i.castSucc, w (Fin.last N))
          invFun := fun p => Fin.lastCases (motive := fun i : Fin (N + 1) => Fin (b i.1))
            p.2 (fun i => p.1 i)
          left_inv := fun w => by
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · exact Fin.lastCases_last
            · exact Fin.lastCases_castSucc j
          right_inv := fun p => by
            apply Prod.ext
            · funext j; dsimp only; exact Fin.lastCases_castSucc j
            · dsimp only; exact Fin.lastCases_last }
      have hbij : (Finset.univ.filter (fun w : (∀ i : Fin (N + 1), Fin (b i.1)) =>
            (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_succ_of_le h)⟩) = u)).card =
          ((Finset.univ.filter (fun w : (∀ i : Fin N, Fin (b i.1)) =>
            (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)) ×ˢ
            (Finset.univ : Finset (Fin (b N)))).card := by
        apply Finset.card_bij (fun w _ => e w)
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true] at hw ⊢
          exact hw
        · intro w₁ _ w₂ _ heq
          exact e.injective heq
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hcast : ∀ i : Fin n, e.symm p ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_succ_of_le h)⟩ =
              p.1 ⟨i.1, lt_of_lt_of_le i.2 h⟩ := fun i => by
            change Fin.lastCases (motive := fun j : Fin (N + 1) => Fin (b j.1))
              p.2 (fun j => p.1 j) (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin N).castSucc =
              p.1 ⟨i.1, lt_of_lt_of_le i.2 h⟩
            exact Fin.lastCases_castSucc (⟨i.1, lt_of_lt_of_le i.2 h⟩ : Fin N)
          funext i
          rw [hcast i]
          exact congrFun hp i
      rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_fin, Fin.prod_univ_castSucc]
      calc (Finset.univ.filter (fun w : (∀ i : Fin N, Fin (b i.1)) =>
              (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)).card *
              b N * (∏ i : Fin n, b i.1)
          = ((Finset.univ.filter (fun w : (∀ i : Fin N, Fin (b i.1)) =>
              (fun i : Fin n => w ⟨i.1, lt_of_lt_of_le i.2 h⟩) = u)).card *
              (∏ i : Fin n, b i.1)) * b N := by ring
        _ = (∏ i : Fin N, b i.1) * b N := by rw [ih]

/-- 固定第 `n` 层前缀 `u`，第 `N` 层（`n ≤ N`）扩展词数满足 `fiberCard * M_n = M_N`。 -/
lemma card_prefix_fiber_mul (n N : ℕ) (h : n ≤ N) (u : CWord β J n) :
    (Finset.univ.filter (fun w : CWord β J N => prefixWord β J h w = u)).card * wordCount β J n =
      wordCount β J N :=
  card_prefix_fiber_mul_aux (fun k => branchNum β (J + k)) n N h u

/-! ## 4. Cantor 集 `K` 的紧致性、非空交与包含于精确极限集 -/

/-- 第 `n` 层紧致集 `K_n`。 -/
def cantorLevel (n : ℕ) : Set ℝ :=
  ⋃ w : CWord β J n, cInterv α c β (J + n) (centerInt α c β J n w)

/-- Cantor 集 `K = ⋂_n K_n`。 -/
def cantorSet : Set ℝ :=
  ⋂ n : ℕ, cantorLevel α c β J n

lemma isCompact_cantorLevel (n : ℕ) : IsCompact (cantorLevel α c β J n) :=
  isCompact_iUnion (fun _ => isCompact_Icc)

lemma isCompact_cantorSet : IsCompact (cantorSet α c β J) := by
  apply IsCompact.of_isClosed_subset (isCompact_cantorLevel α c β J 0)
  · exact isClosed_iInter (fun n => (isCompact_cantorLevel α c β J n).isClosed)
  · exact Set.iInter_subset _ 0

/-- 给定第 `n` 层词 `u`，向右不断补 `0` 得到无穷分支。 -/
def extendZero (hβ1 : β < 1) (hJ : 1 ≤ J) {n : ℕ} (u : CWord β J n) (m : ℕ) : CWord β J (n + m) :=
  fun i =>
    if h : i.1 < n then u ⟨i.1, h⟩
    else ⟨0, branchNum_pos β hβ1 (J + i.1) (by omega)⟩

/-- 每个第 `n` 层区间都与 Cantor 集 `K` 非空相交。 -/
lemma cInterv_inter_cantorSet_nonempty (hβ : 0 < β) (hβ1 : β < 1) (hJ : 1 ≤ J)
    (n : ℕ) (u : CWord β J n) :
    (cInterv α c β (J + n) (centerInt α c β J n u) ∩ cantorSet α c β J).Nonempty := by
  let F : ℕ → Set ℝ := fun m => cInterv α c β (J + (n + m)) (centerInt α c β J (n + m) (extendZero β J hβ1 hJ u m))
  have hanti : ∀ m, F (m + 1) ⊆ F m := by
    intro m
    change cInterv α c β (J + (n + (m + 1))) _ ⊆ cInterv α c β (J + (n + m)) _
    have hsub := cInterv_prefix_subset α c β J hβ hJ (show n + m ≤ n + (m + 1) by omega)
      (extendZero β J hβ1 hJ u (m + 1))
    have hpre : prefixWord β J (show n + m ≤ n + (m + 1) by omega) (extendZero β J hβ1 hJ u (m + 1)) =
        extendZero β J hβ1 hJ u m := by
      funext i
      simp only [prefixWord, extendZero]
    rwa [hpre] at hsub
  have hne : ∀ m, (F m).Nonempty := fun m => by
    refine ⟨cCenter α c β (J + (n + m)) (centerInt α c β J (n + m) (extendZero β J hβ1 hJ u m)), ?_⟩
    have hr := le_of_lt (cRad_pos β (J + (n + m)) (by omega))
    simp only [F, cInterv, Set.mem_Icc]
    constructor <;> linarith
  have hcomp : ∀ m, IsCompact (F m) := fun _ => isCompact_Icc
  have hclosed : ∀ m, IsClosed (F m) := fun _ => isClosed_Icc
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hanti hne (hcomp 0) hclosed
  have hpre0 : extendZero β J hβ1 hJ u 0 = u := by
    funext i
    have hi : i.1 < n := by omega
    simp only [extendZero, hi, ↓reduceDIte]
    rfl
  refine ⟨x, ?_, ?_⟩
  · have hx0 : x ∈ F 0 := Set.mem_iInter.mp hx 0
    simpa [F, hpre0] using hx0
  · rw [cantorSet, Set.mem_iInter]
    intro k
    by_cases hkn : k ≤ n
    · have hx0 : x ∈ F 0 := Set.mem_iInter.mp hx 0
      have hxu : x ∈ cInterv α c β (J + n) (centerInt α c β J n u) := by
        simpa [F, hpre0] using hx0
      have hsub := cInterv_prefix_subset α c β J hβ hJ hkn u
      exact Set.mem_iUnion.mpr ⟨prefixWord β J hkn u, hsub hxu⟩
    · have hxk : x ∈ F (k - n) := Set.mem_iInter.mp hx (k - n)
      generalize hm : k - n = m at hxk
      have heq : n + m = k := by omega
      subst heq
      exact Set.mem_iUnion.mpr ⟨extendZero β J hβ1 hJ u m, hxk⟩

/-- Cantor 集包含于精确极限集 `exactLimitSetα α c`。 -/
lemma cantorSet_subset_exactLimitSetα (hα0 : 0 ≤ α) (hβ : 0 < β) (hαβ : α < β)
    (hJ : 1 ≤ J) (hwJ : wWidth β J ≤ 1 / 8)
    (htarget : ∀ j, J ≤ j → 0 ≤ c * (j : ℝ) ^ (-α) ∧ c * (j : ℝ) ^ (-α) ≤ 1 / 2) :
    cantorSet α c β J ⊆ exactLimitSetα α c := by
  intro x hx
  have hx0 : x ∈ cantorLevel α c β J 0 := Set.mem_iInter.mp hx 0
  obtain ⟨w0, hw0⟩ := Set.mem_iUnion.mp hx0
  have hc0 : centerInt α c β J 0 w0 = 0 := rfl
  rw [hc0] at hw0
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [cInterv, Set.mem_Icc] at hw0 ⊢
    have hQj : 0 < (Qsel J : ℝ) := by exact_mod_cast Qsel_pos J hJ
    have hQj1 : (1 : ℝ) ≤ (Qsel J : ℝ) := by exact_mod_cast DimHCore.Qsel_ge_one J hJ
    have hθ_lo : wWidth β J ≤ cTheta α c β J := le_max_left _ _
    have hθ_hi : cTheta α c β J ≤ 1 / 2 - wWidth β J := max_le (by linarith) (min_le_right _ _)
    have hleft : 0 ≤ cCenter α c β J 0 - cRad β J := by
      have heq : cCenter α c β J 0 - cRad β J = ((0 : ℤ) + cTheta α c β J - wWidth β J) / (Qsel J : ℝ) := by
        unfold cCenter cRad; ring
      rw [heq]
      exact div_nonneg (by push_cast; linarith) (le_of_lt hQj)
    have hright : cCenter α c β J 0 + cRad β J ≤ 1 := by
      have heq : cCenter α c β J 0 + cRad β J = ((0 : ℤ) + cTheta α c β J + wWidth β J) / (Qsel J : ℝ) := by
        unfold cCenter cRad; ring
      rw [heq, div_le_one hQj]
      push_cast; linarith
    rw [Nat.add_zero] at hw0
    exact ⟨le_trans hleft hw0.1, le_trans hw0.2 hright⟩
  refine ⟨hxIcc, ?_⟩
  -- 证明 apprSeqα α x j → c
  have hbound : ∀ j, J ≤ j → |apprSeqα α x j - c| ≤ 2 * (j : ℝ) ^ (-(β - α)) := by
    intro j hj
    have hxj : x ∈ cantorLevel α c β J (j - J) := Set.mem_iInter.mp hx (j - J)
    have hjeq : J + (j - J) = j := by omega
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hxj
    rw [hjeq] at hw
    have hwj : wWidth β j ≤ 1 / 8 := le_trans (wWidth_antitone β hβ hJ hj) hwJ
    have hdist1 := distToNearestInt_cInterv_bound α c β j (by omega) hwj _ hw
    have hdist2 := abs_cTheta_sub_le α c β j hwj (htarget j hj).1 (htarget j hj).2
    have hdist : |distToNearestInt ((Qsel j : ℝ) * x) - c * (j : ℝ) ^ (-α)| ≤ 2 * wWidth β j := by
      calc |distToNearestInt ((Qsel j : ℝ) * x) - c * (j : ℝ) ^ (-α)|
          ≤ |distToNearestInt ((Qsel j : ℝ) * x) - cTheta α c β j| +
            |cTheta α c β j - c * (j : ℝ) ^ (-α)| := abs_sub_le _ _ _
        _ ≤ wWidth β j + wWidth β j := add_le_add hdist1 hdist2
        _ = 2 * wWidth β j := by ring
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hjαpos : 0 < (j : ℝ) ^ α := Real.rpow_pos_of_pos hjpos α
    have hmul : (j : ℝ) ^ α * (c * (j : ℝ) ^ (-α)) = c := by
      calc (j : ℝ) ^ α * (c * (j : ℝ) ^ (-α))
          = c * ((j : ℝ) ^ α * (j : ℝ) ^ (-α)) := by ring
        _ = c * (j : ℝ) ^ (α + -α) := by rw [← Real.rpow_add hjpos]
        _ = c * 1 := by simp
        _ = c := mul_one c
    have hmulw : (j : ℝ) ^ α * wWidth β j = (j : ℝ) ^ (-(β - α)) := by
      unfold wWidth
      rw [← Real.rpow_add hjpos]
      congr 1; ring
    have heq : apprSeqα α x j - c = (j : ℝ) ^ α * (distToNearestInt ((Qsel j : ℝ) * x) - c * (j : ℝ) ^ (-α)) := by
      unfold apprSeqα; rw [mul_sub, hmul]
    rw [heq, abs_mul, abs_of_pos hjαpos]
    calc (j : ℝ) ^ α * |distToNearestInt ((Qsel j : ℝ) * x) - c * (j : ℝ) ^ (-α)|
        ≤ (j : ℝ) ^ α * (2 * wWidth β j) := mul_le_mul_of_nonneg_left hdist (le_of_lt hjαpos)
      _ = 2 * ((j : ℝ) ^ α * wWidth β j) := by ring
      _ = 2 * (j : ℝ) ^ (-(β - α)) := by rw [hmulw]
  have htend0 : Tendsto (fun j : ℕ => 2 * (j : ℝ) ^ (-(β - α))) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (-(β - α))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h2 : Tendsto (fun j : ℕ => (j : ℝ) ^ (-(β - α))) atTop (nhds 0) :=
      h1.comp tendsto_natCast_atTop_atTop
    simpa using h2.const_mul 2
  rw [Metric.tendsto_atTop] at htend0 ⊢
  intro δ hδ
  obtain ⟨N, hN⟩ := htend0 δ hδ
  refine ⟨max J N, fun j hj => ?_⟩
  rw [Real.dist_eq]
  have h1 := hbound j (le_trans (le_max_left _ _) hj)
  have h2 := hN j (le_trans (le_max_right _ _) hj)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  exact lt_of_le_of_lt h1 h2

/-! ## 5. 渐近增长比较与 Hausdorff 测度正性 -/

/-- 阶乘积恒等式：`(J - 1)! * ∏_{i < n} (J + i) = (J + n - 1)!`（`J ≥ 1`）。 -/
lemma fact_mul_prod_add (hJ : 1 ≤ J) (n : ℕ) :
    Nat.factorial (J - 1) * (∏ i : Fin n, (J + i.1)) = Nat.factorial (J + n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      have h1 : J + (n + 1) - 1 = (J + n - 1) + 1 := by omega
      have h2 : (J + n - 1) + 1 = J + n := by omega
      rw [h1, Nat.factorial_succ, h2]
      calc Nat.factorial (J - 1) * ((∏ i : Fin n, (J + i.1)) * (J + n))
          = (Nat.factorial (J - 1) * ∏ i : Fin n, (J + i.1)) * (J + n) := by ring
        _ = Nat.factorial (J + n - 1) * (J + n) := by rw [ih]
        _ = (J + n) * Nat.factorial (J + n - 1) := by ring

/-- `M_n ≥ ((J+n-1)! / (J-1)!)^{1-β}`（`J ≥ 1`, `β < 1`）。 -/
lemma wordCount_ge_fact_rpow (hβ1 : β < 1) (hJ : 1 ≤ J) (n : ℕ) :
    ((Nat.factorial (J + n - 1) : ℝ) / (Nat.factorial (J - 1) : ℝ)) ^ (1 - β) ≤
      (wordCount β J n : ℝ) := by
  have hprod : (∏ i : Fin n, ((J + i.1 : ℕ) : ℝ)) ^ (1 - β) ≤ (wordCount β J n : ℝ) := by
    unfold wordCount
    rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _)]
    gcongr with i _
    have h5 := branchNum_ge_five β hβ1 (J + i.1) (by omega)
    have hpow : (0 : ℝ) ≤ ((J + i.1 : ℕ) : ℝ) ^ (1 - β) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hfact := fact_mul_prod_add J hJ n
  have hfactR : (Nat.factorial (J - 1) : ℝ) * (∏ i : Fin n, ((J + i.1 : ℕ) : ℝ)) =
      (Nat.factorial (J + n - 1) : ℝ) := by
    have : ((Nat.factorial (J - 1) * ∏ i : Fin n, (J + i.1) : ℕ) : ℝ) =
        (Nat.factorial (J + n - 1) : ℝ) := by exact_mod_cast hfact
    simpa [Nat.cast_mul, Nat.cast_prod] using this
  have hpos : 0 < (Nat.factorial (J - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (J - 1)
  have hdiv : (Nat.factorial (J + n - 1) : ℝ) / (Nat.factorial (J - 1) : ℝ) =
      ∏ i : Fin n, ((J + i.1 : ℕ) : ℝ) := by
    rw [← hfactR, mul_div_cancel_left₀ _ (ne_of_gt hpos)]
  rwa [hdiv]

/-- 存在 `N0 ≥ 1`，对一切 `n ≥ N0` 有 `2 / M_n ≤ (1 / Q_{J+n+1})^s`。 -/
lemma exists_level_threshold (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hJ : 2 ≤ J) {s : ℝ} (hs0 : 0 < s) (hs : s < 1 - β) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ n, N0 ≤ n →
      (2 : ℝ) / (wordCount β J n : ℝ) ≤ (1 / (Qsel (J + n + 1) : ℝ)) ^ s := by
  set ε := (1 - β) - s with hεdef
  have hε : 0 < ε := by linarith
  have hs1 : s < 1 := by linarith
  -- 直接用 DimHFinite.tendsto_powB_div_factorial_rpow：28^m / (m!)^ε → 0
  have hcore := DimHFinite.tendsto_powB_div_factorial_rpow (28 : ℝ) (by norm_num) ε hε
  set C0 : ℝ := 2 * (Nat.factorial (J - 1) : ℝ) ^ (1 - β) * (28 : ℝ) ^ (2 * s)
  have hC0 : 0 < C0 := by positivity
  have hlim : Tendsto (fun m : ℕ => C0 * ((28 : ℝ) ^ m / (Nat.factorial m : ℝ) ^ ε)) atTop (nhds 0) := by
    simpa using hcore.const_mul C0
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨M0, hM0⟩ := hlim 1 (by norm_num)
  refine ⟨max 1 M0, le_max_left _ _, fun n hn => ?_⟩
  set m := J + n - 1 with hmdef
  have hm_ge : M0 ≤ m := by omega
  have hm_eq : J + n + 1 = m + 2 := by omega
  have hQ_pos : 0 < (Qsel (J + n + 1) : ℝ) := by exact_mod_cast Qsel_pos (J + n + 1) (by omega)
  have hM_pos : 0 < (wordCount β J n : ℝ) := by exact_mod_cast wordCount_pos β J hβ1 (by omega) n
  -- Q_{m+2} ≤ 7^{m+2} (m+2)! ≤ 28^{m+2} m!
  have hQ_ub : (Qsel (J + n + 1) : ℝ) ≤ (28 : ℝ) ^ (m + 2) * (Nat.factorial m : ℝ) := by
    have h1 := Qsel_le_seven_pow_mul_fact (J + n + 1) (by omega)
    rw [hm_eq] at h1 ⊢
    have hfact2 : (Nat.factorial (m + 2) : ℝ) = ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) * (Nat.factorial m : ℝ) := by
      have : Nat.factorial (m + 2) = (m + 2) * (m + 1) * Nat.factorial m := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring
      exact_mod_cast this
    have h2m1 : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
      exact_mod_cast Nat.lt_two_pow_self.le
    have h2m2 : ((m + 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 2) := by
      exact_mod_cast Nat.lt_two_pow_self.le
    have hprod2 : ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (m + 2) := by
      calc ((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (m + 2) * (2 : ℝ) ^ (m + 1) := by gcongr
        _ ≤ (2 : ℝ) ^ (m + 2) * (2 : ℝ) ^ (m + 2) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
        _ = (4 : ℝ) ^ (m + 2) := by rw [← mul_pow]; norm_num
    calc (Qsel (m + 2) : ℝ)
        ≤ (7 : ℝ) ^ (m + 2) * (Nat.factorial (m + 2) : ℝ) := h1
      _ = (7 : ℝ) ^ (m + 2) * (((m + 2 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * (Nat.factorial m : ℝ) := by
          rw [hfact2]; ring
      _ ≤ (7 : ℝ) ^ (m + 2) * (4 : ℝ) ^ (m + 2) * (Nat.factorial m : ℝ) := by gcongr
      _ = (28 : ℝ) ^ (m + 2) * (Nat.factorial m : ℝ) := by rw [← mul_pow]; norm_num
  -- 化为等价不等式 2 * Q_{J+n+1}^s ≤ M_n
  rw [Real.div_rpow (by norm_num) (le_of_lt hQ_pos) s, Real.one_rpow,
    div_le_div_iff₀ hM_pos (Real.rpow_pos_of_pos hQ_pos s), one_mul]
  have hM_lb := wordCount_ge_fact_rpow β J hβ1 (by omega) n
  have hfact_pos : 0 < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hJfact_pos : 0 < (Nat.factorial (J - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (J - 1)
  have hQs : (Qsel (J + n + 1) : ℝ) ^ s ≤ ((28 : ℝ) ^ (m + 2)) ^ s * (Nat.factorial m : ℝ) ^ s := by
    calc (Qsel (J + n + 1) : ℝ) ^ s
        ≤ ((28 : ℝ) ^ (m + 2) * (Nat.factorial m : ℝ)) ^ s :=
          Real.rpow_le_rpow (le_of_lt hQ_pos) hQ_ub (le_of_lt hs0)
      _ = ((28 : ℝ) ^ (m + 2)) ^ s * (Nat.factorial m : ℝ) ^ s :=
          Real.mul_rpow (by positivity) (le_of_lt hfact_pos)
  have h28s : ((28 : ℝ) ^ (m + 2)) ^ s ≤ (28 : ℝ) ^ (2 * s) * (28 : ℝ) ^ m := by
    have hpow : ((28 : ℝ) ^ (m + 2)) ^ s = ((28 : ℝ) ^ m) ^ s * ((28 : ℝ) ^ 2) ^ s := by
      rw [pow_add, Real.mul_rpow (by positivity) (by positivity)]
    rw [hpow]
    have h1 : ((28 : ℝ) ^ m) ^ s ≤ (28 : ℝ) ^ m := by
      by_cases hsle : s ≤ 1
      · calc ((28 : ℝ) ^ m) ^ s ≤ ((28 : ℝ) ^ m) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hsle
          _ = (28 : ℝ) ^ m := Real.rpow_one _
      · exfalso
        -- s < 1 - β; we will pass hβ : 0 < β or note s ≤ 1? Wait: let's add (hβ0 : 0 ≤ β) to lemma!
        linarith
    have h2 : ((28 : ℝ) ^ (2 : ℕ)) ^ s = (28 : ℝ) ^ (2 * s) := by
      rw [← Real.rpow_natCast (28 : ℝ) 2, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h2]
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 28) (2 * s)]
  have hsmall := hM0 m hm_ge
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  have hratio : 2 * ((28 : ℝ) ^ (2 * s) * (28 : ℝ) ^ m) * (Nat.factorial m : ℝ) ^ s ≤
      ((Nat.factorial m : ℝ) / (Nat.factorial (J - 1) : ℝ)) ^ (1 - β) := by
    rw [Real.div_rpow (le_of_lt hfact_pos) (le_of_lt hJfact_pos) (1 - β),
      le_div_iff₀ (Real.rpow_pos_of_pos hJfact_pos (1 - β))]
    have hsplit : (Nat.factorial m : ℝ) ^ (1 - β) = (Nat.factorial m : ℝ) ^ s * (Nat.factorial m : ℝ) ^ ε := by
      rw [← Real.rpow_add hfact_pos]; congr 1; linarith
    rw [hsplit]
    have hsmall' : C0 * (28 : ℝ) ^ m ≤ (Nat.factorial m : ℝ) ^ ε := by
      have h1 : C0 * ((28 : ℝ) ^ m / (Nat.factorial m : ℝ) ^ ε) ≤ 1 := le_of_lt hsmall
      rw [← mul_div_assoc] at h1
      exact (div_le_one (Real.rpow_pos_of_pos hfact_pos ε)).mp h1
    calc 2 * ((28 : ℝ) ^ (2 * s) * (28 : ℝ) ^ m) * (Nat.factorial m : ℝ) ^ s *
            (Nat.factorial (J - 1) : ℝ) ^ (1 - β)
        = (C0 * (28 : ℝ) ^ m) * (Nat.factorial m : ℝ) ^ s := by simp only [C0]; ring
      _ ≤ (Nat.factorial m : ℝ) ^ ε * (Nat.factorial m : ℝ) ^ s := by
          gcongr
      _ = (Nat.factorial m : ℝ) ^ s * (Nat.factorial m : ℝ) ^ ε := mul_comm _ _
  calc 2 * (Qsel (J + n + 1) : ℝ) ^ s
      ≤ 2 * (((28 : ℝ) ^ (m + 2)) ^ s * (Nat.factorial m : ℝ) ^ s) := by gcongr
    _ ≤ 2 * (((28 : ℝ) ^ (2 * s) * (28 : ℝ) ^ m) * (Nat.factorial m : ℝ) ^ s) := by gcongr
    _ = 2 * ((28 : ℝ) ^ (2 * s) * (28 : ℝ) ^ m) * (Nat.factorial m : ℝ) ^ s := by ring
    _ ≤ ((Nat.factorial m : ℝ) / (Nat.factorial (J - 1) : ℝ)) ^ (1 - β) := hratio
    _ ≤ (wordCount β J n : ℝ) := hM_lb

/-- `Metric.thickening ρ A` 的直径上界。 -/
lemma ediam_thickening_le {A : Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Metric.ediam (Metric.thickening ρ A) ≤ Metric.ediam A + 2 * ENNReal.ofReal ρ := by
  rw [Metric.ediam_le_iff]
  intro x hx y hy
  obtain ⟨a, ha, hxa⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨b, hb, hyb⟩ := Metric.mem_thickening_iff.mp hy
  have h1 : edist x a ≤ ENNReal.ofReal ρ := by
    rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (le_of_lt hxa)
  have h2 : edist b y ≤ ENNReal.ofReal ρ := by
    rw [edist_comm, edist_dist]; exact ENNReal.ofReal_le_ofReal (le_of_lt hyb)
  have h3 : edist a b ≤ Metric.ediam A := Metric.edist_le_ediam_of_mem ha hb
  calc edist x y ≤ edist x a + edist a b + edist b y := edist_triangle4 x a b y
    _ ≤ ENNReal.ofReal ρ + Metric.ediam A + ENNReal.ofReal ρ := by gcongr
    _ = Metric.ediam A + 2 * ENNReal.ofReal ρ := by ring

/-- 非空集膨胀后的直径严格为正。 -/
lemma diam_thickening_pos {A : Set ℝ} (hA : A.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hbd : Bornology.IsBounded (Metric.thickening ρ A)) :
    0 < Metric.diam (Metric.thickening ρ A) := by
  obtain ⟨a, ha⟩ := hA
  have h1 : a ∈ Metric.thickening ρ A := Metric.mem_thickening_iff.mpr ⟨a, ha, by simp [hρ]⟩
  have h2 : a + ρ / 2 ∈ Metric.thickening ρ A := by
    refine Metric.mem_thickening_iff.mpr ⟨a, ha, ?_⟩
    rw [Real.dist_eq]
    have : a + ρ / 2 - a = ρ / 2 := by ring
    rw [this, abs_of_pos (by linarith)]
    linarith
  have hd := Metric.dist_le_diam_of_mem hbd h1 h2
  rw [Real.dist_eq] at hd
  have : a - (a + ρ / 2) = -(ρ / 2) := by ring
  rw [this, abs_neg, abs_of_pos (by linarith)] at hd
  linarith

/-- **核心下界**：对 `0 < s < 1 - β`（`0 < β < 1`），Cantor 集的 `s`-维 Hausdorff 测度 `≥ 1`（故非零）。 -/
lemma one_le_hausdorffMeasure_cantorSet (hβ : 0 < β) (hβ1 : β < 1) (hJ : 2 ≤ J)
    (hwJ : wWidth β J ≤ 1 / 8) {s : ℝ} (hs0 : 0 < s) (hs : s < 1 - β) :
    (1 : ℝ≥0∞) ≤ μH[s] (cantorSet α c β J) := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨N0, hN0_ge, hN0⟩ := exists_level_threshold β J (le_of_lt hβ) hβ1 hJ hs0 hs
  have hQN0_pos : 0 < (Qsel (J + N0) : ℝ) := by exact_mod_cast Qsel_pos (J + N0) (by omega)
  set r0R : ℝ := 1 / (2 * (Qsel (J + N0) : ℝ)) with hr0Rdef
  have hr0R_pos : 0 < r0R := by positivity
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R with hr0def
  have hr0_pos : 0 < r0 := ENNReal.ofReal_pos.mpr hr0R_pos
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : cantorSet α c β J ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) r0 hr0_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push_neg at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s with hSdef
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hlt le_top)
  have hSR_lt : S.toReal < 1 := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.one_ne_top).mpr hlt
    simpa using h1
  set δ0 : ℝ := (1 - S.toReal) / 2 with hδ0def
  have hδ0 : 0 < δ0 := by linarith
  -- 对每个 i 构造开膨胀 V i = thickening (ρ i) (t i)
  let ρ : ℕ → ℝ := fun i => min (r0R / 2) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
  have hρ_pos : ∀ i, 0 < ρ i := fun i => by
    apply lt_min (by positivity)
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    have hpos2 : 0 < (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := Real.rpow_pos_of_pos hpos1 (1 / s)
    linarith
  have h2ρ_le_r0 : ∀ i, 2 * ρ i ≤ r0R := fun i => by
    have := min_le_left (r0R / 2) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
    linarith
  have h2ρ_rpow : ∀ i, (2 * ρ i) ^ s ≤ δ0 / (2 : ℝ) ^ (i + 1) := fun i => by
    have h1 : 2 * ρ i ≤ (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := by
      have := min_le_right (r0R / 2) ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) / 2)
      linarith
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    calc (2 * ρ i) ^ s
        ≤ ((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) ^ s :=
          Real.rpow_le_rpow (by linarith [hρ_pos i]) h1 (le_of_lt hs0)
      _ = (δ0 / (2 : ℝ) ^ (i + 1)) ^ ((1 / s) * s) :=
          (Real.rpow_mul (le_of_lt hpos1) (1 / s) s).symm
      _ = δ0 / (2 : ℝ) ^ (i + 1) := by rw [one_div_mul_cancel (ne_of_gt hs0), Real.rpow_one]
  let V : ℕ → Set ℝ := fun i => Metric.thickening (ρ i) (t i)
  have hV_open : ∀ i, IsOpen (V i) := fun i => Metric.isOpen_thickening
  have hV_cov : cantorSet α c β J ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos i) (t i) hi
  -- 用紧致性取有限子覆盖 F
  obtain ⟨F, hFcov⟩ := (isCompact_cantorSet α c β J).elim_finite_subcover
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) (fun i => hV_open i.1) hV_cov
  -- 每个 i ∈ F 的 V i 有界、正直径且 diam (V i) ≤ 1 / Q_{J+N0}
  have hV_ediam_le : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal (1 / (Qsel (J + N0) : ℝ)) := fun i => by
    calc Metric.ediam (V i)
        ≤ Metric.ediam (t i) + 2 * ENNReal.ofReal (ρ i) :=
          ediam_thickening_le (le_of_lt (hρ_pos i))
      _ ≤ r0 + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]; gcongr; exact hdiam i
      _ ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := by
          gcongr; exact h2ρ_le_r0 i
      _ = ENNReal.ofReal (1 / (Qsel (J + N0) : ℝ)) := by
          rw [← ENNReal.ofReal_add (le_of_lt hr0R_pos) (le_of_lt hr0R_pos)]
          congr 1; simp only [r0R]; ring
  have hV_bd : ∀ i, Bornology.IsBounded (V i) := fun i =>
    Metric.isBounded_iff_ediam_ne_top.mpr (ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top))
  have hV_diam_le : ∀ i, Metric.diam (V i) ≤ 1 / (Qsel (J + N0) : ℝ) := fun i => by
    unfold Metric.diam
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hV_diam_pos : ∀ i : {i : ℕ // (t i).Nonempty}, 0 < Metric.diam (V i.1) := fun i =>
    diam_thickening_pos i.2 (hρ_pos i.1) (hV_bd i.1)
  -- 对每个 i ∈ F 选层级 n_i ≥ N0 使 1 / Q_{J + n_i + 1} < diam (V i) ≤ 1 / Q_{J + n_i}
  have hex_lvl : ∀ i : {i : ℕ // (t i).Nonempty},
      ∃ n : ℕ, N0 ≤ n ∧ 1 / (Qsel (J + n + 1) : ℝ) < Metric.diam (V i.1) ∧
        Metric.diam (V i.1) ≤ 1 / (Qsel (J + n) : ℝ) := by
    intro i
    set d := Metric.diam (V i.1)
    have hd_pos : 0 < d := hV_diam_pos i
    have hd_le : d ≤ 1 / (Qsel (J + N0) : ℝ) := hV_diam_le i.1
    have hex_m : ∃ m : ℕ, N0 ≤ m ∧ 1 / (Qsel (J + m) : ℝ) < d := by
      have hfact_top : Tendsto (fun m : ℕ => (Nat.factorial (J + m) : ℝ)) atTop atTop := by
        have h1 : Tendsto (fun m : ℕ => Nat.factorial (J + m)) atTop atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro b
          obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp factorial_tendsto_atTop b
          exact ⟨K, fun m hm => hK (J + m) (by omega)⟩
        exact tendsto_natCast_atTop_atTop.comp h1
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hfact_top.eventually_gt_atTop (1 / d))
      refine ⟨max N0 M, le_max_left _ _, ?_⟩
      have hQpos : 0 < (Qsel (J + max N0 M) : ℝ) := by exact_mod_cast Qsel_pos (J + max N0 M) (by omega)
      have hQge : (Nat.factorial (J + max N0 M) : ℝ) ≤ (Qsel (J + max N0 M) : ℝ) := by
        exact_mod_cast DimHCore.Qsel_ge_factorial (J + max N0 M) (by omega)
      have hgt : 1 / d < (Qsel (J + max N0 M) : ℝ) := lt_of_lt_of_le (hM (max N0 M) (le_max_right _ _)) hQge
      rw [div_lt_iff₀ hQpos]
      have := (div_lt_iff₀ hd_pos).mp hgt
      linarith
    classical
    let m0 := Nat.find hex_m
    have hm0 : N0 ≤ m0 ∧ 1 / (Qsel (J + m0) : ℝ) < d := Nat.find_spec hex_m
    have hm0_gt : N0 < m0 := by
      by_contra hle
      have heq : m0 = N0 := by omega
      rw [heq] at hm0
      linarith [hm0.2, hd_le]
    refine ⟨m0 - 1, by omega, ?_, ?_⟩
    · have heq : J + (m0 - 1) + 1 = J + m0 := by omega
      rw [heq]; exact hm0.2
    · by_contra hgt
      push_neg at hgt
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) ⟨by omega, hgt⟩
  choose lvl hlvl_ge hlvl_gt hlvl_le using hex_lvl
  -- 取最大层级 N
  set N : ℕ := F.sup (fun i => lvl i) with hNdef
  have hN_ge : ∀ i ∈ F, lvl i ≤ N := fun i hi => Finset.le_sup hi
  -- 证明 1 ≤ ∑_{i ∈ F} (2 / M_{lvl i})
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F, (2 : ℝ) / (wordCount β J (lvl i) : ℝ) := by
    classical
    have hMN_pos : 0 < (wordCount β J N : ℝ) := by exact_mod_cast wordCount_pos β J hβ1 (by omega) N
    -- 每个 w : CWord β J N 的区间都交 K，故交某个 V i (i ∈ F)
    have hcover_words : (Finset.univ : Finset (CWord β J N)) ⊆
        F.biUnion (fun i => Finset.univ.filter (fun w : CWord β J N =>
          (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)) := by
      intro w _
      obtain ⟨x, hxI, hxK⟩ := cInterv_inter_cantorSet_nonempty α c β J hβ hβ1 (by omega) N w
      obtain ⟨i, hiF, hxiV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
      exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxiV, hxI⟩⟩⟩
    -- 对每个 i ∈ F，与 V i 相交的第 N 层词数 * M_{lvl i} ≤ 2 * M_N
    have hcard_i : ∀ i ∈ F,
        ((Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card : ℝ) ≤
          (2 : ℝ) * (wordCount β J N : ℝ) / (wordCount β J (lvl i) : ℝ) := by
      intro i hiF
      have hleN : lvl i ≤ N := hN_ge i hiF
      set A_i := Finset.univ.filter (fun u : CWord β J (lvl i) =>
        (V i.1 ∩ cInterv α c β (J + lvl i) (centerInt α c β J (lvl i) u)).Nonempty)
      have hAi_le : A_i.card ≤ 2 := by
        apply card_le_two_of_abs_sub_le_one (centerInt α c β J (lvl i))
          (centerInt_injective α c β J hβ (by omega) hwJ (lvl i)) A_i
        intro u₁ hu₁ u₂ hu₂
        obtain ⟨x₁, hx₁⟩ := (Finset.mem_filter.mp hu₁).2
        obtain ⟨x₂, hx₂⟩ := (Finset.mem_filter.mp hu₂).2
        have hwl : wWidth β (J + lvl i) ≤ 1 / 8 :=
          le_trans (wWidth_antitone β hβ (by omega) (by omega)) hwJ
        exact intersect_cInterv_abs_sub_le_one α c β (J + lvl i) (by omega) hwl
          (hV_bd i.1) (hlvl_le i) hx₁ hx₂
      have hsub_fib : Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty) ⊆
          A_i.biUnion (fun u => Finset.univ.filter (fun w : CWord β J N =>
            prefixWord β J hleN w = u)) := by
        intro w hw
        obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hw).2
        have hxI' := cInterv_prefix_subset α c β J hβ (by omega) hleN w hxI
        refine Finset.mem_biUnion.mpr ⟨prefixWord β J hleN w, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hMli_pos : 0 < (wordCount β J (lvl i) : ℝ) := by
        exact_mod_cast wordCount_pos β J hβ1 (by omega) (lvl i)
      have hcard_mul : (Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card *
            wordCount β J (lvl i) ≤ 2 * wordCount β J N := by
        calc (Finset.univ.filter (fun w : CWord β J N =>
                (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card *
                wordCount β J (lvl i)
            ≤ (A_i.biUnion (fun u => Finset.univ.filter (fun w : CWord β J N =>
                prefixWord β J hleN w = u))).card * wordCount β J (lvl i) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub_fib)
          _ ≤ (∑ u ∈ A_i, (Finset.univ.filter (fun w : CWord β J N =>
                prefixWord β J hleN w = u)).card) * wordCount β J (lvl i) :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ u ∈ A_i, ((Finset.univ.filter (fun w : CWord β J N =>
                prefixWord β J hleN w = u)).card * wordCount β J (lvl i)) :=
              Finset.sum_mul _ _ _
          _ = ∑ _u ∈ A_i, wordCount β J N :=
              Finset.sum_congr rfl (fun u _ => card_prefix_fiber_mul β J (lvl i) N hleN u)
          _ = A_i.card * wordCount β J N := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * wordCount β J N := Nat.mul_le_mul_right _ hAi_le
      have hcard_mulR : ((Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card : ℝ) *
            (wordCount β J (lvl i) : ℝ) ≤ (2 : ℝ) * (wordCount β J N : ℝ) := by
        exact_mod_cast hcard_mul
      exact (le_div_iff₀ hMli_pos).mpr hcard_mulR
    have htotal : (wordCount β J N : ℝ) ≤
        ∑ i ∈ F, (2 : ℝ) * (wordCount β J N : ℝ) / (wordCount β J (lvl i) : ℝ) := by
      have h1 : (wordCount β J N : ℕ) ≤
          ∑ i ∈ F, (Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card := by
        rw [← card_CWord β J N, ← Finset.card_univ]
        exact le_trans (Finset.card_le_card hcover_words) Finset.card_biUnion_le
      have h1R : (wordCount β J N : ℝ) ≤
          ∑ i ∈ F, ((Finset.univ.filter (fun w : CWord β J N =>
            (V i.1 ∩ cInterv α c β (J + N) (centerInt α c β J N w)).Nonempty)).card : ℝ) := by
        exact_mod_cast h1
      exact le_trans h1R (Finset.sum_le_sum hcard_i)
    have hfactor : ∑ i ∈ F, (2 : ℝ) * (wordCount β J N : ℝ) / (wordCount β J (lvl i) : ℝ) =
        (wordCount β J N : ℝ) * ∑ i ∈ F, (2 : ℝ) / (wordCount β J (lvl i) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hfactor] at htotal
    exact le_of_mul_le_mul_left (by simpa using htotal) hMN_pos
  -- 另一方面 ∑_{i ∈ F} (diam V i)^s ≤ S.toReal + δ0 < 1
  have hsum_le_diam : ∑ i ∈ F, (2 : ℝ) / (wordCount β J (lvl i) : ℝ) ≤
      ∑ i ∈ F, Metric.diam (V i.1) ^ s := by
    apply Finset.sum_le_sum
    intro i _
    have h1 := hN0 (lvl i) (hlvl_ge i)
    have hQpos : 0 < (Qsel (J + lvl i + 1) : ℝ) := by exact_mod_cast Qsel_pos (J + lvl i + 1) (by omega)
    have h2 : (1 / (Qsel (J + lvl i + 1) : ℝ)) ^ s ≤ Metric.diam (V i.1) ^ s :=
      Real.rpow_le_rpow (by positivity) (le_of_lt (hlvl_gt i)) (le_of_lt hs0)
    exact le_trans h1 h2
  have hdiam_bound : ∀ i ∈ F, Metric.diam (V i.1) ^ s ≤
      (Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1) := by
    intro i _
    have ht_ne_top : Metric.ediam (t i.1) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (hdiam i.1) ENNReal.ofReal_lt_top)
    have hdiam_le_add : Metric.diam (V i.1) ≤ (Metric.ediam (t i.1)).toReal + 2 * ρ i.1 := by
      unfold Metric.diam
      have h1 : Metric.ediam (V i.1) ≤ Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i.1) := by
        have h2 : 2 * ENNReal.ofReal (ρ i.1) = ENNReal.ofReal (2 * ρ i.1) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
        rw [← h2]
        exact ediam_thickening_le (le_of_lt (hρ_pos i.1))
      have htop : Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i.1) ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨ht_ne_top, ENNReal.ofReal_ne_top⟩
      have htoR := ENNReal.toReal_mono htop h1
      rw [ENNReal.toReal_add ht_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith [hρ_pos i.1])] at htoR
      exact htoR
    have hpow_le : Metric.diam (V i.1) ^ s ≤
        (Metric.ediam (t i.1)).toReal ^ s + (2 * ρ i.1) ^ s := by
      calc Metric.diam (V i.1) ^ s
          ≤ ((Metric.ediam (t i.1)).toReal + 2 * ρ i.1) ^ s :=
            Real.rpow_le_rpow Metric.diam_nonneg hdiam_le_add (le_of_lt hs0)
        _ ≤ (Metric.ediam (t i.1)).toReal ^ s + (2 * ρ i.1) ^ s :=
            rpow_add_le_add_rpow ENNReal.toReal_nonneg (by linarith [hρ_pos i.1]) hs0 hs1
    have htoR_rpow : (Metric.ediam (t i.1)).toReal ^ s = (Metric.ediam (t i.1) ^ s).toReal :=
      ENNReal.toReal_rpow (Metric.ediam (t i.1)) s
    rw [htoR_rpow] at hpow_le
    linarith [h2ρ_rpow i.1]
  have hsum_t : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal ≤ S.toReal := by
    let G : Finset ℕ := F.image Subtype.val
    have hG_eq : ∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal =
        ∑ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s).toReal := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro i _
      simp [i.2]
    rw [hG_eq]
    have hleE : ∑ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) ≤ S :=
      ENNReal.sum_le_tsum G
    have hsum_ne_top : ∀ n ∈ G, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) ≠ ⊤ := by
      intro n hn
      have hle := le_trans (Finset.single_le_sum (fun _ _ => bot_le) hn) hleE
      exact ne_of_lt (lt_of_le_of_lt hle (lt_of_lt_of_le hlt le_top))
    rw [← ENNReal.toReal_sum hsum_ne_top]
    exact ENNReal.toReal_mono hS_ne_top hleE
  have hsum_geom : ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) ≤ δ0 := by
    let G : Finset ℕ := F.image Subtype.val
    have hG_eq : ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) = ∑ n ∈ G, δ0 * ((1 / 2 : ℝ) ^ (n + 1)) := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      apply Finset.sum_congr rfl
      intro i _
      rw [one_div, inv_pow, div_eq_mul_inv]
    rw [hG_eq, ← Finset.mul_sum]
    have hgeom : ∑ n ∈ G, ((1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
      have hsumm : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
        have h1 := summable_geometric_two
        have h2 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          funext n; rw [pow_succ']
        rw [h2]; exact h1.mul_left _
      have hle := hsumm.sum_le_tsum G (fun _ _ => by positivity)
      have htsum : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
        have h2 : (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
          funext n; rw [pow_succ']
        rw [h2, tsum_mul_left, tsum_geometric_two]; norm_num
      linarith
    nlinarith
  have htotal_lt : ∑ i ∈ F, Metric.diam (V i.1) ^ s < 1 := by
    calc ∑ i ∈ F, Metric.diam (V i.1) ^ s
        ≤ ∑ i ∈ F, ((Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1)) :=
          Finset.sum_le_sum hdiam_bound
      _ = (∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal) + ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) :=
          Finset.sum_add_distrib
      _ ≤ S.toReal + δ0 := add_le_add hsum_t hsum_geom
      _ < 1 := by linarith
  linarith

end CantorConstruction

/-! ## 6. 主定理：精确极限集与加权子水平集的精确 Hausdorff 维数 -/

/-- **OBL-3b 核心下界**：
    对 `0 < α < 1, c ≥ 0` 或 `α = 0, 0 ≤ c ≤ 1/2`，
    `dimH {x ∈ [0,1] | j^α ‖Q_j x‖ → c} ≥ 1 - α`。 -/
theorem dimH_exactLimitSetα_ge (α c : ℝ) (hα1 : α < 1)
    (hc : (0 < α ∧ 0 ≤ c) ∨ (α = 0 ∧ 0 ≤ c ∧ c ≤ 1 / 2)) :
    ENNReal.ofReal (1 - α) ≤ dimH (exactLimitSetα α c) := by
  have hα0 : 0 ≤ α := by rcases hc with ⟨h1, _⟩ | ⟨rfl, _, _⟩ <;> linarith
  -- 先证对一切 s ∈ (0, 1 - α) 有 ENNReal.ofReal s ≤ dimH (exactLimitSetα α c)
  have hfor_s : ∀ s : ℝ, 0 < s → s < 1 - α → ENNReal.ofReal s ≤ dimH (exactLimitSetα α c) := by
    intro s hs0 hs
    set ε := (1 - α - s) / 2 with hεdef
    have hε : 0 < ε := by linarith
    set β := α + ε with hβdef
    have hβ : 0 < β := by linarith
    have hβ1 : β < 1 := by linarith
    have hαβ : α < β := by linarith
    have hs_lt : s < 1 - β := by linarith
    -- 选 J ≥ 2 使 w_J ≤ 1/8 且对一切 j ≥ J 有 0 ≤ c j^{-α} ≤ 1/2
    have hw_lim : Tendsto (fun j : ℕ => wWidth β j) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => x ^ (-β)) atTop (nhds 0) := tendsto_rpow_neg_atTop hβ
      exact h1.comp tendsto_natCast_atTop_atTop
    obtain ⟨J1, hJ1⟩ := Filter.eventually_atTop.mp (hw_lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
    have htarget_ev : ∃ J2 : ℕ, ∀ j, J2 ≤ j → 0 ≤ c * (j : ℝ) ^ (-α) ∧ c * (j : ℝ) ^ (-α) ≤ 1 / 2 := by
      rcases hc with ⟨hαpos, hc0⟩ | ⟨rfl, hc0, hc12⟩
      · have hlim : Tendsto (fun j : ℕ => c * (j : ℝ) ^ (-α)) atTop (nhds 0) := by
          have h1 : Tendsto (fun x : ℝ => x ^ (-α)) atTop (nhds 0) := tendsto_rpow_neg_atTop hαpos
          simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul c
        obtain ⟨J2, hJ2⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
        refine ⟨max 1 J2, fun j hj => ?_⟩
        refine ⟨mul_nonneg hc0 (Real.rpow_nonneg (Nat.cast_nonneg j) (-α)), le_of_lt (hJ2 j (le_trans (le_max_right _ _) hj))⟩
      · refine ⟨1, fun j _ => ?_⟩
        simp only [neg_zero, Real.rpow_zero, mul_one]
        exact ⟨hc0, hc12⟩
    obtain ⟨J2, hJ2⟩ := htarget_ev
    set J := max 2 (max J1 J2) with hJdef
    have hJ2ge : 2 ≤ J := le_max_left _ _
    have hwJ : wWidth β J ≤ 1 / 8 := le_of_lt (hJ1 J (le_trans (le_max_left _ _) (le_max_right _ _)))
    have htargetJ : ∀ j, J ≤ j → 0 ≤ c * (j : ℝ) ^ (-α) ∧ c * (j : ℝ) ^ (-α) ≤ 1 / 2 :=
      fun j hj => hJ2 j (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj)
    have hmu := one_le_hausdorffMeasure_cantorSet α c β J hβ hβ1 hJ2ge hwJ hs0 hs_lt
    have hmu_ne : μH[s] (cantorSet α c β J) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hmu)
    set d : ℝ≥0 := ⟨s, le_of_lt hs0⟩
    have hdimK : (d : ℝ≥0∞) ≤ dimH (cantorSet α c β J) :=
      le_dimH_of_hausdorffMeasure_ne_zero hmu_ne
    have hd_eq : (d : ℝ≥0∞) = ENNReal.ofReal s := by
      simp only [d, ENNReal.ofReal]
      congr 1
      exact (Real.toNNReal_of_nonneg (le_of_lt hs0)).symm
    rw [hd_eq] at hdimK
    have hsub := cantorSet_subset_exactLimitSetα α c β J hα0 hβ hαβ (by omega) hwJ htargetJ
    exact le_trans hdimK (dimH_mono hsub)
  -- 令 s ↑ 1 - α
  by_contra hlt
  push_neg at hlt
  have hne_top : dimH (exactLimitSetα α c) ≠ ⊤ :=
    ne_of_lt (lt_of_lt_of_le hlt le_top)
  have hltR : (dimH (exactLimitSetα α c)).toReal < 1 - α := by
    have h1 := (ENNReal.toReal_lt_toReal hne_top ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal (by linarith)] at h1
  set s := max ((1 - α) / 2) (((dimH (exactLimitSetα α c)).toReal + (1 - α)) / 2)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs1 : s < 1 - α := max_lt (by linarith) (by linarith)
  have hs_gt : (dimH (exactLimitSetα α c)).toReal < s :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hle := hfor_s s hs0 hs1
  have hleR := ENNReal.toReal_mono hne_top hle
  rw [ENNReal.toReal_ofReal (le_of_lt hs0)] at hleR
  linarith

/-- **OBL-3b 定理 1（精确极限集维数等式，对应论文二 Theorem `\ref{conj:weight}`）**：
    对 `0 < α < 1, c ≥ 0` 或 `α = 0, 0 ≤ c ≤ 1/2`，
    `dimH {x ∈ [0,1] | j^α ‖Q_j x‖ → c} = 1 - α`。 -/
theorem dimH_exactLimitSetα_eq (α c : ℝ) (hα1 : α < 1)
    (hc : (0 < α ∧ 0 ≤ c) ∨ (α = 0 ∧ 0 ≤ c ∧ c ≤ 1 / 2)) :
    dimH (exactLimitSetα α c) = ENNReal.ofReal (1 - α) := by
  have hα0 : 0 ≤ α := by rcases hc with ⟨h1, _⟩ | ⟨rfl, _, _⟩ <;> linarith
  apply le_antisymm
  · exact le_trans (dimH_mono (exactLimitSetα_subset_levelSetα α c))
      (WeightedFinal.dimH_levelSetα_le α c hα0 (le_of_lt hα1))
  · exact dimH_exactLimitSetα_ge α c hα1 hc

/-- **OBL-3b 主定理 2（加权子水平集精确维数等式）**：
    对一切 `0 ≤ α < 1` 与 `c ≥ 0`（含 `c = 0`），
    `dimH {x ∈ ℝ | Λ_α(x) ≤ c} = 1 - α`。 -/
theorem dimH_levelSetα_eq (α c : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hc0 : 0 ≤ c) :
    dimH (levelSetα α (ENNReal.ofReal c)) = ENNReal.ofReal (1 - α) := by
  apply le_antisymm
  · exact WeightedFinal.dimH_levelSetα_le α c hα0 (le_of_lt hα1)
  · have hc_zero : (0 < α ∧ (0 : ℝ) ≤ 0) ∨ (α = 0 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2) := by
      rcases eq_or_lt_of_le hα0 with rfl | hpos
      · right; norm_num
      · left; exact ⟨hpos, le_refl 0⟩
    have hsub : exactLimitSetα α 0 ⊆ levelSetα α (ENNReal.ofReal c) := by
      intro x hx
      have h0 : apprExponentα α x ≤ ENNReal.ofReal 0 := exactLimitSetα_subset_levelSetα α 0 hx
      exact le_trans h0 (ENNReal.ofReal_le_ofReal hc0)
    exact le_trans (dimH_exactLimitSetα_ge α 0 hα1 hc_zero) (dimH_mono hsub)

/-- **OBL-3b 推论（加权零点集精确维数等式）**：
    对一切 `0 ≤ α < 1`，`dimH {x ∈ ℝ | Λ_α(x) = 0} = 1 - α`。 -/
theorem dimH_apprExponentα_eq_zero (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    dimH {x : ℝ | apprExponentα α x = 0} = ENNReal.ofReal (1 - α) := by
  have heq : {x : ℝ | apprExponentα α x = 0} = levelSetα α (ENNReal.ofReal 0) := by
    ext x
    simp only [Set.mem_setOf_eq, levelSetα, ENNReal.ofReal_zero, nonpos_iff_eq_zero]
  rw [heq]
  exact dimH_levelSetα_eq α 0 hα0 hα1 (le_refl 0)

end

end WeightedExactDim

#print axioms WeightedExactDim.dimH_exactLimitSetα_ge
#print axioms WeightedExactDim.dimH_exactLimitSetα_eq
#print axioms WeightedExactDim.dimH_levelSetα_eq
#print axioms WeightedExactDim.dimH_apprExponentα_eq_zero
