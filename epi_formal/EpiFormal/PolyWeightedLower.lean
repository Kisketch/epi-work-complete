import EpiFormal.PolyWeightedUpper

/-! The lower bound in the subcritical dimension theorem for polynomial
recurrences. The nested intervals use the construction in WeightedExactDim
with a real branching exponent below the degree of the recurrence. -/

open Real Filter Topology Set Finset MeasureTheory TrichotomyAndPolyExtension SpectralGap
open scoped ENNReal NNReal

namespace PolyWeightedLower
noncomputable section

/-- A power that is eventually bounded by the growth of the denominators. -/
structure LowerGrowth where
  P : PolyRecData
  γ : ℝ
  γpos : 0 < γ
  start : ℕ
  one_le_start : 1 ≤ start
  lower : ∀ j, start ≤ j → 4 * (j : ℝ) ^ γ * (P.Q j : ℝ) ≤ (P.Q (j + 1) : ℝ)

def polyExactLimit (P : PolyRecData) (α t : ℝ) : Set ℝ :=
  {x ∈ Set.Icc (0 : ℝ) 1 | Tendsto (P.polyWeightedSeq α x) atTop (nhds t)}

theorem exists_lower_growth (P : PolyRecData) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ : γ < (P.r : ℝ)) :
    ∃ D : LowerGrowth, D.P = P ∧ D.γ = γ := by
  have hzero : Tendsto (fun j : ℕ => (j : ℝ) ^ (γ - (P.r : ℝ))) atTop (nhds 0) := by
    have ht : Tendsto (fun x : ℝ => x ^ (-( (P.r : ℝ) - γ))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (sub_pos.mpr hγ)
    simpa only [neg_sub, Function.comp_def] using ht.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hzero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)))
  let J := max P.J₁ N
  have hJ : 1 ≤ J := (by have := P.two_le_J₁; omega : 1 ≤ P.J₁).trans (le_max_left _ _)
  refine ⟨⟨P, γ, hγ0, J, hJ, ?_⟩, rfl, rfl⟩
  intro j hj
  have hN' := hN j ((le_max_right _ _).trans hj)
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j from lt_of_lt_of_le (by decide) (hJ.trans hj))
  have hPj : P.J₁ ≤ j := (le_max_left _ _).trans hj
  have hsmall : 4 * (j : ℝ) ^ γ ≤ (1/2) * (j : ℝ) ^ P.r := by
    rw [Real.rpow_sub hjp, Real.rpow_natCast, div_lt_iff₀ (pow_pos hjp _)] at hN'
    linarith
  have hc : (1 : ℝ) ≤ P.c := by exact_mod_cast P.hc
  have hA := P.poly_A_ge_half_c hPj
  have hA' : 4 * (j : ℝ) ^ γ ≤ (P.A j : ℝ) := by
    apply hsmall.trans (le_trans _ hA)
    nlinarith [pow_nonneg hjp.le P.r]
  have hJ₀ := P.J₁_ge_J₀_succ
  have hQ : (0 : ℝ) < P.Q j := by exact_mod_cast P.hQ_pos j
  have hrec : (P.A j : ℝ) * (P.Q j : ℝ) < (P.Q (j+1) : ℝ) := by
    exact_mod_cast P.poly_Q_succ_gt_A_mul (show P.J₀ ≤ j by omega)
  exact (mul_le_mul_of_nonneg_right hA' hQ.le).trans hrec.le



/-! ## 2. 均匀嵌套 Cantor 树构造（固定 `α, c, s`） -/

section CantorConstruction

variable (D : LowerGrowth) (α c β : ℝ)

/-- 第 `j` 层偏移宽 `w_j = j^{-β}`。 -/
def wWidth (j : ℕ) : ℝ := (j : ℝ) ^ (-β)

/-- 第 `j` 层区间半径 `r_j = w_j / Q_j`。 -/
def cRad (j : ℕ) : ℝ := wWidth β j / (D.P.Q j : ℝ)

/-- 第 `j` 层钳位偏移 `θ_j = max(w_j, min(c j^{-α}, 1/2 - w_j))`。 -/
def cTheta (j : ℕ) : ℝ := max (wWidth β j) (min (c * (j : ℝ) ^ (-α)) (1 / 2 - wWidth β j))

/-- 第 `j` 层第 `k` 块区间中心 `(k + θ_j) / Q_j`。 -/
def cCenter (j : ℕ) (k : ℤ) : ℝ := ((k : ℝ) + cTheta α c β j) / (D.P.Q j : ℝ)

/-- 第 `j` 层第 `k` 块闭区间。 -/
def cInterv (j : ℕ) (k : ℤ) : Set ℝ :=
  Set.Icc (cCenter D α c β j k - cRad D β j) (cCenter D α c β j k + cRad D β j)

/-- 第 `j` 层均匀分支数 `b_j = ⌊6 j^{1-β}⌋₊`。 -/
def branchNum (j : ℕ) : ℕ := Nat.floor (6 * (j : ℝ) ^ (D.γ - β))

lemma wWidth_pos (j : ℕ) (hj : 1 ≤ j) : 0 < wWidth β j :=
  Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < j)) (-β)

lemma cRad_pos (j : ℕ) (hj : 1 ≤ j) : 0 < cRad D β j :=
  div_pos (wWidth_pos β j hj) (by exact_mod_cast D.P.hQ_pos j)

lemma wWidth_antitone (hβ : 0 < β) {j₁ j₂ : ℕ} (hj₁ : 1 ≤ j₁) (h : j₁ ≤ j₂) :
    wWidth β j₂ ≤ wWidth β j₁ := by
  unfold wWidth
  have hj1pos : (0 : ℝ) < (j₁ : ℝ) := by exact_mod_cast (by omega : 0 < j₁)
  have hle : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h
  exact Real.rpow_le_rpow_of_nonpos hj1pos hle (by linarith)

lemma cRad_succ_le_quarter (hβ : 0 < β) (j : ℕ) (hj : D.start ≤ j) :
    cRad D β (j + 1) ≤ (1 / 4) * cRad D β j := by
  have hj₁ := D.one_le_start.trans hj
  unfold cRad
  have hQj : 0 < (D.P.Q j : ℝ) := by exact_mod_cast D.P.hQ_pos j
  have hQj1 : 0 < (D.P.Q (j + 1) : ℝ) := by exact_mod_cast D.P.hQ_pos (j + 1)
  have hfour : 4 * (D.P.Q j : ℝ) ≤ (D.P.Q (j + 1) : ℝ) := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
    have hpow := Real.one_le_rpow hjR D.γpos.le
    have hg := D.lower j hj
    nlinarith
  have hw : wWidth β (j + 1) ≤ wWidth β j := wWidth_antitone β hβ hj₁ (by omega)
  have hw0 : 0 ≤ wWidth β (j + 1) := le_of_lt (wWidth_pos β (j + 1) (by omega))
  calc wWidth β (j + 1) / (D.P.Q (j + 1) : ℝ)
      ≤ wWidth β (j + 1) / (4 * (D.P.Q j : ℝ)) :=
        div_le_div_of_nonneg_left hw0 (by positivity) hfour
    _ ≤ wWidth β j / (4 * (D.P.Q j : ℝ)) :=
        div_le_div_of_nonneg_right hw (by positivity)
    _ = (1 / 4) * (wWidth β j / (D.P.Q j : ℝ)) := by ring

lemma branchNum_ge_five (hβ1 : β < D.γ) (j : ℕ) (hj : 1 ≤ j) :
    5 * (j : ℝ) ^ (D.γ - β) ≤ (branchNum D β j : ℝ) := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpow : (1 : ℝ) ≤ (j : ℝ) ^ (D.γ - β) := Real.one_le_rpow hj1 (by linarith)
  have hlt := Nat.lt_floor_add_one (6 * (j : ℝ) ^ (D.γ - β))
  change 6 * (j : ℝ) ^ (D.γ - β) < (branchNum D β j : ℝ) + 1 at hlt
  linarith

lemma branchNum_pos (hβ1 : β < D.γ) (j : ℕ) (hj : 1 ≤ j) : 0 < branchNum D β j := by
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpow : (1 : ℝ) ≤ (j : ℝ) ^ (D.γ - β) := Real.one_le_rpow hj1 (by linarith)
  have h5 := branchNum_ge_five D β hβ1 j hj
  have hpos : (0 : ℝ) < (branchNum D β j : ℝ) := by linarith
  exact_mod_cast hpos

/-- 嵌套子中心左端点。 -/
def childLeft (j : ℕ) (k : ℤ) : ℝ :=
  (D.P.Q (j + 1) : ℝ) * (cCenter D α c β j k - (cRad D β j - cRad D β (j + 1))) - cTheta α c β (j + 1)

/-- 嵌套子中心右端点。 -/
def childRight (j : ℕ) (k : ℤ) : ℝ :=
  (D.P.Q (j + 1) : ℝ) * (cCenter D α c β j k + (cRad D β j - cRad D β (j + 1))) - cTheta α c β (j + 1)

lemma childRight_sub_childLeft_ge (hβ : 0 < β) (j : ℕ) (hj : D.start ≤ j) (k : ℤ) :
    6 * (j : ℝ) ^ (D.γ - β) ≤ childRight D α c β j k - childLeft D α c β j k := by
  have hdiff : childRight D α c β j k - childLeft D α c β j k =
      2 * (cRad D β j - cRad D β (j + 1)) * (D.P.Q (j + 1) : ℝ) := by
    unfold childRight childLeft; ring
  rw [hdiff]
  have hr := cRad_succ_le_quarter D β hβ j hj
  have hQj : 0 < (D.P.Q j : ℝ) := by exact_mod_cast D.P.hQ_pos j
  have hQj1 : 0 < (D.P.Q (j + 1) : ℝ) := by exact_mod_cast D.P.hQ_pos (j + 1)
  have hfour := D.lower j hj
  have := D.one_le_start
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hrad_nn : 0 ≤ cRad D β j := le_of_lt (cRad_pos D β j (D.one_le_start.trans hj))
  have hstep1 : 2 * ((3 / 4) * cRad D β j) * (D.P.Q (j + 1) : ℝ) ≤
      2 * (cRad D β j - cRad D β (j + 1)) * (D.P.Q (j + 1) : ℝ) := by
    nlinarith
  have hstep2 : 2 * ((3 / 4) * cRad D β j) * (4 * (j : ℝ) ^ D.γ * (D.P.Q j : ℝ)) ≤
      2 * ((3 / 4) * cRad D β j) * (D.P.Q (j + 1) : ℝ) := by
    gcongr
  have hcalc : 2 * ((3 / 4) * cRad D β j) * (4 * (j : ℝ) ^ D.γ * (D.P.Q j : ℝ)) = 6 * (j : ℝ) ^ (D.γ - β) := by
    unfold cRad wWidth
    have hmul : (j : ℝ) ^ (-β) * (j : ℝ) ^ D.γ = (j : ℝ) ^ (D.γ - β) := by
      rw [← Real.rpow_add hjpos]
      congr 1
      ring
    have hQj_ne : (D.P.Q j : ℝ) ≠ 0 := ne_of_gt hQj
    field_simp
    nlinarith [hmul]
  linarith

/-- 第 `j` 层父节点 `k` 的第 `m` 个嵌套子节点整数索引。 -/
def childInt (j : ℕ) (k : ℤ) (m : ℕ) : ℤ :=
  Int.ceil (childLeft D α c β j k) + (m : ℤ)

lemma childInt_mem_bounds (hβ : 0 < β) (j : ℕ) (hj : D.start ≤ j) (k : ℤ) (m : ℕ)
    (hm : m < branchNum D β j) :
    childLeft D α c β j k ≤ (childInt D α c β j k m : ℝ) ∧
      (childInt D α c β j k m : ℝ) ≤ childRight D α c β j k := by
  set A := childLeft D α c β j k
  set B := childRight D α c β j k
  have hceil_le : A ≤ (Int.ceil A : ℝ) := Int.le_ceil A
  have hceil_lt : (Int.ceil A : ℝ) < A + 1 := Int.ceil_lt_add_one A
  have hwidth := childRight_sub_childLeft_ge D α c β hβ j hj k
  have hfloor_le : (branchNum D β j : ℝ) ≤ 6 * (j : ℝ) ^ (D.γ - β) :=
    Nat.floor_le (by positivity)
  have hm1 : (m : ℝ) + 1 ≤ (branchNum D β j : ℝ) := by
    have : m + 1 ≤ branchNum D β j := by omega
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
lemma cInterv_child_subset (hβ : 0 < β) (j : ℕ) (hj : D.start ≤ j) (k : ℤ) (m : ℕ)
    (hm : m < branchNum D β j) :
    cInterv D α c β (j + 1) (childInt D α c β j k m) ⊆ cInterv D α c β j k := by
  have hb := childInt_mem_bounds D α c β hβ j hj k m hm
  have hQj1 : 0 < (D.P.Q (j + 1) : ℝ) := by exact_mod_cast D.P.hQ_pos (j + 1)
  have hlo : cCenter D α c β j k - (cRad D β j - cRad D β (j + 1)) ≤
      cCenter D α c β (j + 1) (childInt D α c β j k m) := by
    change cCenter D α c β j k - (cRad D β j - cRad D β (j + 1)) ≤
      ((childInt D α c β j k m : ℝ) + cTheta α c β (j + 1)) / (D.P.Q (j + 1) : ℝ)
    rw [le_div_iff₀ hQj1]
    have h1 := hb.1
    unfold childLeft at h1
    linarith
  have hhi : cCenter D α c β (j + 1) (childInt D α c β j k m) ≤
      cCenter D α c β j k + (cRad D β j - cRad D β (j + 1)) := by
    change ((childInt D α c β j k m : ℝ) + cTheta α c β (j + 1)) / (D.P.Q (j + 1) : ℝ) ≤
      cCenter D α c β j k + (cRad D β j - cRad D β (j + 1))
    rw [div_le_iff₀ hQj1]
    have h2 := hb.2
    unfold childRight at h2
    linarith
  intro x hx
  simp only [cInterv, Set.mem_Icc] at hx ⊢
  constructor <;> linarith

/-- 同级区间不交（需 `w_j ≤ 1/8`）。 -/
lemma cInterv_disjoint (j : ℕ) (_hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    {k₁ k₂ : ℤ} (hne : k₁ ≠ k₂) :
    Disjoint (cInterv D α c β j k₁) (cInterv D α c β j k₂) := by
  rw [Set.disjoint_iff]
  intro x hx
  have h1 := hx.1
  have h2 := hx.2
  simp only [cInterv, Set.mem_Icc] at h1 h2
  have hQj : 0 < (D.P.Q j : ℝ) := by exact_mod_cast D.P.hQ_pos j
  have hdist : |cCenter D α c β j k₁ - cCenter D α c β j k₂| ≤ 2 * cRad D β j := by
    rw [abs_le]; constructor <;> linarith
  have hdiff : cCenter D α c β j k₁ - cCenter D α c β j k₂ = ((k₁ : ℝ) - (k₂ : ℝ)) / (D.P.Q j : ℝ) := by
    unfold cCenter; ring
  rw [hdiff, abs_div, abs_of_pos hQj] at hdist
  have h1le : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
    have : 1 ≤ |k₁ - k₂| := Int.one_le_abs (sub_ne_zero.mpr hne)
    exact_mod_cast this
  have hmul := (div_le_iff₀ hQj).mp hdist
  unfold cRad at hmul
  have hsimp : 2 * (wWidth β j / (D.P.Q j : ℝ)) * (D.P.Q j : ℝ) = 2 * wWidth β j := by
    field_simp
  rw [hsimp] at hmul
  linarith

/-- 若 `x ∈ cInterv j k` 且 `w_j ≤ 1/8`，则 `|distToNearestInt (Q_j x) - θ_j| ≤ w_j`。 -/
lemma distToNearestInt_cInterv_bound (j : ℕ) (_hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    (k : ℤ) {x : ℝ} (hx : x ∈ cInterv D α c β j k) :
    |distToNearestInt ((D.P.Q j : ℝ) * x) - cTheta α c β j| ≤ wWidth β j := by
  simp only [cInterv, Set.mem_Icc] at hx
  have hQj : 0 < (D.P.Q j : ℝ) := by exact_mod_cast D.P.hQ_pos j
  have hθ_lo : wWidth β j ≤ cTheta α c β j := le_max_left _ _
  have hθ_hi : cTheta α c β j ≤ 1 / 2 - wWidth β j :=
    max_le (by linarith) (min_le_right _ _)
  have hQx_lo : (k : ℝ) + cTheta α c β j - wWidth β j ≤ (D.P.Q j : ℝ) * x := by
    have h1 := mul_le_mul_of_nonneg_left hx.1 (le_of_lt hQj)
    have h2 : (D.P.Q j : ℝ) * (cCenter D α c β j k - cRad D β j) =
        (k : ℝ) + cTheta α c β j - wWidth β j := by
      unfold cCenter cRad; field_simp
    linarith
  have hQx_hi : (D.P.Q j : ℝ) * x ≤ (k : ℝ) + cTheta α c β j + wWidth β j := by
    have h1 := mul_le_mul_of_nonneg_left hx.2 (le_of_lt hQj)
    have h2 : (D.P.Q j : ℝ) * (cCenter D α c β j k + cRad D β j) =
        (k : ℝ) + cTheta α c β j + wWidth β j := by
      unfold cCenter cRad; field_simp
    linarith
  have hd := WeightedExactDim.distToNearestInt_eq_sub_of_mem_Icc k ((D.P.Q j : ℝ) * x)
    (by linarith) (by linarith)
  rw [hd, abs_le]
  constructor <;> linarith

/-- 钳位偏移与目标 `c j^{-α}` 的距离至多 `w_j`。 -/
lemma abs_cTheta_sub_le (j : ℕ) (_hw : wWidth β j ≤ 1 / 8)
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
lemma intersect_cInterv_abs_sub_le_one (j : ℕ) (_hj : 1 ≤ j) (hw : wWidth β j ≤ 1 / 8)
    {V : Set ℝ} (hbd : Bornology.IsBounded V) (hdiam : Metric.diam V ≤ 1 / (D.P.Q j : ℝ))
    {k₁ k₂ : ℤ} {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ V ∩ cInterv D α c β j k₁) (hx₂ : x₂ ∈ V ∩ cInterv D α c β j k₂) :
    |k₁ - k₂| ≤ 1 := by
  have hQj : 0 < (D.P.Q j : ℝ) := by exact_mod_cast D.P.hQ_pos j
  have h1 := hx₁.2
  have h2 := hx₂.2
  simp only [cInterv, Set.mem_Icc] at h1 h2
  have hdx : |x₁ - x₂| ≤ 1 / (D.P.Q j : ℝ) := by
    have := Metric.dist_le_diam_of_mem hbd hx₁.1 hx₂.1
    rw [Real.dist_eq] at this
    exact le_trans this hdiam
  have hdx' := abs_le.mp hdx
  have hcdiff : |cCenter D α c β j k₁ - cCenter D α c β j k₂| ≤ 2 * cRad D β j + 1 / (D.P.Q j : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hdiff : cCenter D α c β j k₁ - cCenter D α c β j k₂ = ((k₁ : ℝ) - (k₂ : ℝ)) / (D.P.Q j : ℝ) := by
    unfold cCenter; ring
  rw [hdiff, abs_div, abs_of_pos hQj] at hcdiff
  have hmul := (div_le_iff₀ hQj).mp hcdiff
  have hsimp : (2 * cRad D β j + 1 / (D.P.Q j : ℝ)) * (D.P.Q j : ℝ) = 2 * wWidth β j + 1 := by
    unfold cRad; field_simp
  rw [hsimp] at hmul
  have hlt2 : |(k₁ : ℝ) - (k₂ : ℝ)| < 2 := by linarith
  have hlt2Z : |k₁ - k₂| < 2 := by exact_mod_cast hlt2
  omega

/-! ## 3. Cantor 树词、投影与纤维计数 -/

variable (J : ℕ)

/-- 第 `n` 层词类型。 -/
abbrev CWord (n : ℕ) : Type := ∀ i : Fin n, Fin (branchNum D β (J + i.1))

/-- 第 `n` 层词总数 `M_n = ∏_{i=0}^{n-1} b_{J+i}`。 -/
def wordCount (n : ℕ) : ℕ := ∏ i : Fin n, branchNum D β (J + i.1)

lemma card_CWord (n : ℕ) : Fintype.card (CWord D β J n) = wordCount D β J n := by
  unfold CWord wordCount
  simp [Fintype.card_pi]

lemma wordCount_pos (hβ1 : β < D.γ) (hJ : 1 ≤ J) (n : ℕ) : 0 < wordCount D β J n := by
  unfold wordCount
  exact Finset.prod_pos (fun i _ => branchNum_pos D β hβ1 (J + i.1) (by omega))

lemma wordCount_succ (n : ℕ) :
    wordCount D β J (n + 1) = wordCount D β J n * branchNum D β (J + n) := by
  unfold wordCount
  rw [Fin.prod_univ_castSucc]
  rfl

/-- 第 `n` 层词对应的整数中心（根为 `0`）。 -/
def centerInt : ∀ n, CWord D β J n → ℤ
  | 0, _ => 0
  | n + 1, w => childInt D α c β (J + n) (centerInt n (fun i => w i.castSucc)) (w (Fin.last n)).1

/-- 前缀投影 `Word N → Word n`（`n ≤ N`）。 -/
def prefixWord {n N : ℕ} (h : n ≤ N) (w : CWord D β J N) : CWord D β J n :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

lemma prefixWord_self (n : ℕ) (w : CWord D β J n) : prefixWord D β J (le_refl n) w = w := by
  funext i; rfl

lemma prefixWord_succ {n N : ℕ} (h : n ≤ N) (w : CWord D β J (N + 1)) :
    prefixWord D β J (Nat.le_succ_of_le h) w = prefixWord D β J h (fun i => w i.castSucc) := by
  funext i; rfl

/-- 子区间嵌套到祖先区间。 -/
lemma cInterv_prefix_subset (hβ : 0 < β) (hJ : D.start ≤ J) {n N : ℕ} (h : n ≤ N) (w : CWord D β J N) :
    cInterv D α c β (J + N) (centerInt D α c β J N w) ⊆
      cInterv D α c β (J + n) (centerInt D α c β J n (prefixWord D β J h w)) := by
  induction N, h using Nat.le_induction with
  | base =>
      rw [prefixWord_self]
  | succ N h ih =>
      have hstep : cInterv D α c β (J + (N + 1)) (centerInt D α c β J (N + 1) w) ⊆
          cInterv D α c β (J + N) (centerInt D α c β J N (fun i => w i.castSucc)) := by
        have heq : J + (N + 1) = (J + N) + 1 := by omega
        rw [heq]
        exact cInterv_child_subset D α c β hβ (J + N) (by omega)
          (centerInt D α c β J N (fun i => w i.castSucc)) (w (Fin.last N)).1 (w (Fin.last N)).2
      rw [prefixWord_succ D β J h w]
      exact Set.Subset.trans hstep (ih (fun i => w i.castSucc))

/-- `centerInt n` 单射（需对一切 `m ≥ J` 有 `w_m ≤ 1/8`）。 -/
lemma centerInt_injective (hβ : 0 < β) (hJ : D.start ≤ J)
    (hwJ : wWidth β J ≤ 1 / 8) (n : ℕ) :
    Function.Injective (centerInt D α c β J n) := by
  induction n with
  | zero =>
      intro w₁ w₂ _
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro w₁ w₂ heq
      set p₁ : CWord D β J n := fun i => w₁ i.castSucc
      set p₂ : CWord D β J n := fun i => w₂ i.castSucc
      have hp : p₁ = p₂ := by
        by_contra hne
        have hkne : centerInt D α c β J n p₁ ≠ centerInt D α c β J n p₂ :=
          fun hc => hne (ih hc)
        have hwn : wWidth β (J + n) ≤ 1 / 8 :=
          le_trans (wWidth_antitone β hβ (D.one_le_start.trans hJ) (by omega)) hwJ
        have hdisj := cInterv_disjoint D α c β (J + n) (by have := D.one_le_start; omega) hwn hkne
        have hsub1 : cInterv D α c β (J + (n + 1)) (centerInt D α c β J (n + 1) w₁) ⊆
            cInterv D α c β (J + n) (centerInt D α c β J n p₁) := by
          have heq1 : J + (n + 1) = (J + n) + 1 := by omega
          rw [heq1]
          exact cInterv_child_subset D α c β hβ (J + n) (by omega) _ _ (w₁ (Fin.last n)).2
        have hsub2 : cInterv D α c β (J + (n + 1)) (centerInt D α c β J (n + 1) w₂) ⊆
            cInterv D α c β (J + n) (centerInt D α c β J n p₂) := by
          have heq1 : J + (n + 1) = (J + n) + 1 := by omega
          rw [heq1]
          exact cInterv_child_subset D α c β hβ (J + n) (by omega) _ _ (w₂ (Fin.last n)).2
        rw [heq] at hsub1
        have hmem : cCenter D α c β (J + (n + 1)) (centerInt D α c β J (n + 1) w₂) ∈
            cInterv D α c β (J + (n + 1)) (centerInt D α c β J (n + 1) w₂) := by
          have hr := le_of_lt (cRad_pos D β (J + (n + 1)) (by omega))
          simp only [cInterv, Set.mem_Icc]
          constructor <;> linarith
        exact Set.disjoint_left.mp hdisj (hsub1 hmem) (hsub2 hmem)
      have hlast : w₁ (Fin.last n) = w₂ (Fin.last n) := by
        have hci : childInt D α c β (J + n) (centerInt D α c β J n p₁) (w₁ (Fin.last n)).1 =
            childInt D α c β (J + n) (centerInt D α c β J n p₁) (w₂ (Fin.last n)).1 := by
          have := heq
          simp only [centerInt] at this
          change childInt D α c β (J + n) (centerInt D α c β J n p₁) (w₁ (Fin.last n)).1 =
            childInt D α c β (J + n) (centerInt D α c β J n p₂) (w₂ (Fin.last n)).1 at this
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
lemma card_prefix_fiber_mul (n N : ℕ) (h : n ≤ N) (u : CWord D β J n) :
    (Finset.univ.filter (fun w : CWord D β J N => prefixWord D β J h w = u)).card * wordCount D β J n =
      wordCount D β J N :=
  card_prefix_fiber_mul_aux (fun k => branchNum D β (J + k)) n N h u

/-! ## 4. Cantor 集 `K` 的紧致性、非空交与包含于精确极限集 -/

/-- 第 `n` 层紧致集 `K_n`。 -/
def cantorLevel (n : ℕ) : Set ℝ :=
  ⋃ w : CWord D β J n, cInterv D α c β (J + n) (centerInt D α c β J n w)

/-- Cantor 集 `K = ⋂_n K_n`。 -/
def cantorSet : Set ℝ :=
  ⋂ n : ℕ, cantorLevel D α c β J n

lemma isCompact_cantorLevel (n : ℕ) : IsCompact (cantorLevel D α c β J n) :=
  isCompact_iUnion (fun _ => isCompact_Icc)

lemma isCompact_cantorSet : IsCompact (cantorSet D α c β J) := by
  apply IsCompact.of_isClosed_subset (isCompact_cantorLevel D α c β J 0)
  · exact isClosed_iInter (fun n => (isCompact_cantorLevel D α c β J n).isClosed)
  · exact Set.iInter_subset _ 0

/-- 给定第 `n` 层词 `u`，向右不断补 `0` 得到无穷分支。 -/
def extendZero (hβ1 : β < D.γ) (hJ : 1 ≤ J) {n : ℕ} (u : CWord D β J n) (m : ℕ) : CWord D β J (n + m) :=
  fun i =>
    if h : i.1 < n then u ⟨i.1, h⟩
    else ⟨0, branchNum_pos D β hβ1 (J + i.1) (by omega)⟩

/-- 每个第 `n` 层区间都与 Cantor 集 `K` 非空相交。 -/
lemma cInterv_inter_cantorSet_nonempty (hβ : 0 < β) (hβ1 : β < D.γ) (hJ : D.start ≤ J)
    (n : ℕ) (u : CWord D β J n) :
    (cInterv D α c β (J + n) (centerInt D α c β J n u) ∩ cantorSet D α c β J).Nonempty := by
  let F : ℕ → Set ℝ := fun m => cInterv D α c β (J + (n + m)) (centerInt D α c β J (n + m) (extendZero D β J hβ1 (D.one_le_start.trans hJ) u m))
  have hanti : ∀ m, F (m + 1) ⊆ F m := by
    intro m
    change cInterv D α c β (J + (n + (m + 1))) _ ⊆ cInterv D α c β (J + (n + m)) _
    have hsub := cInterv_prefix_subset D α c β J hβ hJ (show n + m ≤ n + (m + 1) by omega)
      (extendZero D β J hβ1 (D.one_le_start.trans hJ) u (m + 1))
    have hpre : prefixWord D β J (show n + m ≤ n + (m + 1) by omega) (extendZero D β J hβ1 (D.one_le_start.trans hJ) u (m + 1)) =
        extendZero D β J hβ1 (D.one_le_start.trans hJ) u m := by
      funext i
      simp only [prefixWord, extendZero]
    rwa [hpre] at hsub
  have hne : ∀ m, (F m).Nonempty := fun m => by
    refine ⟨cCenter D α c β (J + (n + m)) (centerInt D α c β J (n + m) (extendZero D β J hβ1 (D.one_le_start.trans hJ) u m)), ?_⟩
    have hr := le_of_lt (cRad_pos D β (J + (n + m)) (by have := D.one_le_start; omega))
    simp only [F, cInterv, Set.mem_Icc]
    constructor <;> linarith
  have hcomp : ∀ m, IsCompact (F m) := fun _ => isCompact_Icc
  have hclosed : ∀ m, IsClosed (F m) := fun _ => isClosed_Icc
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hanti hne (hcomp 0) hclosed
  have hpre0 : extendZero D β J hβ1 (D.one_le_start.trans hJ) u 0 = u := by
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
      have hxu : x ∈ cInterv D α c β (J + n) (centerInt D α c β J n u) := by
        simpa [F, hpre0] using hx0
      have hsub := cInterv_prefix_subset D α c β J hβ hJ hkn u
      exact Set.mem_iUnion.mpr ⟨prefixWord D β J hkn u, hsub hxu⟩
    · have hxk : x ∈ F (k - n) := Set.mem_iInter.mp hx (k - n)
      generalize hm : k - n = m at hxk
      have heq : n + m = k := by omega
      subst heq
      exact Set.mem_iUnion.mpr ⟨extendZero D β J hβ1 (D.one_le_start.trans hJ) u m, hxk⟩

/-- Cantor 集包含于精确极限集 `polyExactLimit D.P α c`。 -/
lemma cantorSet_subset_exactLimitSetα (_hα0 : 0 ≤ α) (hβ : 0 < β) (hαβ : α < β)
    (hJ : 1 ≤ J) (hwJ : wWidth β J ≤ 1 / 8)
    (htarget : ∀ j, J ≤ j → 0 ≤ c * (j : ℝ) ^ (-α) ∧ c * (j : ℝ) ^ (-α) ≤ 1 / 2) :
    cantorSet D α c β J ⊆ polyExactLimit D.P α c := by
  intro x hx
  have hx0 : x ∈ cantorLevel D α c β J 0 := Set.mem_iInter.mp hx 0
  obtain ⟨w0, hw0⟩ := Set.mem_iUnion.mp hx0
  have hc0 : centerInt D α c β J 0 w0 = 0 := rfl
  rw [hc0] at hw0
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [cInterv, Set.mem_Icc] at hw0 ⊢
    have hQj : 0 < (D.P.Q J : ℝ) := by exact_mod_cast D.P.hQ_pos J
    have hQj1 : (1 : ℝ) ≤ (D.P.Q J : ℝ) := by exact_mod_cast (show 1 ≤ D.P.Q J by have := D.P.hQ_pos J; omega)
    have hθ_lo : wWidth β J ≤ cTheta α c β J := le_max_left _ _
    have hθ_hi : cTheta α c β J ≤ 1 / 2 - wWidth β J := max_le (by linarith) (min_le_right _ _)
    have hleft : 0 ≤ cCenter D α c β J 0 - cRad D β J := by
      have heq : cCenter D α c β J 0 - cRad D β J = ((0 : ℤ) + cTheta α c β J - wWidth β J) / (D.P.Q J : ℝ) := by
        unfold cCenter cRad; ring
      rw [heq]
      exact div_nonneg (by push_cast; linarith) (le_of_lt hQj)
    have hright : cCenter D α c β J 0 + cRad D β J ≤ 1 := by
      have heq : cCenter D α c β J 0 + cRad D β J = ((0 : ℤ) + cTheta α c β J + wWidth β J) / (D.P.Q J : ℝ) := by
        unfold cCenter cRad; ring
      rw [heq, div_le_one hQj]
      push_cast; linarith
    rw [Nat.add_zero] at hw0
    exact ⟨le_trans hleft hw0.1, le_trans hw0.2 hright⟩
  refine ⟨hxIcc, ?_⟩
  -- 证明 D.P.polyWeightedSeq α x j → c
  have hbound : ∀ j, J ≤ j → |D.P.polyWeightedSeq α x j - c| ≤ 2 * (j : ℝ) ^ (-(β - α)) := by
    intro j hj
    have hxj : x ∈ cantorLevel D α c β J (j - J) := Set.mem_iInter.mp hx (j - J)
    have hjeq : J + (j - J) = j := by omega
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hxj
    rw [hjeq] at hw
    have hwj : wWidth β j ≤ 1 / 8 := le_trans (wWidth_antitone β hβ hJ hj) hwJ
    have hdist1 := distToNearestInt_cInterv_bound D α c β j (by omega) hwj _ hw
    have hdist2 := abs_cTheta_sub_le α c β j hwj (htarget j hj).1 (htarget j hj).2
    have hdist : |distToNearestInt ((D.P.Q j : ℝ) * x) - c * (j : ℝ) ^ (-α)| ≤ 2 * wWidth β j := by
      calc |distToNearestInt ((D.P.Q j : ℝ) * x) - c * (j : ℝ) ^ (-α)|
          ≤ |distToNearestInt ((D.P.Q j : ℝ) * x) - cTheta α c β j| +
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
    have heq : D.P.polyWeightedSeq α x j - c = (j : ℝ) ^ α * (distToNearestInt ((D.P.Q j : ℝ) * x) - c * (j : ℝ) ^ (-α)) := by
      unfold PolyRecData.polyWeightedSeq; rw [mul_sub, hmul]
    rw [heq, abs_mul, abs_of_pos hjαpos]
    calc (j : ℝ) ^ α * |distToNearestInt ((D.P.Q j : ℝ) * x) - c * (j : ℝ) ^ (-α)|
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

/-- `M_n ≥ ((J+n-1)! / (J-1)!)^{1-β}`（`J ≥ 1`, `β < D.γ`）。 -/
lemma wordCount_ge_fact_rpow (hβ1 : β < D.γ) (hJ : 1 ≤ J) (n : ℕ) :
    ((Nat.factorial (J + n - 1) : ℝ) / (Nat.factorial (J - 1) : ℝ)) ^ (D.γ - β) ≤
      (wordCount D β J n : ℝ) := by
  have hprod : (∏ i : Fin n, ((J + i.1 : ℕ) : ℝ)) ^ (D.γ - β) ≤ (wordCount D β J n : ℝ) := by
    unfold wordCount
    rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _)]
    gcongr with i _
    have h5 := branchNum_ge_five D β hβ1 (J + i.1) (by omega)
    have hpow : (0 : ℝ) ≤ ((J + i.1 : ℕ) : ℝ) ^ (D.γ - β) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hfact := WeightedExactDim.fact_mul_prod_add J hJ n
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


/-- Uniform mass at level n is bounded by the next mesh to the power s. -/
lemma exists_level_threshold (hJ : 1 ≤ J) {s : ℝ} (hs0 : 0 < s)
    (hs : s * (D.P.r : ℝ) < D.γ - β) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ n, N0 ≤ n →
      (2 : ℝ) / (wordCount D β J n : ℝ) ≤ (1 / (D.P.Q (J + n + 1) : ℝ)) ^ s := by
  have hr : (0 : ℝ) < D.P.r := by exact_mod_cast (show 0 < D.P.r from D.P.hr)
  have hβγ : β < D.γ := by nlinarith [mul_pos hs0 hr]
  obtain ⟨C,K,hC,hK,hQ⟩ := PolyGaugeAndPhaseTransition.poly_Q_le_factorial D.P
  let L : ℝ := K * (4 : ℝ) ^ D.P.r
  have hL : 0 < L := mul_pos (zero_lt_one.trans hK) (by positivity)
  let B : ℝ := L ^ s
  have hB : 0 < B := Real.rpow_pos_of_pos hL _
  let e : ℝ := D.γ - β - s * (D.P.r : ℝ)
  have he : 0 < e := sub_pos.mpr hs
  let F : ℝ := (Nat.factorial (J-1) : ℝ)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos (J-1)
  let C₀ : ℝ := 2 * C^s * B^2 * F^(D.γ-β)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hlim := (DimHFinite.tendsto_powB_div_factorial_rpow B hB.le e he).const_mul C₀
  simp only [mul_zero] at hlim
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨M,hM⟩ := hlim 1 (by norm_num)
  refine ⟨max 1 M, le_max_left _ _, fun n hn => ?_⟩
  let m := J+n-1
  have hm : J+n+1 = m+2 := by dsimp [m]; omega
  have hmM : M ≤ m := by have := le_max_right 1 M; dsimp [m]; omega
  have hU : (0:ℝ) < Nat.factorial m := by exact_mod_cast Nat.factorial_pos m
  have hfact : (Nat.factorial (m+2) : ℝ) ≤ (4:ℝ)^(m+2) * (Nat.factorial m : ℝ) := by
    have h1 : ((m+1 : ℕ) : ℝ) ≤ (2:ℝ)^(m+1) := by exact_mod_cast Nat.lt_two_pow_self.le
    have h2 : ((m+2 : ℕ) : ℝ) ≤ (2:ℝ)^(m+2) := by exact_mod_cast Nat.lt_two_pow_self.le
    have h3 : (2:ℝ)^(m+1) ≤ (2:ℝ)^(m+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have heq : (Nat.factorial (m+2) : ℝ) = ((m+2:ℕ):ℝ) * ((m+1:ℕ):ℝ) * (Nat.factorial m : ℝ) := by
      simp only [Nat.factorial_succ, Nat.cast_mul]
      ring
    rw [heq, show (4:ℝ) = 2*2 by norm_num, mul_pow]
    gcongr
    exact h1.trans h3
  have hQu : (D.P.Q (m+2) : ℝ) ≤ C * L^(m+2) * (Nat.factorial m : ℝ)^D.P.r := calc
    _ ≤ C * K^(m+2) * (Nat.factorial (m+2) : ℝ)^D.P.r := hQ _
    _ ≤ C * K^(m+2) * ((4:ℝ)^(m+2) * (Nat.factorial m : ℝ))^D.P.r := by
      gcongr
    _ = _ := by dsimp [L]; rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm D.P.r]; ring
  have hQp : (0:ℝ) < D.P.Q (m+2) := by exact_mod_cast D.P.hQ_pos _
  have hp : (D.P.Q (m+2) : ℝ)^s ≤ C^s * (B^m * B^2) * (Nat.factorial m : ℝ)^(s*(D.P.r : ℝ)) := by
    calc
      _ ≤ (C * L^(m+2) * (Nat.factorial m : ℝ)^D.P.r)^s :=
        Real.rpow_le_rpow hQp.le hQu hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC.le (by positivity)]
        have hl : (L^(m+2))^s = B^(m+2) := by
          rw [← Real.rpow_natCast L, ← Real.rpow_mul hL.le, mul_comm, Real.rpow_mul hL.le,
            Real.rpow_natCast]
        rw [hl, pow_add, ← Real.rpow_natCast (Nat.factorial m : ℝ),
          ← Real.rpow_mul hU.le, mul_comm (D.P.r : ℝ) s]
  have hsmall := hM m hmM
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  have hbound : C₀ * B^m ≤ (Nat.factorial m : ℝ)^e := by
    rw [← mul_div_assoc] at hsmall
    exact (div_le_one (Real.rpow_pos_of_pos hU _)).mp hsmall.le
  have hmass := wordCount_ge_fact_rpow D β J hβγ hJ n
  have hW : (0:ℝ) < wordCount D β J n := by exact_mod_cast wordCount_pos D β J hβγ hJ n
  rw [hm, Real.div_rpow zero_le_one hQp.le, Real.one_rpow,
    div_le_div_iff₀ hW (Real.rpow_pos_of_pos hQp _), one_mul]
  apply le_trans _ hmass
  change 2 * (D.P.Q (m+2) : ℝ)^s ≤ ((Nat.factorial m : ℝ) / F)^(D.γ-β)
  rw [Real.div_rpow hU.le hF.le, le_div_iff₀ (Real.rpow_pos_of_pos hF _)]
  calc
    _ ≤ 2 * (C^s * (B^m * B^2) * (Nat.factorial m : ℝ)^(s*(D.P.r : ℝ))) * F^(D.γ-β) := by gcongr
    _ = (C₀ * B^m) * (Nat.factorial m : ℝ)^(s*(D.P.r : ℝ)) := by dsimp [C₀]; ring
    _ ≤ (Nat.factorial m : ℝ)^e * (Nat.factorial m : ℝ)^(s*(D.P.r : ℝ)) := by gcongr
    _ = _ := by rw [← Real.rpow_add hU]; congr 1; dsimp [e]; ring


/-- **核心下界**：对 `0 < s ≤ 1` 且 `s * r < γ - β`，Cantor 集的 `s`-维 Hausdorff 测度 `≥ 1`（故非零）。 -/
lemma one_le_hausdorffMeasure_cantorSet (hβ : 0 < β) (hβ1 : β < D.γ) (hJ : D.start ≤ J)
    (hwJ : wWidth β J ≤ 1 / 8) {s : ℝ} (hs0 : 0 < s)
    (hs_le_one : s ≤ 1) (hs : s * (D.P.r : ℝ) < D.γ - β) :
    (1 : ℝ≥0∞) ≤ μH[s] (cantorSet D α c β J) := by
  have hs1 := hs_le_one
  have hJ1 := D.one_le_start.trans hJ
  obtain ⟨N0, hN0_ge, hN0⟩ := exists_level_threshold D β J hJ1 hs0 hs
  have hQN0_pos : 0 < (D.P.Q (J + N0) : ℝ) := by exact_mod_cast D.P.hQ_pos (J + N0)
  set r0R : ℝ := 1 / (2 * (D.P.Q (J + N0) : ℝ)) with hr0Rdef
  have hr0R_pos : 0 < r0R := by positivity
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R with hr0def
  have hr0_pos : 0 < r0 := ENNReal.ofReal_pos.mpr hr0R_pos
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : cantorSet D α c β J ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) r0 hr0_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push Not at hlt
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
  have hV_cov : cantorSet D α c β J ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos i) (t i) hi
  -- 用紧致性取有限子覆盖 F
  obtain ⟨F, hFcov⟩ := (isCompact_cantorSet D α c β J).elim_finite_subcover
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) (fun i => hV_open i.1) hV_cov
  -- 每个 i ∈ F 的 V i 有界、正直径且 diam (V i) ≤ 1 / Q_{J+N0}
  have hV_ediam_le : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal (1 / (D.P.Q (J + N0) : ℝ)) := fun i => by
    calc Metric.ediam (V i)
        ≤ Metric.ediam (t i) + 2 * ENNReal.ofReal (ρ i) :=
          WeightedExactDim.ediam_thickening_le (le_of_lt (hρ_pos i))
      _ ≤ r0 + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]; gcongr; exact hdiam i
      _ ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := by
          gcongr; exact h2ρ_le_r0 i
      _ = ENNReal.ofReal (1 / (D.P.Q (J + N0) : ℝ)) := by
          rw [← ENNReal.ofReal_add (le_of_lt hr0R_pos) (le_of_lt hr0R_pos)]
          congr 1; simp only [r0R]; ring
  have hV_bd : ∀ i, Bornology.IsBounded (V i) := fun i =>
    Metric.isBounded_iff_ediam_ne_top.mpr (ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top))
  have hV_diam_le : ∀ i, Metric.diam (V i) ≤ 1 / (D.P.Q (J + N0) : ℝ) := fun i => by
    unfold Metric.diam
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hV_diam_pos : ∀ i : {i : ℕ // (t i).Nonempty}, 0 < Metric.diam (V i.1) := fun i =>
    WeightedExactDim.diam_thickening_pos i.2 (hρ_pos i.1) (hV_bd i.1)
  -- 对每个 i ∈ F 选层级 n_i ≥ N0 使 1 / Q_{J + n_i + 1} < diam (V i) ≤ 1 / Q_{J + n_i}
  have hex_lvl : ∀ i : {i : ℕ // (t i).Nonempty},
      ∃ n : ℕ, N0 ≤ n ∧ 1 / (D.P.Q (J + n + 1) : ℝ) < Metric.diam (V i.1) ∧
        Metric.diam (V i.1) ≤ 1 / (D.P.Q (J + n) : ℝ) := by
    intro i
    set d := Metric.diam (V i.1)
    have hd_pos : 0 < d := hV_diam_pos i
    have hd_le : d ≤ 1 / (D.P.Q (J + N0) : ℝ) := hV_diam_le i.1
    have hex_m : ∃ m : ℕ, N0 ≤ m ∧ 1 / (D.P.Q (J + m) : ℝ) < d := by
      have hshift : Tendsto (fun m : ℕ => J + m) atTop atTop :=
        (tendsto_add_atTop_nat J).congr (fun m => Nat.add_comm m J)
      have htop := D.P.poly_Q_tendsto_atTop.comp hshift
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (htop.eventually_gt_atTop (1 / d))
      refine ⟨max N0 M, le_max_left _ _, ?_⟩
      have hQpos : 0 < (D.P.Q (J + max N0 M) : ℝ) := by exact_mod_cast D.P.hQ_pos _
      have hgt : 1 / d < (D.P.Q (J + max N0 M) : ℝ) := hM _ (le_max_right _ _)
      rw [div_lt_iff₀ hQpos]
      have := (div_lt_iff₀ hd_pos).mp hgt
      linarith
    classical
    let m0 := Nat.find hex_m
    have hm0 : N0 ≤ m0 ∧ 1 / (D.P.Q (J + m0) : ℝ) < d := Nat.find_spec hex_m
    have hm0_gt : N0 < m0 := by
      by_contra hle
      have heq : m0 = N0 := by omega
      rw [heq] at hm0
      linarith [hm0.2, hd_le]
    refine ⟨m0 - 1, by omega, ?_, ?_⟩
    · have heq : J + (m0 - 1) + 1 = J + m0 := by omega
      rw [heq]; exact hm0.2
    · by_contra hgt
      push Not at hgt
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) ⟨by omega, hgt⟩
  choose lvl hlvl_ge hlvl_gt hlvl_le using hex_lvl
  -- 取最大层级 N
  set N : ℕ := F.sup (fun i => lvl i) with hNdef
  have hN_ge : ∀ i ∈ F, lvl i ≤ N := fun i hi => Finset.le_sup hi
  -- 证明 1 ≤ ∑_{i ∈ F} (2 / M_{lvl i})
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F, (2 : ℝ) / (wordCount D β J (lvl i) : ℝ) := by
    classical
    have hMN_pos : 0 < (wordCount D β J N : ℝ) := by exact_mod_cast wordCount_pos D β J hβ1 hJ1 N
    -- 每个 w : CWord D β J N 的区间都交 K，故交某个 V i (i ∈ F)
    have hcover_words : (Finset.univ : Finset (CWord D β J N)) ⊆
        F.biUnion (fun i => Finset.univ.filter (fun w : CWord D β J N =>
          (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)) := by
      intro w _
      obtain ⟨x, hxI, hxK⟩ := cInterv_inter_cantorSet_nonempty D α c β J hβ hβ1 (by omega) N w
      obtain ⟨i, hiF, hxiV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
      exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxiV, hxI⟩⟩⟩
    -- 对每个 i ∈ F，与 V i 相交的第 N 层词数 * M_{lvl i} ≤ 2 * M_N
    have hcard_i : ∀ i ∈ F,
        ((Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card : ℝ) ≤
          (2 : ℝ) * (wordCount D β J N : ℝ) / (wordCount D β J (lvl i) : ℝ) := by
      intro i hiF
      have hleN : lvl i ≤ N := hN_ge i hiF
      set A_i := Finset.univ.filter (fun u : CWord D β J (lvl i) =>
        (V i.1 ∩ cInterv D α c β (J + lvl i) (centerInt D α c β J (lvl i) u)).Nonempty)
      have hAi_le : A_i.card ≤ 2 := by
        apply WeightedExactDim.card_le_two_of_abs_sub_le_one (centerInt D α c β J (lvl i))
          (centerInt_injective D α c β J hβ (by omega) hwJ (lvl i)) A_i
        intro u₁ hu₁ u₂ hu₂
        obtain ⟨x₁, hx₁⟩ := (Finset.mem_filter.mp hu₁).2
        obtain ⟨x₂, hx₂⟩ := (Finset.mem_filter.mp hu₂).2
        have hwl : wWidth β (J + lvl i) ≤ 1 / 8 :=
          le_trans (wWidth_antitone β hβ (by omega) (by omega)) hwJ
        exact intersect_cInterv_abs_sub_le_one D α c β (J + lvl i) (by omega) hwl
          (hV_bd i.1) (hlvl_le i) hx₁ hx₂
      have hsub_fib : Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty) ⊆
          A_i.biUnion (fun u => Finset.univ.filter (fun w : CWord D β J N =>
            prefixWord D β J hleN w = u)) := by
        intro w hw
        obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hw).2
        have hxI' := cInterv_prefix_subset D α c β J hβ (by omega) hleN w hxI
        refine Finset.mem_biUnion.mpr ⟨prefixWord D β J hleN w, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hMli_pos : 0 < (wordCount D β J (lvl i) : ℝ) := by
        exact_mod_cast wordCount_pos D β J hβ1 hJ1 (lvl i)
      have hcard_mul : (Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card *
            wordCount D β J (lvl i) ≤ 2 * wordCount D β J N := by
        calc (Finset.univ.filter (fun w : CWord D β J N =>
                (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card *
                wordCount D β J (lvl i)
            ≤ (A_i.biUnion (fun u => Finset.univ.filter (fun w : CWord D β J N =>
                prefixWord D β J hleN w = u))).card * wordCount D β J (lvl i) :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub_fib)
          _ ≤ (∑ u ∈ A_i, (Finset.univ.filter (fun w : CWord D β J N =>
                prefixWord D β J hleN w = u)).card) * wordCount D β J (lvl i) :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
          _ = ∑ u ∈ A_i, ((Finset.univ.filter (fun w : CWord D β J N =>
                prefixWord D β J hleN w = u)).card * wordCount D β J (lvl i)) :=
              Finset.sum_mul _ _ _
          _ = ∑ _u ∈ A_i, wordCount D β J N :=
              Finset.sum_congr rfl (fun u _ => card_prefix_fiber_mul D β J (lvl i) N hleN u)
          _ = A_i.card * wordCount D β J N := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * wordCount D β J N := Nat.mul_le_mul_right _ hAi_le
      have hcard_mulR : ((Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card : ℝ) *
            (wordCount D β J (lvl i) : ℝ) ≤ (2 : ℝ) * (wordCount D β J N : ℝ) := by
        exact_mod_cast hcard_mul
      exact (le_div_iff₀ hMli_pos).mpr hcard_mulR
    have htotal : (wordCount D β J N : ℝ) ≤
        ∑ i ∈ F, (2 : ℝ) * (wordCount D β J N : ℝ) / (wordCount D β J (lvl i) : ℝ) := by
      have h1 : (wordCount D β J N : ℕ) ≤
          ∑ i ∈ F, (Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card := by
        rw [← card_CWord D β J N, ← Finset.card_univ]
        exact le_trans (Finset.card_le_card hcover_words) Finset.card_biUnion_le
      have h1R : (wordCount D β J N : ℝ) ≤
          ∑ i ∈ F, ((Finset.univ.filter (fun w : CWord D β J N =>
            (V i.1 ∩ cInterv D α c β (J + N) (centerInt D α c β J N w)).Nonempty)).card : ℝ) := by
        exact_mod_cast h1
      exact le_trans h1R (Finset.sum_le_sum hcard_i)
    have hfactor : ∑ i ∈ F, (2 : ℝ) * (wordCount D β J N : ℝ) / (wordCount D β J (lvl i) : ℝ) =
        (wordCount D β J N : ℝ) * ∑ i ∈ F, (2 : ℝ) / (wordCount D β J (lvl i) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hfactor] at htotal
    exact le_of_mul_le_mul_left (by simpa using htotal) hMN_pos
  -- 另一方面 ∑_{i ∈ F} (diam V i)^s ≤ S.toReal + δ0 < 1
  have hsum_le_diam : ∑ i ∈ F, (2 : ℝ) / (wordCount D β J (lvl i) : ℝ) ≤
      ∑ i ∈ F, Metric.diam (V i.1) ^ s := by
    apply Finset.sum_le_sum
    intro i _
    have h1 := hN0 (lvl i) (hlvl_ge i)
    have hQpos : 0 < (D.P.Q (J + lvl i + 1) : ℝ) := by exact_mod_cast D.P.hQ_pos (J + lvl i + 1)
    have h2 : (1 / (D.P.Q (J + lvl i + 1) : ℝ)) ^ s ≤ Metric.diam (V i.1) ^ s :=
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
        exact WeightedExactDim.ediam_thickening_le (le_of_lt (hρ_pos i.1))
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
            WeightedExactDim.rpow_add_le_add_rpow ENNReal.toReal_nonneg (by linarith [hρ_pos i.1]) hs0 hs1
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


/-- The lower bound at every admissible exact limit for polynomial growth. -/
theorem dimH_polyExactLimit_ge (P : PolyRecData) (α t : ℝ) (hα : α < (P.r : ℝ))
    (ht : (0 < α ∧ 0 ≤ t) ∨ (α = 0 ∧ 0 ≤ t ∧ t ≤ 1/2)) :
    ENNReal.ofReal (1 - α/(P.r : ℝ)) ≤ dimH (polyExactLimit P α t) := by
  have hα0 : 0 ≤ α := by rcases ht with h | h <;> linarith [h.1]
  have hr : (0:ℝ) < P.r := by exact_mod_cast (show 0 < P.r from P.hr)
  let d := 1 - α/(P.r : ℝ)
  have hd : 0 < d := sub_pos.mpr ((div_lt_iff₀ hr).mpr (by simpa using hα))
  have hd1 : d ≤ 1 := sub_le_self _ (div_nonneg hα0 hr.le)
  have hfor : ∀ s : ℝ, 0 < s → s < d → ENNReal.ofReal s ≤ dimH (polyExactLimit P α t) := by
    intro s hs0 hs
    have hsr : s * (P.r : ℝ) + α < P.r := by
      have hh := mul_lt_mul_of_pos_right hs hr
      dsimp [d] at hh
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hr.ne'] at hh
      linarith
    let ε := ((P.r : ℝ) - α - s * (P.r : ℝ)) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    let β := α+ε
    let γ := (P.r : ℝ)-ε
    have hβ : 0 < β := add_pos_of_nonneg_of_pos hα0 hε
    have hαβ : α < β := by dsimp [β]; linarith
    have hγ : γ < (P.r : ℝ) := sub_lt_self _ hε
    have hmass : s*(P.r : ℝ) < γ-β := by dsimp [β,γ,ε]; linarith
    have hγβ : β < γ := by nlinarith [mul_pos hs0 hr]
    obtain ⟨D,hDP,hDγ⟩ := exists_lower_growth P (hβ.trans hγβ) hγ
    have hDβ : β < D.γ := hDγ ▸ hγβ
    have hDmass : s*(D.P.r : ℝ) < D.γ-β := by simpa [hDP,hDγ] using hmass
    have hwlim : Tendsto (fun j : ℕ => wWidth β j) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop
    obtain ⟨J₁,hJ₁⟩ := eventually_atTop.mp (hwlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)))
    have htarget : ∀ᶠ j : ℕ in atTop,
        0 ≤ t*(j:ℝ)^(-α) ∧ t*(j:ℝ)^(-α) ≤ 1/2 := by
      rcases ht with ⟨hαp,ht0⟩ | ⟨rfl,ht0,ht1⟩
      · have hlim : Tendsto (fun j : ℕ => t*(j:ℝ)^(-α)) atTop (nhds 0) := by
          simpa using ((tendsto_rpow_neg_atTop hαp).comp tendsto_natCast_atTop_atTop).const_mul t
        filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with j hj
        exact ⟨mul_nonneg ht0 (Real.rpow_nonneg (Nat.cast_nonneg _) _), hj.le⟩
      · exact Eventually.of_forall (fun j => by simpa only [neg_zero, Real.rpow_zero, mul_one] using And.intro ht0 ht1)
    obtain ⟨J₂,hJ₂⟩ := eventually_atTop.mp htarget
    let J := max D.start (max J₁ J₂)
    have hJ : D.start ≤ J := le_max_left _ _
    have hw : wWidth β J ≤ 1/8 := (hJ₁ J ((le_max_left _ _).trans (le_max_right _ _))).le
    have htJ : ∀ j, J ≤ j → 0 ≤ t*(j:ℝ)^(-α) ∧ t*(j:ℝ)^(-α) ≤ 1/2 :=
      fun j hj => hJ₂ j ((le_max_right J₁ J₂).trans ((le_max_right D.start _).trans hj))
    have hμ := one_le_hausdorffMeasure_cantorSet D α t β J hβ hDβ hJ hw hs0 (hs.le.trans hd1) hDmass
    have hμ_ne : μH[s] (cantorSet D α t β J) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1) hμ)
    let s' : ℝ≥0 := ⟨s, hs0.le⟩
    have hdim : (s' : ℝ≥0∞) ≤ dimH (cantorSet D α t β J) :=
      le_dimH_of_hausdorffMeasure_ne_zero hμ_ne
    have hsub := cantorSet_subset_exactLimitSetα D α t β J hα0 hβ hαβ (D.one_le_start.trans hJ) hw htJ
    rw [hDP] at hsub
    have hs' : (s' : ℝ≥0∞) = ENNReal.ofReal s := by
      simp only [s', ENNReal.ofReal]
      congr 1
      exact (Real.toNNReal_of_nonneg hs0.le).symm
    rw [hs'] at hdim
    exact hdim.trans (dimH_mono hsub)
  change ENNReal.ofReal d ≤ _
  by_contra! h
  have hfin : dimH (polyExactLimit P α t) ≠ ⊤ := ne_of_lt (h.trans_le le_top)
  have hreal : (dimH (polyExactLimit P α t)).toReal < d := by
    simpa [ENNReal.toReal_ofReal hd.le] using (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr h
  let s := max (d/2) (((dimH (polyExactLimit P α t)).toReal+d)/2)
  have hs0 : 0 < s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs : s < d := max_lt (by linarith) (by linarith)
  have hh := ENNReal.toReal_mono hfin (hfor s hs0 hs)
  rw [ENNReal.toReal_ofReal hs0.le] at hh
  have := le_max_right (d/2) (((dimH (polyExactLimit P α t)).toReal+d)/2)
  change _ ≤ s at this
  linarith

theorem polyExactLimit_subset_polyWeightedSublevel (P : PolyRecData) (α t : ℝ) :
    polyExactLimit P α t ⊆ {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t} := by
  intro x hx
  exact (ENNReal.tendsto_ofReal hx.2).limsup_eq.le

theorem dimH_polyExactLimit_eq (P : PolyRecData) (α t : ℝ) (hα : α < (P.r : ℝ))
    (ht : (0 < α ∧ 0 ≤ t) ∨ (α = 0 ∧ 0 ≤ t ∧ t ≤ 1/2)) :
    dimH (polyExactLimit P α t) = ENNReal.ofReal (1 - α/(P.r : ℝ)) :=
  le_antisymm
    ((dimH_mono (polyExactLimit_subset_polyWeightedSublevel P α t)).trans
      (PolyWeightedUpper.dimH_polyWeightedExponent_le P α t hα.le))
    (dimH_polyExactLimit_ge P α t hα ht)

theorem dimH_polyWeightedSublevel_eq (P : PolyRecData) (α t : ℝ)
    (hα0 : 0 ≤ α) (hα : α < (P.r : ℝ)) (ht : 0 ≤ t) :
    dimH {x : ℝ | P.polyWeightedExponent α x ≤ ENNReal.ofReal t} =
      ENNReal.ofReal (1 - α/(P.r : ℝ)) := by
  have hzero : (0 < α ∧ (0:ℝ) ≤ 0) ∨ (α = 0 ∧ (0:ℝ) ≤ 0 ∧ (0:ℝ) ≤ 1/2) := by
    rcases eq_or_lt_of_le hα0 with h | h
    · right; exact ⟨h.symm, le_rfl, by norm_num⟩
    · exact Or.inl ⟨h, le_rfl⟩
  refine le_antisymm (PolyWeightedUpper.dimH_polyWeightedExponent_le P α t hα.le) ?_
  refine (dimH_polyExactLimit_ge P α 0 hα hzero).trans (dimH_mono ?_)
  intro x hx
  exact (polyExactLimit_subset_polyWeightedSublevel P α 0 hx).trans (ENNReal.ofReal_le_ofReal ht)


/-- For weight zero, every approximation error is at most one half. -/
theorem polyZeroWeightSublevel_eq_univ (P : PolyRecData) {t : ℝ} (ht : 1/2 ≤ t) :
    {x : ℝ | P.polyWeightedExponent 0 x ≤ ENNReal.ofReal t} = Set.univ := by
  refine Set.eq_univ_of_forall (fun x => ?_)
  change P.polyWeightedExponent 0 x ≤ ENNReal.ofReal t
  unfold PolyRecData.polyWeightedExponent
  apply limsup_le_of_le (by isBoundedDefault)
  refine Eventually.of_forall (fun j => ENNReal.ofReal_le_ofReal ?_)
  simpa only [PolyRecData.polyWeightedSeq, Real.rpow_zero, one_mul] using
    (distToNearestInt_le_half ((P.Q j : ℝ) * x)).trans ht

theorem polyExactLimit_zero_eq_empty (P : PolyRecData) {t : ℝ} (ht : 1/2 < t) :
    polyExactLimit P 0 t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hb : ∀ j : ℕ, P.polyWeightedSeq 0 x j ≤ 1/2 := fun j => by
    simpa only [PolyRecData.polyWeightedSeq, Real.rpow_zero, one_mul] using
      distToNearestInt_le_half ((P.Q j : ℝ) * x)
  exact ht.not_ge (le_of_tendsto hx.2 (Eventually.of_forall hb))

end
end PolyWeightedLower

#print axioms PolyWeightedLower.dimH_polyExactLimit_eq
#print axioms PolyWeightedLower.dimH_polyWeightedSublevel_eq

#print axioms PolyWeightedLower.polyZeroWeightSublevel_eq_univ
#print axioms PolyWeightedLower.polyExactLimit_zero_eq_empty

