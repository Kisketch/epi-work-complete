import Mathlib
import EpiFormal.DimHFinite
import EpiFormal.GaugeNull
import EpiFormal.FullSpectrumDiscrete
import EpiFormal.WeightedExactDim

/-!
# §4 补集满测度与 §6 临界规范测度完整理论（GaugeExact）

本模块在 Lean 4 中无条件形式化论文二（第二阶段：沿 e 收敛子分母的逼近谱隙与水平集维数）
的四个核心板块：
1. **§4 补集（无限水平集 $\{\Lambda = \infty\}$）的 Lebesgue 满测度与 Hausdorff 维数 1 定理**：
   - `volume_finiteLevel_zero`：有限水平集 $\{\Lambda < \top\}$ 的 Lebesgue 测度为 $0$；
   - `volume_infiniteLevel_Icc`：无限水平集 $\{\Lambda = \top\}$ 在任意闭区间 $[a, b]$（$a \le b$）上的 Lebesgue 测度为 $b - a$；
   - `ae_apprExponent_eq_top`：在 $\mathbb{R}$ 上对 Lebesgue 测度几乎处处有 $\Lambda(x) = \top$；
   - `dimH_infiniteLevel_eq_one` / `dimH_infiniteLevel_inter_Icc_zero_one`：无限水平集及其与 $[0,1]$ 的交的 Hausdorff 维数均为 $1$。
2. **Theorem 13 的 $\sigma$-有限性分解与 $L$-平移不变性**：
   - `apprExponent_add_latticeL`：对任意 $y \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$，$\Lambda(x + y) = \Lambda(x)$；
   - `exactLevel_add_latticeL`：精确水平集 $\{\Lambda(x) = k/4\}$ 在 $L$-平移下不变；
   - `mkMetric_digitClass_le` / `mkMetric_digitClass_lt_top`：在临界规范上界 $m(1/Q_n) \le C (2k+1)^{-n}$ 下，每个 `digitClass k N m0 m1` 的 `Measure.mkMetric m` 测度有限（$\le C (2k+1)^{-N} < \top$），从而 $\{\Lambda \le k/4\}$ 与 $\{\Lambda = k/4\}$ 均可表为可数个有限规范测度集合之并（限制测度 $\sigma$-有限）。
3. **Corollary 14(iii) 规范比较与更大阶规范的非 $\sigma$-有限性 / 无穷测度定理**：
   - `mkMetric_le_mul_of_eventually_le`：小尺度最终 $h(t) \le c \cdot g(t)$ 蕴涵 $\mathcal{H}^h(E) \le c \cdot \mathcal{H}^g(E)$；
   - `mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top`：若 $h(t)/g(t) \to 0$（$t \to 0^+$）且 $\mathcal{H}^g(E) < \top$，则 $\mathcal{H}^h(E) = 0$；
   - `not_countable_union_finite_of_ratio_tendsto_zero`（Corollary 14(iii) 精确形式化）：若 $h(t)/g(t) \to 0$ 且 $\mathcal{H}^h(S) > 0$，则 $\mathcal{H}^g(S) = \top$ 且 $S$ 不能被可数个 $\mathcal{H}^g$-测度有限的集合覆盖（非 $\sigma$-有限）；
   - `gauge_ratio_adjacent_levels_tendsto_zero`（Remark 15 能级分离）：$k \ge 1$ 时 $((2k-1)/(2k+1))^n \to 0$。
4. **Theorem 13 临界规范正测度下界与 Theorem 16(ii) 无符号精确极限集普适规范 $g_2$ 定理**：
   - `mkMetric_unsignedExactLimit_null_of_hk`：对一切 $k \ge 1$，无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 在临界规范 $h_k$ 下测度为 $0$（因为 $2 < 2k+1$）；
   - `mkMetric_unsignedExactLimit_null_of_subgauge_base2` / `mkMetric_unsignedExactLimit_sigma_finite_of_base2`：$E_{\mathrm{lim}}(k/4)$ 对一切 $2^n g(1/Q_n) \to 0$ 的次临界规范测度为 $0$，且在 $m(1/Q_n) \le C \cdot 2^{-n}$ 的普适规范 $g_2$ 下可表为可数个有限测度集之并（$\sigma$-有限）；
   - `one_le_sum_inv_pow_of_cover` / `mkMetric_cantorTree_pos` / `mkMetric_exactLevel_pos_of_cantorTree`：均匀 $b$-叉 Cantor 树的质量分布有限覆盖下界定理，以及结合 `mkMetric_strictLevel_null` 导出精确水平集在临界规范下的正测度定理。
-/

open Real Filter Topology Set MeasureTheory Classification SpectralGap DimHCore DimHFinite
  FullSpectrumDiscrete GaugeNull WeightedUpper WeightedFinal WeightedExactDim
open scoped ENNReal NNReal

namespace GaugeExact

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 第一部分：§4 补集（无限水平集 $\{\Lambda = \infty\}$）的 Lebesgue 满测度与 Hausdorff 维数 1 -/

/-- 有限水平集 $\{x : \Lambda(x) < \top\}$ 可表示为可数个整数水平集 `levelSet (ofReal n)`（$n \in \mathbb{N}$）之并。 -/
lemma finiteLevel_eq_iUnion_nat :
    {x : ℝ | apprExponent x < ⊤} = ⋃ n : ℕ, levelSet (ENNReal.ofReal (n : ℝ)) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, levelSet]
  constructor
  · intro hx
    have hfin : apprExponent x ≠ ⊤ := ne_of_lt hx
    obtain ⟨n, hn⟩ := exists_nat_ge (apprExponent x).toReal
    refine ⟨n, ?_⟩
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hn
  · rintro ⟨n, hn⟩
    exact lt_of_le_of_lt hn ENNReal.ofReal_lt_top

/-- **定理（有限水平集的 Hausdorff 维数为 $0$）**：
    $\dim_H \{x \in \mathbb{R} : \Lambda(x) < \top\} = 0$。 -/
theorem dimH_finiteLevel_zero :
    dimH {x : ℝ | apprExponent x < ⊤} = 0 := by
  apply le_antisymm _ zero_le
  rw [finiteLevel_eq_iUnion_nat, dimH_iUnion]
  apply iSup_le
  intro n
  rw [DimHFinite.dimH_levelSet_finite (n : ℝ)]

/-- 对任意实数 $c$，水平集 `levelSet (ofReal c)` 的 Lebesgue 测度为 $0$。 -/
lemma volume_levelSet_finite_zero (c : ℝ) :
    MeasureTheory.volume (levelSet (ENNReal.ofReal c)) = 0 := by
  set c' := max c 0
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hmono0 : levelSet (ENNReal.ofReal c) ⊆ levelSet (ENNReal.ofReal c') := by
    intro x hx
    exact le_trans hx (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  set t := c' + 1
  have hct : c' < t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hsub := Set.Subset.trans hmono0 (DimHFinite.levelSet_subset_iUnion_tailSet c' t hc'0 hct)
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro J
  apply measure_iUnion_null
  intro m
  -- 平移不变或直接用 tailSet_cover
  have htail_null : MeasureTheory.volume (DimHFinite.tailSet t J.1) = 0 := by
    apply le_antisymm _ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simp only [zero_add]
    have hlim := DimHFinite.tendsto_contentBound t ht0 J.1 J.2 1 (by norm_num)
    have hof : Tendsto (fun n : ℕ => ENNReal.ofReal
        ((((Qsel J.1).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ (1 : ℝ) *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J.1 + n) : ℝ) ^ (1 : ℝ)))
        atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    have hev : ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal ((((Qsel J.1).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ (1 : ℝ) *
          ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J.1 + n) : ℝ) ^ (1 : ℝ)) < (ε : ℝ≥0∞) :=
      hof.eventually (Iio_mem_nhds (by exact_mod_cast hε))
    obtain ⟨n, hn⟩ := hev.exists
    have hcov := DimHFinite.tailSet_cover t ht0 J.1 J.2 n
    calc MeasureTheory.volume (DimHFinite.tailSet t J.1)
        ≤ MeasureTheory.volume (⋃ k : (DimHFinite.survSet t J.1 n : Set ℕ),
            DimHFinite.interv t (J.1 + n) k.1) := measure_mono hcov
      _ ≤ ∑ k : (DimHFinite.survSet t J.1 n : Set ℕ),
            MeasureTheory.volume (DimHFinite.interv t (J.1 + n) k.1) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : (DimHFinite.survSet t J.1 n : Set ℕ),
            ENNReal.ofReal (2 * rad t (J.1 + n)) := by
          apply Finset.sum_le_sum
          intro k _
          unfold DimHFinite.interv
          rw [Real.volume_Icc]
          have hsub_eq : ((k.1 : ℝ) / (Qsel (J.1 + n) : ℝ) + rad t (J.1 + n)) -
              ((k.1 : ℝ) / (Qsel (J.1 + n) : ℝ) - rad t (J.1 + n)) = 2 * rad t (J.1 + n) := by ring
          rw [hsub_eq]
      _ = ((DimHFinite.survSet t J.1 n).card : ℝ≥0∞) * ENNReal.ofReal (2 * rad t (J.1 + n)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp
      _ = ENNReal.ofReal (((DimHFinite.survSet t J.1 n).card : ℝ) * (2 * rad t (J.1 + n))) := by
          have hcast : ((DimHFinite.survSet t J.1 n).card : ℝ≥0∞) =
              ENNReal.ofReal ((DimHFinite.survSet t J.1 n).card : ℝ) := by simp
          rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((((Qsel J.1).toNat + 1 : ℕ) : ℝ) * (2 * t) ^ (1 : ℝ) *
            ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J.1 + n) : ℝ) ^ (1 : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hcard := DimHFinite.card_survSet_le t ht0 J.1 J.2 n
          have hcardR : ((DimHFinite.survSet t J.1 n).card : ℝ) ≤
              (((Qsel J.1).toNat + 1 : ℕ) : ℝ) * ((branchB t : ℕ) : ℝ) ^ n := by
            exact_mod_cast hcard
          have hrad := DimHFinite.rad_le_factorial t ht0 J.1 n (by omega)
          have hfactpos : 0 < (Nat.factorial (J.1 + n) : ℝ) := by exact_mod_cast Nat.factorial_pos _
          have hm1 : 1 ≤ ((J.1 + n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ J.1 + n)
          have hden2 : (Nat.factorial (J.1 + n) : ℝ) ≤
              ((J.1 + n : ℕ) : ℝ) * (Nat.factorial (J.1 + n) : ℝ) := by nlinarith
          have hrad2 : 2 * rad t (J.1 + n) ≤ (2 * t) / (Nat.factorial (J.1 + n) : ℝ) := by
            calc 2 * rad t (J.1 + n)
                ≤ 2 * (t / (((J.1 + n : ℕ) : ℝ) * (Nat.factorial (J.1 + n) : ℝ))) := by gcongr
              _ = (2 * t) / (((J.1 + n : ℕ) : ℝ) * (Nat.factorial (J.1 + n) : ℝ)) := by ring
              _ ≤ (2 * t) / (Nat.factorial (J.1 + n) : ℝ) :=
                  div_le_div_of_nonneg_left (by linarith) (by positivity) hden2
          simp only [Real.rpow_one]
          calc ((DimHFinite.survSet t J.1 n).card : ℝ) * (2 * rad t (J.1 + n))
              ≤ ((((Qsel J.1).toNat + 1 : ℕ) : ℝ) * ((branchB t : ℕ) : ℝ) ^ n) *
                ((2 * t) / (Nat.factorial (J.1 + n) : ℝ)) := by
                gcongr
                exact mul_nonneg (by norm_num) (rad_nonneg t ht0 (J.1 + n))
            _ = (((Qsel J.1).toNat + 1 : ℕ) : ℝ) * (2 * t) *
                ((branchB t : ℕ) : ℝ) ^ n / (Nat.factorial (J.1 + n) : ℝ) := by ring
      _ ≤ (ε : ℝ≥0∞) := le_of_lt hn
  have himg : (fun y : ℝ => y + (m : ℝ)) '' DimHFinite.tailSet t J.1 =
      (fun y : ℝ => y + -(m : ℝ)) ⁻¹' DimHFinite.tailSet t J.1 := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : y + (m : ℝ) + -(m : ℝ) = y := by ring
      rwa [this]
    · intro hx
      exact ⟨x + -(m : ℝ), hx, by ring⟩
  rw [himg, measure_preimage_add_right]
  exact htail_null

/-- **定理（有限水平集的 Lebesgue 测度为 $0$）**：
    `MeasureTheory.volume {x : ℝ | apprExponent x < ⊤} = 0`。 -/
theorem volume_finiteLevel_zero :
    MeasureTheory.volume {x : ℝ | apprExponent x < ⊤} = 0 := by
  rw [finiteLevel_eq_iUnion_nat]
  apply measure_iUnion_null
  intro n
  exact volume_levelSet_finite_zero (n : ℝ)

/-- **推论（在 $\mathbb{R}$ 上对 Lebesgue 测度几乎处处有 $\Lambda(x) = \top$）**：
    `∀ᵐ x ∂MeasureTheory.volume, apprExponent x = ⊤`。 -/
theorem ae_apprExponent_eq_top :
    ∀ᵐ x ∂MeasureTheory.volume, apprExponent x = ⊤ := by
  rw [ae_iff]
  have heq : {x : ℝ | ¬apprExponent x = ⊤} = {x : ℝ | apprExponent x < ⊤} := by
    ext x
    simp [lt_top_iff_ne_top]
  rw [heq]
  exact volume_finiteLevel_zero

/-- **定理（无限水平集在任意闭区间 $[a, b]$ 上具有满 Lebesgue 测度 $b - a$）**：
    对任意 $a, b \in \mathbb{R}$，
    `MeasureTheory.volume ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) = ENNReal.ofReal (b - a)`。 -/
theorem volume_infiniteLevel_Icc (a b : ℝ) :
    MeasureTheory.volume ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) =
      ENNReal.ofReal (b - a) := by
  have hsub : Set.Icc a b ⊆
      ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) ∪ {x : ℝ | apprExponent x < ⊤} := by
    intro x hx
    by_cases htop : apprExponent x = ⊤
    · exact Or.inl ⟨htop, hx⟩
    · exact Or.inr (lt_top_iff_ne_top.mpr htop)
  apply le_antisymm
  · rw [← Real.volume_Icc]
    exact measure_mono Set.inter_subset_right
  · calc ENNReal.ofReal (b - a)
        = MeasureTheory.volume (Set.Icc a b) := Real.volume_Icc.symm
      _ ≤ MeasureTheory.volume (({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) ∪
            {x : ℝ | apprExponent x < ⊤}) := measure_mono hsub
      _ ≤ MeasureTheory.volume ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) +
            MeasureTheory.volume {x : ℝ | apprExponent x < ⊤} := measure_union_le _ _
      _ = MeasureTheory.volume ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc a b) := by
            rw [volume_finiteLevel_zero, add_zero]

/-- 特别地，无限水平集在单位区间 $[0, 1]$ 上的 Lebesgue 测度为 $1$。 -/
theorem volume_infiniteLevel_Icc_zero_one :
    MeasureTheory.volume ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) = 1 := by
  rw [volume_infiniteLevel_Icc 0 1]
  simp

/-- 实数集的精确加权极限集 `exactLimitSetα 0 0`（对应 $\lim_{j\to\infty} \|Q_j x\| = 0$，维数为 $1$）
    与有限水平集的差集包含于无限水平集与 $[0, 1]$ 的交。 -/
lemma exactLimitSetα_zero_zero_sdiff_subset_infiniteLevel :
    exactLimitSetα 0 0 \ {x : ℝ | apprExponent x < ⊤} ⊆
      {x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨⟨hxIcc, _⟩, hnot_lt⟩
  simp only [Set.mem_ofPred_eq, lt_top_iff_ne_top, not_not] at hnot_lt
  exact ⟨hnot_lt, hxIcc⟩

/-- 对一切 $x \in \mathbb{R}$，加权指数 $\Lambda_0(x) \le 1/2$（即 `levelSetα 0 (ofReal 1) = Set.univ`）。 -/
lemma subset_levelSetα_zero_one (S : Set ℝ) :
    S ⊆ levelSetα 0 (ENNReal.ofReal 1) := by
  intro x _
  show apprExponentα 0 x ≤ ENNReal.ofReal 1
  unfold apprExponentα
  apply limsup_le_of_le (by isBoundedDefault)
  refine Filter.Eventually.of_forall (fun j => ?_)
  unfold apprSeqαE apprSeqα
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.rpow_zero, one_mul]
  exact le_trans (distToNearestInt_le_half _) (by norm_num)

/-- $\mathbb{R}$ 的任何子集 $S$ 的 Hausdorff 维数不超过 $1$（由 `WeightedFinal.dimH_levelSetα_le 0 1` 直接导出）。 -/
lemma dimH_real_subset_le_one (S : Set ℝ) : dimH S ≤ 1 := by
  calc dimH S ≤ dimH (levelSetα 0 (ENNReal.ofReal 1)) := dimH_mono (subset_levelSetα_zero_one S)
    _ ≤ ENNReal.ofReal (1 - 0) := WeightedFinal.dimH_levelSetα_le 0 1 (le_refl 0) (by norm_num)
    _ = 1 := by simp

/-- **定理（无限水平集与 $[0, 1]$ 之交的 Hausdorff 维数为 $1$）**：
    `dimH ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) = 1`。 -/
theorem dimH_infiniteLevel_inter_Icc_zero_one :
    dimH ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) = 1 := by
  apply le_antisymm (dimH_real_subset_le_one _)
  have hcov : exactLimitSetα 0 0 ⊆
      ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) ∪ {x : ℝ | apprExponent x < ⊤} := by
    intro x hx
    by_cases htop : apprExponent x = ⊤
    · exact Or.inl ⟨htop, hx.1⟩
    · exact Or.inr (lt_top_iff_ne_top.mpr htop)
  have hdim0 : dimH (exactLimitSetα 0 0) = 1 := by
    have h := WeightedExactDim.dimH_exactLimitSetα_eq 0 0 (by norm_num)
      (Or.inr ⟨rfl, le_refl 0, by norm_num⟩)
    simpa using h
  calc (1 : ℝ≥0∞) = dimH (exactLimitSetα 0 0) := hdim0.symm
    _ ≤ dimH (({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) ∪
          {x : ℝ | apprExponent x < ⊤}) := dimH_mono hcov
    _ = max (dimH ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1))
          (dimH {x : ℝ | apprExponent x < ⊤}) := dimH_union _ _
    _ = dimH ({x : ℝ | apprExponent x = ⊤} ∩ Set.Icc (0 : ℝ) 1) := by
          rw [dimH_finiteLevel_zero]
          simp

/-- **定理（§4 无限水平集 $\{\Lambda = \infty\}$ 的 Hausdorff 维数为 $1$）**：
    `dimH {x : ℝ | apprExponent x = ⊤} = 1`。 -/
theorem dimH_infiniteLevel_eq_one :
    dimH {x : ℝ | apprExponent x = ⊤} = 1 := by
  apply le_antisymm (dimH_real_subset_le_one _)
  rw [← dimH_infiniteLevel_inter_Icc_zero_one]
  exact dimH_mono Set.inter_subset_left

/-! ## 第二部分：Theorem 13 的 $\sigma$-有限性分解与 $L$-平移不变性 -/

/-- 到最近整数距离的三角不等式：`distToNearestInt (u + v) ≤ distToNearestInt u + distToNearestInt v`。 -/
lemma distToNearestInt_add_le (u v : ℝ) :
    distToNearestInt (u + v) ≤ distToNearestInt u + distToNearestInt v := by
  calc distToNearestInt (u + v)
      ≤ |(u + v) - ((round u + round v : ℤ) : ℝ)| := distToNearestInt_le (u + v) (round u + round v)
    _ = |(u - (round u : ℝ)) + (v - (round v : ℝ))| := by push_cast; ring_nf
    _ ≤ |u - (round u : ℝ)| + |v - (round v : ℝ)| := abs_add_le _ _
    _ = distToNearestInt u + distToNearestInt v := rfl

/-- 到最近整数距离的反三角不等式：`|distToNearestInt (u + v) - distToNearestInt u| ≤ distToNearestInt v`。 -/
lemma abs_distToNearestInt_add_sub_le (u v : ℝ) :
    |distToNearestInt (u + v) - distToNearestInt u| ≤ distToNearestInt v := by
  rw [abs_le]
  constructor
  · have h1 := distToNearestInt_add_le (u + v) (-v)
    have h2 : u + v + -v = u := by ring
    rw [h2, distToNearestInt_neg] at h1
    linarith
  · have h1 := distToNearestInt_add_le u v
    linarith

/-- 对任意 $x, y \in \mathbb{R}$ 与 $j \in \mathbb{N}$，
    `|apprSeq (x + y) j - apprSeq x j| ≤ apprSeq y j`。 -/
lemma abs_apprSeq_add_sub_le (x y : ℝ) (j : ℕ) :
    |apprSeq (x + y) j - apprSeq x j| ≤ apprSeq y j := by
  unfold apprSeq
  have h1 : (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * (x + y)) -
      (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x) =
      (j : ℝ) * (distToNearestInt ((Qsel j : ℝ) * x + (Qsel j : ℝ) * y) -
        distToNearestInt ((Qsel j : ℝ) * x)) := by ring
  rw [h1, abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  exact mul_le_mul_of_nonneg_left
    (abs_distToNearestInt_add_sub_le ((Qsel j : ℝ) * x) ((Qsel j : ℝ) * y))
    (Nat.cast_nonneg j)

/-- 对任意 $x, y \in \mathbb{R}$ 与 $j \in \mathbb{N}$，
    `apprSeqE (x + y) j ≤ apprSeqE x j + apprSeqE y j`。 -/
lemma apprSeqE_add_le (x y : ℝ) (j : ℕ) :
    apprSeqE (x + y) j ≤ apprSeqE x j + apprSeqE y j := by
  unfold apprSeqE
  rw [← ENNReal.ofReal_add (apprSeq_nonneg x j) (apprSeq_nonneg y j)]
  apply ENNReal.ofReal_le_ofReal
  have h := (abs_le.mp (abs_apprSeq_add_sub_le x y j)).2
  linarith

/-- 若 $y \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$，则 $-y \in L$。 -/
lemma neg_mem_latticeL {y : ℝ} (hy : y ∈ latticeL) : -y ∈ latticeL := by
  rcases hy with ⟨m, n, rfl⟩
  refine ⟨-m, -n, ?_⟩
  push_cast
  ring

/-- 单侧上界：若 $y \in L$，则对任意 $x \in \mathbb{R}$ 有 `apprExponent (x + y) ≤ apprExponent x`。 -/
lemma apprExponent_add_latticeL_le (x : ℝ) {y : ℝ} (hy : y ∈ latticeL) :
    apprExponent (x + y) ≤ apprExponent x := by
  by_cases htop : apprExponent x = ⊤
  · rw [htop]; exact le_top
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hy0 : Tendsto (apprSeq y) atTop (nhds 0) :=
      (Classification.theorem2_classification y).mpr hy
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hev : ∀ᶠ j : ℕ in atTop, apprSeq y j < (ε : ℝ) :=
      hy0.eventually (Iio_mem_nhds hεR)
    have hevE : ∀ᶠ j : ℕ in atTop, apprSeqE (x + y) j ≤ apprSeqE x j + (ε : ℝ≥0∞) := by
      filter_upwards [hev] with j hj
      calc apprSeqE (x + y) j
          ≤ apprSeqE x j + apprSeqE y j := apprSeqE_add_le x y j
        _ ≤ apprSeqE x j + ENNReal.ofReal (ε : ℝ) := by
            gcongr
            exact ENNReal.ofReal_le_ofReal (le_of_lt hj)
        _ = apprSeqE x j + (ε : ℝ≥0∞) := by simp
    calc apprExponent (x + y)
        = Filter.limsup (apprSeqE (x + y)) atTop := rfl
      _ ≤ Filter.limsup (fun j => apprSeqE x j + (ε : ℝ≥0∞)) atTop :=
          Filter.limsup_le_limsup hevE
      _ ≤ apprExponent x + (ε : ℝ≥0∞) := by
          apply ENNReal.le_of_forall_pos_le_add
          intro δ hδ _
          have hlt : apprExponent x < apprExponent x + (δ : ℝ≥0∞) :=
            ENNReal.lt_add_right htop (by exact_mod_cast hδ.ne')
          have hev_x : ∀ᶠ j : ℕ in atTop, apprSeqE x j < apprExponent x + (δ : ℝ≥0∞) :=
            Filter.eventually_lt_of_limsup_lt hlt
          refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
          filter_upwards [hev_x] with j hj
          calc apprSeqE x j + (ε : ℝ≥0∞)
              ≤ (apprExponent x + (δ : ℝ≥0∞)) + (ε : ℝ≥0∞) := add_le_add (le_of_lt hj) le_rfl
            _ = apprExponent x + (ε : ℝ≥0∞) + (δ : ℝ≥0∞) := by ring

/-- **定理（逼近指数 $\Lambda$ 的 $L$-平移不变性，Theorem 13 平移不变性）**：
    对任意 $x \in \mathbb{R}$ 与 $y \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$，
    `apprExponent (x + y) = apprExponent x`。 -/
theorem apprExponent_add_latticeL (x : ℝ) {y : ℝ} (hy : y ∈ latticeL) :
    apprExponent (x + y) = apprExponent x := by
  apply le_antisymm (apprExponent_add_latticeL_le x hy)
  have h := apprExponent_add_latticeL_le (x + y) (neg_mem_latticeL hy)
  have heq : x + y + -y = x := by ring
  rwa [heq] at h

/-- **推论（精确水平集在 $L$-平移下不变）**：
    对任意 $c \in \mathbb{R}_{\ge 0\infty}$ 与 $y \in L$，
    `(fun x : ℝ => x + y) ⁻¹' {x : ℝ | apprExponent x = c} = {x : ℝ | apprExponent x = c}`。 -/
theorem exactLevel_add_latticeL (c : ℝ≥0∞) {y : ℝ} (hy : y ∈ latticeL) :
    (fun x : ℝ => x + y) ⁻¹' {x : ℝ | apprExponent x = c} =
      {x : ℝ | apprExponent x = c} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, apprExponent_add_latticeL x hy]

/-- **定理（Theorem 13 $\sigma$-有限性核心：`digitClass` 的规范测度有限界）**：
    设 $r, N \in \mathbb{N}$（$N \ge 1$），$m_0, m_1 \in \mathbb{Z}$，单调非减函数
    $m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 满足对一切 $n \ge N$ 有
    $m(1 / Q_n) \le C \cdot (2r+1)^{-n}$。则
    `Measure.mkMetric m (digitClass r N m0 m1) ≤ ENNReal.ofReal (max C 0 * (2 * (r : ℝ) + 1) ^ (-(N : ℤ)))`
    （特别地严格小于 $\top$）。 -/
theorem mkMetric_digitClass_le (r N : ℕ) (_hN : 1 ≤ N) (m0 m1 : ℤ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, N ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (r : ℝ) + 1) ^ (-(n : ℤ)))) :
    Measure.mkMetric m (digitClass r N m0 m1) ≤
      ENNReal.ofReal (max C 0 * (2 * (r : ℝ) + 1) ^ (-(N : ℤ))) := by
  let ι : ℕ → Type _ := fun n => {p // p ∈ pairTree r N m0 m1 n}
  let radSeq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))
  let cov : ∀ n, ι n → Set ℝ := fun n p => gaugeInterv (N + n) p.1.1
  have hr : Tendsto radSeq atTop (nhds 0) := tendsto_inv_Qsel_shift N
  have ht_diam : ∀ᶠ n in atTop, ∀ p : ι n, Metric.ediam (cov n p) ≤ radSeq n :=
    Filter.Eventually.of_forall (fun n p => ediam_gaugeInterv_le (N + n) p.1.1)
  have hst : ∀ᶠ n in atTop, digitClass r N m0 m1 ⊆ ⋃ p : ι n, cov n p :=
    Filter.Eventually.of_forall (fun n => digitClass_cover r N m0 m1 n)
  have hmain := MeasureTheory.Measure.mkMetric_le_liminf_sum
    (digitClass r N m0 m1) radSeq hr cov ht_diam hst m
  set C' := max C 0
  set b : ℝ := 2 * (r : ℝ) + 1
  have hb_pos : 0 < b := by
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    dsimp [b]; linarith
  have hsum_le : ∀ n : ℕ, ∑ p : ι n, m (Metric.ediam (cov n p)) ≤
      ENNReal.ofReal (C' * b ^ (-(N : ℤ))) := by
    intro n
    have hb_zpow_nn : 0 ≤ b ^ (-((N + n : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb_pos) _
    have hCC' : C * b ^ (-((N + n : ℕ) : ℤ)) ≤ C' * b ^ (-((N + n : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hb_zpow_nn
    have hcast_b : (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (b ^ n) := by
      have h1 : (((2 * r + 1) ^ n : ℕ) : ℝ) = b ^ n := by dsimp [b]; push_cast; rfl
      rw [← ENNReal.ofReal_natCast, h1]
    have halg : b ^ n * (C' * b ^ (-((N + n : ℕ) : ℤ))) = C' * b ^ (-(N : ℤ)) := by
      rw [zpow_neg, zpow_natCast, pow_add, zpow_neg, zpow_natCast]
      have hbN : b ^ N ≠ 0 := pow_ne_zero N (ne_of_gt hb_pos)
      have hbn : b ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      field_simp
    calc ∑ p : ι n, m (Metric.ediam (cov n p))
        ≤ ∑ _p : ι n, m (radSeq n) :=
          Finset.sum_le_sum (fun p _ => hm (ediam_gaugeInterv_le (N + n) p.1.1))
      _ = ((pairTree r N m0 m1 n).card : ℝ≥0∞) * m (radSeq n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp [ι]
          rw [Fintype.card_coe]
      _ ≤ (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
          gcongr
          exact_mod_cast card_pairTree_le r N m0 m1 n
      _ ≤ ENNReal.ofReal (b ^ n) * ENNReal.ofReal (C' * b ^ (-((N + n : ℕ) : ℤ))) := by
          rw [hcast_b]
          gcongr
          exact le_trans (hbound (N + n) (by omega)) (ENNReal.ofReal_le_ofReal hCC')
      _ = ENNReal.ofReal (b ^ n * (C' * b ^ (-((N + n : ℕ) : ℤ)))) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (le_of_lt hb_pos) n)]
      _ = ENNReal.ofReal (C' * b ^ (-(N : ℤ))) := by rw [halg]
  have hlim : Filter.liminf (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop ≤
      ENNReal.ofReal (C' * b ^ (-(N : ℤ))) :=
    Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hsum_le)
  exact le_trans hmain hlim

/-- 每个 `digitClass r N m0 m1` 在临界规范上界下的 `Measure.mkMetric m` 测度有限（`< ⊤`）。 -/
theorem mkMetric_digitClass_lt_top (r N : ℕ) (hN : 1 ≤ N) (m0 m1 : ℤ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, N ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (r : ℝ) + 1) ^ (-(n : ℤ)))) :
    Measure.mkMetric m (digitClass r N m0 m1) < ⊤ :=
  lt_of_le_of_lt (mkMetric_digitClass_le r N hN m0 m1 m hm C hbound) ENNReal.ofReal_lt_top

/-- **推论（Theorem 13 精确水平集与子水平集的 $\sigma$-有限可数覆盖分解）**：
    若单调函数 $m$ 对一切 $n \ge 1$ 满足 $m(1/Q_n) \le C (2k+1)^{-n}$，则存在可数族
    $E : \mathbb{N} \times \mathbb{Z} \times \mathbb{Z} \to \mathrm{Set}\ \mathbb{R}$ 使得
    $\{x : \Lambda(x) = k/4\} \subseteq \{x : \Lambda(x) \le k/4\} \subseteq \bigcup_i E_i$，
    且每个 $E_i$ 满足 `Measure.mkMetric m (E i) < ⊤`。 -/
theorem exactLevel_countable_cover_finite_mkMetric (k : ℕ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-(n : ℤ)))) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric m (E i) < ⊤ := by
  refine ⟨fun i => digitClass k i.1.1 i.2.1 i.2.2, ?_, ?_, ?_⟩
  · intro x hx
    have hle : apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4) := le_of_eq hx
    have hmem := levelSet_quarter_subset_iUnion_digitClass k hle
    rcases Set.mem_iUnion.mp hmem with ⟨N, h1⟩
    rcases Set.mem_iUnion.mp h1 with ⟨m0, h2⟩
    rcases Set.mem_iUnion.mp h2 with ⟨m1, h3⟩
    exact Set.mem_iUnion.mpr ⟨(N, m0, m1), h3⟩
  · intro x hx
    have hmem := levelSet_quarter_subset_iUnion_digitClass k hx
    rcases Set.mem_iUnion.mp hmem with ⟨N, h1⟩
    rcases Set.mem_iUnion.mp h1 with ⟨m0, h2⟩
    rcases Set.mem_iUnion.mp h2 with ⟨m1, h3⟩
    exact Set.mem_iUnion.mpr ⟨(N, m0, m1), h3⟩
  · intro i
    exact mkMetric_digitClass_lt_top k i.1.1 i.1.2 i.2.1 i.2.2 m hm C
      (fun n hn => hbound n (le_trans i.1.2 hn))

/-! ## 第三部分：Corollary 14(iii) 规范比较与更大阶规范的非 $\sigma$-有限性 / 无穷测度定理 -/

/-- **规范比较引理**：
    设 $h, g : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$，$c \in \mathbb{R}_{\ge 0}$，
    若存在 $\delta > 0$ 使对一切 $r \le \delta$ 有 $h(r) \le c \cdot g(r)$，
    则对任意集合 $E \subseteq \mathbb{R}$，
    `Measure.mkMetric h E ≤ (c : ℝ≥0∞) * Measure.mkMetric g E`。 -/
theorem mkMetric_le_mul_of_eventually_le
    (h g : ℝ≥0∞ → ℝ≥0∞) {δ : ℝ≥0∞} (c : ℝ≥0) (hδ : 0 < δ)
    (hle : ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (c : ℝ≥0∞) * g r) (E : Set ℝ) :
    Measure.mkMetric h E ≤ (c : ℝ≥0∞) * Measure.mkMetric g E := by
  by_cases hc : c = 0
  · subst hc
    simp only [ENNReal.coe_zero, zero_mul] at hle ⊢
    rw [Measure.mkMetric_apply]
    refine iSup₂_le fun r hr => ?_
    set r' := min (min r δ) 1
    have hr'_pos : 0 < r' := lt_min (lt_min hr hδ) zero_lt_one
    have hr'_lt_top : r' < ⊤ := lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top
    set d : ℝ := r'.toReal
    have hd_pos : 0 < d := ENNReal.toReal_pos (ne_of_gt hr'_pos) (ne_of_lt hr'_lt_top)
    have hd_le_r : ENNReal.ofReal d ≤ r := by
      rw [ENNReal.ofReal_toReal (ne_of_lt hr'_lt_top)]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hd_le_δ : ENNReal.ofReal d ≤ δ := by
      rw [ENNReal.ofReal_toReal (ne_of_lt hr'_lt_top)]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    let e := (Denumerable.eqv ℤ).symm
    let t : ℕ → Set ℝ := fun n => Set.Icc ((e n : ℝ) * d) (((e n : ℝ) + 1) * d)
    have hcov : E ⊆ ⋃ n, t n := by
      intro x _
      set z : ℤ := Int.floor (x / d)
      refine Set.mem_iUnion.mpr ⟨(Denumerable.eqv ℤ) z, ?_⟩
      simp only [t, e, Equiv.symm_apply_apply]
      have hz1 : (z : ℝ) ≤ x / d := Int.floor_le (x / d)
      have hz2 : x / d < (z : ℝ) + 1 := Int.lt_floor_add_one (x / d)
      constructor
      · exact (le_div_iff₀ hd_pos).mp hz1
      · exact le_of_lt ((div_lt_iff₀ hd_pos).mp hz2)
    have hdiam : ∀ n, Metric.ediam (t n) ≤ r := fun n => by
      have hed : Metric.ediam (t n) = ENNReal.ofReal d := by
        dsimp [t]
        rw [Real.ediam_Icc]
        congr 1
        ring
      rw [hed]
      exact hd_le_r
    refine le_trans (iInf_le _ t) (le_trans (iInf_le _ hcov) (le_trans (iInf_le _ hdiam) ?_))
    have hzero : ∀ n, (⨆ _ : (t n).Nonempty, h (Metric.ediam (t n))) = 0 := fun n => by
      have hdm : Metric.ediam (t n) ≤ δ := by
        have hed : Metric.ediam (t n) = ENNReal.ofReal d := by
          dsimp [t]; rw [Real.ediam_Icc]; congr 1; ring
        rw [hed]; exact hd_le_δ
      have h0 : h (Metric.ediam (t n)) = 0 := le_antisymm (hle _ hdm) zero_le
      simp [h0]
    simp [hzero]
  · have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
    rw [Measure.mkMetric_apply, Measure.mkMetric_apply, ENNReal.mul_iSup]
    apply iSup₂_le
    intro r hr
    set r' := min r δ
    have hr'_pos : 0 < r' := lt_min hr hδ
    have hr'_le_r : r' ≤ r := min_le_left r δ
    have hr'_le_δ : r' ≤ δ := min_le_right r δ
    refine le_trans ?_ (le_iSup (f := fun r0 : ℝ≥0∞ =>
      (c : ℝ≥0∞) * ⨆ (_ : 0 < r0),
        ⨅ (t : ℕ → Set ℝ) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r0),
          ∑' n, ⨆ _ : (t n).Nonempty, g (Metric.ediam (t n))) r')
    rw [ENNReal.mul_iSup]
    refine le_trans ?_ (le_iSup (f := fun _ : 0 < r' =>
      (c : ℝ≥0∞) * ⨅ (t : ℕ → Set ℝ) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r'),
        ∑' n, ⨆ _ : (t n).Nonempty, g (Metric.ediam (t n))) hr'_pos)
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun t => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun hcov => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun hdiam => ?_
    have hdiam_r : ∀ n, Metric.ediam (t n) ≤ r := fun n => le_trans (hdiam n) hr'_le_r
    refine le_trans (iInf_le _ t) ?_
    refine le_trans (iInf_le _ hcov) ?_
    refine le_trans (iInf_le _ hdiam_r) ?_
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hne : (t n).Nonempty
    · simp [hne, hle (Metric.ediam (t n)) (le_trans (hdiam n) hr'_le_δ)]
    · simp [hne]

/-- **定理（小阶规范比 $\to 0$ 时，在有限大规范测度集上小规范测度必为 $0$）**：
    若对任意 $\varepsilon > 0$（$\varepsilon \in \mathbb{R}_{\ge 0}$），存在 $\delta > 0$ 使对一切 $r \le \delta$
    有 $h(r) \le \varepsilon \cdot g(r)$（即 $h(r)/g(r) \to 0$ 当 $r \to 0^+$），则对任意满足
    `Measure.mkMetric g E < ⊤` 的集合 $E \subseteq \mathbb{R}$，必有 `Measure.mkMetric h E = 0`。 -/
theorem mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top
    (h g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (ε : ℝ≥0∞) * g r)
    {E : Set ℝ} (hfin : Measure.mkMetric g E < ⊤) :
    Measure.mkMetric h E = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  simp only [zero_add]
  set M := (Measure.mkMetric g E).toNNReal + 1
  have hM_pos : (0 : ℝ≥0) < M := add_pos_of_nonneg_of_pos bot_le zero_lt_one
  set ε : ℝ≥0 := η / M
  have hε_pos : 0 < ε := div_pos hη hM_pos
  obtain ⟨δ, hδ_pos, hle⟩ := hratio ε hε_pos
  have hcomp := mkMetric_le_mul_of_eventually_le h g ε hδ_pos hle E
  have hMg : Measure.mkMetric g E ≤ (M : ℝ≥0∞) := by
    have h1 : ((Measure.mkMetric g E).toNNReal : ℝ≥0∞) = Measure.mkMetric g E :=
      ENNReal.coe_toNNReal (ne_of_lt hfin)
    dsimp [M]
    rw [h1]
    exact le_self_add
  calc Measure.mkMetric h E
      ≤ (ε : ℝ≥0∞) * Measure.mkMetric g E := hcomp
    _ ≤ (ε : ℝ≥0∞) * (M : ℝ≥0∞) := by gcongr
    _ = ((ε * M : ℝ≥0) : ℝ≥0∞) := by rfl
    _ = (η : ℝ≥0∞) := by
        congr 1
        dsimp [ε]
        exact div_mul_cancel₀ η (ne_of_gt hM_pos)

/-- **定理（Corollary 14(iii) 精确形式化：更大阶规范在正测度集上必为无穷测度且非 $\sigma$-有限）**：
    设规范函数 $h, g : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 满足 $h(r)/g(r) \to 0$（$r \to 0^+$），
    且集合 $S \subseteq \mathbb{R}$ 满足 `0 < Measure.mkMetric h S`。则：
    1. `Measure.mkMetric g S = ⊤`（无穷测度）；
    2. **不存在**可数族 $E : \mathbb{N} \to \mathrm{Set}\ \mathbb{R}$ 满足 $S \subseteq \bigcup_i E_i$ 且
       $\forall i,\ \mathrm{Measure.mkMetric}\ g\ (E_i) < \top$（即 $S$ 对 $\mathcal{H}^g$ **非 $\sigma$-有限**）。 -/
theorem not_countable_union_finite_of_ratio_tendsto_zero
    (h g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (ε : ℝ≥0∞) * g r)
    {S : Set ℝ} (hpos : 0 < Measure.mkMetric h S) :
    Measure.mkMetric g S = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, S ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  constructor
  · by_contra hne_top
    have hlt : Measure.mkMetric g S < ⊤ := lt_top_iff_ne_top.mpr hne_top
    have hzero := mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top h g hratio hlt
    exact (ne_of_gt hpos) hzero
  · rintro ⟨E, hcov, hfin⟩
    have hzero_i : ∀ i : ℕ, Measure.mkMetric h (E i) = 0 :=
      fun i => mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top h g hratio (hfin i)
    have hzero_union : Measure.mkMetric h (⋃ i, E i) = 0 :=
      measure_iUnion_null hzero_i
    have hzero_S : Measure.mkMetric h S = 0 :=
      measure_mono_null hcov hzero_union
    exact (ne_of_gt hpos) hzero_S

/-- **Remark 15 相邻能级规范分离定理**：
    对一切 $k \ge 1$，相邻能级临界规范比序列 $((2k-1)/(2k+1))^n \to 0$（$n \to \infty$）。 -/
theorem gauge_ratio_adjacent_levels_tendsto_zero (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun n : ℕ => ((2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1)) ^ n) atTop (nhds 0) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 < 2 * (k : ℝ) + 1 := by linarith
  have hnn : 0 ≤ (2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1) :=
    div_nonneg (by linarith) (le_of_lt hden_pos)
  have hlt1 : (2 * (k : ℝ) - 1) / (2 * (k : ℝ) + 1) < 1 :=
    (div_lt_one hden_pos).mpr (by linarith)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt1

/-! ## 第四部分：Theorem 16(ii) 无符号精确极限集的普适 $2$-叉树规范 $g_2$ 与临界规范 $h_k$ 零测度定理 -/

/-- 无符号精确极限集 $E_{\mathrm{lim}}(k/4) = \{x \in \mathbb{R} : \lim_{j\to\infty} j \|Q_j x\| = k/4\}$。 -/
def unsignedExactLimitSet (k : ℕ) : Set ℝ :=
  {x : ℝ | Tendsto (apprSeq x) atTop (nhds ((k : ℝ) / 4))}

/-- 二值数字字母表 $\{-k, k\}$（当 $k \ge 1$ 时恰有 $2$ 个元素）。 -/
def binaryAlphabet (k : ℕ) : Finset ℤ :=
  {-(k : ℤ), (k : ℤ)}

lemma mem_binaryAlphabet_iff (k : ℕ) (d : ℤ) :
    d ∈ binaryAlphabet k ↔ d = (k : ℤ) ∨ d = -(k : ℤ) := by
  simp only [binaryAlphabet, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma card_binaryAlphabet_le_two (k : ℕ) :
    (binaryAlphabet k).card ≤ 2 :=
  Finset.card_le_two

/-- 二值单步转移：给定第 $j$ 层相邻整数对 $p = (M_j, M_{j+1})$，仅用 $d \in \{-k, k\}$ 生成下一层对。 -/
def binaryStepPairs (k : ℕ) (j : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (binaryAlphabet k).image (fun d => (p.2, (4 * (j : ℤ) + 6) * p.2 + p.1 + d))

lemma card_binaryStepPairs_le (k : ℕ) (j : ℕ) (p : ℤ × ℤ) :
    (binaryStepPairs k j p).card ≤ 2 :=
  le_trans Finset.card_image_le (card_binaryAlphabet_le_two k)

/-- 从起点下标 $N$ 与初始对 $(m_0, m_1)$ 出发的 $n$ 步二值存活整数对树 `binaryPairTree`。 -/
def binaryPairTree (k : ℕ) (N : ℕ) (m0 m1 : ℤ) : ℕ → Finset (ℤ × ℤ)
  | 0 => {(m0, m1)}
  | n + 1 => (binaryPairTree k N m0 m1 n).biUnion (fun p => binaryStepPairs k (N + n) p)

lemma binaryPairTree_succ (k N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    binaryPairTree k N m0 m1 (n + 1) =
      (binaryPairTree k N m0 m1 n).biUnion (fun p => binaryStepPairs k (N + n) p) := rfl

lemma card_binaryPairTree_le (k N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    (binaryPairTree k N m0 m1 n).card ≤ 2 ^ n := by
  induction n with
  | zero => simp [binaryPairTree]
  | succ n ih =>
      rw [binaryPairTree_succ]
      have hstep : ∀ p ∈ binaryPairTree k N m0 m1 n, (binaryStepPairs k (N + n) p).card ≤ 2 :=
        fun p _ => card_binaryStepPairs_le k (N + n) p
      calc ((binaryPairTree k N m0 m1 n).biUnion (fun p => binaryStepPairs k (N + n) p)).card
          ≤ (binaryPairTree k N m0 m1 n).card * 2 :=
            Finset.card_biUnion_le_card_mul _ _ _ hstep
        _ ≤ 2 ^ n * 2 := Nat.mul_le_mul_right _ ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]

/-- 固定起点 $N$、初值 $(m_0, m_1)$ 且尾部数字 $d'_j(x) \in \{-k, k\}$（$j \ge N$）的二值数字类。 -/
def binaryDigitClass (k : ℕ) (N : ℕ) (m0 m1 : ℤ) : Set ℝ :=
  {x : ℝ | nearestInt ((Qsel N : ℝ) * x) = m0 ∧
           nearestInt ((Qsel (N + 1) : ℝ) * x) = m1 ∧
           ∀ j : ℕ, N ≤ j → defectShift x j = (k : ℤ) ∨ defectShift x j = -(k : ℤ)}

lemma mem_binaryPairTree_of_mem_binaryDigitClass {k N : ℕ} {m0 m1 : ℤ} {x : ℝ}
    (hx : x ∈ binaryDigitClass k N m0 m1) (n : ℕ) :
    (nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)) ∈
      binaryPairTree k N m0 m1 n := by
  rcases hx with ⟨hm0, hm1, hdef⟩
  induction n with
  | zero => simp [binaryPairTree, hm0, hm1]
  | succ n ih =>
      rw [binaryPairTree_succ, Finset.mem_biUnion]
      refine ⟨(nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)), ih, ?_⟩
      unfold binaryStepPairs
      rw [Finset.mem_image]
      refine ⟨defectShift x (N + n), ?_, ?_⟩
      · rw [mem_binaryAlphabet_iff]
        exact hdef (N + n) (by omega)
      · ext
        · rfl
        · dsimp
          exact (nearestInt_add_two_eq x (N + n)).symm

lemma binaryDigitClass_cover (k N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    binaryDigitClass k N m0 m1 ⊆
      ⋃ p : (binaryPairTree k N m0 m1 n : Set (ℤ × ℤ)), gaugeInterv (N + n) p.1.1 := by
  intro x hx
  have hmem := mem_binaryPairTree_of_mem_binaryDigitClass hx n
  have hinterv := mem_gaugeInterv_nearestInt x (N + n)
  refine Set.mem_iUnion.mpr ?_
  exact ⟨⟨(nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)), hmem⟩, hinterv⟩

/-- 无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 包含于二值数字类 `binaryDigitClass k N m0 m1` 的可数并。 -/
lemma unsignedExactLimitSet_subset_iUnion_binaryDigitClass (k : ℕ) :
    unsignedExactLimitSet k ⊆
      ⋃ (N : {N : ℕ // 1 ≤ N}) (m0 : ℤ) (m1 : ℤ), binaryDigitClass k N.1 m0 m1 := by
  intro x hx
  have hbin := (FullSpectrumDiscrete.unsigned_exact_limit_iff_defect_binary x k).mp hx
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hbin.2
  set N := max 1 N0
  have hN1 : 1 ≤ N := le_max_left _ _
  have hdef : ∀ j : ℕ, N ≤ j → defectShift x j = (k : ℤ) ∨ defectShift x j = -(k : ℤ) := by
    intro j hj
    rw [defectShift_eq_defect_succ]
    exact hN0 (j + 1) (by omega)
  refine Set.mem_iUnion.mpr ⟨⟨N, hN1⟩, ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel N : ℝ) * x), ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel (N + 1) : ℝ) * x), ?_⟩
  exact ⟨rfl, rfl, hdef⟩

/-- 二值数字类的规范零测度引理：若 $2^n m(1/Q_{N+n}) \to 0$，则 `Measure.mkMetric m (binaryDigitClass k N m0 m1) = 0`。 -/
theorem mkMetric_binaryDigitClass_null (k N : ℕ) (m0 m1 : ℤ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m)
    (hcost : Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ≥0∞) *
      m (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ)))) atTop (nhds 0)) :
    Measure.mkMetric m (binaryDigitClass k N m0 m1) = 0 := by
  let ι : ℕ → Type _ := fun n => {p // p ∈ binaryPairTree k N m0 m1 n}
  let radSeq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))
  let cov : ∀ n, ι n → Set ℝ := fun n p => gaugeInterv (N + n) p.1.1
  have hr : Tendsto radSeq atTop (nhds 0) := tendsto_inv_Qsel_shift N
  have ht_diam : ∀ᶠ n in atTop, ∀ p : ι n, Metric.ediam (cov n p) ≤ radSeq n :=
    Filter.Eventually.of_forall (fun n p => ediam_gaugeInterv_le (N + n) p.1.1)
  have hst : ∀ᶠ n in atTop, binaryDigitClass k N m0 m1 ⊆ ⋃ p : ι n, cov n p :=
    Filter.Eventually.of_forall (fun n => binaryDigitClass_cover k N m0 m1 n)
  have hmain := MeasureTheory.Measure.mkMetric_le_liminf_sum
    (binaryDigitClass k N m0 m1) radSeq hr cov ht_diam hst m
  have hsum_le : ∀ n : ℕ, ∑ p : ι n, m (Metric.ediam (cov n p)) ≤
      ((2 ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
    intro n
    calc ∑ p : ι n, m (Metric.ediam (cov n p))
        ≤ ∑ _p : ι n, m (radSeq n) :=
          Finset.sum_le_sum (fun p _ => hm (ediam_gaugeInterv_le (N + n) p.1.1))
      _ = ((binaryPairTree k N m0 m1 n).card : ℝ≥0∞) * m (radSeq n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp [ι]
          rw [Fintype.card_coe]
      _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
          gcongr
          exact_mod_cast card_binaryPairTree_le k N m0 m1 n
  have hlim : Filter.liminf (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop ≤ 0 := by
    have hle' : ∀ᶠ n in atTop, (∑ p : ι n, m (Metric.ediam (cov n p))) ≤
        ((2 ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) :=
      Filter.Eventually.of_forall hsum_le
    have hlimsup0 : Filter.limsup (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop ≤ 0 := by
      have hmono := Filter.limsup_le_limsup hle'
      have heq := hcost.limsup_eq
      rwa [heq] at hmono
    exact le_trans Filter.liminf_le_limsup hlimsup0
  have hlim0 : Filter.liminf (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop = 0 :=
    le_antisymm hlim bot_le
  rw [hlim0] at hmain
  exact le_antisymm hmain bot_le

/-- 二值数字类在普适基数 $2$ 规范 $m(1/Q_n) \le C \cdot 2^{-n}$ 下的有限测度上界：
    `Measure.mkMetric m (binaryDigitClass k N m0 m1) ≤ ENNReal.ofReal (max C 0 * 2 ^ (-N))`。 -/
theorem mkMetric_binaryDigitClass_le (k N : ℕ) (_hN : 1 ≤ N) (m0 m1 : ℤ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, N ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-(n : ℤ)))) :
    Measure.mkMetric m (binaryDigitClass k N m0 m1) ≤
      ENNReal.ofReal (max C 0 * (2 : ℝ) ^ (-(N : ℤ))) := by
  let ι : ℕ → Type _ := fun n => {p // p ∈ binaryPairTree k N m0 m1 n}
  let radSeq : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))
  let cov : ∀ n, ι n → Set ℝ := fun n p => gaugeInterv (N + n) p.1.1
  have hr : Tendsto radSeq atTop (nhds 0) := tendsto_inv_Qsel_shift N
  have ht_diam : ∀ᶠ n in atTop, ∀ p : ι n, Metric.ediam (cov n p) ≤ radSeq n :=
    Filter.Eventually.of_forall (fun n p => ediam_gaugeInterv_le (N + n) p.1.1)
  have hst : ∀ᶠ n in atTop, binaryDigitClass k N m0 m1 ⊆ ⋃ p : ι n, cov n p :=
    Filter.Eventually.of_forall (fun n => binaryDigitClass_cover k N m0 m1 n)
  have hmain := MeasureTheory.Measure.mkMetric_le_liminf_sum
    (binaryDigitClass k N m0 m1) radSeq hr cov ht_diam hst m
  set C' := max C 0
  have hsum_le : ∀ n : ℕ, ∑ p : ι n, m (Metric.ediam (cov n p)) ≤
      ENNReal.ofReal (C' * (2 : ℝ) ^ (-(N : ℤ))) := by
    intro n
    have h2_zpow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-((N + n : ℕ) : ℤ)) := by positivity
    have hCC' : C * (2 : ℝ) ^ (-((N + n : ℕ) : ℤ)) ≤ C' * (2 : ℝ) ^ (-((N + n : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) h2_zpow_nn
    have hcast_2 : ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    have halg : (2 : ℝ) ^ n * (C' * (2 : ℝ) ^ (-((N + n : ℕ) : ℤ))) = C' * (2 : ℝ) ^ (-(N : ℤ)) := by
      rw [zpow_neg, zpow_natCast, pow_add, zpow_neg, zpow_natCast]
      have h2N : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N (by norm_num)
      have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp
    calc ∑ p : ι n, m (Metric.ediam (cov n p))
        ≤ ∑ _p : ι n, m (radSeq n) :=
          Finset.sum_le_sum (fun p _ => hm (ediam_gaugeInterv_le (N + n) p.1.1))
      _ = ((binaryPairTree k N m0 m1 n).card : ℝ≥0∞) * m (radSeq n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp [ι]
          rw [Fintype.card_coe]
      _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
          gcongr
          exact_mod_cast card_binaryPairTree_le k N m0 m1 n
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (C' * (2 : ℝ) ^ (-((N + n : ℕ) : ℤ))) := by
          rw [hcast_2]
          gcongr
          exact le_trans (hbound (N + n) (by omega)) (ENNReal.ofReal_le_ofReal hCC')
      _ = ENNReal.ofReal ((2 : ℝ) ^ n * (C' * (2 : ℝ) ^ (-((N + n : ℕ) : ℤ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (C' * (2 : ℝ) ^ (-(N : ℤ))) := by rw [halg]
  have hlim : Filter.liminf (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop ≤
      ENNReal.ofReal (C' * (2 : ℝ) ^ (-(N : ℤ))) :=
    Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hsum_le)
  exact le_trans hmain hlim

/-- **定理（Theorem 16(ii) 第一部分：对一切 $k \ge 1$，无符号精确极限集在临界规范 $h_k$ 下测度为 $0$）**：
    由于 $2 < 2k+1$ 对一切 $k \ge 1$ 成立，只要单调函数 $m$ 满足 $m(1/Q_n) \le C (2k+1)^{-n}$，就有
    `Measure.mkMetric m (unsignedExactLimitSet k) = 0`。 -/
theorem mkMetric_unsignedExactLimit_null_of_hk (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-(n : ℤ)))) :
    Measure.mkMetric m (unsignedExactLimitSet k) = 0 := by
  apply measure_mono_null (unsignedExactLimitSet_subset_iUnion_binaryDigitClass k)
  apply measure_iUnion_null
  intro N
  apply measure_iUnion_null
  intro m0
  apply measure_iUnion_null
  intro m1
  apply mkMetric_binaryDigitClass_null k N.1 m0 m1 m hm
  set C' := max C 0
  set b : ℝ := 2 * (k : ℝ) + 1
  have hb_gt2 : (2 : ℝ) < b := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    dsimp [b]; linarith
  have hb_pos : 0 < b := by linarith
  have hratio_nn : 0 ≤ (2 : ℝ) / b := div_nonneg (by norm_num) (le_of_lt hb_pos)
  have hratio_lt : (2 : ℝ) / b < 1 := (div_lt_one hb_pos).mpr hb_gt2
  have hpow0 : Tendsto (fun n : ℕ => ((2 : ℝ) / b) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt
  have hreal0 : Tendsto (fun n : ℕ => (C' / b ^ N.1) * ((2 : ℝ) / b) ^ n) atTop (nhds 0) := by
    simpa using hpow0.const_mul (C' / b ^ N.1)
  have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal ((C' / b ^ N.1) * ((2 : ℝ) / b) ^ n))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hreal0
  have hle : ∀ n : ℕ,
      ((2 ^ n : ℕ) : ℝ≥0∞) * m (ENNReal.ofReal (1 / (Qsel (N.1 + n) : ℝ))) ≤
      ENNReal.ofReal ((C' / b ^ N.1) * ((2 : ℝ) / b) ^ n) := by
    intro n
    have hb_zpow_nn : 0 ≤ b ^ (-((N.1 + n : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb_pos) _
    have hCC' : C * b ^ (-((N.1 + n : ℕ) : ℤ)) ≤ C' * b ^ (-((N.1 + n : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hb_zpow_nn
    have hcast_2 : ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    have halg : (2 : ℝ) ^ n * (C' * b ^ (-((N.1 + n : ℕ) : ℤ))) = (C' / b ^ N.1) * ((2 : ℝ) / b) ^ n := by
      rw [zpow_neg, zpow_natCast, pow_add, div_pow]
      have hbN : b ^ N.1 ≠ 0 := pow_ne_zero N.1 (ne_of_gt hb_pos)
      have hbn : b ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      field_simp
    calc ((2 ^ n : ℕ) : ℝ≥0∞) * m (ENNReal.ofReal (1 / (Qsel (N.1 + n) : ℝ)))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal (C' * b ^ (-((N.1 + n : ℕ) : ℤ))) := by
          rw [hcast_2]
          gcongr
          exact le_trans (hbound (N.1 + n) (by omega)) (ENNReal.ofReal_le_ofReal hCC')
      _ = ENNReal.ofReal ((2 : ℝ) ^ n * (C' * b ^ (-((N.1 + n : ℕ) : ℤ)))) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((C' / b ^ N.1) * ((2 : ℝ) / b) ^ n) := by rw [halg]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof0
    (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall hle)

/-- **定理（Theorem 16(ii) 第二部分：无符号精确极限集在一切次临界规范 $2^n g(1/Q_n) \to 0$ 下测度为 $0$）**：
    对任意 $k \in \mathbb{N}$ 与满足 $2^n g(1/Q_n) \to 0$ 的单调函数 $g$，
    `Measure.mkMetric g (unsignedExactLimitSet k) = 0`。 -/
theorem mkMetric_unsignedExactLimit_null_of_subgauge_base2 (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hsub : Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ≥0∞) *
      g (ENNReal.ofReal (1 / (Qsel n : ℝ)))) atTop (nhds 0)) :
    Measure.mkMetric g (unsignedExactLimitSet k) = 0 := by
  apply measure_mono_null (unsignedExactLimitSet_subset_iUnion_binaryDigitClass k)
  apply measure_iUnion_null
  intro N
  apply measure_iUnion_null
  intro m0
  apply measure_iUnion_null
  intro m1
  apply mkMetric_binaryDigitClass_null k N.1 m0 m1 g hg
  have hshift : Tendsto (fun n : ℕ => N.1 + n) atTop atTop :=
    (tendsto_add_atTop_nat N.1).congr (fun n => Nat.add_comm n N.1)
  have hcomp : Tendsto (fun n : ℕ => ((2 ^ (N.1 + n) : ℕ) : ℝ≥0∞) *
      g (ENNReal.ofReal (1 / (Qsel (N.1 + n) : ℝ)))) atTop (nhds 0) :=
    hsub.comp hshift
  have hle : ∀ n : ℕ,
      ((2 ^ n : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (Qsel (N.1 + n) : ℝ))) ≤
      ((2 ^ (N.1 + n) : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (Qsel (N.1 + n) : ℝ))) := by
    intro n
    have hpow : ((2 ^ n : ℕ) : ℝ≥0∞) ≤ ((2 ^ (N.1 + n) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    exact mul_le_mul_of_nonneg_right hpow bot_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
    (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall hle)

/-- **定理（Theorem 16(ii) 第三部分：无符号精确极限集在普适规范 $g_2$ 下的 $\sigma$-有限可数覆盖分解）**：
    若单调函数 $m$ 满足 $m(1/Q_n) \le C \cdot 2^{-n}$，则 $E_{\mathrm{lim}}(k/4)$ 可表为可数个
    `Measure.mkMetric m` 测度有限集合之并。 -/
theorem unsignedExactLimit_countable_cover_finite_mkMetric_base2 (k : ℕ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-(n : ℤ)))) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      unsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric m (E i) < ⊤ := by
  refine ⟨fun i => binaryDigitClass k i.1.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro x hx
    have hmem := unsignedExactLimitSet_subset_iUnion_binaryDigitClass k hx
    rcases Set.mem_iUnion.mp hmem with ⟨N, h1⟩
    rcases Set.mem_iUnion.mp h1 with ⟨m0, h2⟩
    rcases Set.mem_iUnion.mp h2 with ⟨m1, h3⟩
    exact Set.mem_iUnion.mpr ⟨(N, m0, m1), h3⟩
  · intro i
    exact lt_of_le_of_lt
      (mkMetric_binaryDigitClass_le k i.1.1 i.1.2 i.2.1 i.2.2 m hm C
        (fun n hn => hbound n (le_trans i.1.2 hn)))
      ENNReal.ofReal_lt_top

/-! ## 第五部分：Theorem 13 临界规范正测度下界与精确水平集无穷测度定理 -/

/-- 均匀 $(2k+1)$-叉 Cantor 树的起始层级 $J_k = 2k + 2$。 -/
def J_cantor (k : ℕ) : ℕ := 2 * k + 2

/-- 将 `Fin (2 * k + 1)` 映射到数字字母表 `{-k, ..., k}`。 -/
def digitOf (k : ℕ) (a : Fin (2 * k + 1)) : ℤ :=
  (a.1 : ℤ) - (k : ℤ)

lemma abs_digitOf_le (k : ℕ) (a : Fin (2 * k + 1)) :
    |digitOf k a| ≤ (k : ℤ) := by
  unfold digitOf
  rw [abs_le]
  omega

lemma digitOf_injective (k : ℕ) : Function.Injective (digitOf k) := by
  intro a b h
  unfold digitOf at h
  ext
  omega

/-- 沿 $w : \mathrm{Fin}\ n \to \mathrm{Fin}(2k+1)$ 递推生成的整数对 $(M_{J+n}, M_{J+n+1})$。 -/
def pairOfWord (k : ℕ) : ∀ n : ℕ, (Fin n → Fin (2 * k + 1)) → ℤ × ℤ
  | 0, _ => (0, 0)
  | n + 1, w =>
      let p := pairOfWord k n (Fin.init w)
      (p.2, (4 * ((J_cantor k + n : ℕ) : ℤ) + 6) * p.2 + p.1 + digitOf k (w (Fin.last n)))

/-- 第 $n$ 级中心整数 $M_{J+n+1}(w)$。 -/
def centerIntC (k n : ℕ) (w : Fin n → Fin (2 * k + 1)) : ℤ :=
  (pairOfWord k n w).2

/-- 截取长度为 $n \le N$ 的前缀词。 -/
def prefixWordC {k n N : ℕ} (h : n ≤ N) (w : Fin N → Fin (2 * k + 1)) :
    Fin n → Fin (2 * k + 1) :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

lemma prefixWordC_self {k n : ℕ} (w : Fin n → Fin (2 * k + 1)) :
    prefixWordC (le_refl n) w = w := by
  ext i; rfl

/-- 向右补零延拓词以构造嵌套子柱集。 -/
def extendZeroC (k : ℕ) {n : ℕ} (u : Fin n → Fin (2 * k + 1)) (m : ℕ) :
    Fin (n + m) → Fin (2 * k + 1) :=
  fun i => if hi : i.1 < n then u ⟨i.1, hi⟩ else ⟨0, by omega⟩

lemma extendZeroC_zero (k : ℕ) {n : ℕ} (u : Fin n → Fin (2 * k + 1)) :
    extendZeroC k u 0 = u := by
  funext ⟨i, hi⟩
  have hin : i < n := by omega
  simp [extendZeroC, hin]

lemma prefix_extendZeroC (k : ℕ) {n : ℕ} (u : Fin n → Fin (2 * k + 1)) (m : ℕ) :
    prefixWordC (Nat.le_add_right n m) (extendZeroC k u m) = u := by
  funext i
  simp [prefixWordC, extendZeroC, i.2]

lemma Qsel_succ_ge_mul (m : ℕ) (hm : 1 ≤ m) :
    (4 * (m : ℝ) + 2) * (Qsel m : ℝ) ≤ (Qsel (m + 1) : ℝ) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hrec : (Qsel (t + 2) : ℝ) = (4 * (t : ℝ) + 6) * (Qsel (t + 1) : ℝ) + (Qsel t : ℝ) := by
    exact_mod_cast Classification.Qsel_rec t
  have hQ0 : (0 : ℝ) ≤ (Qsel t : ℝ) := by
    cases t with
    | zero => norm_num [Qsel]
    | succ s => exact_mod_cast (Qsel_pos (s + 1) (by omega) |>.le)
  have hcast : 4 * ((t + 1 : ℕ) : ℝ) + 2 = 4 * (t : ℝ) + 6 := by push_cast; ring
  rw [hcast, hrec]
  linarith

lemma Qsel_succ_ge_four_mul (m : ℕ) (hm : 1 ≤ m) :
    4 * (Qsel m : ℝ) ≤ (Qsel (m + 1) : ℝ) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hQpos : (0 : ℝ) ≤ (Qsel m : ℝ) := by
    exact_mod_cast (Qsel_pos m (by omega) |>.le)
  calc 4 * (Qsel m : ℝ)
      ≤ (4 * (m : ℝ) + 2) * (Qsel m : ℝ) := by nlinarith
    _ ≤ (Qsel (m + 1) : ℝ) := Qsel_succ_ge_mul m hm

/-- 交错行列式 $\Delta_n(w) = M_{J+n+1} Q_{J+n} - M_{J+n} Q_{J+n+1}$ 满足 $|\Delta_n(w)| \le (k+1) Q_{J+n}$。 -/
lemma abs_det_pairOfWord_le (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (w : Fin n → Fin (2 * k + 1)) :
    |(pairOfWord k n w).2 * (Qsel (J_cantor k + n) : ℤ) -
      (pairOfWord k n w).1 * (Qsel (J_cantor k + n + 1) : ℤ)| ≤
      ((k : ℤ) + 1) * (Qsel (J_cantor k + n) : ℤ) := by
  induction n with
  | zero =>
      simp only [pairOfWord, zero_mul, sub_self, abs_zero]
      exact mul_nonneg (by omega) (Qsel_pos (J_cantor k + 0) (by unfold J_cantor; omega) |>.le)
  | succ n ih =>
      set p := pairOfWord k n (Fin.init w)
      set d := digitOf k (w (Fin.last n))
      have hQrec : Qsel (J_cantor k + n + 2) =
          (4 * (J_cantor k + n) + 6) * Qsel (J_cantor k + n + 1) + Qsel (J_cantor k + n) :=
        Classification.Qsel_rec (J_cantor k + n)
      have hdet_eq :
          (pairOfWord k (n + 1) w).2 * (Qsel (J_cantor k + (n + 1)) : ℤ) -
            (pairOfWord k (n + 1) w).1 * (Qsel (J_cantor k + (n + 1) + 1) : ℤ) =
          -(p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ)) +
            d * (Qsel (J_cantor k + n + 1) : ℤ) := by
        change ((4 * ((J_cantor k + n : ℕ) : ℤ) + 6) * p.2 + p.1 + d) *
            (Qsel (J_cantor k + n + 1) : ℤ) -
            p.2 * (Qsel (J_cantor k + n + 2) : ℤ) = _
        have hQrecZ : (Qsel (J_cantor k + n + 2) : ℤ) =
            (4 * ((J_cantor k + n : ℕ) : ℤ) + 6) * (Qsel (J_cantor k + n + 1) : ℤ) +
              (Qsel (J_cantor k + n) : ℤ) := by
          exact_mod_cast hQrec
        rw [hQrecZ]
        ring
      rw [hdet_eq]
      have htri : |-(p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ)) +
          d * (Qsel (J_cantor k + n + 1) : ℤ)| ≤
          |p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ)| +
            |d| * (Qsel (J_cantor k + n + 1) : ℤ) := by
        calc |-(p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ)) +
              d * (Qsel (J_cantor k + n + 1) : ℤ)|
            ≤ |-(p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ))| +
                |d * (Qsel (J_cantor k + n + 1) : ℤ)| := abs_add_le _ _
          _ = |p.2 * (Qsel (J_cantor k + n) : ℤ) - p.1 * (Qsel (J_cantor k + n + 1) : ℤ)| +
                |d| * |(Qsel (J_cantor k + n + 1) : ℤ)| := by rw [abs_neg, abs_mul]
          _ = _ := by
                congr 2
                exact abs_of_nonneg (Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega) |>.le)
      have ih' := ih (Fin.init w)
      have hd : |d| ≤ (k : ℤ) := abs_digitOf_le k (w (Fin.last n))
      have hQ_ge : ((k : ℤ) + 1) * (Qsel (J_cantor k + n) : ℤ) ≤
          (Qsel (J_cantor k + n + 1) : ℤ) := by
        have h1 : (4 * ((J_cantor k + n : ℕ) : ℝ) + 2) * (Qsel (J_cantor k + n) : ℝ) ≤
            (Qsel (J_cantor k + n + 1) : ℝ) :=
          Qsel_succ_ge_mul (J_cantor k + n) (by unfold J_cantor; omega)
        have h2 : ((k : ℝ) + 1) * (Qsel (J_cantor k + n) : ℝ) ≤
            (4 * ((J_cantor k + n : ℕ) : ℝ) + 2) * (Qsel (J_cantor k + n) : ℝ) := by
          have hkR : (k : ℝ) + 1 ≤ 4 * ((J_cantor k + n : ℕ) : ℝ) + 2 := by
            unfold J_cantor
            push_cast
            linarith
          have hQnnR : (0 : ℝ) ≤ (Qsel (J_cantor k + n) : ℝ) := by
            exact_mod_cast (Qsel_pos (J_cantor k + n) (by unfold J_cantor; omega) |>.le)
          exact mul_le_mul_of_nonneg_right hkR hQnnR
        exact_mod_cast le_trans h2 h1
      have hQnn : (0 : ℤ) ≤ (Qsel (J_cantor k + n + 1) : ℤ) :=
        Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega) |>.le
      have hmuld : |d| * (Qsel (J_cantor k + n + 1) : ℤ) ≤ (k : ℤ) * (Qsel (J_cantor k + n + 1) : ℤ) :=
        mul_le_mul_of_nonneg_right hd hQnn
      have hadd : J_cantor k + (n + 1) = J_cantor k + n + 1 := by omega
      rw [hadd]
      linarith

/-- 第 $n$ 级柱集半径 $r_n = (2k+2) / Q_{J+n+2}$。 -/
def radC (k n : ℕ) : ℝ :=
  (2 * (k : ℝ) + 2) / (Qsel (J_cantor k + n + 2) : ℝ)

lemma radC_pos (k n : ℕ) : 0 < radC k n := by
  unfold radC
  have hQ : 0 < (Qsel (J_cantor k + n + 2) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 2) (by unfold J_cantor; omega)
  positivity

lemma radC_le_quarter_inv (k n : ℕ) (hk : 1 ≤ k) :
    radC k n ≤ 1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) := by
  unfold radC
  have hQ1 : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have hQ2 : 0 < (Qsel (J_cantor k + n + 2) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 2) (by unfold J_cantor; omega)
  rw [div_le_div_iff₀ hQ2 (by positivity)]
  have hrec := Qsel_succ_ge_mul (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have h1 : (2 * (k : ℝ) + 2) * 4 ≤ 4 * ((J_cantor k + n + 1 : ℕ) : ℝ) + 2 := by
    unfold J_cantor
    push_cast
    linarith
  calc (2 * (k : ℝ) + 2) * (4 * (Qsel (J_cantor k + n + 1) : ℝ))
      = ((2 * (k : ℝ) + 2) * 4) * (Qsel (J_cantor k + n + 1) : ℝ) := by ring
    _ ≤ (4 * ((J_cantor k + n + 1 : ℕ) : ℝ) + 2) * (Qsel (J_cantor k + n + 1) : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hQ1)
    _ ≤ (Qsel (J_cantor k + n + 1 + 1) : ℝ) := hrec
    _ = 1 * (Qsel (J_cantor k + n + 2) : ℝ) := by simp

/-- 第 $n$ 级柱集闭区间 $I_n(w)$。 -/
def cIntervC (k n : ℕ) (w : Fin n → Fin (2 * k + 1)) : Set ℝ :=
  Set.Icc ((centerIntC k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - radC k n)
          ((centerIntC k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) + radC k n)

lemma isCompact_cIntervC (k n : ℕ) (w : Fin n → Fin (2 * k + 1)) :
    IsCompact (cIntervC k n w) := isCompact_Icc

lemma isClosed_cIntervC (k n : ℕ) (w : Fin n → Fin (2 * k + 1)) :
    IsClosed (cIntervC k n w) := isClosed_Icc

lemma cIntervC_nonempty (k n : ℕ) (w : Fin n → Fin (2 * k + 1)) :
    (cIntervC k n w).Nonempty := by
  refine ⟨(centerIntC k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ), ?_⟩
  have hr := le_of_lt (radC_pos k n)
  exact ⟨by linarith, by linarith⟩

/-- 柱集嵌套性：$I_{n+1}(w) \subseteq I_n(\mathrm{init}(w))$。 -/
lemma cIntervC_succ_subset (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (w : Fin (n + 1) → Fin (2 * k + 1)) :
    cIntervC k (n + 1) w ⊆ cIntervC k n (Fin.init w) := by
  intro x hx
  have hQ1 : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have hQ2 : 0 < (Qsel (J_cantor k + n + 2) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 2) (by unfold J_cantor; omega)
  have hQ3 : 0 < (Qsel (J_cantor k + n + 3) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 3) (by unfold J_cantor; omega)
  have hdet : |(centerIntC k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
      (centerIntC k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)| ≤
      ((k : ℝ) + 1) * (Qsel (J_cantor k + n + 1) : ℝ) := by
    have h1 := abs_det_pairOfWord_le k hk (n + 1) w
    have h1' : ((pairOfWord k (n + 1) w).2 : ℝ) = (centerIntC k (n + 1) w : ℝ) := rfl
    have h2' : ((pairOfWord k (n + 1) w).1 : ℝ) = (centerIntC k n (Fin.init w) : ℝ) := rfl
    have hR : |((pairOfWord k (n + 1) w).2 : ℝ) * (Qsel (J_cantor k + (n + 1)) : ℝ) -
        ((pairOfWord k (n + 1) w).1 : ℝ) * (Qsel (J_cantor k + (n + 1) + 1) : ℝ)| ≤
        ((k : ℝ) + 1) * (Qsel (J_cantor k + (n + 1)) : ℝ) := by
      exact_mod_cast h1
    simpa [h1', h2', add_assoc] using hR
  have hcdiff : |(centerIntC k (n + 1) w : ℝ) / (Qsel (J_cantor k + n + 2) : ℝ) -
      (centerIntC k n (Fin.init w) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤
      ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) := by
    have heq : (centerIntC k (n + 1) w : ℝ) / (Qsel (J_cantor k + n + 2) : ℝ) -
        (centerIntC k n (Fin.init w) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
        ((centerIntC k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) /
          ((Qsel (J_cantor k + n + 1) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) := by
      field_simp
    rw [heq, abs_div, abs_of_pos (mul_pos hQ1 hQ2), div_le_div_iff₀ (mul_pos hQ1 hQ2) hQ2]
    calc |(centerIntC k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
            (centerIntC k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)| *
            (Qsel (J_cantor k + n + 2) : ℝ)
        ≤ (((k : ℝ) + 1) * (Qsel (J_cantor k + n + 1) : ℝ)) * (Qsel (J_cantor k + n + 2) : ℝ) :=
          mul_le_mul_of_nonneg_right hdet (le_of_lt hQ2)
      _ = ((k : ℝ) + 1) * ((Qsel (J_cantor k + n + 1) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) := by
          ring
  have hrad_succ : radC k (n + 1) ≤ ((k : ℝ) + 1) / (2 * (Qsel (J_cantor k + n + 2) : ℝ)) := by
    unfold radC
    rw [div_le_div_iff₀ (by simpa [add_assoc] using hQ3) (by positivity)]
    have h4 : 4 * (Qsel (J_cantor k + n + 2) : ℝ) ≤ (Qsel (J_cantor k + n + 3) : ℝ) :=
      Qsel_succ_ge_four_mul (J_cantor k + n + 2) (by unfold J_cantor; omega)
    have h4' : 4 * (Qsel (J_cantor k + n + 2) : ℝ) ≤ (Qsel (J_cantor k + (n + 1) + 2) : ℝ) := by
      simpa [add_assoc] using h4
    nlinarith
  have hrad_sum : ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) + radC k (n + 1) ≤ radC k n := by
    have h1 : radC k n = (2 * ((k : ℝ) + 1)) / (Qsel (J_cantor k + n + 2) : ℝ) := by
      unfold radC; ring_nf
    rw [h1]
    have h2 : ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) +
        ((k : ℝ) + 1) / (2 * (Qsel (J_cantor k + n + 2) : ℝ)) ≤
        (2 * ((k : ℝ) + 1)) / (Qsel (J_cantor k + n + 2) : ℝ) := by
      have h32 : ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) +
          ((k : ℝ) + 1) / (2 * (Qsel (J_cantor k + n + 2) : ℝ)) =
          (3 / 2 : ℝ) * (((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ)) := by ring
      rw [h32]
      have hpos_div : 0 ≤ ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) := by positivity
      have h2eq : (2 * ((k : ℝ) + 1)) / (Qsel (J_cantor k + n + 2) : ℝ) =
          2 * (((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ)) := by ring
      rw [h2eq]
      linarith
    linarith
  rcases hx with ⟨hxL, hxR⟩
  have hadd : J_cantor k + (n + 1) + 1 = J_cantor k + n + 2 := by omega
  rw [hadd] at hxL hxR
  have hc_abs := abs_le.mp hcdiff
  constructor <;> linarith

lemma cIntervC_prefix_subset (k : ℕ) (hk : 1 ≤ k) {n N : ℕ} (h : n ≤ N)
    (w : Fin N → Fin (2 * k + 1)) :
    cIntervC k N w ⊆ cIntervC k n (prefixWordC h w) := by
  induction N with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      rw [prefixWordC_self]
  | succ N ih =>
      rcases eq_or_lt_of_le h with rfl | hlt
      · rw [prefixWordC_self]
      · have hle : n ≤ N := Nat.le_of_lt_succ hlt
        calc cIntervC k (N + 1) w
            ⊆ cIntervC k N (Fin.init w) := cIntervC_succ_subset k hk N w
          _ ⊆ cIntervC k n (prefixWordC hle (Fin.init w)) := ih hle (Fin.init w)
          _ = cIntervC k n (prefixWordC h w) := by ext i; rfl

/-- `centerIntC k n` 在长度 $n$ 的词上单射。 -/
lemma centerIntC_injective (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    Function.Injective (centerIntC k n) := by
  intro w1 w2 heq
  by_contra hne
  have hex : ∃ i : ℕ, ∃ hi : i < n, w1 ⟨i, hi⟩ ≠ w2 ⟨i, hi⟩ := by
    by_contra hno
    push_neg at hno
    apply hne
    funext ⟨i, hi⟩
    exact hno i hi
  classical
  let i0 := Nat.find hex
  have hi0_spec := Nat.find_spec hex
  have hi0_lt : i0 < n := hi0_spec.1
  have hi0_ne : w1 ⟨i0, hi0_lt⟩ ≠ w2 ⟨i0, hi0_lt⟩ := hi0_spec.2
  have hmin : ∀ j < i0, ∀ hj : j < n, w1 ⟨j, hj⟩ = w2 ⟨j, hj⟩ := by
    intro j hj hj_n
    by_contra hne_j
    exact Nat.find_min hex hj ⟨hj_n, hne_j⟩
  have hprefix_eq : prefixWordC (le_of_lt hi0_lt) w1 = prefixWordC (le_of_lt hi0_lt) w2 := by
    funext ⟨j, hj⟩
    exact hmin j hj (lt_trans hj hi0_lt)
  have hgrow : ∀ t : ℕ, ∀ ht : i0 + 1 ≤ t, ∀ htn : t ≤ n,
      1 ≤ |centerIntC k t (prefixWordC htn w1) - centerIntC k t (prefixWordC htn w2)| ∧
      |(pairOfWord k t (prefixWordC htn w1)).1 - (pairOfWord k t (prefixWordC htn w2)).1| ≤
        |centerIntC k t (prefixWordC htn w1) - centerIntC k t (prefixWordC htn w2)| := by
    intro t ht htn
    induction t with
    | zero => omega
    | succ t ih =>
        rcases eq_or_lt_of_le ht with ht_eq | ht_gt
        · have ht0 : t = i0 := by omega
          subst ht0
          have hinit1 : Fin.init (prefixWordC htn w1) = prefixWordC (le_of_lt hi0_lt) w1 := by
            funext ⟨j, hj⟩; rfl
          have hinit2 : Fin.init (prefixWordC htn w2) = prefixWordC (le_of_lt hi0_lt) w2 := by
            funext ⟨j, hj⟩; rfl
          have hp_eq : pairOfWord k i0 (Fin.init (prefixWordC htn w1)) =
              pairOfWord k i0 (Fin.init (prefixWordC htn w2)) := by
            rw [hinit1, hinit2, hprefix_eq]
          have h1 : (pairOfWord k (i0 + 1) (prefixWordC htn w1)).1 =
              (pairOfWord k (i0 + 1) (prefixWordC htn w2)).1 := by
            change (pairOfWord k i0 (Fin.init (prefixWordC htn w1))).2 =
              (pairOfWord k i0 (Fin.init (prefixWordC htn w2))).2
            rw [hp_eq]
          have h2 : centerIntC k (i0 + 1) (prefixWordC htn w1) -
              centerIntC k (i0 + 1) (prefixWordC htn w2) =
              digitOf k (w1 ⟨i0, hi0_lt⟩) - digitOf k (w2 ⟨i0, hi0_lt⟩) := by
            change ((4 * ((J_cantor k + i0 : ℕ) : ℤ) + 6) *
                (pairOfWord k i0 (Fin.init (prefixWordC htn w1))).2 +
                (pairOfWord k i0 (Fin.init (prefixWordC htn w1))).1 +
                digitOf k (prefixWordC htn w1 (Fin.last i0))) -
              ((4 * ((J_cantor k + i0 : ℕ) : ℤ) + 6) *
                (pairOfWord k i0 (Fin.init (prefixWordC htn w2))).2 +
                (pairOfWord k i0 (Fin.init (prefixWordC htn w2))).1 +
                digitOf k (prefixWordC htn w2 (Fin.last i0))) = _
            rw [hp_eq]
            simp only [prefixWordC, Fin.last, Fin.coe_castSucc]
            ring
          have hd_ne : digitOf k (w1 ⟨i0, hi0_lt⟩) ≠ digitOf k (w2 ⟨i0, hi0_lt⟩) :=
            fun h => hi0_ne (digitOf_injective k h)
          have hge1 : 1 ≤ |digitOf k (w1 ⟨i0, hi0_lt⟩) - digitOf k (w2 ⟨i0, hi0_lt⟩)| := by
            have hne0 : digitOf k (w1 ⟨i0, hi0_lt⟩) - digitOf k (w2 ⟨i0, hi0_lt⟩) ≠ 0 :=
              sub_ne_zero.mpr hd_ne
            exact Int.one_le_abs hne0
          rw [h1, sub_self, abs_zero, h2]
          exact ⟨hge1, le_trans (by norm_num) hge1⟩
        · have ht_ge : i0 + 1 ≤ t := by omega
          have htn_le : t ≤ n := by omega
          obtain ⟨ih1, ih2⟩ := ih ht_ge htn_le
          have hinit1 : Fin.init (prefixWordC htn w1) = prefixWordC htn_le w1 := by
            funext ⟨j, hj⟩; rfl
          have hinit2 : Fin.init (prefixWordC htn w2) = prefixWordC htn_le w2 := by
            funext ⟨j, hj⟩; rfl
          set E_t := centerIntC k t (prefixWordC htn_le w1) - centerIntC k t (prefixWordC htn_le w2)
          set P_t := (pairOfWord k t (prefixWordC htn_le w1)).1 -
            (pairOfWord k t (prefixWordC htn_le w2)).1
          have hP_next : (pairOfWord k (t + 1) (prefixWordC htn w1)).1 -
              (pairOfWord k (t + 1) (prefixWordC htn w2)).1 = E_t := by
            change (pairOfWord k t (Fin.init (prefixWordC htn w1))).2 -
              (pairOfWord k t (Fin.init (prefixWordC htn w2))).2 = E_t
            rw [hinit1, hinit2]
            rfl
          have hE_next : centerIntC k (t + 1) (prefixWordC htn w1) -
              centerIntC k (t + 1) (prefixWordC htn w2) =
              (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * E_t + P_t +
                (digitOf k (prefixWordC htn w1 (Fin.last t)) -
                  digitOf k (prefixWordC htn w2 (Fin.last t))) := by
            change ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) *
                (pairOfWord k t (Fin.init (prefixWordC htn w1))).2 +
                (pairOfWord k t (Fin.init (prefixWordC htn w1))).1 +
                digitOf k (prefixWordC htn w1 (Fin.last t))) -
              ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) *
                (pairOfWord k t (Fin.init (prefixWordC htn w2))).2 +
                (pairOfWord k t (Fin.init (prefixWordC htn w2))).1 +
                digitOf k (prefixWordC htn w2 (Fin.last t))) = _
            rw [hinit1, hinit2]
            dsimp [E_t, P_t, centerIntC]
            ring
          set Δd := digitOf k (prefixWordC htn w1 (Fin.last t)) -
            digitOf k (prefixWordC htn w2 (Fin.last t))
          have hΔd : |Δd| ≤ 2 * (k : ℤ) := by
            have h1 := abs_digitOf_le k (prefixWordC htn w1 (Fin.last t))
            have h2 := abs_digitOf_le k (prefixWordC htn w2 (Fin.last t))
            calc |Δd| ≤ |digitOf k (prefixWordC htn w1 (Fin.last t))| +
                  |digitOf k (prefixWordC htn w2 (Fin.last t))| := abs_sub _ _
              _ ≤ 2 * (k : ℤ) := by linarith
          have hcoeff : 2 * (k : ℤ) + 2 ≤ 4 * ((J_cantor k + t : ℕ) : ℤ) + 6 := by
            unfold J_cantor; omega
          have hlb : (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * |E_t| - |P_t| - |Δd| ≤
              |centerIntC k (t + 1) (prefixWordC htn w1) -
                centerIntC k (t + 1) (prefixWordC htn w2)| := by
            rw [hE_next]
            have h1 := abs_sub_abs_le_abs_add ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * E_t + P_t) Δd
            have h2 := abs_sub_abs_le_abs_add ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * E_t) P_t
            have hmul : |(4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * E_t| =
                (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * |E_t| := by
              rw [abs_mul, abs_of_nonneg (by omega)]
            linarith
          have hE_ge : |E_t| ≤ (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * |E_t| - |P_t| - |Δd| := by
            have h3 : |Δd| ≤ 2 * (k : ℤ) * |E_t| := by
              calc |Δd| ≤ 2 * (k : ℤ) := hΔd
                _ = 2 * (k : ℤ) * 1 := by ring
                _ ≤ 2 * (k : ℤ) * |E_t| := mul_le_mul_of_nonneg_left ih1 (by omega)
            nlinarith
          rw [hP_next]
          exact ⟨le_trans ih1 (le_trans hE_ge hlb), le_trans hE_ge hlb⟩
  have hfinal := (hgrow n (by omega) (le_refl n)).1
  rw [prefixWordC_self, prefixWordC_self, heq, sub_self, abs_zero] at hfinal
  omega

/-- 若直径 $\le 1/Q_{J+n+1}$ 的集合 $V$ 同时交第 $n$ 级柱集 $I_n(u_1)$ 与 $I_n(u_2)$，
    则 $|M_{J+n+1}(u_1) - M_{J+n+1}(u_2)| \le 1$。 -/
lemma intersect_cIntervC_abs_sub_le_one (k : ℕ) (hk : 1 ≤ k) (n : ℕ) {V : Set ℝ}
    (hVbd : Bornology.IsBounded V) (hVdiam : Metric.diam V ≤ 1 / (Qsel (J_cantor k + n + 1) : ℝ))
    {u1 u2 : Fin n → Fin (2 * k + 1)}
    (h1 : (V ∩ cIntervC k n u1).Nonempty) (h2 : (V ∩ cIntervC k n u2).Nonempty) :
    |centerIntC k n u1 - centerIntC k n u2| ≤ 1 := by
  obtain ⟨x1, hx1V, hx1I⟩ := h1
  obtain ⟨x2, hx2V, hx2I⟩ := h2
  have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have hr := radC_le_quarter_inv k n hk
  have hd1 : |x1 - (centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
    abs_le.mpr ⟨by linarith [hx1I.1], by linarith [hx1I.2]⟩
  have hd2 : |x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
    abs_le.mpr ⟨by linarith [hx2I.1], by linarith [hx2I.2]⟩
  have hdist : |x1 - x2| ≤ 1 / (Qsel (J_cantor k + n + 1) : ℝ) :=
    le_trans (by simpa [Real.dist_eq] using Metric.dist_le_diam_of_mem hVbd hx1V hx2V) hVdiam
  have hcdiff : |(centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
      (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| <
      2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
    have htri : |(centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤
        |(centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1| +
          |x1 - x2| + |x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
      have hsub1 : (centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
          ((centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2) +
            (x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) := by ring
      rw [hsub1]
      calc |((centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2) +
              (x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))|
          ≤ |((centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2)| +
              |x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ |(centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1| + |x1 - x2| +
              |x2 - (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
            gcongr
            exact abs_add_le _ _
    rw [abs_sub_comm ((centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) x1] at htri
    have hsum : radC k n + 1 / (Qsel (J_cantor k + n + 1) : ℝ) + radC k n <
        2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
      have h14 : 1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) +
          1 / (Qsel (J_cantor k + n + 1) : ℝ) +
          1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) < 2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
        have h32 : 1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) +
            1 / (Qsel (J_cantor k + n + 1) : ℝ) +
            1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) =
            (3 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) := by field_simp; ring
        rw [h32, div_lt_div_iff_of_pos_right hQpos]
        linarith
      linarith
    linarith
  have hlt2 : (|centerIntC k n u1 - centerIntC k n u2| : ℝ) < 2 := by
    have heq : |(centerIntC k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (centerIntC k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| =
        |(centerIntC k n u1 - centerIntC k n u2 : ℤ)| / (Qsel (J_cantor k + n + 1) : ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hQpos]
      push_cast; rfl
    rw [heq, div_lt_div_iff_of_pos_right hQpos] at hcdiff
    exact_mod_cast hcdiff
  have hlt2Z : |centerIntC k n u1 - centerIntC k n u2| < 2 := by exact_mod_cast hlt2
  omega

/-- 第 $n$ 级 Cantor 并集与紧致 Cantor 树 $K_k$。 -/
def cantorLevelC (k n : ℕ) : Set ℝ :=
  ⋃ w : Fin n → Fin (2 * k + 1), cIntervC k n w

def cantorTreeC (k : ℕ) : Set ℝ :=
  ⋂ n : ℕ, cantorLevelC k n

lemma isCompact_cantorLevelC (k n : ℕ) : IsCompact (cantorLevelC k n) :=
  isCompact_iUnion (fun w => isCompact_cIntervC k n w)

lemma isClosed_cantorLevelC (k n : ℕ) : IsClosed (cantorLevelC k n) :=
  (isCompact_cantorLevelC k n).isClosed

lemma isCompact_cantorTreeC (k : ℕ) : IsCompact (cantorTreeC k) := by
  apply IsCompact.of_isClosed_subset (isCompact_cantorLevelC k 0)
  · exact isClosed_iInter (fun n => isClosed_cantorLevelC k n)
  · exact Set.iInter_subset _ 0

lemma cantorLevelC_antitone (k : ℕ) (hk : 1 ≤ k) : Antitone (cantorLevelC k) := by
  intro m n hmn x hx
  rcases Set.mem_iUnion.mp hx with ⟨w, hw⟩
  exact Set.mem_iUnion.mpr ⟨prefixWordC hmn w, cIntervC_prefix_subset k hk hmn w hw⟩

lemma cIntervC_inter_cantorTreeC_nonempty (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (u : Fin n → Fin (2 * k + 1)) :
    (cIntervC k n u ∩ cantorTreeC k).Nonempty := by
  let S : ℕ → Set ℝ := fun m => cIntervC k (n + m) (extendZeroC k u m)
  have hS_ne : ∀ m, (S m).Nonempty := fun m => cIntervC_nonempty k (n + m) (extendZeroC k u m)
  have hS_comp : ∀ m, IsCompact (S m) := fun m => isCompact_cIntervC k (n + m) _
  have hS_closed : ∀ m, IsClosed (S m) := fun m => isClosed_cIntervC k (n + m) _
  have hS_anti : Antitone S := by
    intro a b hab
    have hpre : prefixWordC (Nat.add_le_add_left hab n) (extendZeroC k u b) = extendZeroC k u a := by
      funext ⟨i, hi⟩
      by_cases hin : i < n
      · simp [prefixWordC, extendZeroC, hin]
      · simp [prefixWordC, extendZeroC, hin]
    have hsub := cIntervC_prefix_subset k hk (Nat.add_le_add_left hab n) (extendZeroC k u b)
    rwa [hpre] at hsub
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun i => hS_anti (Nat.le_succ i)) hS_ne (hS_comp 0) hS_closed
  have hx0 : x ∈ cIntervC k n u := by
    have h0 := Set.mem_iInter.mp hx 0
    dsimp [S] at h0
    have hzero : extendZeroC k u 0 = u := extendZeroC_zero k u
    simpa [hzero] using h0
  refine ⟨x, hx0, ?_⟩
  · rw [cantorTreeC, Set.mem_iInter]
    intro m
    by_cases hm : n ≤ m
    · obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
      exact Set.mem_iUnion.mpr ⟨extendZeroC k u d, Set.mem_iInter.mp hx d⟩
    · have hm_lt : m ≤ n := by omega
      exact cantorLevelC_antitone k hk hm_lt (Set.mem_iUnion.mpr ⟨u, hx0⟩)

/-- 紧致 Cantor 树 $K_k$ 包含于子水平集 $\{x \in \mathbb{R} : \Lambda(x) \le k/4\}$。 -/
lemma cantorTreeC_subset_levelSet (k : ℕ) (hk : 1 ≤ k) :
    cantorTreeC k ⊆ {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} := by
  intro x hx
  have hx_lvl : ∀ n : ℕ, ∃ w : Fin n → Fin (2 * k + 1), x ∈ cIntervC k n w := by
    intro n
    exact Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  choose w hw using hx_lvl
  have hnear : ∀ n : ℕ,
      nearestInt ((Qsel (J_cantor k + n + 1) : ℝ) * x) = centerIntC k n (w n) := by
    intro n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hxn := hw n
    have hdiff : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)| ≤
        (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
      have h1 : |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [hxn.1], by linarith [hxn.2]⟩
      calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)|
          = (Qsel (J_cantor k + n + 1) : ℝ) *
              |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
            rw [← abs_of_pos hQpos, ← abs_mul]
            congr 1
            rw [abs_of_pos hQpos]
            field_simp
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hQpos)
    have hr := radC_le_quarter_inv k n hk
    have hlt_half : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)| < 1 / 2 := by
      calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)|
          ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := hdiff
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) :=
            mul_le_mul_of_nonneg_left hr (le_of_lt hQpos)
        _ = 1 / 4 := by field_simp
        _ < 1 / 2 := by norm_num
    have hround : round ((Qsel (J_cantor k + n + 1) : ℝ) * x) = centerIntC k n (w n) := by
      rw [round_eq_iff]
      have habs := abs_lt.mp hlt_half
      exact ⟨by linarith, by linarith⟩
    exact hround
  have hinit_eq : ∀ n : ℕ, Fin.init (w (n + 1)) = w n := by
    intro n
    have h1 : x ∈ cIntervC k n (Fin.init (w (n + 1))) :=
      cIntervC_succ_subset k hk n (w (n + 1)) (hw (n + 1))
    have h2 : x ∈ cIntervC k n (w n) := hw n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hr := radC_le_quarter_inv k n hk
    have hd1 : |x - (centerIntC k n (Fin.init (w (n + 1))) : ℝ) /
        (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
      abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hd2 : |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
      abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hcdiff : |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ 2 * radC k n := by
      have hsub : (centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
          ((centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x) +
            (x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) := by ring
      rw [hsub]
      calc |((centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x) +
              (x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))|
          ≤ |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x| +
              |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ radC k n + radC k n := by
            rw [abs_sub_comm]
            exact add_le_add hd1 hd2
        _ = 2 * radC k n := by ring
    have hlt1 : (|centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| : ℝ) < 1 := by
      have heq : |(centerIntC k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| =
          (|centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| : ℝ) /
            (Qsel (J_cantor k + n + 1) : ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hQpos]
      rw [heq] at hcdiff
      have h2r : 2 * radC k n < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
        calc 2 * radC k n
            ≤ 2 * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) := by linarith
          _ = (1 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) := by ring
          _ < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
              rw [div_lt_div_iff_of_pos_right hQpos]; linarith
      have hlt' : (|centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| : ℝ) /
          (Qsel (J_cantor k + n + 1) : ℝ) < 1 / (Qsel (J_cantor k + n + 1) : ℝ) :=
        lt_of_le_of_lt hcdiff h2r
      exact (div_lt_div_iff_of_pos_right hQpos).mp hlt'
    have hlt1Z : |centerIntC k n (Fin.init (w (n + 1))) - centerIntC k n (w n)| < 1 := by
      exact_mod_cast hlt1
    rw [abs_lt] at hlt1Z
    have hceq : centerIntC k n (Fin.init (w (n + 1))) = centerIntC k n (w n) := by omega
    exact centerIntC_injective k hk n hceq
  have heps0 : Tendsto (eps x) atTop (nhds 0) := by
    have hbound : ∀ᶠ j : ℕ in atTop, |eps x j| ≤ (2 * (k : ℝ) + 2) / (j : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop (J_cantor k + 1)] with j hj
      obtain ⟨n, hn⟩ : ∃ n : ℕ, j = J_cantor k + n + 1 := ⟨j - (J_cantor k + 1), by omega⟩
      subst hn
      have hQ1 : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
      have hQ2 : 0 < (Qsel (J_cantor k + n + 2) : ℝ) := by
        exact_mod_cast Qsel_pos (J_cantor k + n + 2) (by unfold J_cantor; omega)
      have hxn := hw n
      have h1 : |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [hxn.1], by linarith [hxn.2]⟩
      have heps_eq : eps x (J_cantor k + n + 1) =
          (Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ) := by
        unfold eps
        rw [hnear n]
      have hle_rad : |eps x (J_cantor k + n + 1)| ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
        rw [heps_eq]
        calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (centerIntC k n (w n) : ℝ)|
            = |(Qsel (J_cantor k + n + 1) : ℝ) *
                (x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))| := by
              congr 1; field_simp
          _ = |(Qsel (J_cantor k + n + 1) : ℝ)| *
                |x - (centerIntC k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_mul _ _
          _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
              rw [abs_of_pos hQ1]
              exact mul_le_mul_of_nonneg_left h1 (le_of_lt hQ1)
      have hratio : (Qsel (J_cantor k + n + 1) : ℝ) * radC k n ≤
          (2 * (k : ℝ) + 2) / ((J_cantor k + n + 1 : ℕ) : ℝ) := by
        unfold radC
        have hrec := Qsel_succ_ge_mul (J_cantor k + n + 1) (by unfold J_cantor; omega)
        have hj_le : ((J_cantor k + n + 1 : ℕ) : ℝ) ≤ 4 * ((J_cantor k + n + 1 : ℕ) : ℝ) + 2 := by
          linarith
        have hQ_ge : ((J_cantor k + n + 1 : ℕ) : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) ≤
            (Qsel (J_cantor k + n + 2) : ℝ) :=
          le_trans (mul_le_mul_of_nonneg_right hj_le (le_of_lt hQ1)) hrec
        rw [mul_div_assoc', div_le_div_iff₀ hQ2 (by positivity)]
        nlinarith
      exact le_trans hle_rad hratio
    exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound
  have hdef_bound : ∀ᶠ j : ℕ in atTop, |(defect x j : ℝ)| ≤ (k : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (J_cantor k + 2)] with j hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = J_cantor k + n + 2 := ⟨j - (J_cantor k + 2), by omega⟩
    have hdef_eq : defect x (J_cantor k + n + 2) = digitOf k (w (n + 2) (Fin.last (n + 1))) := by
      unfold defect
      have hm0 : nearestInt ((Qsel (J_cantor k + n + 1) : ℝ) * x) = centerIntC k n (w n) :=
        hnear n
      have hm1 : nearestInt ((Qsel (J_cantor k + n + 2) : ℝ) * x) =
          centerIntC k (n + 1) (w (n + 1)) := hnear (n + 1)
      have hm2 : nearestInt ((Qsel (J_cantor k + n + 3) : ℝ) * x) =
          centerIntC k (n + 2) (w (n + 2)) := hnear (n + 2)
      have hsub1 : J_cantor k + n + 2 - 1 = J_cantor k + n + 1 := by omega
      have hsub2 : J_cantor k + n + 2 + 1 = J_cantor k + n + 3 := by omega
      rw [hsub1, hsub2, hm0, hm1, hm2]
      have hrec_w : centerIntC k (n + 2) (w (n + 2)) =
          (4 * ((J_cantor k + (n + 1) : ℕ) : ℤ) + 6) *
            (pairOfWord k (n + 1) (Fin.init (w (n + 2)))).2 +
            (pairOfWord k (n + 1) (Fin.init (w (n + 2)))).1 +
            digitOf k (w (n + 2) (Fin.last (n + 1))) := rfl
      rw [hrec_w, hinit_eq (n + 1)]
      have hp1 : (pairOfWord k (n + 1) (w (n + 1))).1 = centerIntC k n (w n) := by
        change (pairOfWord k n (Fin.init (w (n + 1)))).2 = centerIntC k n (w n)
        rw [hinit_eq n]
        rfl
      rw [hp1]
      have hcast : 4 * ((J_cantor k + (n + 1) : ℕ) : ℤ) + 6 =
          4 * ((J_cantor k + n + 2 : ℕ) : ℤ) + 2 := by
        push_cast; ring
      rw [hcast]
      change _ = digitOf k (w (n + 2) (Fin.last (n + 1)))
      unfold centerIntC
      ring
    rw [hdef_eq]
    exact_mod_cast abs_digitOf_le k (w (n + 2) (Fin.last (n + 1)))
  have heuler := FullSpectrumDiscrete.euler_abs_defect_approx x heps0
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε4 : (0 : ℝ) < 4 * (ε : ℝ) := by positivity
  have hev_euler : ∀ᶠ j : ℕ in atTop,
      |(defect x j : ℝ)| - 4 * apprSeq x j > -(4 * (ε : ℝ)) :=
    heuler.eventually (Ioi_mem_nhds (by linarith : -(4 * (ε : ℝ)) < 0))
  have hev_le : ∀ᶠ j : ℕ in atTop, apprSeqE x j ≤ ENNReal.ofReal ((k : ℝ) / 4) + (ε : ℝ≥0∞) := by
    filter_upwards [hdef_bound, hev_euler] with j hdj hej
    have h4 : apprSeq x j ≤ (k : ℝ) / 4 + (ε : ℝ) := by linarith
    calc apprSeqE x j = ENNReal.ofReal (apprSeq x j) := rfl
      _ ≤ ENNReal.ofReal ((k : ℝ) / 4 + (ε : ℝ)) := ENNReal.ofReal_le_ofReal h4
      _ = ENNReal.ofReal ((k : ℝ) / 4) + ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal ((k : ℝ) / 4) + (ε : ℝ≥0∞) := by simp
  exact limsup_le_of_le (by isBoundedDefault) hev_le

/-- **定理（Theorem 13 均匀 $(2k+1)$-叉 Cantor 树正测度下界）**：
    设 $k \ge 1$，单调连续规范函数 $m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$
    满足对一切 $n \in \mathbb{N}$ 有 $m(1 / Q_{n+1}) \ge c_1 (2k+1)^{-n}$（$c_1 > 0$）。
    则紧致 Cantor 树 $K_k = \mathrm{cantorTreeC}\ k$ 满足
    `0 < Measure.mkMetric m (cantorTreeC k)`。 -/
theorem mkMetric_cantorTree_pos (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (hm_cont : Continuous m) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hlb : ∀ n : ℕ, ENNReal.ofReal (c₁ * (2 * (k : ℝ) + 1) ^ (-(n : ℤ))) ≤
      m (ENNReal.ofReal (1 / (Qsel (n + 1) : ℝ)))) :
    0 < Measure.mkMetric m (cantorTreeC k) := by
  set J := J_cantor k
  set b : ℝ := 2 * (k : ℝ) + 1
  have hb_pos : 0 < b := by positivity
  set c₀R : ℝ := c₁ / (2 * b ^ (J + 1))
  have hc₀R_pos : 0 < c₀R := by positivity
  set c₀ : ℝ≥0∞ := ENNReal.ofReal c₀R
  have hc₀_pos : 0 < c₀ := ENNReal.ofReal_pos.mpr hc₀R_pos
  refine lt_of_lt_of_le hc₀_pos ?_
  have hQJ1_pos : 0 < (Qsel (J + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J + 1) (by dsimp [J]; unfold J_cantor; omega)
  set r0R : ℝ := 1 / (2 * (Qsel (J + 1) : ℝ))
  have hr0R_pos : 0 < r0R := by positivity
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R
  have hr0_pos : 0 < r0 := ENNReal.ofReal_pos.mpr hr0R_pos
  rw [MeasureTheory.Measure.mkMetric_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : cantorTreeC k ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n))) r0 hr0_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push_neg at hlt
  set S : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n))
  have hS_ne_top : S ≠ ⊤ := ne_of_lt (lt_trans hlt ENNReal.ofReal_lt_top)
  have hSR_lt : S.toReal < c₀R := by
    have h1 := (ENNReal.toReal_lt_toReal hS_ne_top ENNReal.ofReal_ne_top).mpr hlt
    rwa [ENNReal.toReal_ofReal (le_of_lt hc₀R_pos)] at h1
  set δ0 : ℝ := (c₀R - S.toReal) / 2
  have hδ0 : 0 < δ0 := by dsimp [δ0]; linarith
  have hex_rho : ∀ i : ℕ, (t i).Nonempty → ∃ ρi : ℝ, 0 < ρi ∧ 2 * ρi ≤ r0R ∧
      m (Metric.ediam (t i) + ENNReal.ofReal (2 * ρi)) ≤
        m (Metric.ediam (t i)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) := by
    intro i hne
    have hm_lt : m (Metric.ediam (t i)) < ⊤ := by
      have hleS : m (Metric.ediam (t i)) ≤ S := by
        have h1 : (⨆ _ : (t i).Nonempty, m (Metric.ediam (t i))) ≤ S :=
          ENNReal.le_tsum (f := fun n => ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n))) i
        simpa [hne] using h1
      exact lt_of_le_of_lt hleS (lt_of_lt_of_le hlt (le_of_lt ENNReal.ofReal_lt_top))
    have hε_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hlt_m : m (Metric.ediam (t i)) <
        m (Metric.ediam (t i)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i + 1)) :=
      ENNReal.lt_add_right (ne_of_lt hm_lt) (ne_of_gt hε_pos)
    have hcont_add : Tendsto (fun x : ℝ≥0∞ => m (Metric.ediam (t i) + x)) (nhds 0)
        (nhds (m (Metric.ediam (t i)))) := by
      have h1 : Tendsto (fun x : ℝ≥0∞ => Metric.ediam (t i) + x) (nhds 0)
          (nhds (Metric.ediam (t i) + 0)) := tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h1
      exact (hm_cont.continuousAt).tendsto.comp h1
    have hev := hcont_add.eventually (Iio_mem_nhds hlt_m)
    rw [ENNReal.nhds_zero_basis.eventually_iff] at hev
    obtain ⟨η, hη_pos, hη⟩ := hev
    by_cases htop : η = ⊤
    · refine ⟨r0R / 2, by linarith, by linarith, ?_⟩
      apply le_of_lt
      apply hη
      rw [htop]
      exact ENNReal.ofReal_lt_top
    · have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη_pos) htop
      set ρi : ℝ := min (r0R / 2) (η.toReal / 4)
      have hρi_pos : 0 < ρi := lt_min (by linarith) (by linarith)
      have h2ρ_le : 2 * ρi ≤ r0R := by
        have := min_le_left (r0R / 2) (η.toReal / 4)
        linarith
      have h2ρ_lt_η : ENNReal.ofReal (2 * ρi) < η := by
        have h1 : 2 * ρi ≤ η.toReal / 2 := by
          have := min_le_right (r0R / 2) (η.toReal / 4); linarith
        calc ENNReal.ofReal (2 * ρi)
            ≤ ENNReal.ofReal (η.toReal / 2) := ENNReal.ofReal_le_ofReal h1
          _ < ENNReal.ofReal η.toReal :=
              (ENNReal.ofReal_lt_ofReal_iff hηpos).mpr (by linarith)
          _ = η := ENNReal.ofReal_toReal htop
      exact ⟨ρi, hρi_pos, h2ρ_le, le_of_lt (hη h2ρ_lt_η)⟩
  choose ρ hρ_pos h2ρ_le hρ_m using fun i : {i : ℕ // (t i).Nonempty} => hex_rho i.1 i.2
  let V : {i : ℕ // (t i).Nonempty} → Set ℝ := fun i => Metric.thickening (ρ i) (t i.1)
  have hV_open : ∀ i, IsOpen (V i) := fun _ => Metric.isOpen_thickening
  have hV_cov : cantorTreeC k ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos ⟨i, ⟨x, hi⟩⟩) (t i) hi
  obtain ⟨F, hFcov⟩ := (isCompact_cantorTreeC k).elim_finite_subcover V hV_open hV_cov
  have hV_ediam_le : ∀ i : {i : ℕ // (t i).Nonempty},
      Metric.ediam (V i) ≤ ENNReal.ofReal (1 / (Qsel (J + 1) : ℝ)) := fun i => by
    calc Metric.ediam (V i)
        ≤ Metric.ediam (t i.1) + 2 * ENNReal.ofReal (ρ i) :=
          ediam_thickening_le (le_of_lt (hρ_pos i))
      _ ≤ r0 + ENNReal.ofReal (2 * ρ i) := by
          have h2 : 2 * ENNReal.ofReal (ρ i) = ENNReal.ofReal (2 * ρ i) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]; gcongr; exact hdiam i.1
      _ ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := by
          gcongr; exact h2ρ_le i
      _ = ENNReal.ofReal (1 / (Qsel (J + 1) : ℝ)) := by
          rw [← ENNReal.ofReal_add (le_of_lt hr0R_pos) (le_of_lt hr0R_pos)]
          congr 1; simp only [r0R]; ring
  have hV_bd : ∀ i, Bornology.IsBounded (V i) := fun i =>
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top))
  have hV_diam_le : ∀ i, Metric.diam (V i) ≤ 1 / (Qsel (J + 1) : ℝ) := fun i => by
    unfold Metric.diam
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hV_ediam_le i)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h1
  have hV_diam_pos : ∀ i, 0 < Metric.diam (V i) := fun i =>
    diam_thickening_pos i.2 (hρ_pos i) (hV_bd i)
  have hex_lvl : ∀ i : {i : ℕ // (t i).Nonempty},
      ∃ n : ℕ, 1 ≤ n ∧ 1 / (Qsel (J + n + 1) : ℝ) < Metric.diam (V i) ∧
        Metric.diam (V i) ≤ 1 / (Qsel (J + n) : ℝ) := by
    intro i
    set d := Metric.diam (V i)
    have hd_pos : 0 < d := hV_diam_pos i
    have hd_le : d ≤ 1 / (Qsel (J + 1) : ℝ) := hV_diam_le i
    have hex_m : ∃ m : ℕ, 1 ≤ m ∧ 1 / (Qsel (J + m) : ℝ) < d := by
      have hfact_top : Tendsto (fun m : ℕ => (Nat.factorial (J + m) : ℝ)) atTop atTop := by
        have h1 : Tendsto (fun m : ℕ => Nat.factorial (J + m)) atTop atTop := by
          rw [Filter.tendsto_atTop_atTop]
          intro B
          obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp factorial_tendsto_atTop B
          exact ⟨K, fun m hm => hK (J + m) (by omega)⟩
        exact tendsto_natCast_atTop_atTop.comp h1
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hfact_top.eventually_gt_atTop (1 / d))
      refine ⟨max 1 M, le_max_left _ _, ?_⟩
      have hQpos : 0 < (Qsel (J + max 1 M) : ℝ) := by
        exact_mod_cast Qsel_pos (J + max 1 M) (by dsimp [J]; unfold J_cantor; omega)
      have hQge : (Nat.factorial (J + max 1 M) : ℝ) ≤ (Qsel (J + max 1 M) : ℝ) := by
        exact_mod_cast DimHCore.Qsel_ge_factorial (J + max 1 M) (by dsimp [J]; unfold J_cantor; omega)
      have hgt : 1 / d < (Qsel (J + max 1 M) : ℝ) :=
        lt_of_lt_of_le (hM (max 1 M) (le_max_right _ _)) hQge
      rw [div_lt_iff₀ hQpos]
      have := (div_lt_iff₀ hd_pos).mp hgt
      linarith
    classical
    let m0 := Nat.find hex_m
    have hm0 : 1 ≤ m0 ∧ 1 / (Qsel (J + m0) : ℝ) < d := Nat.find_spec hex_m
    have hm0_gt : 1 < m0 := by
      by_contra hle
      have heq : m0 = 1 := by omega
      rw [heq] at hm0
      linarith [hm0.2, hd_le]
    refine ⟨m0 - 1, by omega, ?_, ?_⟩
    · have heq : J + (m0 - 1) + 1 = J + m0 := by omega
      rw [heq]; exact hm0.2
    · by_contra hgt
      push_neg at hgt
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) ⟨by omega, hgt⟩
  choose lvl hlvl_ge hlvl_gt hlvl_le using hex_lvl
  set N : ℕ := F.sup (fun i => lvl i)
  have hN_ge : ∀ i ∈ F, lvl i ≤ N := fun i hi => Finset.le_sup hi
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F, 2 * b * b ^ (-(lvl i : ℤ)) := by
    classical
    have hcover_words : (Finset.univ : Finset (Fin N → Fin (2 * k + 1))) ⊆
        F.biUnion (fun i => Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
          (V i ∩ cIntervC k N w).Nonempty)) := by
      intro w _
      obtain ⟨x, hxI, hxK⟩ := cIntervC_inter_cantorTreeC_nonempty k hk N w
      obtain ⟨i, hiF, hxiV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
      exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxiV, hxI⟩⟩⟩
    have hcard_i : ∀ i ∈ F,
        ((Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            (V i ∩ cIntervC k N w).Nonempty)).card : ℝ) ≤
          2 * b * b ^ (N - lvl i) := by
      intro i hiF
      have hleN : lvl i ≤ N := hN_ge i hiF
      have hl1 : lvl i - 1 ≤ N := by omega
      set m := lvl i - 1
      have hm_eq : m + 1 = lvl i := by have := hlvl_ge i; omega
      set A_i := Finset.univ.filter (fun u : Fin m → Fin (2 * k + 1) =>
        (V i ∩ cIntervC k m u).Nonempty)
      have hAi_le : A_i.card ≤ 2 := by
        apply card_le_two_of_abs_sub_le_one (centerIntC k m)
          (centerIntC_injective k hk m) A_i
        intro u1 hu1 u2 hu2
        have hdiam_m : Metric.diam (V i) ≤ 1 / (Qsel (J + m + 1) : ℝ) := by
          have : J + m + 1 = J + lvl i := by omega
          rw [this]
          exact hlvl_le i
        exact intersect_cIntervC_abs_sub_le_one k hk m (hV_bd i) hdiam_m
          (Finset.mem_filter.mp hu1).2 (Finset.mem_filter.mp hu2).2
      have hsub_fib : Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            (V i ∩ cIntervC k N w).Nonempty) ⊆
          A_i.biUnion (fun u => Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            prefixWordC hl1 w = u)) := by
        intro w hw
        obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hw).2
        have hxI' := cIntervC_prefix_subset k hk hl1 w hxI
        refine Finset.mem_biUnion.mpr ⟨prefixWordC hl1 w, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hfib_card : ∀ u : Fin m → Fin (2 * k + 1),
          (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            prefixWordC hl1 w = u)).card = (2 * k + 1) ^ (N - m) := by
        intro u
        let e : {w : Fin N → Fin (2 * k + 1) // prefixWordC hl1 w = u} ≃
            (Fin (N - m) → Fin (2 * k + 1)) :=
          { toFun := fun w j => w.1 ⟨m + j.1, by omega⟩
            invFun := fun tail =>
              ⟨fun t => if ht : t.1 < m then u ⟨t.1, ht⟩ else tail ⟨t.1 - m, by omega⟩, by
                funext ⟨t, ht⟩
                simp [prefixWordC, ht]⟩
            left_inv := fun w => by
              ext ⟨t, ht⟩
              by_cases htm : t < m
              · simp only [htm, ↓reduceDIte]
                have h2 := congr_fun w.2 ⟨t, htm⟩
                exact Fin.ext_iff.mp h2.symm
              · simp only [htm, ↓reduceDIte]
                have hsub : m + (t - m) = t := by omega
                have hidx : (⟨m + (t - m), by omega⟩ : Fin N) = ⟨t, ht⟩ := Fin.ext hsub
                rw [hidx]
            right_inv := fun tail => by
              funext ⟨j, hj⟩
              have hnot : ¬ (m + j < m) := by omega
              simp [hnot] }
        have hcard_eq : (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            prefixWordC hl1 w = u)).card =
            Fintype.card {w : Fin N → Fin (2 * k + 1) // prefixWordC hl1 w = u} :=
          (Fintype.card_subtype _).symm
        rw [hcard_eq, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hcard_nat : (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            (V i ∩ cIntervC k N w).Nonempty)).card ≤ 2 * (2 * k + 1) * (2 * k + 1) ^ (N - lvl i) := by
        calc (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
                (V i ∩ cIntervC k N w).Nonempty)).card
            ≤ (A_i.biUnion (fun u => Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
                prefixWordC hl1 w = u))).card := Finset.card_le_card hsub_fib
          _ ≤ ∑ u ∈ A_i, (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
                prefixWordC hl1 w = u)).card := Finset.card_biUnion_le
          _ = ∑ _u ∈ A_i, (2 * k + 1) ^ (N - m) :=
              Finset.sum_congr rfl (fun u _ => hfib_card u)
          _ = A_i.card * (2 * k + 1) ^ (N - m) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * (2 * k + 1) ^ (N - m) := Nat.mul_le_mul_right _ hAi_le
          _ = 2 * ((2 * k + 1) * (2 * k + 1) ^ (N - lvl i)) := by
              have hexp : N - m = (N - lvl i) + 1 := by omega
              rw [hexp, pow_succ']
          _ = 2 * (2 * k + 1) * (2 * k + 1) ^ (N - lvl i) := by ring
      have hcardR : ((Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
            (V i ∩ cIntervC k N w).Nonempty)).card : ℝ) ≤
            (2 * (2 * k + 1) * (2 * k + 1) ^ (N - lvl i) : ℕ) := by exact_mod_cast hcard_nat
      push_cast [b] at hcardR ⊢
      exact hcardR
    have htotal : b ^ N ≤ ∑ i ∈ F, 2 * b * b ^ (N - lvl i) := by
      have h1 : (2 * k + 1) ^ N ≤ ∑ i ∈ F, (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
          (V i ∩ cIntervC k N w).Nonempty)).card := by
        have hcard_univ : (Finset.univ : Finset (Fin N → Fin (2 * k + 1))).card = (2 * k + 1) ^ N := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [← hcard_univ]
        exact le_trans (Finset.card_le_card hcover_words) Finset.card_biUnion_le
      have h1R : b ^ N ≤ ∑ i ∈ F, ((Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
          (V i ∩ cIntervC k N w).Nonempty)).card : ℝ) := by
        have h1' : (((2 * k + 1) ^ N : ℕ) : ℝ) ≤
            ((∑ i ∈ F, (Finset.univ.filter (fun w : Fin N → Fin (2 * k + 1) =>
              (V i ∩ cIntervC k N w).Nonempty)).card : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast [b] at h1' ⊢
        exact h1'
      exact le_trans h1R (Finset.sum_le_sum (fun i hi => hcard_i i hi))
    have hbN_pos : 0 < b ^ N := pow_pos hb_pos N
    calc (1 : ℝ) = (b ^ N) / (b ^ N) := (div_self (ne_of_gt hbN_pos)).symm
      _ ≤ (∑ i ∈ F, 2 * b * b ^ (N - lvl i)) / (b ^ N) :=
          div_le_div_of_nonneg_right htotal (le_of_lt hbN_pos)
      _ = ∑ i ∈ F, (2 * b * b ^ (N - lvl i)) / (b ^ N) := Finset.sum_div _ _ _
      _ = ∑ i ∈ F, 2 * b * b ^ (-(lvl i : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hleN := hN_ge i hi
          have hpow_sub : b ^ (N - lvl i) / b ^ N = b ^ (-(lvl i : ℤ)) := by
            rw [zpow_neg, zpow_natCast]
            have h1 : N = (N - lvl i) + lvl i := by omega
            conv_lhs => rhs; rw [h1, pow_add]
            have hbn : b ^ (N - lvl i) ≠ 0 := pow_ne_zero _ (ne_of_gt hb_pos)
            have hbl : b ^ lvl i ≠ 0 := pow_ne_zero _ (ne_of_gt hb_pos)
            field_simp
          calc (2 * b * b ^ (N - lvl i)) / b ^ N
              = 2 * b * (b ^ (N - lvl i) / b ^ N) := by ring
            _ = 2 * b * b ^ (-(lvl i : ℤ)) := by rw [hpow_sub]
  have hmV_ge : ∀ i ∈ F,
      ENNReal.ofReal (c₀R * (2 * b * b ^ (-(lvl i : ℤ)))) ≤ m (Metric.ediam (V i)) := by
    intro i _
    have hed_ge : ENNReal.ofReal (1 / (Qsel (J + lvl i + 1) : ℝ)) ≤ Metric.ediam (V i) := by
      have hne_top : Metric.ediam (V i) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (hV_ediam_le i) ENNReal.ofReal_lt_top)
      rw [← ENNReal.ofReal_toReal hne_top]
      exact ENNReal.ofReal_le_ofReal (le_of_lt (hlvl_gt i))
    have hlb_i := hlb (J + lvl i)
    have halg : c₀R * (2 * b * b ^ (-(lvl i : ℤ))) = c₁ * b ^ (-((J + lvl i : ℕ) : ℤ)) := by
      dsimp [c₀R]
      rw [← Nat.cast_add, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, pow_add]
      have hbJ : b ^ J ≠ 0 := pow_ne_zero _ (ne_of_gt hb_pos)
      have hbl : b ^ lvl i ≠ 0 := pow_ne_zero _ (ne_of_gt hb_pos)
      have hb0 : b ≠ 0 := ne_of_gt hb_pos
      field_simp
    rw [halg]
    exact le_trans hlb_i (hm hed_ge)
  have hsum_lb : c₀ ≤ ∑ i ∈ F, m (Metric.ediam (V i)) := by
    calc c₀ = ENNReal.ofReal (c₀R * 1) := by simp [c₀]
      _ ≤ ENNReal.ofReal (c₀R * ∑ i ∈ F, 2 * b * b ^ (-(lvl i : ℤ))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum_ge_one (le_of_lt hc₀R_pos))
      _ = ENNReal.ofReal (∑ i ∈ F, c₀R * (2 * b * b ^ (-(lvl i : ℤ)))) := by
          rw [Finset.mul_sum]
      _ = ∑ i ∈ F, ENNReal.ofReal (c₀R * (2 * b * b ^ (-(lvl i : ℤ)))) :=
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)
      _ ≤ ∑ i ∈ F, m (Metric.ediam (V i)) := Finset.sum_le_sum hmV_ge
  have hsum_ub : ∑ i ∈ F, m (Metric.ediam (V i)) ≤ S + ENNReal.ofReal δ0 := by
    have h1 : ∑ i ∈ F, m (Metric.ediam (V i)) ≤
        ∑ i ∈ F, (m (Metric.ediam (t i.1)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      calc m (Metric.ediam (V i))
          ≤ m (Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i)) := by
              apply hm
              calc Metric.ediam (V i)
                  ≤ Metric.ediam (t i.1) + 2 * ENNReal.ofReal (ρ i) :=
                    ediam_thickening_le (le_of_lt (hρ_pos i))
                _ = Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i) := by
                    rw [ENNReal.ofReal_mul (by norm_num)]; simp
        _ ≤ m (Metric.ediam (t i.1)) + ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)) := hρ_m i
    rw [Finset.sum_add_distrib] at h1
    have hS_ge : ∑ i ∈ F, m (Metric.ediam (t i.1)) ≤ S := by
      have h_inj : Function.Injective (fun i : {i : ℕ // (t i).Nonempty} => i.1) :=
        fun a b h => Subtype.ext h
      calc ∑ i ∈ F, m (Metric.ediam (t i.1))
          = ∑ i ∈ F, ⨆ _ : (t i.1).Nonempty, m (Metric.ediam (t i.1)) := by
              apply Finset.sum_congr rfl; intro i _; simp [i.2]
        _ = ∑ n ∈ F.image Subtype.val, ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n)) :=
              (Finset.sum_image (f := fun n => ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n)))
                (fun a _ b _ h => h_inj h)).symm
        _ ≤ S := ENNReal.sum_le_tsum _
    have hδ_ge : ∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1)) ≤ ENNReal.ofReal δ0 := by
      have h_inj : Function.Injective (fun i : {i : ℕ // (t i).Nonempty} => i.1) :=
        fun a b h => Subtype.ext h
      have hsum_geom : Summable (fun n : ℕ => δ0 / (2 : ℝ) ^ (n + 1)) := by
        have h0 : Summable (fun n : ℕ => δ0 * (1 / 2 : ℝ) ^ (n + 1)) :=
          (summable_geometric_two.comp_injective Nat.succ_injective).mul_left δ0
        simpa [div_eq_mul_inv, one_div, inv_pow] using h0
      calc ∑ i ∈ F, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (i.1 + 1))
          = ∑ n ∈ F.image Subtype.val, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)) :=
              (Finset.sum_image (f := fun n => ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)))
                (fun a _ b _ h => h_inj h)).symm
        _ ≤ ∑' n : ℕ, ENNReal.ofReal (δ0 / (2 : ℝ) ^ (n + 1)) := ENNReal.sum_le_tsum _
        _ = ENNReal.ofReal (∑' n : ℕ, δ0 / (2 : ℝ) ^ (n + 1)) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum_geom).symm
        _ = ENNReal.ofReal δ0 := by
              congr 1
              have htsum : (∑' n : ℕ, δ0 / (2 : ℝ) ^ (n + 1)) =
                  δ0 * ((1 / 2 : ℝ) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n) := by
                have h1 : (fun n : ℕ => δ0 / (2 : ℝ) ^ (n + 1)) =
                    fun n => (δ0 * (1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ n := by
                  ext n
                  rw [pow_succ, div_eq_mul_inv, mul_inv, ← inv_pow]
                  simp only [one_div]
                  ring
                rw [h1, tsum_mul_left]
                ring
              rw [htsum, tsum_geometric_two]
              ring
    exact le_trans h1 (add_le_add hS_ge hδ_ge)
  have hlt_c0 : S + ENNReal.ofReal δ0 < c₀ := by
    have h1 : S + ENNReal.ofReal δ0 = ENNReal.ofReal (S.toReal + δ0) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_of_lt hδ0), ENNReal.ofReal_toReal hS_ne_top]
    rw [h1]
    exact (ENNReal.ofReal_lt_ofReal_iff hc₀R_pos).mpr (by dsimp [δ0]; linarith)
  exact not_lt_of_ge (le_trans hsum_lb hsum_ub) hlt_c0

/-- **定理（Theorem 13 精确水平集在临界规范下的正测度定理）**：
    设 $k \ge 1$，单调连续规范函数 $m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$
    同时满足临界规范的双侧界：
    - 上界：$\forall n \ge 1,\ m(1/Q_n) \le C (2k+1)^{-n}$；
    - 下界：$\forall n \in \mathbb{N},\ m(1/Q_{n+1}) \ge c_1 (2k+1)^{-n}$（$c_1 > 0$）。
    则精确水平集 $\{x \in \mathbb{R} : \Lambda(x) = k/4\}$ 满足
    `0 < Measure.mkMetric m {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)}`。 -/
theorem mkMetric_exactLevel_pos (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (hm_cont : Continuous m)
    (C c₁ : ℝ) (hc₁ : 0 < c₁)
    (hub : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-(n : ℤ))))
    (hlb : ∀ n : ℕ, ENNReal.ofReal (c₁ * (2 * (k : ℝ) + 1) ^ (-(n : ℤ))) ≤
      m (ENNReal.ofReal (1 / (Qsel (n + 1) : ℝ)))) :
    0 < Measure.mkMetric m {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
  have htree_pos : 0 < Measure.mkMetric m (cantorTreeC k) :=
    mkMetric_cantorTree_pos k hk m hm hm_cont c₁ hc₁ hlb
  have hle_pos : 0 < Measure.mkMetric m {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} :=
    lt_of_lt_of_le htree_pos (measure_mono (cantorTreeC_subset_levelSet k hk))
  have hstrict_null :
      Measure.mkMetric m {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 :=
    GaugeNull.mkMetric_strictLevel_null k hk m hm C hub
  have hsplit : {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ⊆
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∪
        {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} := by
    intro x hx
    rcases lt_or_eq_of_le (show apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4) from hx) with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq
  have hle_sum : Measure.mkMetric m {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ≤
      Measure.mkMetric m {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} +
        Measure.mkMetric m {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} :=
    le_trans (measure_mono hsplit) (measure_union_le _ _)
  rw [hstrict_null, add_zero] at hle_sum
  exact lt_of_lt_of_le hle_pos hle_sum

/-- `Measure.mkMetric m` 在实数平移 $x \mapsto x + z$ 下的不变性。 -/
lemma mkMetric_image_add (m : ℝ≥0∞ → ℝ≥0∞) (z : ℝ) (A : Set ℝ) :
    Measure.mkMetric m ((fun x : ℝ => x + z) '' A) = Measure.mkMetric m A := by
  have h_ediam_add : ∀ s : Set ℝ, Metric.ediam ((fun x : ℝ => x + z) '' s) = Metric.ediam s := by
    intro s
    apply le_antisymm
    · rw [Metric.ediam_le_iff]
      intro y hy w hw
      rcases hy with ⟨x, hx, rfl⟩
      rcases hw with ⟨u, hu, rfl⟩
      simpa [edist_dist, Real.dist_eq] using Metric.edist_le_ediam_of_mem hx hu
    · rw [Metric.ediam_le_iff]
      intro x hx y hy
      have h1 := Metric.edist_le_ediam_of_mem
        (Set.mem_image_of_mem (fun x : ℝ => x + z) hx)
        (Set.mem_image_of_mem (fun x : ℝ => x + z) hy)
      simpa [edist_dist, Real.dist_eq] using h1
  have h_ediam_sub : ∀ s : Set ℝ, Metric.ediam ((fun x : ℝ => x - z) '' s) = Metric.ediam s := by
    intro s
    apply le_antisymm
    · rw [Metric.ediam_le_iff]
      intro y hy w hw
      rcases hy with ⟨x, hx, rfl⟩
      rcases hw with ⟨u, hu, rfl⟩
      simpa [edist_dist, Real.dist_eq] using Metric.edist_le_ediam_of_mem hx hu
    · rw [Metric.ediam_le_iff]
      intro x hx y hy
      have h1 := Metric.edist_le_ediam_of_mem
        (Set.mem_image_of_mem (fun x : ℝ => x - z) hx)
        (Set.mem_image_of_mem (fun x : ℝ => x - z) hy)
      simpa [edist_dist, Real.dist_eq] using h1
  apply le_antisymm
  · rw [Measure.mkMetric_apply, Measure.mkMetric_apply]
    refine iSup₂_le fun r hr => le_trans ?_ (le_iSup₂ r hr)
    refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
    let t' : ℕ → Set ℝ := fun n => (fun x : ℝ => x + z) '' t n
    have hcov' : (fun x : ℝ => x + z) '' A ⊆ ⋃ n, t' n := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨n, ⟨x, hn, rfl⟩⟩
    have hdiam' : ∀ n, Metric.ediam (t' n) ≤ r := fun n => by
      dsimp [t']; rw [h_ediam_add]; exact hdiam n
    refine le_trans (iInf_le _ t') (le_trans (iInf_le _ hcov') (le_trans (iInf_le _ hdiam') ?_))
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp [t']
    rw [h_ediam_add]
    by_cases hne : (t n).Nonempty
    · have hne' : ((fun x : ℝ => x + z) '' t n).Nonempty := hne.image _
      simp only [hne, hne', ciSup_pos, le_refl]
    · have hne' : ¬ ((fun x : ℝ => x + z) '' t n).Nonempty := by
        rintro ⟨y, x, hx, _⟩; exact hne ⟨x, hx⟩
      simp only [hne, hne', ciSup_false, le_refl]
  · rw [Measure.mkMetric_apply, Measure.mkMetric_apply]
    refine iSup₂_le fun r hr => le_trans ?_ (le_iSup₂ r hr)
    refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
    let t' : ℕ → Set ℝ := fun n => (fun x : ℝ => x - z) '' t n
    have hcov' : A ⊆ ⋃ n, t' n := by
      intro x hx
      have hxz : x + z ∈ (fun y : ℝ => y + z) '' A := ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hxz)
      refine Set.mem_iUnion.mpr ⟨n, ⟨x + z, hn, ?_⟩⟩
      ring
    have hdiam' : ∀ n, Metric.ediam (t' n) ≤ r := fun n => by
      dsimp [t']; rw [h_ediam_sub]; exact hdiam n
    refine le_trans (iInf_le _ t') (le_trans (iInf_le _ hcov') (le_trans (iInf_le _ hdiam') ?_))
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp [t']
    rw [h_ediam_sub]
    by_cases hne : (t n).Nonempty
    · have hne' : ((fun x : ℝ => x - z) '' t n).Nonempty := hne.image _
      simp only [hne, hne', ciSup_pos, le_refl]
    · have hne' : ¬ ((fun x : ℝ => x - z) '' t n).Nonempty := by
        rintro ⟨y, x, hx, _⟩; exact hne ⟨x, hx⟩
      simp only [hne, hne', ciSup_false, le_refl]

/-- **推论（Theorem 13 精确水平集在临界规范下的无穷测度定理）**：
    在 `mkMetric_exactLevel_pos` 的同一双侧临界规范假设下，结合 $\Lambda$ 的 $L$-平移不变性
    （由于 $\mathbb{Z} \subseteq L$），精确水平集 $\{x \in \mathbb{R} : \Lambda(x) = k/4\}$
    在 $\mathbb{R}$ 上的全局测度为无穷大：
    `Measure.mkMetric m {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤`。 -/
theorem mkMetric_exactLevel_eq_top (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (hm_cont : Continuous m)
    (C c₁ : ℝ) (hc₁ : 0 < c₁)
    (hub : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-(n : ℤ))))
    (hlb : ∀ n : ℕ, ENNReal.ofReal (c₁ * (2 * (k : ℝ) + 1) ^ (-(n : ℤ))) ≤
      m (ENNReal.ofReal (1 / (Qsel (n + 1) : ℝ)))) :
    Measure.mkMetric m {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ := by
  set E : Set ℝ := {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)}
  set μ : Measure ℝ := Measure.mkMetric m
  have htree_pos : 0 < μ (cantorTreeC k) :=
    mkMetric_cantorTree_pos k hk m hm hm_cont c₁ hc₁ hlb
  have hstrict_null : μ {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 :=
    GaugeNull.mkMetric_strictLevel_null k hk m hm C hub
  have htree_bound : cantorTreeC k ⊆ Set.Icc (-1 / 4 : ℝ) (1 / 4) := by
    intro x hx
    have hx0 := Set.mem_iInter.mp hx 0
    rcases Set.mem_iUnion.mp hx0 with ⟨w, hw⟩
    have hc0 : centerIntC k 0 w = 0 := rfl
    have hr0 : radC k 0 ≤ 1 / 4 := by
      have h1 := radC_le_quarter_inv k 0 hk
      have hQ1 : (1 : ℝ) ≤ (Qsel (J_cantor k + 0 + 1) : ℝ) := by
        exact_mod_cast Qsel_pos (J_cantor k + 0 + 1) (by unfold J_cantor; omega)
      have h14 : 1 / (4 * (Qsel (J_cantor k + 0 + 1) : ℝ)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      exact le_trans h1 h14
    rw [cIntervC, hc0, Int.cast_zero, zero_div, zero_sub, zero_add] at hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  let A : ℕ → Set ℝ := fun z => (fun x : ℝ => x + (z : ℝ)) '' cantorTreeC k
  have hA_meas : ∀ z : ℕ, MeasurableSet (A z) := fun z =>
    ((isCompact_cantorTreeC k).image (continuous_id.add continuous_const)).measurableSet
  have hA_disj : Pairwise (fun z1 z2 => Disjoint (A z1) (A z2)) := by
    intro z1 z2 hne
    rw [Set.disjoint_left]
    rintro y ⟨x1, hx1, rfl⟩ ⟨x2, hx2, heq⟩
    have h1 := htree_bound hx1
    have h2 := htree_bound hx2
    have hdiff : |(z1 : ℝ) - (z2 : ℝ)| ≤ 1 / 2 := by
      have : (z1 : ℝ) - (z2 : ℝ) = x2 - x1 := by linarith
      rw [this]
      exact abs_le.mpr ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.2]⟩
    have hge1 : (1 : ℝ) ≤ |(z1 : ℝ) - (z2 : ℝ)| := by
      have hneZ : (z1 : ℤ) - (z2 : ℤ) ≠ 0 := by omega
      have h1Z : (1 : ℤ) ≤ |(z1 : ℤ) - (z2 : ℤ)| := Int.one_le_abs hneZ
      exact_mod_cast h1Z
    linarith
  have hz_mem_L : ∀ z : ℕ, (z : ℝ) ∈ latticeL := fun z => by
    refine ⟨(z : ℤ), 0, ?_⟩
    simp
  have hA_rest : ∀ z : ℕ, μ (cantorTreeC k) ≤ (μ.restrict E) (A z) := by
    intro z
    rw [Measure.restrict_apply (hA_meas z)]
    have hdiff_null : μ (A z \ E) = 0 := by
      apply measure_mono_null _ hstrict_null
      rintro y ⟨⟨x, hxK, rfl⟩, hyE⟩
      have hle_x : apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4) :=
        cantorTreeC_subset_levelSet k hk hxK
      have hle_y : apprExponent (x + (z : ℝ)) ≤ ENNReal.ofReal ((k : ℝ) / 4) := by
        rw [apprExponent_add_latticeL x (hz_mem_L z)]
        exact hle_x
      exact lt_of_le_of_ne hle_y hyE
    have hcov_Az : A z ⊆ (A z ∩ E) ∪ (A z \ E) := by
      intro y hy
      by_cases hyE : y ∈ E
      · exact Or.inl ⟨hy, hyE⟩
      · exact Or.inr ⟨hy, hyE⟩
    have hle_Az : μ (A z) ≤ μ (A z ∩ E) + μ (A z \ E) :=
      le_trans (measure_mono hcov_Az) (measure_union_le _ _)
    rw [hdiff_null, add_zero] at hle_Az
    have heq_img : μ (A z) = μ (cantorTreeC k) := mkMetric_image_add m (z : ℝ) (cantorTreeC k)
    rw [heq_img] at hle_Az
    simpa [Set.inter_comm] using hle_Az
  have hsum_top : (∑' z : ℕ, μ (cantorTreeC k)) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (ne_of_gt htree_pos)
  have hle_E : (∑' z : ℕ, μ (cantorTreeC k)) ≤ μ E := by
    calc (∑' z : ℕ, μ (cantorTreeC k))
        ≤ ∑' z : ℕ, (μ.restrict E) (A z) := ENNReal.tsum_le_tsum hA_rest
      _ = (μ.restrict E) (⋃ z : ℕ, A z) := (measure_iUnion hA_disj hA_meas).symm
      _ ≤ (μ.restrict E) Set.univ := measure_mono (Set.subset_univ _)
      _ = μ E := by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [hsum_top] at hle_E
  exact top_unique hle_E

end
end GaugeExact

/-! ## 公理依赖审计（#print axioms） -/
#print axioms GaugeExact.dimH_finiteLevel_zero
#print axioms GaugeExact.volume_finiteLevel_zero
#print axioms GaugeExact.ae_apprExponent_eq_top
#print axioms GaugeExact.volume_infiniteLevel_Icc
#print axioms GaugeExact.volume_infiniteLevel_Icc_zero_one
#print axioms GaugeExact.dimH_infiniteLevel_inter_Icc_zero_one
#print axioms GaugeExact.dimH_infiniteLevel_eq_one
#print axioms GaugeExact.apprExponent_add_latticeL
#print axioms GaugeExact.exactLevel_add_latticeL
#print axioms GaugeExact.mkMetric_digitClass_le
#print axioms GaugeExact.mkMetric_digitClass_lt_top
#print axioms GaugeExact.exactLevel_countable_cover_finite_mkMetric
#print axioms GaugeExact.mkMetric_le_mul_of_eventually_le
#print axioms GaugeExact.mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top
#print axioms GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero
#print axioms GaugeExact.gauge_ratio_adjacent_levels_tendsto_zero
#print axioms GaugeExact.mkMetric_unsignedExactLimit_null_of_hk
#print axioms GaugeExact.mkMetric_unsignedExactLimit_null_of_subgauge_base2
#print axioms GaugeExact.unsignedExactLimit_countable_cover_finite_mkMetric_base2
#print axioms GaugeExact.mkMetric_cantorTree_pos
#print axioms GaugeExact.mkMetric_exactLevel_pos
#print axioms GaugeExact.mkMetric_exactLevel_eq_top
