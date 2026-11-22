import Mathlib
import EpiFormal.Classification
import EpiFormal.SpectralGap
import EpiFormal.DimHCore
import EpiFormal.FullSpectrumDiscrete

/-!
# 临界能级严格子水平集与次临界规范的 Hausdorff 规范零测度定理（GaugeNull）

本模块在 Lean 4 中形式化论文二（第二阶段：沿 e 收敛子分母的逼近谱隙与水平集维数）
关于临界能级 $k/4$（$k \ge 1$）Hausdorff 规范测度（`MeasureTheory.Measure.mkMetric`）的零测度定理：

1. **平移一位的递推数字 $d'_j(x) = M_{j+2} - (4j+6)M_{j+1} - M_j$**：
   利用 `Classification.Qsel_rec`（$Q_{j+2} = (4j+6)Q_{j+1} + Q_j$，对一切 $j \in \mathbb{N}$ 成立，无自然数减法截断），
   建立平移缺陷恒等式 $d'_j(x) = (4j+6) u_{j+1} + u_j - u_{j+2}$ 与递推重构式。
2. **存活相邻整数对有限树 `pairTree` 与统一覆盖**：
   对任意数字上界 $r \in \mathbb{N}$、起点下标 $N \ge 1$ 及初始整数对 $(m_0, m_1) \in \mathbb{Z}^2$，
   尾部分支满足 $|d'_j(x)| \le r$（$j \ge N$）的点集 `digitClass r N m0 m1` 在第 $N+n$ 层最多产生
   $(2r+1)^n$ 个相邻整数对 $(M_{N+n}, M_{N+n+1})$，每个整数对对应一个直径不超过 $1 / Q_{N+n}$ 的闭区间。
3. **主定理 `mkMetric_strictLevel_null`（Theorem 13 严格子水平集零测度部分）**：
   设 $k \ge 1$，$m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 为任意单调非减函数，
   满足对一切 $n \ge 1$ 有 $m(1/Q_n) \le C (2k+1)^{-n}$。则
   $$\mathrm{Measure.mkMetric}\ m\ \{x \in \mathbb{R} : \Lambda(x) < k/4\} = 0.$$
   不需要 $m$ 的连续性假设。
4. **推论 `mkMetric_levelSet_null_of_subgauge`（Corollary 14(ii) 更小阶规范零测度定理）**：
   设 $k \ge 0$，$g : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 为任意单调非减函数，
   满足 $(2k+1)^n g(1/Q_n) \to 0$（即 $g(1/Q_n) / h_k(1/Q_n) \to 0$）。则非严格子水平集同样为零测度：
   $$\mathrm{Measure.mkMetric}\ g\ \{x \in \mathbb{R} : \Lambda(x) \le k/4\} = 0.$$
-/

open Real Filter Topology Set MeasureTheory Classification SpectralGap DimHCore FullSpectrumDiscrete
open scoped ENNReal NNReal

namespace GaugeNull

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. 平移一位的整数递推数字 $d'_j(x) = M_{j+2} - (4j+6)M_{j+1} - M_j$ -/

/-- 索引平移一位的整数递推数字 $d'_j(x) = M_{j+2} - (4j+6)M_{j+1} - M_j$。 -/
def defectShift (x : ℝ) (j : ℕ) : ℤ :=
  nearestInt ((Qsel (j + 2) : ℝ) * x) -
    (4 * (j : ℤ) + 6) * nearestInt ((Qsel (j + 1) : ℝ) * x) -
    nearestInt ((Qsel j : ℝ) * x)

lemma defectShift_eq_defect_succ (x : ℝ) (j : ℕ) :
    defectShift x j = defect x (j + 1) := by
  unfold defectShift defect
  have h1 : (j + 1 - 1 : ℕ) = j := by omega
  rw [h1]
  push_cast
  ring

/-- 平移缺陷恒等式：$d'_j(x) = (4j+6) \varepsilon_{j+1}(x) + \varepsilon_j(x) - \varepsilon_{j+2}(x)$。 -/
lemma defectShift_identity (x : ℝ) (j : ℕ) :
    (defectShift x j : ℝ) =
      (4 * (j : ℝ) + 6) * eps x (j + 1) + eps x j - eps x (j + 2) := by
  have hQ : (Qsel (j + 2) : ℝ) = (4 * (j : ℝ) + 6) * (Qsel (j + 1) : ℝ) + (Qsel j : ℝ) := by
    have := Classification.Qsel_rec j
    exact_mod_cast this
  simp only [defectShift, eps, nearestInt]
  push_cast
  rw [hQ]
  ring

/-- 由 $(M_j, M_{j+1})$ 与 $d'_j$ 恢复 $M_{j+2}$。 -/
lemma nearestInt_add_two_eq (x : ℝ) (j : ℕ) :
    nearestInt ((Qsel (j + 2) : ℝ) * x) =
      (4 * (j : ℤ) + 6) * nearestInt ((Qsel (j + 1) : ℝ) * x) +
        nearestInt ((Qsel j : ℝ) * x) + defectShift x j := by
  unfold defectShift
  ring

/-! ## 2. 数字字母表与存活相邻整数对有限树 `pairTree` -/

/-- 数字字母表 $\{-r, \dots, r\}$，基数恰为 $2r+1$。 -/
def digitAlphabet (r : ℕ) : Finset ℤ :=
  Finset.Icc (-(r : ℤ)) (r : ℤ)

lemma mem_digitAlphabet_iff (r : ℕ) (d : ℤ) :
    d ∈ digitAlphabet r ↔ |d| ≤ (r : ℤ) := by
  simp only [digitAlphabet, Finset.mem_Icc, abs_le]

lemma card_digitAlphabet (r : ℕ) :
    (digitAlphabet r).card = 2 * r + 1 := by
  simp only [digitAlphabet, Int.card_Icc]
  omega

/-- 单步转移：给定第 $j$ 层的相邻整数对 $p = (M_j, M_{j+1})$，生成第 $j+1$ 层的候选对 $(M_{j+1}, M_{j+2})$。 -/
def stepPairs (r : ℕ) (j : ℕ) (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (digitAlphabet r).image (fun d => (p.2, (4 * (j : ℤ) + 6) * p.2 + p.1 + d))

lemma card_stepPairs_le (r : ℕ) (j : ℕ) (p : ℤ × ℤ) :
    (stepPairs r j p).card ≤ 2 * r + 1 := by
  calc (stepPairs r j p).card
      ≤ (digitAlphabet r).card := Finset.card_image_le
    _ = 2 * r + 1 := card_digitAlphabet r

/-- 从起点下标 $N$ 与初始对 $(m_0, m_1)$ 出发的 $n$ 步存活整数对集合。 -/
def pairTree (r : ℕ) (N : ℕ) (m0 m1 : ℤ) : ℕ → Finset (ℤ × ℤ)
  | 0 => {(m0, m1)}
  | n + 1 => (pairTree r N m0 m1 n).biUnion (fun p => stepPairs r (N + n) p)

lemma pairTree_succ (r N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    pairTree r N m0 m1 (n + 1) =
      (pairTree r N m0 m1 n).biUnion (fun p => stepPairs r (N + n) p) := rfl

lemma card_pairTree_le (r N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    (pairTree r N m0 m1 n).card ≤ (2 * r + 1) ^ n := by
  induction n with
  | zero => simp [pairTree]
  | succ n ih =>
      rw [pairTree_succ]
      have hstep : ∀ p ∈ pairTree r N m0 m1 n, (stepPairs r (N + n) p).card ≤ 2 * r + 1 :=
        fun p _ => card_stepPairs_le r (N + n) p
      calc ((pairTree r N m0 m1 n).biUnion (fun p => stepPairs r (N + n) p)).card
          ≤ (pairTree r N m0 m1 n).card * (2 * r + 1) :=
            Finset.card_biUnion_le_card_mul _ _ _ hstep
        _ ≤ (2 * r + 1) ^ n * (2 * r + 1) := Nat.mul_le_mul_right _ ih
        _ = (2 * r + 1) ^ (n + 1) := by rw [pow_succ]

/-! ## 3. 数字类 `digitClass` 与直径 $1 / Q_j$ 区间覆盖 -/

/-- 固定起点 $N$、初值 $(m_0, m_1)$ 与尾部数字界 $|d'_j| \le r$ 的数字类。 -/
def digitClass (r : ℕ) (N : ℕ) (m0 m1 : ℤ) : Set ℝ :=
  {x : ℝ | nearestInt ((Qsel N : ℝ) * x) = m0 ∧
           nearestInt ((Qsel (N + 1) : ℝ) * x) = m1 ∧
           ∀ j : ℕ, N ≤ j → |defectShift x j| ≤ (r : ℤ)}

lemma mem_pairTree_of_mem_digitClass {r N : ℕ} {m0 m1 : ℤ} {x : ℝ}
    (hx : x ∈ digitClass r N m0 m1) (n : ℕ) :
    (nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)) ∈
      pairTree r N m0 m1 n := by
  rcases hx with ⟨hm0, hm1, hdef⟩
  induction n with
  | zero =>
      simp [pairTree, hm0, hm1]
  | succ n ih =>
      rw [pairTree_succ, Finset.mem_biUnion]
      refine ⟨(nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)), ih, ?_⟩
      unfold stepPairs
      rw [Finset.mem_image]
      refine ⟨defectShift x (N + n), ?_, ?_⟩
      · rw [mem_digitAlphabet_iff]
        exact hdef (N + n) (by omega)
      · ext
        · rfl
        · dsimp
          exact (nearestInt_add_two_eq x (N + n)).symm

/-- 以 $m / Q_j$ 为中心、半径为 $1 / (2 Q_j)$（直径为 $1 / Q_j$）的闭区间。 -/
def gaugeInterv (j : ℕ) (m : ℤ) : Set ℝ :=
  Icc (((m : ℝ) - 1 / 2) / (Qsel j : ℝ)) (((m : ℝ) + 1 / 2) / (Qsel j : ℝ))

lemma ediam_gaugeInterv_le (j : ℕ) (m : ℤ) :
    Metric.ediam (gaugeInterv j m) ≤ ENNReal.ofReal (1 / (Qsel j : ℝ)) := by
  have hsub : (((m : ℝ) + 1 / 2) / (Qsel j : ℝ)) - (((m : ℝ) - 1 / 2) / (Qsel j : ℝ)) =
      1 / (Qsel j : ℝ) := by ring
  rw [gaugeInterv, Real.ediam_Icc, hsub]

lemma mem_gaugeInterv_nearestInt (x : ℝ) (j : ℕ) :
    x ∈ gaugeInterv j (nearestInt ((Qsel j : ℝ) * x)) := by
  have hQ : (0 : ℝ) < (Qsel j : ℝ) := by exact_mod_cast Classification.Qsel_pos j
  have habs : |(Qsel j : ℝ) * x - (nearestInt ((Qsel j : ℝ) * x) : ℝ)| ≤ 1 / 2 :=
    Classification.abs_eps_le_half x j
  have hle := abs_le.mp habs
  unfold gaugeInterv
  rw [mem_Icc]
  constructor
  · rw [div_le_iff₀ hQ]
    linarith
  · rw [le_div_iff₀ hQ]
    linarith

lemma digitClass_cover (r N : ℕ) (m0 m1 : ℤ) (n : ℕ) :
    digitClass r N m0 m1 ⊆
      ⋃ p : (pairTree r N m0 m1 n : Set (ℤ × ℤ)), gaugeInterv (N + n) p.1.1 := by
  intro x hx
  have hmem := mem_pairTree_of_mem_digitClass hx n
  have hinterv := mem_gaugeInterv_nearestInt x (N + n)
  refine Set.mem_iUnion.mpr ?_
  exact ⟨⟨(nearestInt ((Qsel (N + n) : ℝ) * x), nearestInt ((Qsel (N + n + 1) : ℝ) * x)), hmem⟩, hinterv⟩

lemma tendsto_inv_Qsel_shift (N : ℕ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))) atTop (nhds 0) := by
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop :=
    (tendsto_add_atTop_nat N).congr (fun n => Nat.add_comm n N)
  have hQ : Tendsto (fun n : ℕ => (Qsel (N + n) : ℝ)) atTop atTop :=
    Classification.Qsel_tendsto_atTop.comp hshift
  have hdiv : Tendsto (fun n : ℕ => 1 / (Qsel (N + n) : ℝ)) atTop (nhds 0) :=
    hQ.const_div_atTop 1
  have hof : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))) atTop
      (nhds (ENNReal.ofReal 0)) := ENNReal.tendsto_ofReal hdiv
  simpa using hof

/-- **通用数字类规范零测度引理**：
    若单调函数 $m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 满足
    $(2r+1)^n m(1 / Q_{N+n}) \to 0$（$n \to \infty$），则
    `Measure.mkMetric m (digitClass r N m0 m1) = 0`。 -/
theorem mkMetric_digitClass_null (r N : ℕ) (m0 m1 : ℤ)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m)
    (hcost : Tendsto (fun n : ℕ => (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) *
      m (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ)))) atTop (nhds 0)) :
    Measure.mkMetric m (digitClass r N m0 m1) = 0 := by
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
  have hsum_le : ∀ n : ℕ, ∑ p : ι n, m (Metric.ediam (cov n p)) ≤
      (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
    intro n
    calc ∑ p : ι n, m (Metric.ediam (cov n p))
        ≤ ∑ _p : ι n, m (radSeq n) :=
          Finset.sum_le_sum (fun p _ => hm (ediam_gaugeInterv_le (N + n) p.1.1))
      _ = (Fintype.card (ι n) : ℝ≥0∞) * m (radSeq n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ((pairTree r N m0 m1 n).card : ℝ≥0∞) * m (radSeq n) := by
          rw [Fintype.card_coe]
      _ ≤ (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) := by
          gcongr
          exact_mod_cast card_pairTree_le r N m0 m1 n
  have hlim : Filter.liminf (fun n => ∑ p : ι n, m (Metric.ediam (cov n p))) atTop ≤ 0 := by
    have hle' : ∀ᶠ n in atTop, (∑ p : ι n, m (Metric.ediam (cov n p))) ≤
        (((2 * r + 1) ^ n : ℕ) : ℝ≥0∞) * m (radSeq n) :=
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

/-- 可数并归零：若每个 `digitClass r N m0 m1`（$N \ge 1, m_0, m_1 \in \mathbb{Z}$）的 $\mu$-测度均为 $0$，
    则它们的可数并的 $\mu$-测度为 $0$。 -/
lemma measure_iUnion_digitClass_null (r : ℕ) (μ : Measure ℝ)
    (hnull : ∀ (N : ℕ), 1 ≤ N → ∀ (m0 m1 : ℤ), μ (digitClass r N m0 m1) = 0) :
    μ (⋃ (N : {N : ℕ // 1 ≤ N}) (m0 : ℤ) (m1 : ℤ), digitClass r N.1 m0 m1) = 0 := by
  apply measure_iUnion_null
  intro N
  apply measure_iUnion_null
  intro m0
  apply measure_iUnion_null
  intro m1
  exact hnull N.1 N.2 m0 m1

/-! ## 4. 子水平集与严格子水平集向 `digitClass` 可数并的包含关系 -/

/-- 非严格子水平集 $\{x : \Lambda(x) \le k/4\}$ 包含于 `digitClass k N m0 m1` 的可数并。 -/
lemma levelSet_quarter_subset_iUnion_digitClass (k : ℕ) :
    {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ⊆
      ⋃ (N : {N : ℕ // 1 ≤ N}) (m0 : ℤ) (m1 : ℤ), digitClass k N.1 m0 m1 := by
  intro x hx
  have hc : (k : ℝ) / 4 < ((k : ℝ) + 1) / 4 := by linarith
  have hev := FullSpectrumDiscrete.eventually_abs_defect_le_of_apprExponent_le k hc x hx
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max 1 N0
  have hN1 : 1 ≤ N := le_max_left _ _
  have hdef : ∀ j : ℕ, N ≤ j → |defectShift x j| ≤ (k : ℤ) := by
    intro j hj
    rw [defectShift_eq_defect_succ]
    exact hN0 (j + 1) (by omega)
  refine Set.mem_iUnion.mpr ⟨⟨N, hN1⟩, ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel N : ℝ) * x), ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel (N + 1) : ℝ) * x), ?_⟩
  exact ⟨rfl, rfl, hdef⟩

/-- 严格子水平集 $\{x : \Lambda(x) < k/4\}$（$k \ge 1$）等于 $\{x : \Lambda(x) \le (k-1)/4\}$，
    因而包含于 `digitClass (k - 1) N m0 m1` 的可数并。 -/
lemma strictLevel_subset_iUnion_digitClass (k : ℕ) (hk : 1 ≤ k) :
    {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} ⊆
      ⋃ (N : {N : ℕ // 1 ≤ N}) (m0 : ℤ) (m1 : ℤ), digitClass (k - 1) N.1 m0 m1 := by
  intro x hx
  have hx_lt : apprExponent x < ENNReal.ofReal ((k : ℝ) / 4) := hx
  have hfin : apprExponent x ≠ ⊤ := ne_of_lt (lt_trans hx_lt ENNReal.ofReal_lt_top)
  set c := (apprExponent x).toReal
  have hkpos : (0 : ℝ) < (k : ℝ) / 4 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hck : c < (k : ℝ) / 4 := by
    have h1 : ENNReal.ofReal c < ENNReal.ofReal ((k : ℝ) / 4) := by
      rwa [ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hkpos).mp h1
  have hrk : (((k - 1 : ℕ) : ℝ) + 1) / 4 = (k : ℝ) / 4 := by
    have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hk
    rw [hcast]
  have hcr : c < (((k - 1 : ℕ) : ℝ) + 1) / 4 := by linarith
  have hx_le : apprExponent x ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_toReal hfin]
  have hev := FullSpectrumDiscrete.eventually_abs_defect_le_of_apprExponent_le (k - 1) hcr x hx_le
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set N := max 1 N0
  have hN1 : 1 ≤ N := le_max_left _ _
  have hdef : ∀ j : ℕ, N ≤ j → |defectShift x j| ≤ ((k - 1 : ℕ) : ℤ) := by
    intro j hj
    rw [defectShift_eq_defect_succ]
    exact hN0 (j + 1) (by omega)
  refine Set.mem_iUnion.mpr ⟨⟨N, hN1⟩, ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel N : ℝ) * x), ?_⟩
  refine Set.mem_iUnion.mpr ⟨nearestInt ((Qsel (N + 1) : ℝ) * x), ?_⟩
  exact ⟨rfl, rfl, hdef⟩

/-! ## 5. 主定理：`mkMetric_strictLevel_null` 与次临界规范推论 -/

/-- 指数衰减上界引理：当 $k \ge 1$ 时，$(2(k-1)+1)^n \cdot C (2k+1)^{-(N+n)} \to 0$。 -/
lemma tendsto_strictLevel_cost (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (C : ℝ) :
    Tendsto (fun n : ℕ => (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-((N + n : ℕ) : ℤ)))) atTop (nhds 0) := by
  set C' := max C 0
  set a : ℝ := ((2 * (k - 1) + 1 : ℕ) : ℝ)
  set b : ℝ := 2 * (k : ℝ) + 1
  have hb_pos : 0 < b := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp [b]; linarith
  have ha_nonneg : 0 ≤ a := Nat.cast_nonneg _
  have hab_lt : a < b := by
    have hnat : 2 * (k - 1) + 1 < 2 * k + 1 := by omega
    have hcast : ((2 * k + 1 : ℕ) : ℝ) = b := by dsimp [b]; push_cast; ring
    rw [← hcast]
    dsimp [a]
    exact_mod_cast hnat
  have hratio_nonneg : 0 ≤ a / b := div_nonneg ha_nonneg (le_of_lt hb_pos)
  have hratio_lt : a / b < 1 := (div_lt_one hb_pos).mpr hab_lt
  have hpow0 : Tendsto (fun n : ℕ => (a / b) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt
  have hreal0 : Tendsto (fun n : ℕ => (C' / b ^ N) * (a / b) ^ n) atTop (nhds 0) := by
    have h1 := hpow0.const_mul (C' / b ^ N)
    simpa using h1
  have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal ((C' / b ^ N) * (a / b) ^ n)) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hreal0
  have hle : ∀ n : ℕ,
      (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (C * b ^ (-((N + n : ℕ) : ℤ))) ≤
      ENNReal.ofReal ((C' / b ^ N) * (a / b) ^ n) := by
    intro n
    have hb_zpow_pos : 0 ≤ b ^ (-((N + n : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb_pos) _
    have hCC' : C * b ^ (-((N + n : ℕ) : ℤ)) ≤ C' * b ^ (-((N + n : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hb_zpow_pos
    have hcast_a : (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (a ^ n) := by
      have h1 : (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ) = a ^ n := by
        dsimp [a]; push_cast; rfl
      rw [← ENNReal.ofReal_natCast, h1]
    have halg : a ^ n * (C' * b ^ (-((N + n : ℕ) : ℤ))) = (C' / b ^ N) * (a / b) ^ n := by
      rw [zpow_neg, zpow_natCast, pow_add, div_pow]
      have hbN : b ^ N ≠ 0 := pow_ne_zero N (ne_of_gt hb_pos)
      have hbn : b ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      field_simp
    calc (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (C * b ^ (-((N + n : ℕ) : ℤ)))
        ≤ ENNReal.ofReal (a ^ n) * ENNReal.ofReal (C' * b ^ (-((N + n : ℕ) : ℤ))) := by
          rw [hcast_a]
          gcongr
      _ = ENNReal.ofReal (a ^ n * (C' * b ^ (-((N + n : ℕ) : ℤ)))) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg ha_nonneg n)]
      _ = ENNReal.ofReal ((C' / b ^ N) * (a / b) ^ n) := by
          rw [halg]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof0
    (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall hle)

/-- **主定理（Theorem 13 的零测度部分，`GaugeNull.mkMetric_strictLevel_null`）**：
    设 $k \ge 1$，$m : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 为任意单调非减函数，
    满足对一切 $n \ge 1$ 有 $m(1/Q_n) \le C (2k+1)^{-n}$。则由 $m$ 构造的 Hausdorff 测度
    （mathlib 的 `Measure.mkMetric m`）在严格子水平集 $\{x \in \mathbb{R} : \Lambda(x) < k/4\}$ 上为零。 -/
theorem mkMetric_strictLevel_null (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (C : ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      m (ENNReal.ofReal (1 / (Qsel n : ℝ))) ≤
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-(n : ℤ)))) :
    Measure.mkMetric m {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
  apply measure_mono_null (strictLevel_subset_iUnion_digitClass k hk)
  apply measure_iUnion_digitClass_null (k - 1) (Measure.mkMetric m)
  intro N hN m0 m1
  apply mkMetric_digitClass_null (k - 1) N m0 m1 m hm
  have hcost0 := tendsto_strictLevel_cost k hk N C
  have hle : ∀ n : ℕ,
      (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) *
        m (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))) ≤
      (((2 * (k - 1) + 1) ^ n : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (C * (2 * (k : ℝ) + 1) ^ (-((N + n : ℕ) : ℤ))) := by
    intro n
    gcongr
    exact hbound (N + n) (by omega)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcost0
    (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall hle)

/-- **推论（Corollary 14(ii)，更小阶规范在非严格子水平集上为零测度）**：
    设 $k \ge 0$，$g : \mathbb{R}_{\ge 0\infty} \to \mathbb{R}_{\ge 0\infty}$ 为任意单调非减函数，
    满足 $(2k+1)^n g(1/Q_n) \to 0$（即 $g(1/Q_n) / h_k(1/Q_n) \to 0$）。则
    `Measure.mkMetric g {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} = 0`。 -/
theorem mkMetric_levelSet_null_of_subgauge (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hsub : Tendsto (fun n : ℕ => (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) *
      g (ENNReal.ofReal (1 / (Qsel n : ℝ)))) atTop (nhds 0)) :
    Measure.mkMetric g {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
  apply measure_mono_null (levelSet_quarter_subset_iUnion_digitClass k)
  apply measure_iUnion_digitClass_null k (Measure.mkMetric g)
  intro N _hN m0 m1
  apply mkMetric_digitClass_null k N m0 m1 g hg
  have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop :=
    (tendsto_add_atTop_nat N).congr (fun n => Nat.add_comm n N)
  have hcomp : Tendsto (fun n : ℕ => (((2 * k + 1) ^ (N + n) : ℕ) : ℝ≥0∞) *
      g (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ)))) atTop (nhds 0) :=
    hsub.comp hshift
  have hle : ∀ n : ℕ,
      (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))) ≤
      (((2 * k + 1) ^ (N + n) : ℕ) : ℝ≥0∞) * g (ENNReal.ofReal (1 / (Qsel (N + n) : ℝ))) := by
    intro n
    have hpow : (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) ≤ (((2 * k + 1) ^ (N + n) : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
    exact mul_le_mul_of_nonneg_right hpow bot_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
    (Filter.Eventually.of_forall (fun _ => bot_le)) (Filter.Eventually.of_forall hle)

end

end GaugeNull

#print axioms GaugeNull.mkMetric_digitClass_null
#print axioms GaugeNull.mkMetric_strictLevel_null
#print axioms GaugeNull.mkMetric_levelSet_null_of_subgauge
