import Mathlib
import EpiFormal.GaugeNull
import EpiFormal.GaugeExact

/-!
# 显式临界规范函数 `critGauge` / `binaryGauge` 与非空开区间无穷测度定理（GaugeCircle）

本模块补全论文二 §6（Theorem 13、Corollary 14(i) 与 Theorem 16(ii)）的 Lean 4 Layer A 形式化：

1. **显式分片线性规范函数 `interpGauge b`（实例化 `critGauge k` 与 `binaryGauge`）**：
   - 构造与论文二 §6 完全一致的分片线性规范 $h_k(0)=0$、$h_k(1/Q_n) = (2k+1)^{-n}$（$n \ge 1$）、
     在 $[1/Q_{n+1}, 1/Q_n]$ 上线性插值并在 $t \ge 1/Q_1 = 1$ 取常值 $(2k+1)^{-1}$；
   - 严格证明单调性（`critGauge_mono` / `binaryGauge_mono`）、连续性（`critGauge_continuous` /
     `binaryGauge_continuous`，包含 $0^+$ 与 $\top$ 处连续性）及端点精确值（`critGauge_at_inv_Qsel` /
     `binaryGauge_at_inv_Qsel`）；
   - 直接实例化 `GaugeNull.mkMetric_strictLevel_null` 与 `GaugeExact.mkMetric_exactLevel_pos` /
     `mkMetric_exactLevel_eq_top` / `exactLevel_countable_cover_finite_mkMetric`，得到完全无需外部
     `hm_cont` 假设的 Theorem 13 显式完整定理。

2. **Corollary 14(i)：任意非空开区间 $(a, b) \subset \mathbb{R}$ 上的 $\mathcal{H}^{h_k}$ 无穷测度**：
   - 利用 $Q_j e - P_j = \delta_j$ 与 $P_j, Q_j$ 均为奇数，直接证明 $\delta_j / 2 \in L = \mathbb{Z} + \mathbb{Z}\frac{e+1}{2}$
     且 $0 < |\delta_j / 2| \to 0$，从而 $L$ 中存在任意小的正元素（不依赖 Kronecker 定理或 Haar 测度唯一性）；
   - 将正测度紧致 Cantor 树 `cantorTreeC k` 在第 $M$ 层分裂为 $(2k+1)^M$ 个直径 $\le 1/(2 Q_{J+M+1})$ 的柱集，
     选取最大测度柱集并用 $L$ 的小步长平移在任意非空开区间 $(a, b)$ 内摆放 $\Omega((b-a) Q_{J+M+1})$ 个互不相交拷贝，
     结合 $Q_{J+M+1} \ge (J+M+1)! \gg (2k+1)^M$ 严格证明：
     `Measure.mkMetric (critGauge k) ({x | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo a b) = ⊤`
     （以及在 $[0, 1]$ 与任何包含非空开区间的集合上的无穷测度）。

3. **Theorem 16(ii)：无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 在普适二进规范 `binaryGauge` 下的完整下界与无穷测度**：
   - 构造二值数字字母表 $\{-k, k\}$ 对应的均匀 $2$-叉紧致 Cantor 树 `binCantorTree k`，证明其完全含于
     $E_{\mathrm{lim}}(k/4) = \mathrm{unsignedExactLimitSet}\ k$ 且满足 $2$-叉树正测度下界；
   - 证明 `unsignedExactLimitSet k` 的 $L$-平移不变性，进而导出：
     - `mkMetric_binaryGauge_unsignedExactLimit_pos`
     - `mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top`
     - `mkMetric_binaryGauge_unsignedExactLimit_eq_top`
     - `binaryGauge_unsignedExactLimit_sigma_finite_cover`
     - `critGauge_unsignedExactLimit_null`
-/

open Real Filter Topology Set MeasureTheory Classification SpectralGap DimHCore DimHFinite
  FullSpectrumDiscrete GaugeNull GaugeExact WeightedExactDim
open scoped ENNReal NNReal

namespace GaugeCircle

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 第一部分：显式分片线性规范函数 `interpGauge`（`critGauge` 与 `binaryGauge`） -/

/-- 倒数尺度序列 $q_n = 1 / Q_n$。 -/
def invQ (n : ℕ) : ℝ := 1 / (Qsel n : ℝ)

lemma invQ_one : invQ 1 = 1 := by
  simp [invQ, Qsel_one]

lemma invQ_pos (n : ℕ) : 0 < invQ n := by
  unfold invQ
  have hQ : 0 < (Qsel n : ℝ) := by exact_mod_cast Classification.Qsel_pos n
  positivity

lemma invQ_succ_lt (n : ℕ) (hn : 1 ≤ n) : invQ (n + 1) < invQ n := by
  unfold invQ
  have hQ1 : 0 < (Qsel n : ℝ) := by exact_mod_cast Classification.Qsel_pos n
  have hlt : (Qsel n : ℝ) < (Qsel (n + 1) : ℝ) := by
    exact_mod_cast _root_.Qsel_lt_succ n hn
  exact one_div_lt_one_div_of_lt hQ1 hlt

lemma invQ_antitoneOn : AntitoneOn invQ (Set.Ici 1) := by
  intro m hm n hn hmn
  unfold invQ
  have hQpos : 0 < (Qsel m : ℝ) := by exact_mod_cast Classification.Qsel_pos m
  have hQle : (Qsel m : ℝ) ≤ (Qsel n : ℝ) := by
    exact_mod_cast _root_.Qsel_strictMono.monotoneOn hm hn hmn
  exact one_div_le_one_div_of_le hQpos hQle

lemma invQ_le_one {n : ℕ} (hn : 1 ≤ n) : invQ n ≤ 1 := by
  rw [← invQ_one]
  exact invQ_antitoneOn (Set.mem_Ici.mpr (le_refl 1)) (Set.mem_Ici.mpr hn) hn

lemma tendsto_invQ : Tendsto invQ atTop (nhds 0) :=
  Classification.Qsel_tendsto_atTop.const_div_atTop 1

/-- 第 $n$ 段 $[1/Q_{n+1}, 1/Q_n]$ 上的线性插值函数。 -/
def segVal (b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  b ^ (-((n + 1 : ℕ) : ℤ)) +
    ((t - invQ (n + 1)) / (invQ n - invQ (n + 1))) *
      (b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)))

lemma segVal_at_left (b : ℝ) (n : ℕ) :
    segVal b n (invQ (n + 1)) = b ^ (-((n + 1 : ℕ) : ℤ)) := by
  simp [segVal]

lemma segVal_at_right (b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    segVal b n (invQ n) = b ^ (-(n : ℤ)) := by
  have hne : invQ n - invQ (n + 1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (invQ_succ_lt n hn))
  simp [segVal, hne]

lemma segVal_continuous (b : ℝ) (n : ℕ) : Continuous (segVal b n) := by
  unfold segVal
  fun_prop

lemma segVal_mono {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n) : Monotone (segVal b n) := by
  intro s t hst
  have hq : 0 < invQ n - invQ (n + 1) := sub_pos.mpr (invQ_succ_lt n hn)
  have hpow : b ^ (-((n + 1 : ℕ) : ℤ)) ≤ b ^ (-(n : ℤ)) := by
    rw [zpow_le_zpow_iff_right₀ hb]
    omega
  have hdiff : 0 ≤ b ^ (-(n : ℤ)) - b ^ (-((n + 1 : ℕ) : ℤ)) := sub_nonneg.mpr hpow
  unfold segVal
  gcongr

lemma segVal_nonneg {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : invQ (n + 1) ≤ t) : 0 ≤ segVal b n t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have h1 : 0 ≤ b ^ (-((n + 1 : ℕ) : ℤ)) := zpow_nonneg (le_of_lt hb0) _
  have h2 := segVal_mono hb hn ht
  rw [segVal_at_left] at h2
  exact le_trans h1 h2

lemma segVal_le_right {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : t ≤ invQ n) : segVal b n t ≤ b ^ (-(n : ℤ)) := by
  have h := segVal_mono hb hn ht
  rwa [segVal_at_right b hn] at h

/-- 对 $0 < t < 1$，找出满足 $1/Q_{n+1} \le t < 1/Q_n$ 的唯一指标 $n \ge 1$。 -/
def interpIdx (t : ℝ) : ℕ :=
  if h : 0 < t ∧ t < 1 then
    Nat.find (show ∃ n : ℕ, 1 ≤ n ∧ invQ (n + 1) ≤ t by
      have hev := tendsto_invQ.eventually (Iio_mem_nhds h.1)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine ⟨max 1 N, le_max_left _ _, ?_⟩
      have h1 : invQ (max 1 N + 1) ≤ invQ (max 1 N) :=
        le_of_lt (invQ_succ_lt (max 1 N) (le_max_left _ _))
      have h2 : invQ (max 1 N) < t := hN (max 1 N) (le_max_right _ _)
      exact le_trans h1 (le_of_lt h2))
  else 1

lemma interpIdx_spec {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 ≤ interpIdx t ∧ invQ (interpIdx t + 1) ≤ t ∧ t < invQ (interpIdx t) := by
  have h : 0 < t ∧ t < 1 := ⟨ht0, ht1⟩
  have hex : ∃ n : ℕ, 1 ≤ n ∧ invQ (n + 1) ≤ t := by
    have hev := tendsto_invQ.eventually (Iio_mem_nhds h.1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max 1 N, le_max_left _ _, ?_⟩
    have h1 : invQ (max 1 N + 1) ≤ invQ (max 1 N) :=
      le_of_lt (invQ_succ_lt (max 1 N) (le_max_left _ _))
    have h2 : invQ (max 1 N) < t := hN (max 1 N) (le_max_right _ _)
    exact le_trans h1 (le_of_lt h2)
  have hdef : interpIdx t = Nat.find hex := by simp [interpIdx, h]
  have hspec := Nat.find_spec hex
  rw [← hdef] at hspec
  refine ⟨hspec.1, hspec.2, ?_⟩
  by_cases hn1 : interpIdx t = 1
  · rw [hn1, invQ_one]; exact ht1
  · have hm1 : 1 ≤ interpIdx t - 1 := by omega
    have hlt : interpIdx t - 1 < interpIdx t := by omega
    have hmin := Nat.find_min hex (by rw [← hdef]; exact hlt)
    push Not at hmin
    have hadd : interpIdx t - 1 + 1 = interpIdx t := by omega
    rw [hadd] at hmin
    exact hmin hm1

lemma interpIdx_eq_of_mem_Ico {t : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hlo : invQ (n + 1) ≤ t) (hhi : t < invQ n) : interpIdx t = n := by
  have ht0 : 0 < t := lt_of_lt_of_le (invQ_pos (n + 1)) hlo
  have ht1 : t < 1 := lt_of_lt_of_le hhi (invQ_le_one hn)
  obtain ⟨hm1, hmlo, hmhi⟩ := interpIdx_spec ht0 ht1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : interpIdx t + 1 ≤ n := by omega
    have hq : invQ n ≤ invQ (interpIdx t + 1) :=
      invQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hn) hle
    linarith
  · have hle : n + 1 ≤ interpIdx t := by omega
    have hq : invQ (interpIdx t) ≤ invQ (n + 1) :=
      invQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hm1) hle
    linarith

lemma interpIdx_antitone {s t : ℝ} (hs0 : 0 < s) (ht1 : t < 1) (hst : s ≤ t) :
    interpIdx t ≤ interpIdx s := by
  have hs1 : s < 1 := lt_of_le_of_lt hst ht1
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  obtain ⟨hn1, hnlo, _⟩ := interpIdx_spec hs0 hs1
  obtain ⟨hm1, _, hmhi⟩ := interpIdx_spec ht0 ht1
  by_contra hlt
  push Not at hlt
  have hle : interpIdx s + 1 ≤ interpIdx t := by omega
  have hq : invQ (interpIdx t) ≤ invQ (interpIdx s + 1) :=
    invQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hm1) hle
  linarith

/-- 实轴上的分片线性规范函数（$t \le 0$ 取 $0$，$t \ge 1$ 取 $b^{-1}$）。 -/
def interpGaugeReal (b : ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if 1 ≤ t then b⁻¹
  else segVal b (interpIdx t) t

lemma interpGaugeReal_le_zero (b : ℝ) {t : ℝ} (ht : t ≤ 0) :
    interpGaugeReal b t = 0 := by
  simp [interpGaugeReal, ht]

lemma interpGaugeReal_zero (b : ℝ) : interpGaugeReal b 0 = 0 :=
  interpGaugeReal_le_zero b (le_refl 0)

lemma interpGaugeReal_ge_one (b : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    interpGaugeReal b t = b⁻¹ := by
  have hnot : ¬ t ≤ 0 := by linarith
  simp [interpGaugeReal, hnot, ht]

lemma interpGaugeReal_eq_segVal {b : ℝ} (_hb : 1 < b) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (hlo : invQ (n + 1) ≤ t) (hhi : t ≤ invQ n) :
    interpGaugeReal b t = segVal b n t := by
  have ht0 : 0 < t := lt_of_lt_of_le (invQ_pos (n + 1)) hlo
  have hnot0 : ¬ t ≤ 0 := not_le.mpr ht0
  rcases eq_or_lt_of_le hhi with rfl | ht_lt
  · rw [segVal_at_right b hn]
    by_cases hn1 : n = 1
    · subst hn1
      rw [invQ_one, interpGaugeReal_ge_one b (le_refl 1)]
      simp [zpow_neg]
    · have hn2 : 2 ≤ n := by omega
      have hn' : 1 ≤ n - 1 := by omega
      have hadd : n - 1 + 1 = n := by omega
      have hlo' : invQ (n - 1 + 1) ≤ invQ n := by rw [hadd]
      have hhi' : invQ n < invQ (n - 1) := by
        simpa [hadd] using invQ_succ_lt (n - 1) hn'
      have ht1 : ¬ 1 ≤ invQ n := by
        have := lt_of_lt_of_le hhi' (invQ_le_one hn')
        linarith
      simp only [interpGaugeReal, hnot0, ↓reduceIte, ht1]
      rw [interpIdx_eq_of_mem_Ico hn' hlo' hhi']
      conv_lhs => rhs; rw [← hadd]
      rw [segVal_at_left, hadd]
  · have ht1 : ¬ 1 ≤ t := by
      have := lt_of_lt_of_le ht_lt (invQ_le_one hn)
      linarith
    simp only [interpGaugeReal, hnot0, ↓reduceIte, ht1]
    rw [interpIdx_eq_of_mem_Ico hn hlo ht_lt]

lemma interpGaugeReal_at_invQ {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n) :
    interpGaugeReal b (invQ n) = b ^ (-(n : ℤ)) := by
  rw [interpGaugeReal_eq_segVal hb hn (le_of_lt (invQ_succ_lt n hn)) (le_refl _),
    segVal_at_right b hn]

lemma interpGaugeReal_nonneg {b : ℝ} (hb : 1 < b) (t : ℝ) :
    0 ≤ interpGaugeReal b t := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  by_cases ht0 : t ≤ 0
  · rw [interpGaugeReal_le_zero b ht0]
  · by_cases ht1 : 1 ≤ t
    · rw [interpGaugeReal_ge_one b ht1]; positivity
    · have ht0' : 0 < t := lt_of_not_ge ht0
      have ht1' : t < 1 := lt_of_not_ge ht1
      obtain ⟨hn1, hnlo, _⟩ := interpIdx_spec ht0' ht1'
      simp only [interpGaugeReal, ht0, ↓reduceIte, ht1]
      exact segVal_nonneg hb hn1 hnlo

lemma interpGaugeReal_mono {b : ℝ} (hb : 1 < b) : Monotone (interpGaugeReal b) := by
  intro s t hst
  by_cases hs0 : s ≤ 0
  · rw [interpGaugeReal_le_zero b hs0]
    exact interpGaugeReal_nonneg hb t
  · have hs0' : 0 < s := lt_of_not_ge hs0
    have ht0' : 0 < t := lt_of_lt_of_le hs0' hst
    have ht0 : ¬ t ≤ 0 := not_le.mpr ht0'
    by_cases ht1 : 1 ≤ t
    · rw [interpGaugeReal_ge_one b ht1]
      by_cases hs1 : 1 ≤ s
      · rw [interpGaugeReal_ge_one b hs1]
      · have hs1' : s < 1 := lt_of_not_ge hs1
        obtain ⟨hn1, _, hnhi⟩ := interpIdx_spec hs0' hs1'
        simp only [interpGaugeReal, hs0, ↓reduceIte, hs1]
        have h1 := segVal_le_right hb hn1 (le_of_lt hnhi)
        have h2 : b ^ (-(interpIdx s : ℤ)) ≤ b⁻¹ := by
          rw [← zpow_neg_one b, zpow_le_zpow_iff_right₀ hb]
          omega
        exact le_trans h1 h2
    · have ht1' : t < 1 := lt_of_not_ge ht1
      have hs1' : s < 1 := lt_of_le_of_lt hst ht1'
      have hs1 : ¬ 1 ≤ s := not_le.mpr hs1'
      obtain ⟨hn1, hnlo, hnhi⟩ := interpIdx_spec hs0' hs1'
      obtain ⟨hm1, hmlo, hmhi⟩ := interpIdx_spec ht0' ht1'
      have hidx : interpIdx t ≤ interpIdx s := interpIdx_antitone hs0' ht1' hst
      simp only [interpGaugeReal, hs0, ht0, ↓reduceIte, hs1, ht1]
      rcases eq_or_lt_of_le hidx with heq | hlt
      · rw [heq]
        exact segVal_mono hb hn1 hst
      · have h1 := segVal_le_right hb hn1 (le_of_lt hnhi)
        have h2 := segVal_mono hb hm1 hmlo
        rw [segVal_at_left] at h2
        have hpow : b ^ (-(interpIdx s : ℤ)) ≤ b ^ (-((interpIdx t + 1 : ℕ) : ℤ)) := by
          rw [zpow_le_zpow_iff_right₀ hb]
          omega
        exact le_trans h1 (le_trans hpow h2)

lemma interpGaugeReal_continuous {b : ℝ} (hb : 1 < b) : Continuous (interpGaugeReal b) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · have hev : ∀ᶠ y in nhds t, (0 : ℝ) = interpGaugeReal b y := by
      filter_upwards [Iio_mem_nhds ht_neg] with y hy
      exact (interpGaugeReal_le_zero b (le_of_lt hy)).symm
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr hev
  · rw [Metric.continuousAt_iff]
    intro ε hε
    have hb_inv : 0 ≤ b⁻¹ := by positivity
    have hb_lt1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
    have hpow0 : Tendsto (fun n : ℕ => b⁻¹ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hb_inv hb_lt1
    obtain ⟨N, hN⟩ := (hpow0.eventually (Iio_mem_nhds hε)).exists
    set n := max 1 N
    have hn1 : 1 ≤ n := le_max_left _ _
    have hNle : N ≤ n := le_max_right _ _
    have hbn : b ^ (-(n : ℤ)) < ε := by
      have h1 : b ^ (-(n : ℤ)) = b⁻¹ ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
      have h2 : b⁻¹ ^ n ≤ b⁻¹ ^ N := pow_le_pow_of_le_one hb_inv (le_of_lt hb_lt1) hNle
      linarith
    refine ⟨invQ n, invQ_pos n, fun {y} hy => ?_⟩
    rw [interpGaugeReal_zero, Real.dist_eq, sub_zero, abs_of_nonneg (interpGaugeReal_nonneg hb y)]
    have hy_lt : y < invQ n := by
      rw [Real.dist_eq, sub_zero] at hy
      exact (abs_lt.mp hy).2
    calc interpGaugeReal b y
        ≤ interpGaugeReal b (invQ n) := interpGaugeReal_mono hb (le_of_lt hy_lt)
      _ = b ^ (-(n : ℤ)) := interpGaugeReal_at_invQ hb hn1
      _ < ε := hbn
  · rcases lt_trichotomy t 1 with ht_lt1 | rfl | ht_gt1
    · set n := interpIdx t
      obtain ⟨hn1, hnlo, hnhi⟩ := interpIdx_spec ht_pos ht_lt1
      rcases eq_or_lt_of_le hnlo with h_eq | h_gt
      · have hleft : ContinuousWithinAt (interpGaugeReal b) (Iic t) t := by
          have hmem : Ioc (invQ (n + 2)) t ∈ nhdsWithin t (Iic t) := by
            rw [← Ioi_inter_Iic]
            exact Filter.inter_mem
              (nhdsWithin_le_nhds (Ioi_mem_nhds (by rw [← h_eq]; exact invQ_succ_lt (n + 1) (by omega))))
              self_mem_nhdsWithin
          have heq : ∀ᶠ y in nhdsWithin t (Iic t), interpGaugeReal b y = segVal b (n + 1) y := by
            filter_upwards [hmem] with y hy
            exact interpGaugeReal_eq_segVal hb (by omega) (le_of_lt hy.1) (by rw [h_eq]; exact hy.2)
          have hfx : interpGaugeReal b t = segVal b (n + 1) t :=
            interpGaugeReal_eq_segVal hb (by omega)
              (le_of_lt (by rw [← h_eq]; exact invQ_succ_lt (n + 1) (by omega))) (by rw [h_eq])
          exact (segVal_continuous b (n + 1)).continuousWithinAt.congr_of_eventuallyEq heq hfx
        have hright : ContinuousWithinAt (interpGaugeReal b) (Ici t) t := by
          have hmem : Ico t (invQ n) ∈ nhdsWithin t (Ici t) := by
            rw [← Ici_inter_Iio]
            exact Filter.inter_mem self_mem_nhdsWithin
              (nhdsWithin_le_nhds (Iio_mem_nhds hnhi))
          have heq : ∀ᶠ y in nhdsWithin t (Ici t), interpGaugeReal b y = segVal b n y := by
            filter_upwards [hmem] with y hy
            exact interpGaugeReal_eq_segVal hb hn1 (by rw [h_eq]; exact hy.1) (le_of_lt hy.2)
          have hfx : interpGaugeReal b t = segVal b n t :=
            interpGaugeReal_eq_segVal hb hn1 hnlo (le_of_lt hnhi)
          exact (segVal_continuous b n).continuousWithinAt.congr_of_eventuallyEq heq hfx
        have hunion := hleft.union hright
        rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
      · have hev : ∀ᶠ y in nhds t, segVal b n y = interpGaugeReal b y := by
          filter_upwards [Ioo_mem_nhds h_gt hnhi] with y hy
          exact (interpGaugeReal_eq_segVal hb hn1 (le_of_lt hy.1) (le_of_lt hy.2)).symm
        exact (segVal_continuous b n).continuousAt.congr hev
    · have hleft : ContinuousWithinAt (interpGaugeReal b) (Iic (1 : ℝ)) 1 := by
        have hmem : Ioc (invQ 2) (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Iic 1) := by
          rw [← Ioi_inter_Iic]
          refine Filter.inter_mem (nhdsWithin_le_nhds (Ioi_mem_nhds ?_)) self_mem_nhdsWithin
          rw [← invQ_one]
          exact invQ_succ_lt 1 (le_refl 1)
        have heq : ∀ᶠ y in nhdsWithin (1 : ℝ) (Iic 1), interpGaugeReal b y = segVal b 1 y := by
          filter_upwards [hmem] with y hy
          exact interpGaugeReal_eq_segVal hb (le_refl 1) (le_of_lt hy.1)
            (by simpa [invQ_one] using hy.2)
        have hfx : interpGaugeReal b 1 = segVal b 1 1 :=
          interpGaugeReal_eq_segVal hb (le_refl 1)
            (by rw [← invQ_one]; exact le_of_lt (invQ_succ_lt 1 (le_refl 1)))
            (by simp [invQ_one])
        exact (segVal_continuous b 1).continuousWithinAt.congr_of_eventuallyEq heq hfx
      have hright : ContinuousWithinAt (interpGaugeReal b) (Ici (1 : ℝ)) 1 := by
        have heq : ∀ᶠ y in nhdsWithin (1 : ℝ) (Ici 1), interpGaugeReal b y = b⁻¹ := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          exact interpGaugeReal_ge_one b hy
        exact continuousWithinAt_const.congr_of_eventuallyEq heq (interpGaugeReal_ge_one b (le_refl 1))
      have hunion := hleft.union hright
      rwa [Iic_union_Ici, continuousWithinAt_univ] at hunion
    · have hev : ∀ᶠ y in nhds t, b⁻¹ = interpGaugeReal b y := by
        filter_upwards [Ioi_mem_nhds ht_gt1] with y hy
        exact (interpGaugeReal_ge_one b (le_of_lt hy)).symm
      exact (continuousAt_const : ContinuousAt (fun _ : ℝ => b⁻¹) t).congr hev

/-- `ℝ≥0∞` 上的显式分片线性规范函数 $g_b$（$1 < b$）。 -/
def interpGauge (b : ℝ) (x : ℝ≥0∞) : ℝ≥0∞ :=
  if 1 ≤ x then ENNReal.ofReal b⁻¹
  else ENNReal.ofReal (interpGaugeReal b x.toReal)

lemma interpGauge_eq_ofReal_toReal {b : ℝ} (_hb : 1 < b) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    interpGauge b x = ENNReal.ofReal (interpGaugeReal b x.toReal) := by
  by_cases hx1 : 1 ≤ x
  · have hx1R : 1 ≤ x.toReal := by
      simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hx).mpr hx1
    simp [interpGauge, hx1, interpGaugeReal_ge_one b hx1R]
  · simp [interpGauge, hx1]

lemma interpGauge_zero (b : ℝ) : interpGauge b 0 = 0 := by
  have h0 : ¬ (1 : ℝ≥0∞) ≤ 0 := by norm_num
  simp [interpGauge, h0, interpGaugeReal_zero]

lemma interpGauge_at_inv_Qsel {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 1 ≤ n) :
    interpGauge b (ENNReal.ofReal (1 / (Qsel n : ℝ))) = ENNReal.ofReal (b ^ (-(n : ℤ))) := by
  rw [interpGauge_eq_ofReal_toReal hb ENNReal.ofReal_ne_top]
  have hpos : 0 ≤ 1 / (Qsel n : ℝ) := le_of_lt (invQ_pos n)
  rw [ENNReal.toReal_ofReal hpos]
  change ENNReal.ofReal (interpGaugeReal b (invQ n)) = _
  rw [interpGaugeReal_at_invQ hb hn]

lemma interpGauge_mono {b : ℝ} (hb : 1 < b) : Monotone (interpGauge b) := by
  intro x y hxy
  by_cases hy1 : 1 ≤ y
  · by_cases hx1 : 1 ≤ x
    · simp [interpGauge, hx1, hy1]
    · have hx_ne : x ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hx1 |>.trans ENNReal.one_lt_top)
      have hx1R : x.toReal ≤ 1 := by
        have := (ENNReal.toReal_le_toReal hx_ne ENNReal.one_ne_top).mpr (le_of_not_ge hx1)
        simpa using this
      simp only [interpGauge, hx1, ↓reduceIte, hy1]
      apply ENNReal.ofReal_le_ofReal
      calc interpGaugeReal b x.toReal ≤ interpGaugeReal b 1 := interpGaugeReal_mono hb hx1R
        _ = b⁻¹ := interpGaugeReal_ge_one b (le_refl 1)
  · have hx1 : ¬ 1 ≤ x := fun h => hy1 (le_trans h hxy)
    have hy_ne : y ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hy1 |>.trans ENNReal.one_lt_top)
    rw [interpGauge_eq_ofReal_toReal hb (ne_top_of_le_ne_top hy_ne hxy),
      interpGauge_eq_ofReal_toReal hb hy_ne]
    exact ENNReal.ofReal_le_ofReal
      (interpGaugeReal_mono hb ((ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hy_ne hxy) hy_ne).mpr hxy))

lemma interpGauge_continuous {b : ℝ} (hb : 1 < b) : Continuous (interpGauge b) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx1 : 1 < x
  · have hev : ∀ᶠ y in nhds x, ENNReal.ofReal b⁻¹ = interpGauge b y := by
      filter_upwards [Ioi_mem_nhds hx1] with y hy
      have hy1 : (1 : ℝ≥0∞) ≤ y := le_of_lt hy
      simp [interpGauge, hy1]
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ≥0∞ => ENNReal.ofReal b⁻¹) x).congr hev
  · have hx_le : x ≤ 1 := le_of_not_gt hx1
    have hx_lt_top : x < ⊤ := lt_of_le_of_lt hx_le ENNReal.one_lt_top
    have hx_ne : x ≠ ⊤ := ne_of_lt hx_lt_top
    have hev : ∀ᶠ y in nhds x, ENNReal.ofReal (interpGaugeReal b y.toReal) = interpGauge b y := by
      filter_upwards [Iio_mem_nhds hx_lt_top] with y hy
      exact (interpGauge_eq_ofReal_toReal hb (ne_of_lt hy)).symm
    have hcomp : ContinuousAt (fun y : ℝ≥0∞ => ENNReal.ofReal (interpGaugeReal b y.toReal)) x :=
      ENNReal.continuous_ofReal.continuousAt.comp
        ((interpGaugeReal_continuous hb).continuousAt.comp (ENNReal.continuousAt_toReal hx_ne))
    exact hcomp.congr hev

/-- 临界能级 $k/4$（$k \ge 1$）的显式分片线性临界规范 $h_k$（底数 $2k+1$）。 -/
def critGauge (k : ℕ) : ℝ≥0∞ → ℝ≥0∞ :=
  interpGauge (2 * (k : ℝ) + 1)

/-- 无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 的普适二进规范 $g_2$（底数 $2$）。 -/
def binaryGauge : ℝ≥0∞ → ℝ≥0∞ :=
  interpGauge 2

lemma critGauge_base_gt_one (k : ℕ) (hk : 1 ≤ k) : (1 : ℝ) < 2 * (k : ℝ) + 1 := by
  have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

lemma critGauge_zero (k : ℕ) : critGauge k 0 = 0 :=
  interpGauge_zero _

lemma critGauge_at_inv_Qsel (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    critGauge k (ENNReal.ofReal (1 / (Qsel n : ℝ))) =
      ENNReal.ofReal ((2 * (k : ℝ) + 1) ^ (-(n : ℤ))) :=
  interpGauge_at_inv_Qsel (critGauge_base_gt_one k hk) hn

lemma critGauge_mono (k : ℕ) (hk : 1 ≤ k) : Monotone (critGauge k) :=
  interpGauge_mono (critGauge_base_gt_one k hk)

lemma critGauge_continuous (k : ℕ) (hk : 1 ≤ k) : Continuous (critGauge k) :=
  interpGauge_continuous (critGauge_base_gt_one k hk)

lemma binaryGauge_zero : binaryGauge 0 = 0 :=
  interpGauge_zero 2

lemma binaryGauge_at_inv_Qsel {n : ℕ} (hn : 1 ≤ n) :
    binaryGauge (ENNReal.ofReal (1 / (Qsel n : ℝ))) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) :=
  interpGauge_at_inv_Qsel (by norm_num) hn

lemma binaryGauge_mono : Monotone binaryGauge :=
  interpGauge_mono (by norm_num)

lemma binaryGauge_continuous : Continuous binaryGauge :=
  interpGauge_continuous (by norm_num)

lemma critGauge_ge_one (k : ℕ) {x : ℝ≥0∞} (hx : 1 ≤ x) :
    critGauge k x = ENNReal.ofReal ((2 * (k : ℝ) + 1)⁻¹) := by
  simp [critGauge, interpGauge, hx]

lemma critGauge_eq_segVal (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (hlo : invQ (n + 1) ≤ t) (hhi : t ≤ invQ n) :
    critGauge k (ENNReal.ofReal t) =
      ENNReal.ofReal (segVal (2 * (k : ℝ) + 1) n t) := by
  have ht0 : 0 ≤ t := le_trans (le_of_lt (invQ_pos (n + 1))) hlo
  rw [critGauge, interpGauge_eq_ofReal_toReal (critGauge_base_gt_one k hk) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal ht0, interpGaugeReal_eq_segVal (critGauge_base_gt_one k hk) hn hlo hhi]

lemma binaryGauge_ge_one {x : ℝ≥0∞} (hx : 1 ≤ x) :
    binaryGauge x = ENNReal.ofReal (2⁻¹ : ℝ) := by
  simp [binaryGauge, interpGauge, hx]

lemma binaryGauge_eq_segVal {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (hlo : invQ (n + 1) ≤ t) (hhi : t ≤ invQ n) :
    binaryGauge (ENNReal.ofReal t) = ENNReal.ofReal (segVal 2 n t) := by
  have ht0 : 0 ≤ t := le_trans (le_of_lt (invQ_pos (n + 1))) hlo
  rw [binaryGauge, interpGauge_eq_ofReal_toReal (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal ht0, interpGaugeReal_eq_segVal (by norm_num) hn hlo hhi]

/-! ### 消除外部 `hm_cont` 假设的 Theorem 13 显式完整实例化 -/

/-- **Theorem 13 显式规范版（严格子水平集零测度）**：$\mathcal{H}^{h_k}(\{\Lambda < k/4\}) = 0$。 -/
theorem mkMetric_critGauge_strictLevel_null (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
  refine GaugeNull.mkMetric_strictLevel_null k hk (critGauge k) (critGauge_mono k hk) 1 ?_
  intro n hn
  rw [critGauge_at_inv_Qsel k hk hn, one_mul]

/-- **Theorem 13 显式规范版（精确水平集正测度）**：$\mathcal{H}^{h_k}(\{\Lambda = k/4\}) > 0$。 -/
theorem mkMetric_critGauge_exactLevel_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Measure.mkMetric (critGauge k) {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
  set b : ℝ := 2 * (k : ℝ) + 1
  have hb_pos : 0 < b := by positivity
  refine GaugeExact.mkMetric_exactLevel_pos k hk (critGauge k)
    (critGauge_mono k hk) (critGauge_continuous k hk) 1 (1 / b) (by positivity) ?_ ?_
  · intro n hn
    rw [critGauge_at_inv_Qsel k hk hn, one_mul]
  · intro n
    rw [critGauge_at_inv_Qsel k hk (by omega : 1 ≤ n + 1)]
    apply ENNReal.ofReal_le_ofReal
    have halg : (1 / b) * b ^ (-(n : ℤ)) = b ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      have hbn : b ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      have hb0 : b ≠ 0 := ne_of_gt hb_pos
      field_simp
    exact le_of_eq halg

/-- **Theorem 13 显式规范版（精确水平集在 $\mathbb{R}$ 上无穷测度）**：
    $\mathcal{H}^{h_k}(\{\Lambda = k/4\}) = \top$。 -/
theorem mkMetric_critGauge_exactLevel_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ := by
  set b : ℝ := 2 * (k : ℝ) + 1
  have hb_pos : 0 < b := by positivity
  refine GaugeExact.mkMetric_exactLevel_eq_top k hk (critGauge k)
    (critGauge_mono k hk) (critGauge_continuous k hk) 1 (1 / b) (by positivity) ?_ ?_
  · intro n hn
    rw [critGauge_at_inv_Qsel k hk hn, one_mul]
  · intro n
    rw [critGauge_at_inv_Qsel k hk (by omega : 1 ≤ n + 1)]
    apply ENNReal.ofReal_le_ofReal
    have halg : (1 / b) * b ^ (-(n : ℤ)) = b ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      have hbn : b ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      have hb0 : b ≠ 0 := ne_of_gt hb_pos
      field_simp
    exact le_of_eq halg

/-- **Theorem 13 显式规范版（$\sigma$-有限可数覆盖分解）**。 -/
theorem critGauge_exactLevel_sigma_finite_cover (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (critGauge k) (E i) < ⊤ := by
  refine GaugeExact.exactLevel_countable_cover_finite_mkMetric k (critGauge k)
    (critGauge_mono k hk) 1 ?_
  intro n hn
  rw [critGauge_at_inv_Qsel k hk hn, one_mul]

/-! ## 第二部分：$L$ 中任意小正元素与通用柱集分裂—平移开区间无穷测度引理 -/

lemma nat_mul_mem_latticeL {y : ℝ} (hy : y ∈ Classification.latticeL) (m : ℕ) :
    (m : ℝ) * y ∈ Classification.latticeL := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨(m : ℤ) * a, (m : ℤ) * b, ?_⟩
  push_cast
  ring

lemma int_mul_mem_latticeL {y : ℝ} (hy : y ∈ Classification.latticeL) (m : ℤ) :
    (m : ℝ) * y ∈ Classification.latticeL := by
  rcases hy with ⟨a, b, rfl⟩
  refine ⟨m * a, m * b, ?_⟩
  push_cast
  ring

lemma add_mem_latticeL {y z : ℝ} (hy : y ∈ Classification.latticeL)
    (hz : z ∈ Classification.latticeL) : y + z ∈ Classification.latticeL := by
  rcases hy with ⟨a₁, b₁, rfl⟩
  rcases hz with ⟨a₂, b₂, rfl⟩
  refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
  push_cast
  ring

/-- 从 `deltaSel` 构造 $L$ 中严格正的任意小元素：由于 $P_j, Q_j$ 均奇，
    $\delta_j / 2 = Q_j \frac{e+1}{2} - \frac{P_j+Q_j}{2} \in L$ 且 $0 < |\delta_j / 2| \to 0$。 -/
lemma exists_mem_latticeL_pos_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ Classification.latticeL, 0 < y ∧ y < ε := by
  have hev : ∀ᶠ j : ℕ in atTop, |deltaSel j| / 2 < ε := by
    have hhalf : Tendsto (fun j : ℕ => |deltaSel j| / 2) atTop (nhds 0) := by
      have h1 : Tendsto (fun j : ℕ => |deltaSel j|) atTop (nhds 0) := by
        simpa using deltaSel_tendsto_zero.abs
      simpa using h1.div_const 2
    exact hhalf.eventually (Iio_mem_nhds hε)
  obtain ⟨j, hjε, hj1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have hsign : (-1 : ℝ) ^ j * deltaSel j = |deltaSel j| := _root_.sign_eq_abs j hj1
  have hpos_abs : 0 < |deltaSel j| := by
    rw [← hsign]
    exact _root_.Hermite.sign_alternation j hj1
  have hPQ_even : Even (Psel j + Qsel j) := by
    obtain ⟨u, hu⟩ := Classification.Psel_odd j
    obtain ⟨v, hv⟩ := Classification.Qsel_odd j
    exact ⟨u + v + 1, by linarith⟩
  obtain ⟨K, hK⟩ := even_iff_two_dvd.mp hPQ_even
  have hKR : (2 : ℝ) * (K : ℝ) = (Psel j : ℝ) + (Qsel j : ℝ) := by exact_mod_cast hK.symm
  have hhalf_mem : deltaSel j / 2 ∈ Classification.latticeL := by
    refine ⟨-K, Qsel j, ?_⟩
    unfold deltaSel
    push_cast
    linarith
  have hpow_cases : (-1 : ℝ) ^ j = 1 ∨ (-1 : ℝ) ^ j = -1 := by
    rcases Nat.even_or_odd j with he | ho
    · left; exact he.neg_one_pow
    · right; exact ho.neg_one_pow
  have habs_mem : |deltaSel j| / 2 ∈ Classification.latticeL := by
    rcases hpow_cases with hp | hp
    · have heq : |deltaSel j| / 2 = deltaSel j / 2 := by rw [← hsign, hp, one_mul]
      rwa [heq]
    · have heq : |deltaSel j| / 2 = -(deltaSel j / 2) := by
        rw [← hsign, hp]; ring
      rw [heq]
      exact GaugeExact.neg_mem_latticeL hhalf_mem
  exact ⟨|deltaSel j| / 2, habs_mem, by linarith, hjε⟩

/-- 在任意非空开区间 $(a, b)$ 内放置 $N = \lfloor (b-a)/(3r) \rfloor$ 个互不相交的
    $[c - r, c + r]$ 的 $L$-平移拷贝。 -/
lemma exists_disjoint_latticeL_translates_in_Ioo
    {a b c r : ℝ} (hab : a < b) (hr : 0 < r) :
    let N : ℕ := Nat.floor ((b - a) / (3 * r))
    ∃ t : Fin N → ℝ,
      (∀ i, t i ∈ Classification.latticeL) ∧
      (∀ i, Set.Icc (c + t i - r) (c + t i + r) ⊆ Set.Ioo a b) ∧
      Pairwise (fun i j =>
        Disjoint (Set.Icc (c + t i - r) (c + t i + r))
                 (Set.Icc (c + t j - r) (c + t j + r))) := by
  intro N
  obtain ⟨y, hyL, hy_pos, hy_lt⟩ := exists_mem_latticeL_pos_lt r hr
  set m : ℕ := Nat.floor (2 * r / y) + 1
  set s : ℝ := (m : ℝ) * y
  have hs_mem : s ∈ Classification.latticeL := nat_mul_mem_latticeL hyL m
  have hs_gt : 2 * r < s := by
    have hm_gt : 2 * r / y < (m : ℝ) := by
      dsimp [m]; push_cast; exact Nat.lt_floor_add_one _
    have := (div_lt_iff₀ hy_pos).mp hm_gt
    linarith
  have hs_lt : s < 3 * r := by
    have hm_le : (m : ℝ) ≤ 2 * r / y + 1 := by
      dsimp [m]; push_cast
      linarith [Nat.floor_le (by positivity : 0 ≤ 2 * r / y)]
    have hmul : (m : ℝ) * y ≤ (2 * r / y + 1) * y :=
      mul_le_mul_of_nonneg_right hm_le (le_of_lt hy_pos)
    have heq : (2 * r / y + 1) * y = 2 * r + y := by field_simp
    linarith
  set k₀ : ℤ := Int.floor ((a + r - c) / y) + 1
  set t₀ : ℝ := (k₀ : ℝ) * y
  have ht₀_mem : t₀ ∈ Classification.latticeL := int_mul_mem_latticeL hyL k₀
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
      mul_le_mul_of_nonneg_right hk_le (le_of_lt hy_pos)
    have heq : ((a + r - c) / y + 1) * y = a + r - c + y := by field_simp
    linarith
  refine ⟨fun i => t₀ + (i.1 : ℝ) * s, ?_, ?_, ?_⟩
  · intro i
    exact add_mem_latticeL ht₀_mem (nat_mul_mem_latticeL hs_mem i.1)
  · intro i x hx
    have hi_nonneg : 0 ≤ (i.1 : ℝ) * s := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hlo : a < x := by linarith [hx.1]
    have hi_le : ((i.1 + 1 : ℕ) : ℝ) ≤ (b - a) / (3 * r) := by
      have h1 : i.1 + 1 ≤ N := i.2
      have h2 : ((i.1 + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
      have h3 : (N : ℝ) ≤ (b - a) / (3 * r) :=
        Nat.floor_le (div_nonneg (sub_nonneg.mpr (le_of_lt hab)) (by positivity))
      exact le_trans h2 h3
    have hmul3 : 3 * ((i.1 + 1 : ℕ) : ℝ) * r ≤ b - a := by
      have h3r : 0 < 3 * r := by positivity
      have := (le_div_iff₀ h3r).mp hi_le
      linarith
    have hhi : x < b := by
      have hmul_s : (i.1 : ℝ) * s ≤ (i.1 : ℝ) * (3 * r) :=
        mul_le_mul_of_nonneg_left (le_of_lt hs_lt) (Nat.cast_nonneg _)
      have hcast : ((i.1 + 1 : ℕ) : ℝ) = (i.1 : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hmul3
      linarith [hx.2]
    exact ⟨hlo, hhi⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · have hij1 : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hlt
      have hstep : (i.1 : ℝ) * s + r < (j.1 : ℝ) * s - r := by
        have h1 : ((i.1 : ℝ) + 1) * s ≤ (j.1 : ℝ) * s :=
          mul_le_mul_of_nonneg_right hij1 (by linarith)
        linarith
      linarith [hxi.2, hxj.1]
    · have hji1 : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast hlt
      have hstep : (j.1 : ℝ) * s + r < (i.1 : ℝ) * s - r := by
        have h1 : ((j.1 : ℝ) + 1) * s ≤ (i.1 : ℝ) * s :=
          mul_le_mul_of_nonneg_right hji1 (by linarith)
        linarith
      linarith [hxj.2, hxi.1]

/-- **通用定理（紧致树分裂 + $L$-平移导出任意非空开区间 $(a, b)$ 上无穷测度）**：
    设 $\mu = \mathrm{Measure.mkMetric}\ m$，$K \subseteq \mathbb{R}$ 为满足 $\mu(K) > 0$ 的紧致集，
    在每个深度 $M$ 可被 $b^M$ 个半径 $r_M \le 1 / (4 Q_{J+M+1})$ 的闭区间覆盖；
    若集合 $E \subseteq \mathbb{R}$ 在 $L$-平移下不变且 $\mu(K \setminus E) = 0$，
    则对任意非空开区间 $(a, b)$ 有 $\mu(E \cap (a, b)) = \top$。 -/
theorem mkMetric_inter_Ioo_eq_top_of_compact_tree
    (m : ℝ≥0∞ → ℝ≥0∞) (K E : Set ℝ)
    (hK_comp : IsCompact K) (hK_pos : 0 < Measure.mkMetric m K)
    (hKE_null : Measure.mkMetric m (K \ E) = 0)
    (hE_inv : ∀ y ∈ Classification.latticeL, (fun x : ℝ => x + y) ⁻¹' E = E)
    (b J : ℕ) (hb : 1 ≤ b) (hJ : 1 ≤ J)
    (center : ∀ M : ℕ, (Fin M → Fin b) → ℝ)
    (rad : ℕ → ℝ) (hrad_pos : ∀ M, 0 < rad M)
    (hrad_le : ∀ M, rad M ≤ 1 / (4 * (Qsel (J + M + 1) : ℝ)))
    (hK_cov : ∀ M : ℕ, K ⊆ ⋃ w : Fin M → Fin b,
      Set.Icc (center M w - rad M) (center M w + rad M))
    {a b_end : ℝ} (hab : a < b_end) :
    Measure.mkMetric m (E ∩ Set.Ioo a b_end) = ⊤ := by
  set μ : Measure ℝ := Measure.mkMetric m
  by_contra hne_top
  have hfin : μ (E ∩ Set.Ioo a b_end) < ⊤ := lt_top_iff_ne_top.mpr hne_top
  set V : ℝ := (μ (E ∩ Set.Ioo a b_end)).toReal
  have hV_nonneg : 0 ≤ V := ENNReal.toReal_nonneg
  have hV_eq : ENNReal.ofReal V = μ (E ∩ Set.Ioo a b_end) := ENNReal.ofReal_toReal hne_top
  have hmin_pos : 0 < min (μ K) 1 := lt_min hK_pos zero_lt_one
  have hmin_lt_top : min (μ K) 1 < ⊤ := lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top
  set c₀ : ℝ := (min (μ K) 1).toReal
  have hc₀_pos : 0 < c₀ := ENNReal.toReal_pos (ne_of_gt hmin_pos) (ne_of_lt hmin_lt_top)
  have hc₀_le_K : ENNReal.ofReal c₀ ≤ μ K := by
    rw [ENNReal.ofReal_toReal (ne_of_lt hmin_lt_top)]
    exact min_le_left _ _
  have hbound_M : ∀ M : ℕ,
      ((b_end - a) * (Qsel (J + M + 1) : ℝ) - 1) * c₀ ≤ ((b ^ M : ℕ) : ℝ) * V := by
    intro M
    let I_M : (Fin M → Fin b) → Set ℝ :=
      fun w => Set.Icc (center M w - rad M) (center M w + rad M)
    have hsum_ge : μ K ≤ ∑ w : Fin M → Fin b, μ (K ∩ I_M w) := by
      have hsub : K ⊆ ⋃ w : Fin M → Fin b, K ∩ I_M w := by
        intro x hx
        obtain ⟨w, hw⟩ := Set.mem_iUnion.mp (hK_cov M hx)
        exact Set.mem_iUnion.mpr ⟨w, hx, hw⟩
      exact le_trans (measure_mono hsub) (measure_iUnion_fintype_le _ _)
    have hex_w : ∃ w : Fin M → Fin b,
        ENNReal.ofReal c₀ ≤ ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w) := by
      by_contra hno
      push Not at hno
      have h_lt_top : ∀ w : Fin M → Fin b, ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w) ≠ ⊤ :=
        fun w => ne_of_lt (lt_trans (hno w) ENNReal.ofReal_lt_top)
      have h_lt_R : ∀ w : Fin M → Fin b,
          (((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal < c₀ := fun w => by
        have h1 := (ENNReal.toReal_lt_toReal (h_lt_top w) ENNReal.ofReal_ne_top).mpr (hno w)
        rwa [ENNReal.toReal_ofReal (le_of_lt hc₀_pos)] at h1
      have hne_univ : (Finset.univ : Finset (Fin M → Fin b)).Nonempty :=
        ⟨fun _ => ⟨0, by omega⟩, Finset.mem_univ _⟩
      have hcard : (Finset.univ : Finset (Fin M → Fin b)).card = b ^ M := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hsum_lt_R :
          ∑ w : Fin M → Fin b, (((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal <
            ((b ^ M : ℕ) : ℝ) * c₀ := by
        calc ∑ w : Fin M → Fin b, (((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal
            < ∑ _w : Fin M → Fin b, c₀ :=
              Finset.sum_lt_sum_of_nonempty hne_univ (fun w _ => h_lt_R w)
          _ = ((b ^ M : ℕ) : ℝ) * c₀ := by
              rw [Finset.sum_const, hcard, nsmul_eq_mul]
      have hsum_toReal :
          (∑ w : Fin M → Fin b, ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal =
            ∑ w : Fin M → Fin b, (((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal :=
        ENNReal.toReal_sum (fun w _ => h_lt_top w)
      have hsum_ge_E : ((b ^ M : ℕ) : ℝ≥0∞) * ENNReal.ofReal c₀ ≤
          ∑ w : Fin M → Fin b, ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w) := by
        calc ((b ^ M : ℕ) : ℝ≥0∞) * ENNReal.ofReal c₀
            ≤ ((b ^ M : ℕ) : ℝ≥0∞) * μ K := by gcongr
          _ ≤ ((b ^ M : ℕ) : ℝ≥0∞) * ∑ w : Fin M → Fin b, μ (K ∩ I_M w) := by gcongr
          _ = ∑ w : Fin M → Fin b, ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w) :=
              Finset.mul_sum _ _ _
      have hsum_ne_top : (∑ w : Fin M → Fin b, ((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr (fun w _ => h_lt_top w)
      have hge_R : ((b ^ M : ℕ) : ℝ) * c₀ ≤
          ∑ w : Fin M → Fin b, (((b ^ M : ℕ) : ℝ≥0∞) * μ (K ∩ I_M w)).toReal := by
        rw [← hsum_toReal]
        have h1 := ENNReal.toReal_mono hsum_ne_top hsum_ge_E
        have h2 : (((b ^ M : ℕ) : ℝ≥0∞) * ENNReal.ofReal c₀).toReal =
            ((b ^ M : ℕ) : ℝ) * c₀ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (le_of_lt hc₀_pos)]
        linarith
      linarith
    obtain ⟨w, hw⟩ := hex_w
    set K' : Set ℝ := K ∩ I_M w
    have hK'_comp : IsCompact K' := hK_comp.inter_right isClosed_Icc
    set N : ℕ := Nat.floor ((b_end - a) / (3 * rad M))
    obtain ⟨t, htL, ht_sub, ht_disj⟩ :=
      exists_disjoint_latticeL_translates_in_Ioo (c := center M w) hab (hrad_pos M)
    let A : Fin N → Set ℝ := fun i => (fun x : ℝ => x + t i) '' K'
    have hA_meas : ∀ i : Fin N, MeasurableSet (A i) := fun i =>
      (hK'_comp.image (continuous_id.add continuous_const)).measurableSet
    have hA_sub_Ioo : ∀ i : Fin N, A i ⊆ Set.Ioo a b_end := by
      rintro i _ ⟨x, hx, rfl⟩
      exact ht_sub i ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    have hA_disj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro y ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, heq⟩
      have hy₁ : x₁ + t i ∈ Set.Icc (center M w + t i - rad M) (center M w + t i + rad M) :=
        ⟨by linarith [hx₁.2.1], by linarith [hx₁.2.2]⟩
      have hy₂ : x₁ + t i ∈ Set.Icc (center M w + t j - rad M) (center M w + t j + rad M) := by
        change x₂ + t j = x₁ + t i at heq
        rw [← heq]
        exact ⟨by linarith [hx₂.2.1], by linarith [hx₂.2.2]⟩
      exact (Set.disjoint_left.mp (ht_disj hij)) hy₁ hy₂
    have hA_rest : ∀ i : Fin N, μ K' ≤ (μ.restrict E) (A i) := by
      intro i
      rw [Measure.restrict_apply (hA_meas i)]
      have hdiff_null : μ (A i \ E) = 0 := by
        have hsub_diff : A i \ E ⊆ (fun x : ℝ => x + t i) '' (K \ E) := by
          rintro y ⟨⟨x, hxK', rfl⟩, hyE⟩
          refine ⟨x, ⟨hxK'.1, ?_⟩, rfl⟩
          intro hxE
          have hmem : x ∈ (fun z : ℝ => z + t i) ⁻¹' E := by
            rw [hE_inv (t i) (htL i)]; exact hxE
          exact hyE hmem
        have h_img_null : μ ((fun x : ℝ => x + t i) '' (K \ E)) = 0 := by
          rw [GaugeExact.mkMetric_image_add m (t i) (K \ E)]
          exact hKE_null
        exact measure_mono_null hsub_diff h_img_null
      have hcov_Ai : A i ⊆ (A i ∩ E) ∪ (A i \ E) := by
        intro y hy
        by_cases hyE : y ∈ E
        · exact Or.inl ⟨hy, hyE⟩
        · exact Or.inr ⟨hy, hyE⟩
      have hle_Ai : μ (A i) ≤ μ (A i ∩ E) + μ (A i \ E) :=
        le_trans (measure_mono hcov_Ai) (measure_union_le _ _)
      rw [hdiff_null, add_zero] at hle_Ai
      have heq_img : μ (A i) = μ K' := GaugeExact.mkMetric_image_add m (t i) K'
      rwa [heq_img] at hle_Ai
    have hsum_le_E : (N : ℝ≥0∞) * μ K' ≤ μ (E ∩ Set.Ioo a b_end) := by
      calc (N : ℝ≥0∞) * μ K'
          = ∑ _i : Fin N, μ K' := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        _ ≤ ∑ i : Fin N, (μ.restrict E) (A i) := Finset.sum_le_sum (fun i _ => hA_rest i)
        _ = ∑' i : Fin N, (μ.restrict E) (A i) := (tsum_fintype _).symm
        _ = (μ.restrict E) (⋃ i : Fin N, A i) := (measure_iUnion hA_disj hA_meas).symm
        _ ≤ (μ.restrict E) (Set.Ioo a b_end) := measure_mono (Set.iUnion_subset hA_sub_Ioo)
        _ = μ (Set.Ioo a b_end ∩ E) := Measure.restrict_apply measurableSet_Ioo
        _ = μ (E ∩ Set.Ioo a b_end) := by rw [Set.inter_comm]
    have hmul_bM : (N : ℝ≥0∞) * ENNReal.ofReal c₀ ≤
        ((b ^ M : ℕ) : ℝ≥0∞) * μ (E ∩ Set.Ioo a b_end) := by
      calc (N : ℝ≥0∞) * ENNReal.ofReal c₀
          ≤ (N : ℝ≥0∞) * (((b ^ M : ℕ) : ℝ≥0∞) * μ K') := by gcongr
        _ = ((b ^ M : ℕ) : ℝ≥0∞) * ((N : ℝ≥0∞) * μ K') := by ring
        _ ≤ ((b ^ M : ℕ) : ℝ≥0∞) * μ (E ∩ Set.Ioo a b_end) := by gcongr
    have hcast_lhs : (N : ℝ≥0∞) * ENNReal.ofReal c₀ = ENNReal.ofReal ((N : ℝ) * c₀) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    have hcast_rhs : ((b ^ M : ℕ) : ℝ≥0∞) * μ (E ∩ Set.Ioo a b_end) =
        ENNReal.ofReal (((b ^ M : ℕ) : ℝ) * V) := by
      rw [← hV_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [hcast_lhs, hcast_rhs] at hmul_bM
    have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) hV_nonneg)).mp hmul_bM
    have hN_ge : (b_end - a) * (Qsel (J + M + 1) : ℝ) - 1 ≤ (N : ℝ) := by
      have hQpos : 0 < (Qsel (J + M + 1) : ℝ) := by
        exact_mod_cast Classification.Qsel_pos (J + M + 1)
      have h3r : 3 * rad M ≤ 3 * (1 / (4 * (Qsel (J + M + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left (hrad_le M) (by norm_num)
      have h3r' : 3 * rad M ≤ 1 / (Qsel (J + M + 1) : ℝ) := by
        have hle : 3 * (1 / (4 * (Qsel (J + M + 1) : ℝ))) ≤ 1 / (Qsel (J + M + 1) : ℝ) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) hQpos]
          linarith
        exact le_trans h3r hle
      have hdiv_ge : (b_end - a) * (Qsel (J + M + 1) : ℝ) ≤ (b_end - a) / (3 * rad M) := by
        rw [le_div_iff₀ (by linarith [hrad_pos M])]
        calc (b_end - a) * (Qsel (J + M + 1) : ℝ) * (3 * rad M)
            ≤ (b_end - a) * (Qsel (J + M + 1) : ℝ) * (1 / (Qsel (J + M + 1) : ℝ)) := by gcongr
          _ = b_end - a := by field_simp
      have hfloor_lt : (b_end - a) / (3 * rad M) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right hN_ge (le_of_lt hc₀_pos)) hreal
  have hcontra : Tendsto (fun M : ℕ =>
      ((b_end - a) * (Qsel (J + M + 1) : ℝ) - 1) * c₀ / ((b ^ M : ℕ) : ℝ)) atTop atTop := by
    have hlim0 : Tendsto (fun M : ℕ => ((b ^ M : ℕ) : ℝ) / (Nat.factorial (J + M + 1) : ℝ))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ((b : ℝ) ^ n) / (Nat.factorial n : ℝ)) atTop (nhds 0) :=
        FloorSemiring.tendsto_pow_div_factorial_atTop (b : ℝ)
      have hshift : Tendsto (fun M : ℕ => J + M + 1) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro K
        refine ⟨K, fun M hM => by omega⟩
      have h2 := h1.comp hshift
      have hb_pow : ∀ M : ℕ, ((b ^ M : ℕ) : ℝ) / (Nat.factorial (J + M + 1) : ℝ) ≤
          ((b : ℝ) ^ (J + M + 1)) / (Nat.factorial (J + M + 1) : ℝ) := by
        intro M
        have h1' : ((b ^ M : ℕ) : ℝ) = (b : ℝ) ^ M := by push_cast; rfl
        rw [h1']
        have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        have hpow_le : (b : ℝ) ^ M ≤ (b : ℝ) ^ (J + M + 1) :=
          pow_le_pow_right₀ hb1 (by omega)
        exact div_le_div_of_nonneg_right hpow_le (by positivity)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
        (Filter.Eventually.of_forall (fun M => by positivity)) (Filter.Eventually.of_forall hb_pow)
    have hinv_top : Tendsto (fun M : ℕ =>
        ((Nat.factorial (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ))) atTop atTop := by
      have heq : (fun M : ℕ => (Nat.factorial (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ)) =
          fun M : ℕ => (((b ^ M : ℕ) : ℝ) / (Nat.factorial (J + M + 1) : ℝ))⁻¹ := by
        funext M; rw [inv_div]
      rw [heq]
      refine Filter.Tendsto.inv_tendsto_nhdsGT_zero ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hlim0, Filter.Eventually.of_forall (fun M => ?_)⟩
      have hbpos : (0 : ℝ) < ((b ^ M : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < b) M
      have hfpos : (0 : ℝ) < (Nat.factorial (J + M + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos _
      exact div_pos hbpos hfpos
    have hcoeff_pos : 0 < (b_end - a) * c₀ := mul_pos (sub_pos.mpr hab) hc₀_pos
    have hscale_top : Tendsto (fun M : ℕ =>
        ((b_end - a) * c₀) * ((Nat.factorial (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ)) - c₀)
        atTop atTop :=
      (hinv_top.const_mul_atTop hcoeff_pos).atTop_add tendsto_const_nhds
    refine tendsto_atTop_mono (fun M => ?_) hscale_top
    have hbM_pos : (0 : ℝ) < ((b ^ M : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < b) M
    have hbM_ge1 : (1 : ℝ) ≤ ((b ^ M : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow M b (by omega)
    have hQge : (Nat.factorial (J + M + 1) : ℝ) ≤ (Qsel (J + M + 1) : ℝ) := by
      exact_mod_cast DimHCore.Qsel_ge_factorial (J + M + 1) (by omega)
    have hc₀_div : c₀ / ((b ^ M : ℕ) : ℝ) ≤ c₀ := div_le_self (le_of_lt hc₀_pos) hbM_ge1
    have h1 : ((b_end - a) * (Qsel (J + M + 1) : ℝ) - 1) * c₀ / ((b ^ M : ℕ) : ℝ) =
        ((b_end - a) * c₀) * ((Qsel (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ)) - c₀ / ((b ^ M : ℕ) : ℝ) := by
      ring
    have h2 : ((b_end - a) * c₀) * ((Nat.factorial (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ)) ≤
        ((b_end - a) * c₀) * ((Qsel (J + M + 1) : ℝ) / ((b ^ M : ℕ) : ℝ)) := by
      gcongr
    linarith
  obtain ⟨M, hM⟩ := (hcontra.eventually_gt_atTop V).exists
  have hbm := hbound_M M
  have hbM_pos : (0 : ℝ) < ((b ^ M : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (by omega : 0 < b) M
  have hleV : ((b_end - a) * (Qsel (J + M + 1) : ℝ) - 1) * c₀ / ((b ^ M : ℕ) : ℝ) ≤ V :=
    (div_le_iff₀ hbM_pos).mpr (by linarith)
  linarith

/-! ## 第三部分：Corollary 14(i) 任意非空开区间（及圆周基本区间）无穷测度定理 -/

/-- **Corollary 14(i)（任意非空开区间上的 $\mathcal{H}^{h_k}$ 无穷测度）**：
    对任意 $k \ge 1$ 与任意非空开区间 $(a, b) \subset \mathbb{R}$（$a < b$），
    `Measure.mkMetric (critGauge k) ({x | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo a b) = ⊤`。 -/
theorem mkMetric_critGauge_exactLevel_inter_Ioo_eq_top (k : ℕ) (hk : 1 ≤ k)
    {a b : ℝ} (hab : a < b) :
    Measure.mkMetric (critGauge k)
      ({x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo a b) = ⊤ := by
  set E : Set ℝ := {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)}
  set b_base : ℝ := 2 * (k : ℝ) + 1
  have hb_pos : 0 < b_base := by positivity
  have htree_pos : 0 < Measure.mkMetric (critGauge k) (cantorTreeC k) := by
    refine mkMetric_cantorTree_pos k hk (critGauge k)
      (critGauge_mono k hk) (critGauge_continuous k hk) (1 / b_base) (by positivity) ?_
    intro n
    rw [critGauge_at_inv_Qsel k hk (by omega : 1 ≤ n + 1)]
    apply ENNReal.ofReal_le_ofReal
    have halg : (1 / b_base) * b_base ^ (-(n : ℤ)) = b_base ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      have hbn : b_base ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb_pos)
      have hb0 : b_base ≠ 0 := ne_of_gt hb_pos
      field_simp
    exact le_of_eq halg
  have hstrict_null : Measure.mkMetric (critGauge k)
      {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} = 0 :=
    mkMetric_critGauge_strictLevel_null k hk
  have hKE_null : Measure.mkMetric (critGauge k) (cantorTreeC k \ E) = 0 := by
    refine measure_mono_null ?_ hstrict_null
    intro x hx
    exact lt_of_le_of_ne (cantorTreeC_subset_levelSet k hk hx.1) hx.2
  have hE_inv : ∀ y ∈ Classification.latticeL, (fun x : ℝ => x + y) ⁻¹' E = E :=
    fun _ hy => exactLevel_add_latticeL (ENNReal.ofReal ((k : ℝ) / 4)) hy
  refine mkMetric_inter_Ioo_eq_top_of_compact_tree (critGauge k) (cantorTreeC k) E
    (isCompact_cantorTreeC k) htree_pos hKE_null hE_inv (2 * k + 1) (J_cantor k)
    (by omega) (by unfold J_cantor; omega)
    (fun M w => (centerIntC k M w : ℝ) / (Qsel (J_cantor k + M + 1) : ℝ))
    (fun M => radC k M) (fun M => radC_pos k M) (fun M => radC_le_quarter_inv k M hk)
    (fun M x hx => by
      have hxM := Set.mem_iInter.mp hx M
      rcases Set.mem_iUnion.mp hxM with ⟨w, hw⟩
      exact Set.mem_iUnion.mpr ⟨w, hw⟩)
    hab

/-- **Corollary 14(i) 推论（单位闭区间 $[0, 1]$ 上的 $\mathcal{H}^{h_k}$ 无穷测度）**。 -/
theorem mkMetric_critGauge_exactLevel_inter_Icc_zero_one_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k)
      ({x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Icc (0 : ℝ) 1) = ⊤ := by
  have hsub : {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo (0 : ℝ) 1 ⊆
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Icc (0 : ℝ) 1 :=
    Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
  have htop := mkMetric_critGauge_exactLevel_inter_Ioo_eq_top k hk (by norm_num : (0 : ℝ) < 1)
  exact top_unique (htop ▸ measure_mono hsub)

/-- **Corollary 14(i) 推论（任何包含非空开区间的集合上均为 $\mathcal{H}^{h_k}$ 无穷测度）**。 -/
theorem mkMetric_critGauge_exactLevel_inter_eq_top_of_Ioo_subset (k : ℕ) (hk : 1 ≤ k)
    {U : Set ℝ} {a b : ℝ} (hab : a < b) (hsub : Set.Ioo a b ⊆ U) :
    Measure.mkMetric (critGauge k)
      ({x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ U) = ⊤ := by
  have h1 : {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo a b ⊆
      {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ U :=
    Set.inter_subset_inter_right _ hsub
  exact top_unique ((mkMetric_critGauge_exactLevel_inter_Ioo_eq_top k hk hab) ▸ measure_mono h1)

/-! ## 第四部分：Theorem 16(ii) 二值 $2$-叉 Cantor 树与普适规范 `binaryGauge` 正测度及开区间无穷测度 -/

/-- 将 `Fin 2` 映射到二值数字字母表 $\{-k, +k\}$。 -/
def binDigitOf (k : ℕ) (a : Fin 2) : ℤ :=
  if a.1 = 0 then -(k : ℤ) else (k : ℤ)

lemma abs_binDigitOf_le (k : ℕ) (a : Fin 2) : |binDigitOf k a| ≤ (k : ℤ) := by
  unfold binDigitOf
  split_ifs <;> simp

lemma binDigitOf_mem_binary (k : ℕ) (a : Fin 2) :
    binDigitOf k a = (k : ℤ) ∨ binDigitOf k a = -(k : ℤ) := by
  unfold binDigitOf
  split_ifs <;> tauto

lemma binDigitOf_injective (k : ℕ) (hk : 1 ≤ k) : Function.Injective (binDigitOf k) := by
  intro a b h
  unfold binDigitOf at h
  rcases a with ⟨va, ha⟩
  rcases b with ⟨vb, hb⟩
  have h1 : va = 0 ∨ va = 1 := by omega
  have h2 : vb = 0 ∨ vb = 1 := by omega
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp at h ⊢ <;> omega

/-- 沿 $w : \mathrm{Fin}\ n \to \mathrm{Fin}\ 2$ 递推生成的二值整数对 $(M_{J+n}, M_{J+n+1})$。 -/
def binPairOfWord (k : ℕ) : ∀ n : ℕ, (Fin n → Fin 2) → ℤ × ℤ
  | 0, _ => (0, 0)
  | n + 1, w =>
      let p := binPairOfWord k n (Fin.init w)
      (p.2, (4 * ((J_cantor k + n : ℕ) : ℤ) + 6) * p.2 + p.1 + binDigitOf k (w (Fin.last n)))

/-- 第 $n$ 级二值 Cantor 中心整数 $M_{J+n+1}(w)$。 -/
def binCenterInt (k n : ℕ) (w : Fin n → Fin 2) : ℤ :=
  (binPairOfWord k n w).2

def binPrefixWord {n N : ℕ} (h : n ≤ N) (w : Fin N → Fin 2) : Fin n → Fin 2 :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 h⟩

lemma binPrefixWord_self {n : ℕ} (w : Fin n → Fin 2) :
    binPrefixWord (le_refl n) w = w := by
  ext i; rfl

def binExtendZero {n : ℕ} (u : Fin n → Fin 2) (m : ℕ) : Fin (n + m) → Fin 2 :=
  fun i => if hi : i.1 < n then u ⟨i.1, hi⟩ else ⟨0, by omega⟩

lemma binExtendZero_zero {n : ℕ} (u : Fin n → Fin 2) : binExtendZero u 0 = u := by
  funext ⟨i, hi⟩
  have hin : i < n := by omega
  simp [binExtendZero, hin]

lemma abs_det_binPairOfWord_le (k : ℕ) (n : ℕ) (w : Fin n → Fin 2) :
    |(binPairOfWord k n w).2 * (Qsel (J_cantor k + n) : ℤ) -
      (binPairOfWord k n w).1 * (Qsel (J_cantor k + n + 1) : ℤ)| ≤
      ((k : ℤ) + 1) * (Qsel (J_cantor k + n) : ℤ) := by
  induction n with
  | zero =>
      simp only [binPairOfWord, zero_mul, sub_self, abs_zero]
      exact mul_nonneg (by omega) (Qsel_pos (J_cantor k + 0) (by unfold J_cantor; omega) |>.le)
  | succ n ih =>
      set p := binPairOfWord k n (Fin.init w)
      set d := binDigitOf k (w (Fin.last n))
      have hQrec : Qsel (J_cantor k + n + 2) =
          (4 * (J_cantor k + n) + 6) * Qsel (J_cantor k + n + 1) + Qsel (J_cantor k + n) :=
        Classification.Qsel_rec (J_cantor k + n)
      have hdet_eq :
          (binPairOfWord k (n + 1) w).2 * (Qsel (J_cantor k + (n + 1)) : ℤ) -
            (binPairOfWord k (n + 1) w).1 * (Qsel (J_cantor k + (n + 1) + 1) : ℤ) =
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
      have hd : |d| ≤ (k : ℤ) := abs_binDigitOf_le k (w (Fin.last n))
      have hQ_ge : ((k : ℤ) + 1) * (Qsel (J_cantor k + n) : ℤ) ≤
          (Qsel (J_cantor k + n + 1) : ℤ) := by
        have h1 : (4 * ((J_cantor k + n : ℕ) : ℝ) + 2) * (Qsel (J_cantor k + n) : ℝ) ≤
            (Qsel (J_cantor k + n + 1) : ℝ) :=
          GaugeExact.Qsel_succ_ge_mul (J_cantor k + n) (by unfold J_cantor; omega)
        have h2 : ((k : ℝ) + 1) * (Qsel (J_cantor k + n) : ℝ) ≤
            (4 * ((J_cantor k + n : ℕ) : ℝ) + 2) * (Qsel (J_cantor k + n) : ℝ) := by
          have hkR : (k : ℝ) + 1 ≤ 4 * ((J_cantor k + n : ℕ) : ℝ) + 2 := by
            unfold J_cantor; push_cast; linarith
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

def binInterv (k n : ℕ) (w : Fin n → Fin 2) : Set ℝ :=
  Set.Icc ((binCenterInt k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - radC k n)
          ((binCenterInt k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) + radC k n)

lemma isCompact_binInterv (k n : ℕ) (w : Fin n → Fin 2) :
    IsCompact (binInterv k n w) := isCompact_Icc

lemma isClosed_binInterv (k n : ℕ) (w : Fin n → Fin 2) :
    IsClosed (binInterv k n w) := isClosed_Icc

lemma binInterv_nonempty (k n : ℕ) (w : Fin n → Fin 2) :
    (binInterv k n w).Nonempty := by
  refine ⟨(binCenterInt k n w : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ), ?_⟩
  have hr := le_of_lt (radC_pos k n)
  exact ⟨by linarith, by linarith⟩

lemma binInterv_succ_subset (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (w : Fin (n + 1) → Fin 2) :
    binInterv k (n + 1) w ⊆ binInterv k n (Fin.init w) := by
  intro x hx
  have hQ1 : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have hQ2 : 0 < (Qsel (J_cantor k + n + 2) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 2) (by unfold J_cantor; omega)
  have hQ3 : 0 < (Qsel (J_cantor k + n + 3) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 3) (by unfold J_cantor; omega)
  have hdet : |(binCenterInt k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
      (binCenterInt k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)| ≤
      ((k : ℝ) + 1) * (Qsel (J_cantor k + n + 1) : ℝ) := by
    have h1 := abs_det_binPairOfWord_le k (n + 1) w
    have h1' : ((binPairOfWord k (n + 1) w).2 : ℝ) = (binCenterInt k (n + 1) w : ℝ) := rfl
    have h2' : ((binPairOfWord k (n + 1) w).1 : ℝ) = (binCenterInt k n (Fin.init w) : ℝ) := rfl
    have hR : |((binPairOfWord k (n + 1) w).2 : ℝ) * (Qsel (J_cantor k + (n + 1)) : ℝ) -
        ((binPairOfWord k (n + 1) w).1 : ℝ) * (Qsel (J_cantor k + (n + 1) + 1) : ℝ)| ≤
        ((k : ℝ) + 1) * (Qsel (J_cantor k + (n + 1)) : ℝ) := by
      exact_mod_cast h1
    simpa [h1', h2', add_assoc] using hR
  have hcdiff : |(binCenterInt k (n + 1) w : ℝ) / (Qsel (J_cantor k + n + 2) : ℝ) -
      (binCenterInt k n (Fin.init w) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤
      ((k : ℝ) + 1) / (Qsel (J_cantor k + n + 2) : ℝ) := by
    have heq : (binCenterInt k (n + 1) w : ℝ) / (Qsel (J_cantor k + n + 2) : ℝ) -
        (binCenterInt k n (Fin.init w) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
        ((binCenterInt k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
          (binCenterInt k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) /
          ((Qsel (J_cantor k + n + 1) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) := by
      field_simp
    rw [heq, abs_div, abs_of_pos (mul_pos hQ1 hQ2), div_le_div_iff₀ (mul_pos hQ1 hQ2) hQ2]
    calc |(binCenterInt k (n + 1) w : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) -
            (binCenterInt k n (Fin.init w) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)| *
            (Qsel (J_cantor k + n + 2) : ℝ)
        ≤ (((k : ℝ) + 1) * (Qsel (J_cantor k + n + 1) : ℝ)) * (Qsel (J_cantor k + n + 2) : ℝ) :=
          mul_le_mul_of_nonneg_right hdet (le_of_lt hQ2)
      _ = ((k : ℝ) + 1) * ((Qsel (J_cantor k + n + 1) : ℝ) * (Qsel (J_cantor k + n + 2) : ℝ)) := by
          ring
  have hrad_succ : radC k (n + 1) ≤ ((k : ℝ) + 1) / (2 * (Qsel (J_cantor k + n + 2) : ℝ)) := by
    unfold radC
    rw [div_le_div_iff₀ (by simpa [add_assoc] using hQ3) (by positivity)]
    have h4 : 4 * (Qsel (J_cantor k + n + 2) : ℝ) ≤ (Qsel (J_cantor k + n + 3) : ℝ) :=
      GaugeExact.Qsel_succ_ge_four_mul (J_cantor k + n + 2) (by unfold J_cantor; omega)
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

lemma binInterv_prefix_subset (k : ℕ) (hk : 1 ≤ k) {n N : ℕ} (h : n ≤ N)
    (w : Fin N → Fin 2) :
    binInterv k N w ⊆ binInterv k n (binPrefixWord h w) := by
  induction N with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      rw [binPrefixWord_self]
  | succ N ih =>
      rcases eq_or_lt_of_le h with rfl | hlt
      · rw [binPrefixWord_self]
      · have hle : n ≤ N := Nat.le_of_lt_succ hlt
        calc binInterv k (N + 1) w
            ⊆ binInterv k N (Fin.init w) := binInterv_succ_subset k hk N w
          _ ⊆ binInterv k n (binPrefixWord hle (Fin.init w)) := ih hle (Fin.init w)
          _ = binInterv k n (binPrefixWord h w) := by ext i; rfl

lemma binCenterInt_injective (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    Function.Injective (binCenterInt k n) := by
  intro w1 w2 heq
  by_contra hne
  have hex : ∃ i : ℕ, ∃ hi : i < n, w1 ⟨i, hi⟩ ≠ w2 ⟨i, hi⟩ := by
    by_contra hno
    push Not at hno
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
  have hprefix_eq : binPrefixWord (le_of_lt hi0_lt) w1 = binPrefixWord (le_of_lt hi0_lt) w2 := by
    funext ⟨j, hj⟩
    exact hmin j hj (lt_trans hj hi0_lt)
  have hgrow : ∀ t : ℕ, ∀ ht : i0 + 1 ≤ t, ∀ htn : t ≤ n,
      1 ≤ |binCenterInt k t (binPrefixWord htn w1) - binCenterInt k t (binPrefixWord htn w2)| ∧
      |(binPairOfWord k t (binPrefixWord htn w1)).1 -
          (binPairOfWord k t (binPrefixWord htn w2)).1| ≤
        |binCenterInt k t (binPrefixWord htn w1) - binCenterInt k t (binPrefixWord htn w2)| := by
    intro t ht htn
    induction t with
    | zero => omega
    | succ t ih =>
        rcases eq_or_lt_of_le ht with ht_eq | ht_gt
        · have ht0 : t = i0 := by omega
          subst ht0
          have hinit1 : Fin.init (binPrefixWord htn w1) = binPrefixWord (le_of_lt hi0_lt) w1 := by
            funext ⟨j, hj⟩; rfl
          have hinit2 : Fin.init (binPrefixWord htn w2) = binPrefixWord (le_of_lt hi0_lt) w2 := by
            funext ⟨j, hj⟩; rfl
          have hp_eq : binPairOfWord k i0 (Fin.init (binPrefixWord htn w1)) =
              binPairOfWord k i0 (Fin.init (binPrefixWord htn w2)) := by
            rw [hinit1, hinit2, hprefix_eq]
          have h1 : (binPairOfWord k (i0 + 1) (binPrefixWord htn w1)).1 =
              (binPairOfWord k (i0 + 1) (binPrefixWord htn w2)).1 := by
            change (binPairOfWord k i0 (Fin.init (binPrefixWord htn w1))).2 =
              (binPairOfWord k i0 (Fin.init (binPrefixWord htn w2))).2
            rw [hp_eq]
          have h2 : binCenterInt k (i0 + 1) (binPrefixWord htn w1) -
              binCenterInt k (i0 + 1) (binPrefixWord htn w2) =
              binDigitOf k (w1 ⟨i0, hi0_lt⟩) - binDigitOf k (w2 ⟨i0, hi0_lt⟩) := by
            change ((4 * ((J_cantor k + i0 : ℕ) : ℤ) + 6) *
                (binPairOfWord k i0 (Fin.init (binPrefixWord htn w1))).2 +
                (binPairOfWord k i0 (Fin.init (binPrefixWord htn w1))).1 +
                binDigitOf k (binPrefixWord htn w1 (Fin.last i0))) -
              ((4 * ((J_cantor k + i0 : ℕ) : ℤ) + 6) *
                (binPairOfWord k i0 (Fin.init (binPrefixWord htn w2))).2 +
                (binPairOfWord k i0 (Fin.init (binPrefixWord htn w2))).1 +
                binDigitOf k (binPrefixWord htn w2 (Fin.last i0))) = _
            rw [hp_eq]
            simp only [binPrefixWord, Fin.last]
            ring
          have hd_ne : binDigitOf k (w1 ⟨i0, hi0_lt⟩) ≠ binDigitOf k (w2 ⟨i0, hi0_lt⟩) :=
            fun h => hi0_ne (binDigitOf_injective k hk h)
          have hge1 : 1 ≤ |binDigitOf k (w1 ⟨i0, hi0_lt⟩) - binDigitOf k (w2 ⟨i0, hi0_lt⟩)| :=
            Int.one_le_abs (sub_ne_zero.mpr hd_ne)
          rw [h1, sub_self, abs_zero, h2]
          exact ⟨hge1, le_trans (by norm_num) hge1⟩
        · have ht_ge : i0 + 1 ≤ t := by omega
          have htn_le : t ≤ n := by omega
          obtain ⟨ih1, ih2⟩ := ih ht_ge htn_le
          have hinit1 : Fin.init (binPrefixWord htn w1) = binPrefixWord htn_le w1 := by
            funext ⟨j, hj⟩; rfl
          have hinit2 : Fin.init (binPrefixWord htn w2) = binPrefixWord htn_le w2 := by
            funext ⟨j, hj⟩; rfl
          set E_t := binCenterInt k t (binPrefixWord htn_le w1) -
            binCenterInt k t (binPrefixWord htn_le w2)
          set P_t := (binPairOfWord k t (binPrefixWord htn_le w1)).1 -
            (binPairOfWord k t (binPrefixWord htn_le w2)).1
          have hP_next : (binPairOfWord k (t + 1) (binPrefixWord htn w1)).1 -
              (binPairOfWord k (t + 1) (binPrefixWord htn w2)).1 = E_t := by
            change (binPairOfWord k t (Fin.init (binPrefixWord htn w1))).2 -
              (binPairOfWord k t (Fin.init (binPrefixWord htn w2))).2 = E_t
            rw [hinit1, hinit2]
            rfl
          have hE_next : binCenterInt k (t + 1) (binPrefixWord htn w1) -
              binCenterInt k (t + 1) (binPrefixWord htn w2) =
              (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * E_t + P_t +
                (binDigitOf k (binPrefixWord htn w1 (Fin.last t)) -
                  binDigitOf k (binPrefixWord htn w2 (Fin.last t))) := by
            change ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) *
                (binPairOfWord k t (Fin.init (binPrefixWord htn w1))).2 +
                (binPairOfWord k t (Fin.init (binPrefixWord htn w1))).1 +
                binDigitOf k (binPrefixWord htn w1 (Fin.last t))) -
              ((4 * ((J_cantor k + t : ℕ) : ℤ) + 6) *
                (binPairOfWord k t (Fin.init (binPrefixWord htn w2))).2 +
                (binPairOfWord k t (Fin.init (binPrefixWord htn w2))).1 +
                binDigitOf k (binPrefixWord htn w2 (Fin.last t))) = _
            rw [hinit1, hinit2]
            dsimp [E_t, P_t, binCenterInt]
            ring
          set Δd := binDigitOf k (binPrefixWord htn w1 (Fin.last t)) -
            binDigitOf k (binPrefixWord htn w2 (Fin.last t))
          have hΔd : |Δd| ≤ 2 * (k : ℤ) := by
            have h1 := abs_binDigitOf_le k (binPrefixWord htn w1 (Fin.last t))
            have h2 := abs_binDigitOf_le k (binPrefixWord htn w2 (Fin.last t))
            calc |Δd| ≤ |binDigitOf k (binPrefixWord htn w1 (Fin.last t))| +
                  |binDigitOf k (binPrefixWord htn w2 (Fin.last t))| := abs_sub _ _
              _ ≤ 2 * (k : ℤ) := by linarith
          have hcoeff : 2 * (k : ℤ) + 2 ≤ 4 * ((J_cantor k + t : ℕ) : ℤ) + 6 := by
            unfold J_cantor; omega
          have hlb : (4 * ((J_cantor k + t : ℕ) : ℤ) + 6) * |E_t| - |P_t| - |Δd| ≤
              |binCenterInt k (t + 1) (binPrefixWord htn w1) -
                binCenterInt k (t + 1) (binPrefixWord htn w2)| := by
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
  rw [binPrefixWord_self, binPrefixWord_self, heq, sub_self, abs_zero] at hfinal
  omega

lemma intersect_binInterv_abs_sub_le_one (k : ℕ) (hk : 1 ≤ k) (n : ℕ) {V : Set ℝ}
    (hVbd : Bornology.IsBounded V) (hVdiam : Metric.diam V ≤ 1 / (Qsel (J_cantor k + n + 1) : ℝ))
    {u1 u2 : Fin n → Fin 2}
    (h1 : (V ∩ binInterv k n u1).Nonempty) (h2 : (V ∩ binInterv k n u2).Nonempty) :
    |binCenterInt k n u1 - binCenterInt k n u2| ≤ 1 := by
  obtain ⟨x1, hx1V, hx1I⟩ := h1
  obtain ⟨x2, hx2V, hx2I⟩ := h2
  have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
    exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
  have hr := radC_le_quarter_inv k n hk
  have hd1 : |x1 - (binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
    abs_le.mpr ⟨by linarith [hx1I.1], by linarith [hx1I.2]⟩
  have hd2 : |x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
    abs_le.mpr ⟨by linarith [hx2I.1], by linarith [hx2I.2]⟩
  have hdist : |x1 - x2| ≤ 1 / (Qsel (J_cantor k + n + 1) : ℝ) :=
    le_trans (by simpa [Real.dist_eq] using Metric.dist_le_diam_of_mem hVbd hx1V hx2V) hVdiam
  have hcdiff : |(binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
      (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| <
      2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
    have htri : |(binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤
        |(binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1| +
          |x1 - x2| + |x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
      have hsub1 : (binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
          ((binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2) +
            (x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) := by ring
      rw [hsub1]
      calc |((binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2) +
              (x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))|
          ≤ |((binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1) + (x1 - x2)| +
              |x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ |(binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x1| + |x1 - x2| +
              |x2 - (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
            gcongr; exact abs_add_le _ _
    rw [abs_sub_comm ((binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) x1] at htri
    have hsum : radC k n + 1 / (Qsel (J_cantor k + n + 1) : ℝ) + radC k n <
        2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
      have h32 : 1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) +
          1 / (Qsel (J_cantor k + n + 1) : ℝ) +
          1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ)) =
          (3 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) := by field_simp; ring
      have h14 : (3 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) <
          2 / (Qsel (J_cantor k + n + 1) : ℝ) := by
        rw [div_lt_div_iff_of_pos_right hQpos]; linarith
      linarith
    linarith
  have hlt2 : (|binCenterInt k n u1 - binCenterInt k n u2| : ℝ) < 2 := by
    have heq : |(binCenterInt k n u1 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (binCenterInt k n u2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| =
        |(binCenterInt k n u1 - binCenterInt k n u2 : ℤ)| / (Qsel (J_cantor k + n + 1) : ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hQpos]
      push_cast; rfl
    rw [heq, div_lt_div_iff_of_pos_right hQpos] at hcdiff
    exact_mod_cast hcdiff
  have hlt2Z : |binCenterInt k n u1 - binCenterInt k n u2| < 2 := by exact_mod_cast hlt2
  omega

def binCantorLevel (k n : ℕ) : Set ℝ :=
  ⋃ w : Fin n → Fin 2, binInterv k n w

def binCantorTree (k : ℕ) : Set ℝ :=
  ⋂ n : ℕ, binCantorLevel k n

lemma isCompact_binCantorLevel (k n : ℕ) : IsCompact (binCantorLevel k n) :=
  isCompact_iUnion (fun w => isCompact_binInterv k n w)

lemma isClosed_binCantorLevel (k n : ℕ) : IsClosed (binCantorLevel k n) :=
  (isCompact_binCantorLevel k n).isClosed

lemma isCompact_binCantorTree (k : ℕ) : IsCompact (binCantorTree k) := by
  apply IsCompact.of_isClosed_subset (isCompact_binCantorLevel k 0)
  · exact isClosed_iInter (fun n => isClosed_binCantorLevel k n)
  · exact Set.iInter_subset _ 0

lemma binCantorLevel_antitone (k : ℕ) (hk : 1 ≤ k) : Antitone (binCantorLevel k) := by
  intro m n hmn x hx
  rcases Set.mem_iUnion.mp hx with ⟨w, hw⟩
  exact Set.mem_iUnion.mpr ⟨binPrefixWord hmn w, binInterv_prefix_subset k hk hmn w hw⟩

lemma binInterv_inter_binCantorTree_nonempty (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (u : Fin n → Fin 2) :
    (binInterv k n u ∩ binCantorTree k).Nonempty := by
  let S : ℕ → Set ℝ := fun m => binInterv k (n + m) (binExtendZero u m)
  have hS_ne : ∀ m, (S m).Nonempty := fun m => binInterv_nonempty k (n + m) (binExtendZero u m)
  have hS_comp : ∀ m, IsCompact (S m) := fun m => isCompact_binInterv k (n + m) _
  have hS_closed : ∀ m, IsClosed (S m) := fun m => isClosed_binInterv k (n + m) _
  have hS_anti : Antitone S := by
    intro a b hab
    have hpre : binPrefixWord (Nat.add_le_add_left hab n) (binExtendZero u b) = binExtendZero u a := by
      funext ⟨i, hi⟩
      by_cases hin : i < n
      · simp [binPrefixWord, binExtendZero, hin]
      · simp [binPrefixWord, binExtendZero, hin]
    have hsub := binInterv_prefix_subset k hk (Nat.add_le_add_left hab n) (binExtendZero u b)
    rwa [hpre] at hsub
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S (fun i => hS_anti (Nat.le_succ i)) hS_ne (hS_comp 0) hS_closed
  have hx0 : x ∈ binInterv k n u := by
    have h0 := Set.mem_iInter.mp hx 0
    dsimp [S] at h0
    have hzero : binExtendZero u 0 = u := binExtendZero_zero u
    simpa [hzero] using h0
  refine ⟨x, hx0, ?_⟩
  · rw [binCantorTree, Set.mem_iInter]
    intro m
    by_cases hm : n ≤ m
    · obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
      exact Set.mem_iUnion.mpr ⟨binExtendZero u d, Set.mem_iInter.mp hx d⟩
    · have hm_lt : m ≤ n := by omega
      exact binCantorLevel_antitone k hk hm_lt (Set.mem_iUnion.mpr ⟨u, hx0⟩)

/-- 二值紧致 Cantor 树 `binCantorTree k` 完全含于无符号精确极限集 $E_{\mathrm{lim}}(k/4)$。 -/
lemma binCantorTree_subset_unsignedExactLimit (k : ℕ) (hk : 1 ≤ k) :
    binCantorTree k ⊆ unsignedExactLimitSet k := by
  intro x hx
  have hx_lvl : ∀ n : ℕ, ∃ w : Fin n → Fin 2, x ∈ binInterv k n w := by
    intro n
    exact Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
  choose w hw using hx_lvl
  have hnear : ∀ n : ℕ,
      nearestInt ((Qsel (J_cantor k + n + 1) : ℝ) * x) = binCenterInt k n (w n) := by
    intro n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hxn := hw n
    have hdiff : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ)| ≤
        (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
      have h1 : |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [hxn.1], by linarith [hxn.2]⟩
      calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ)|
          = (Qsel (J_cantor k + n + 1) : ℝ) *
              |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := by
            rw [← abs_of_pos hQpos, ← abs_mul]
            congr 1
            rw [abs_of_pos hQpos]
            field_simp
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hQpos)
    have hr := radC_le_quarter_inv k n hk
    have hlt_half : |(Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ)| < 1 / 2 := by
      calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ)|
          ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := hdiff
        _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) :=
            mul_le_mul_of_nonneg_left hr (le_of_lt hQpos)
        _ = 1 / 4 := by field_simp
        _ < 1 / 2 := by norm_num
    have hround : round ((Qsel (J_cantor k + n + 1) : ℝ) * x) = binCenterInt k n (w n) := by
      rw [round_eq_iff]
      have habs := abs_lt.mp hlt_half
      exact ⟨by linarith, by linarith⟩
    exact hround
  have hinit_eq : ∀ n : ℕ, Fin.init (w (n + 1)) = w n := by
    intro n
    have h1 : x ∈ binInterv k n (Fin.init (w (n + 1))) :=
      binInterv_succ_subset k hk n (w (n + 1)) (hw (n + 1))
    have h2 : x ∈ binInterv k n (w n) := hw n
    have hQpos : 0 < (Qsel (J_cantor k + n + 1) : ℝ) := by
      exact_mod_cast Qsel_pos (J_cantor k + n + 1) (by unfold J_cantor; omega)
    have hr := radC_le_quarter_inv k n hk
    have hd1 : |x - (binCenterInt k n (Fin.init (w (n + 1))) : ℝ) /
        (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
      abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hd2 : |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
      abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hcdiff : |(binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
        (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ 2 * radC k n := by
      have hsub : (binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) =
          ((binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x) +
            (x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)) := by ring
      rw [hsub]
      calc |((binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x) +
              (x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))|
          ≤ |(binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) - x| +
              |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ radC k n + radC k n := by rw [abs_sub_comm]; exact add_le_add hd1 hd2
        _ = 2 * radC k n := by ring
    have hlt1 : (|binCenterInt k n (Fin.init (w (n + 1))) - binCenterInt k n (w n)| : ℝ) < 1 := by
      have heq : |(binCenterInt k n (Fin.init (w (n + 1))) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) -
          (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| =
          (|binCenterInt k n (Fin.init (w (n + 1))) - binCenterInt k n (w n)| : ℝ) /
            (Qsel (J_cantor k + n + 1) : ℝ) := by
        rw [← sub_div, abs_div, abs_of_pos hQpos]
      rw [heq] at hcdiff
      have h2r : 2 * radC k n < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
        calc 2 * radC k n
            ≤ 2 * (1 / (4 * (Qsel (J_cantor k + n + 1) : ℝ))) := by linarith
          _ = (1 / 2 : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ) := by ring
          _ < 1 / (Qsel (J_cantor k + n + 1) : ℝ) := by
              rw [div_lt_div_iff_of_pos_right hQpos]; linarith
      exact (div_lt_div_iff_of_pos_right hQpos).mp (lt_of_le_of_lt hcdiff h2r)
    have hlt1Z : |binCenterInt k n (Fin.init (w (n + 1))) - binCenterInt k n (w n)| < 1 := by
      exact_mod_cast hlt1
    rw [abs_lt] at hlt1Z
    have hceq : binCenterInt k n (Fin.init (w (n + 1))) = binCenterInt k n (w n) := by omega
    exact binCenterInt_injective k hk n hceq
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
      have h1 : |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| ≤ radC k n :=
        abs_le.mpr ⟨by linarith [hxn.1], by linarith [hxn.2]⟩
      have heps_eq : eps x (J_cantor k + n + 1) =
          (Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ) := by
        unfold eps; rw [hnear n]
      have hle_rad : |eps x (J_cantor k + n + 1)| ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
        rw [heps_eq]
        calc |(Qsel (J_cantor k + n + 1) : ℝ) * x - (binCenterInt k n (w n) : ℝ)|
            = |(Qsel (J_cantor k + n + 1) : ℝ) *
                (x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ))| := by
              congr 1; field_simp
          _ = |(Qsel (J_cantor k + n + 1) : ℝ)| *
                |x - (binCenterInt k n (w n) : ℝ) / (Qsel (J_cantor k + n + 1) : ℝ)| := abs_mul _ _
          _ ≤ (Qsel (J_cantor k + n + 1) : ℝ) * radC k n := by
              rw [abs_of_pos hQ1]
              exact mul_le_mul_of_nonneg_left h1 (le_of_lt hQ1)
      have hratio : (Qsel (J_cantor k + n + 1) : ℝ) * radC k n ≤
          (2 * (k : ℝ) + 2) / ((J_cantor k + n + 1 : ℕ) : ℝ) := by
        unfold radC
        have hrec := GaugeExact.Qsel_succ_ge_mul (J_cantor k + n + 1) (by unfold J_cantor; omega)
        have hj_le : ((J_cantor k + n + 1 : ℕ) : ℝ) ≤ 4 * ((J_cantor k + n + 1 : ℕ) : ℝ) + 2 := by
          linarith
        have hQ_ge : ((J_cantor k + n + 1 : ℕ) : ℝ) * (Qsel (J_cantor k + n + 1) : ℝ) ≤
            (Qsel (J_cantor k + n + 2) : ℝ) :=
          le_trans (mul_le_mul_of_nonneg_right hj_le (le_of_lt hQ1)) hrec
        rw [mul_div_assoc', div_le_div_iff₀ hQ2 (by positivity)]
        nlinarith
      exact le_trans hle_rad hratio
    exact FullSpectrumDiscrete.tendsto_zero_of_eventually_abs_le_div hbound
  have hdef_bin : ∀ᶠ j : ℕ in atTop, defect x j = (k : ℤ) ∨ defect x j = -(k : ℤ) := by
    filter_upwards [Filter.eventually_ge_atTop (J_cantor k + 2)] with j hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = J_cantor k + n + 2 := ⟨j - (J_cantor k + 2), by omega⟩
    have hdef_eq : defect x (J_cantor k + n + 2) =
        binDigitOf k (w (n + 2) (Fin.last (n + 1))) := by
      unfold defect
      have hm0 : nearestInt ((Qsel (J_cantor k + n + 1) : ℝ) * x) = binCenterInt k n (w n) :=
        hnear n
      have hm1 : nearestInt ((Qsel (J_cantor k + n + 2) : ℝ) * x) =
          binCenterInt k (n + 1) (w (n + 1)) := hnear (n + 1)
      have hm2 : nearestInt ((Qsel (J_cantor k + n + 3) : ℝ) * x) =
          binCenterInt k (n + 2) (w (n + 2)) := hnear (n + 2)
      have hsub1 : J_cantor k + n + 2 - 1 = J_cantor k + n + 1 := by omega
      have hsub2 : J_cantor k + n + 2 + 1 = J_cantor k + n + 3 := by omega
      rw [hsub1, hsub2, hm0, hm1, hm2]
      have hrec_w : binCenterInt k (n + 2) (w (n + 2)) =
          (4 * ((J_cantor k + (n + 1) : ℕ) : ℤ) + 6) *
            (binPairOfWord k (n + 1) (Fin.init (w (n + 2)))).2 +
            (binPairOfWord k (n + 1) (Fin.init (w (n + 2)))).1 +
            binDigitOf k (w (n + 2) (Fin.last (n + 1))) := rfl
      rw [hrec_w, hinit_eq (n + 1)]
      have hp1 : (binPairOfWord k (n + 1) (w (n + 1))).1 = binCenterInt k n (w n) := by
        change (binPairOfWord k n (Fin.init (w (n + 1)))).2 = binCenterInt k n (w n)
        rw [hinit_eq n]; rfl
      rw [hp1]
      have hcast : 4 * ((J_cantor k + (n + 1) : ℕ) : ℤ) + 6 =
          4 * ((J_cantor k + n + 2 : ℕ) : ℤ) + 2 := by push_cast; ring
      rw [hcast]
      change _ = binDigitOf k (w (n + 2) (Fin.last (n + 1)))
      unfold binCenterInt
      ring
    rw [hdef_eq]
    exact binDigitOf_mem_binary k (w (n + 2) (Fin.last (n + 1)))
  exact (FullSpectrumDiscrete.unsigned_exact_limit_iff_defect_binary x k).mpr ⟨heps0, hdef_bin⟩

/-- 均匀 $2$-叉 Cantor 树在满足 $m(1/Q_{n+1}) \ge c_1 \cdot 2^{-n}$ 的连续规范下正测度。 -/
theorem mkMetric_binCantorTree_pos (k : ℕ) (hk : 1 ≤ k)
    (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (hm_cont : Continuous m) (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hlb : ∀ n : ℕ, ENNReal.ofReal (c₁ * (2 : ℝ) ^ (-(n : ℤ))) ≤
      m (ENNReal.ofReal (1 / (Qsel (n + 1) : ℝ)))) :
    0 < Measure.mkMetric m (binCantorTree k) := by
  set J := J_cantor k
  set b : ℝ := 2
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
    ⨅ (t : ℕ → Set ℝ) (_ : binCantorTree k ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, m (Metric.ediam (t n))) r0 hr0_pos)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  by_contra hlt
  push Not at hlt
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
        have := min_le_left (r0R / 2) (η.toReal / 4); linarith
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
  have hV_cov : binCantorTree k ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos ⟨i, ⟨x, hi⟩⟩) (t i) hi
  obtain ⟨F, hFcov⟩ := (isCompact_binCantorTree k).elim_finite_subcover V hV_open hV_cov
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
      push Not at hgt
      exact Nat.find_min hex_m (show m0 - 1 < m0 by omega) ⟨by omega, hgt⟩
  choose lvl hlvl_ge hlvl_gt hlvl_le using hex_lvl
  set N : ℕ := F.sup (fun i => lvl i)
  have hN_ge : ∀ i ∈ F, lvl i ≤ N := fun i hi => Finset.le_sup hi
  have hsum_ge_one : (1 : ℝ) ≤ ∑ i ∈ F, 2 * b * b ^ (-(lvl i : ℤ)) := by
    classical
    have hcover_words : (Finset.univ : Finset (Fin N → Fin 2)) ⊆
        F.biUnion (fun i => Finset.univ.filter (fun w : Fin N → Fin 2 =>
          (V i ∩ binInterv k N w).Nonempty)) := by
      intro w _
      obtain ⟨x, hxI, hxK⟩ := binInterv_inter_binCantorTree_nonempty k hk N w
      obtain ⟨i, hiF, hxiV⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
      exact Finset.mem_biUnion.mpr ⟨i, hiF, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxiV, hxI⟩⟩⟩
    have hcard_i : ∀ i ∈ F,
        ((Finset.univ.filter (fun w : Fin N → Fin 2 =>
            (V i ∩ binInterv k N w).Nonempty)).card : ℝ) ≤
          2 * b * b ^ (N - lvl i) := by
      intro i hiF
      have hleN : lvl i ≤ N := hN_ge i hiF
      have hl1 : lvl i - 1 ≤ N := by omega
      set m := lvl i - 1
      have hm_eq : m + 1 = lvl i := by have := hlvl_ge i; omega
      set A_i := Finset.univ.filter (fun u : Fin m → Fin 2 =>
        (V i ∩ binInterv k m u).Nonempty)
      have hAi_le : A_i.card ≤ 2 := by
        apply card_le_two_of_abs_sub_le_one (binCenterInt k m)
          (binCenterInt_injective k hk m) A_i
        intro u1 hu1 u2 hu2
        have hdiam_m : Metric.diam (V i) ≤ 1 / (Qsel (J + m + 1) : ℝ) := by
          have : J + m + 1 = J + lvl i := by omega
          rw [this]
          exact hlvl_le i
        exact intersect_binInterv_abs_sub_le_one k hk m (hV_bd i) hdiam_m
          (Finset.mem_filter.mp hu1).2 (Finset.mem_filter.mp hu2).2
      have hsub_fib : Finset.univ.filter (fun w : Fin N → Fin 2 =>
            (V i ∩ binInterv k N w).Nonempty) ⊆
          A_i.biUnion (fun u => Finset.univ.filter (fun w : Fin N → Fin 2 =>
            binPrefixWord hl1 w = u)) := by
        intro w hw
        obtain ⟨x, hxV, hxI⟩ := (Finset.mem_filter.mp hw).2
        have hxI' := binInterv_prefix_subset k hk hl1 w hxI
        refine Finset.mem_biUnion.mpr ⟨binPrefixWord hl1 w, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hxV, hxI'⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hfib_card : ∀ u : Fin m → Fin 2,
          (Finset.univ.filter (fun w : Fin N → Fin 2 =>
            binPrefixWord hl1 w = u)).card = 2 ^ (N - m) := by
        intro u
        let e : {w : Fin N → Fin 2 // binPrefixWord hl1 w = u} ≃
            (Fin (N - m) → Fin 2) :=
          { toFun := fun w j => w.1 ⟨m + j.1, by omega⟩
            invFun := fun tail =>
              ⟨fun t => if ht : t.1 < m then u ⟨t.1, ht⟩ else tail ⟨t.1 - m, by omega⟩, by
                funext ⟨t, ht⟩
                simp [binPrefixWord, ht]⟩
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
        have hcard_eq : (Finset.univ.filter (fun w : Fin N → Fin 2 =>
            binPrefixWord hl1 w = u)).card =
            Fintype.card {w : Fin N → Fin 2 // binPrefixWord hl1 w = u} :=
          (Fintype.card_subtype _).symm
        rw [hcard_eq, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hcard_nat : (Finset.univ.filter (fun w : Fin N → Fin 2 =>
            (V i ∩ binInterv k N w).Nonempty)).card ≤ 2 * 2 * 2 ^ (N - lvl i) := by
        calc (Finset.univ.filter (fun w : Fin N → Fin 2 =>
                (V i ∩ binInterv k N w).Nonempty)).card
            ≤ (A_i.biUnion (fun u => Finset.univ.filter (fun w : Fin N → Fin 2 =>
                binPrefixWord hl1 w = u))).card := Finset.card_le_card hsub_fib
          _ ≤ ∑ u ∈ A_i, (Finset.univ.filter (fun w : Fin N → Fin 2 =>
                binPrefixWord hl1 w = u)).card := Finset.card_biUnion_le
          _ = ∑ _u ∈ A_i, 2 ^ (N - m) :=
              Finset.sum_congr rfl (fun u _ => hfib_card u)
          _ = A_i.card * 2 ^ (N - m) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 2 * 2 ^ (N - m) := Nat.mul_le_mul_right _ hAi_le
          _ = 2 * (2 * 2 ^ (N - lvl i)) := by
              have hexp : N - m = (N - lvl i) + 1 := by omega
              rw [hexp, pow_succ']
          _ = 2 * 2 * 2 ^ (N - lvl i) := by ring
      have hcardR : ((Finset.univ.filter (fun w : Fin N → Fin 2 =>
            (V i ∩ binInterv k N w).Nonempty)).card : ℝ) ≤
            (2 * 2 * 2 ^ (N - lvl i) : ℕ) := by exact_mod_cast hcard_nat
      push_cast [b] at hcardR ⊢
      linarith
    have htotal : b ^ N ≤ ∑ i ∈ F, 2 * b * b ^ (N - lvl i) := by
      have h1 : 2 ^ N ≤ ∑ i ∈ F, (Finset.univ.filter (fun w : Fin N → Fin 2 =>
          (V i ∩ binInterv k N w).Nonempty)).card := by
        have hcard_univ : (Finset.univ : Finset (Fin N → Fin 2)).card = 2 ^ N := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [← hcard_univ]
        exact le_trans (Finset.card_le_card hcover_words) Finset.card_biUnion_le
      have h1R : b ^ N ≤ ∑ i ∈ F, ((Finset.univ.filter (fun w : Fin N → Fin 2 =>
          (V i ∩ binInterv k N w).Nonempty)).card : ℝ) := by
        have h1' : ((2 ^ N : ℕ) : ℝ) ≤
            ((∑ i ∈ F, (Finset.univ.filter (fun w : Fin N → Fin 2 =>
              (V i ∩ binInterv k N w).Nonempty)).card : ℕ) : ℝ) := by exact_mod_cast h1
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
                  simp only [one_div]; ring
                rw [h1, tsum_mul_left]; ring
              rw [htsum, tsum_geometric_two]; ring
    exact le_trans h1 (add_le_add hS_ge hδ_ge)
  have hlt_c0 : S + ENNReal.ofReal δ0 < c₀ := by
    have h1 : S + ENNReal.ofReal δ0 = ENNReal.ofReal (S.toReal + δ0) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_of_lt hδ0), ENNReal.ofReal_toReal hS_ne_top]
    rw [h1]
    exact (ENNReal.ofReal_lt_ofReal_iff hc₀R_pos).mpr (by dsimp [δ0]; linarith)
  exact not_lt_of_ge (le_trans hsum_lb hsum_ub) hlt_c0

/-- 无符号精确极限集 $E_{\mathrm{lim}}(k/4)$ 在 $L$-平移下不变。 -/
theorem unsignedExactLimit_add_latticeL (k : ℕ) {y : ℝ} (hy : y ∈ Classification.latticeL) :
    (fun x : ℝ => x + y) ⁻¹' unsignedExactLimitSet k = unsignedExactLimitSet k := by
  have hfwd : ∀ (z : ℝ) {w : ℝ} (hw : w ∈ Classification.latticeL),
      z ∈ unsignedExactLimitSet k → z + w ∈ unsignedExactLimitSet k := by
    intro z w hw hz
    have hw0 : Tendsto (apprSeq w) atTop (nhds 0) :=
      (Classification.theorem2_classification w).mpr hw
    have hdiff0 : Tendsto (fun j : ℕ => apprSeq (z + w) j - apprSeq z j) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hw0.neg) hw0 ?_ ?_
      · filter_upwards with j
        exact (abs_le.mp (abs_apprSeq_add_sub_le z w j)).1
      · filter_upwards with j
        exact (abs_le.mp (abs_apprSeq_add_sub_le z w j)).2
    have hsum := hz.add hdiff0
    show Tendsto (apprSeq (z + w)) atTop (nhds ((k : ℝ) / 4))
    simpa [add_zero] using hsum
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro hx
    have h := hfwd (x + y) (neg_mem_latticeL hy) hx
    have heq : x + y + -y = x := by ring
    rwa [heq] at h
  · intro hx
    exact hfwd x hy hx

/-- **Theorem 16(ii) 显式普适规范正测度定理**：
    对一切 $k \ge 1$，$\mathcal{H}^{g_2}(E_{\mathrm{lim}}(k/4)) > 0$。 -/
theorem mkMetric_binaryGauge_unsignedExactLimit_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Measure.mkMetric binaryGauge (unsignedExactLimitSet k) := by
  have htree_pos : 0 < Measure.mkMetric binaryGauge (binCantorTree k) := by
    refine mkMetric_binCantorTree_pos k hk binaryGauge binaryGauge_mono binaryGauge_continuous
      (1 / 2) (by norm_num) ?_
    intro n
    rw [binaryGauge_at_inv_Qsel (by omega : 1 ≤ n + 1)]
    apply ENNReal.ofReal_le_ofReal
    have halg : (1 / 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      field_simp
    exact le_of_eq halg
  exact lt_of_lt_of_le htree_pos (measure_mono (binCantorTree_subset_unsignedExactLimit k hk))

/-- **Theorem 16(ii) 任意非空开区间上的 $\mathcal{H}^{g_2}$ 无穷测度定理**：
    对一切 $k \ge 1$ 与任意 $a < b$，
    `Measure.mkMetric binaryGauge (unsignedExactLimitSet k ∩ Set.Ioo a b) = ⊤`。 -/
theorem mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top (k : ℕ) (hk : 1 ≤ k)
    {a b : ℝ} (hab : a < b) :
    Measure.mkMetric binaryGauge (unsignedExactLimitSet k ∩ Set.Ioo a b) = ⊤ := by
  have htree_pos : 0 < Measure.mkMetric binaryGauge (binCantorTree k) := by
    refine mkMetric_binCantorTree_pos k hk binaryGauge binaryGauge_mono binaryGauge_continuous
      (1 / 2) (by norm_num) ?_
    intro n
    rw [binaryGauge_at_inv_Qsel (by omega : 1 ≤ n + 1)]
    apply ENNReal.ofReal_le_ofReal
    have halg : (1 / 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ]
      field_simp
    exact le_of_eq halg
  have hKE_null : Measure.mkMetric binaryGauge (binCantorTree k \ unsignedExactLimitSet k) = 0 := by
    have hempty : binCantorTree k \ unsignedExactLimitSet k = ∅ :=
      Set.sdiff_eq_empty.mpr (binCantorTree_subset_unsignedExactLimit k hk)
    rw [hempty, measure_empty]
  refine mkMetric_inter_Ioo_eq_top_of_compact_tree binaryGauge (binCantorTree k)
    (unsignedExactLimitSet k) (isCompact_binCantorTree k) htree_pos hKE_null
    (fun _ hy => unsignedExactLimit_add_latticeL k hy) 2 (J_cantor k)
    (by norm_num) (by unfold J_cantor; omega)
    (fun M w => (binCenterInt k M w : ℝ) / (Qsel (J_cantor k + M + 1) : ℝ))
    (fun M => radC k M) (fun M => radC_pos k M) (fun M => radC_le_quarter_inv k M hk)
    (fun M x hx => by
      have hxM := Set.mem_iInter.mp hx M
      rcases Set.mem_iUnion.mp hxM with ⟨w, hw⟩
      exact Set.mem_iUnion.mpr ⟨w, hw⟩)
    hab

/-- **Theorem 16(ii) 全局无穷测度定理**：
    对一切 $k \ge 1$，`Measure.mkMetric binaryGauge (unsignedExactLimitSet k) = ⊤`。 -/
theorem mkMetric_binaryGauge_unsignedExactLimit_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric binaryGauge (unsignedExactLimitSet k) = ⊤ := by
  have h1 := mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top k hk (by norm_num : (0 : ℝ) < 1)
  exact top_unique (h1 ▸ measure_mono Set.inter_subset_left)

/-- **Theorem 16(ii) 显式普适规范 $g_2$ 的 $\sigma$-有限可数覆盖分解**。 -/
theorem binaryGauge_unsignedExactLimit_sigma_finite_cover (k : ℕ) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set ℝ,
      unsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric binaryGauge (E i) < ⊤ := by
  refine GaugeExact.unsignedExactLimit_countable_cover_finite_mkMetric_base2 k
    binaryGauge binaryGauge_mono 1 ?_
  intro n hn
  rw [binaryGauge_at_inv_Qsel hn, one_mul]

/-- **Theorem 16(ii) 显式临界规范 $h_k$ 下无符号精确极限集测度为零**：
    $\mathcal{H}^{h_k}(E_{\mathrm{lim}}(k/4)) = 0$。 -/
theorem critGauge_unsignedExactLimit_null (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) (unsignedExactLimitSet k) = 0 := by
  refine GaugeExact.mkMetric_unsignedExactLimit_null_of_hk k hk (critGauge k)
    (critGauge_mono k hk) 1 ?_
  intro n hn
  rw [critGauge_at_inv_Qsel k hk hn, one_mul]

/-! ## 第五部分：幂规范族 $g_\beta$ 的完整精确性（Theorem 13 与 Theorem 16(ii) 阈值相变） -/

/-- 对任意 $1 < b_1 < b_2$，插值规范比 $g_{b_2}(r) / g_{b_1}(r) \to 0$（$r \to 0^+$）。 -/
lemma interpGauge_ratio_tendsto_zero {b₁ b₂ : ℝ} (hb₁ : 1 < b₁) (hb₂ : b₁ < b₂) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → interpGauge b₂ r ≤ (ε : ℝ≥0∞) * interpGauge b₁ r := by
  intro ε hε
  have hb₁_pos : 0 < b₁ := lt_trans zero_lt_one hb₁
  have hb₂_pos : 0 < b₂ := lt_trans hb₁_pos hb₂
  have hb₂_gt1 : 1 < b₂ := lt_trans hb₁ hb₂
  have hratio_nn : 0 ≤ b₁ / b₂ := div_nonneg (le_of_lt hb₁_pos) (le_of_lt hb₂_pos)
  have hratio_lt : b₁ / b₂ < 1 := (div_lt_one hb₂_pos).mpr hb₂
  have hpow0 : Tendsto (fun n : ℕ => b₁ * (b₁ / b₂) ^ n) atTop (nhds 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt).const_mul b₁
    simpa using h1
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hpow0.eventually (Iio_mem_nhds hεR))
  set N := max 1 N0
  have hN1 : 1 ≤ N := le_max_left _ _
  have hN_bound : b₁ * (b₁ / b₂) ^ N ≤ (ε : ℝ) := le_of_lt (hN0 N (le_max_right _ _))
  refine ⟨ENNReal.ofReal (invQ (N + 1)), ENNReal.ofReal_pos.mpr (invQ_pos (N + 1)), ?_⟩
  intro r hr
  by_cases hr0 : r = 0
  · subst hr0
    simp [interpGauge_zero]
  · have hr_lt_top : r < ⊤ := lt_of_le_of_lt hr ENNReal.ofReal_lt_top
    have hr_ne_top : r ≠ ⊤ := ne_of_lt hr_lt_top
    have hr_pos : 0 < r := pos_iff_ne_zero.mpr hr0
    have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr0 hr_ne_top
    have hr_real_le : r.toReal ≤ invQ (N + 1) := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hr
      rwa [ENNReal.toReal_ofReal (le_of_lt (invQ_pos (N + 1)))] at h1
    have hr_lt_invQN : r.toReal < invQ N :=
      lt_of_le_of_lt hr_real_le (invQ_succ_lt N hN1)
    have hr_lt_one : r.toReal < 1 := lt_of_lt_of_le hr_lt_invQN (invQ_le_one hN1)
    set n := interpIdx r.toReal
    obtain ⟨hn1, hnlo, hnhi⟩ := interpIdx_spec hr_real_pos hr_lt_one
    have hN_le_n : N ≤ n := by
      by_contra hlt
      push Not at hlt
      have hle : n + 1 ≤ N := by omega
      have hq : invQ N ≤ invQ (n + 1) :=
        invQ_antitoneOn (Set.mem_Ici.mpr (by omega)) (Set.mem_Ici.mpr hN1) hle
      linarith
    have hb₂_le : interpGaugeReal b₂ r.toReal ≤ b₂ ^ (-(n : ℤ)) := by
      calc interpGaugeReal b₂ r.toReal
          ≤ interpGaugeReal b₂ (invQ n) := interpGaugeReal_mono hb₂_gt1 (le_of_lt hnhi)
        _ = b₂ ^ (-(n : ℤ)) := interpGaugeReal_at_invQ hb₂_gt1 hn1
    have hb₁_ge : b₁ ^ (-((n + 1 : ℕ) : ℤ)) ≤ interpGaugeReal b₁ r.toReal := by
      calc b₁ ^ (-((n + 1 : ℕ) : ℤ))
          = interpGaugeReal b₁ (invQ (n + 1)) := (interpGaugeReal_at_invQ hb₁ (by omega)).symm
        _ ≤ interpGaugeReal b₁ r.toReal := interpGaugeReal_mono hb₁ hnlo
    have hpow_mono : b₁ * (b₁ / b₂) ^ n ≤ b₁ * (b₁ / b₂) ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hratio_nn (le_of_lt hratio_lt) hN_le_n)
        (le_of_lt hb₁_pos)
    have halg : b₂ ^ (-(n : ℤ)) = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, div_pow]
      have hb1n : b₁ ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb₁_pos)
      have hb2n : b₂ ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hb₂_pos)
      have hb10 : b₁ ≠ 0 := ne_of_gt hb₁_pos
      field_simp
    have hreal : interpGaugeReal b₂ r.toReal ≤ (ε : ℝ) * interpGaugeReal b₁ r.toReal := by
      calc interpGaugeReal b₂ r.toReal
          ≤ b₂ ^ (-(n : ℤ)) := hb₂_le
        _ = (b₁ * (b₁ / b₂) ^ n) * b₁ ^ (-((n + 1 : ℕ) : ℤ)) := halg
        _ ≤ (b₁ * (b₁ / b₂) ^ N) * interpGaugeReal b₁ r.toReal := by
            exact mul_le_mul hpow_mono hb₁_ge (zpow_nonneg (le_of_lt hb₁_pos) _) (by positivity)
        _ ≤ (ε : ℝ) * interpGaugeReal b₁ r.toReal := by
            gcongr
            exact interpGaugeReal_nonneg hb₁ r.toReal
    rw [interpGauge_eq_ofReal_toReal hb₂_gt1 hr_ne_top, interpGauge_eq_ofReal_toReal hb₁ hr_ne_top]
    have hεE : (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) := by simp
    rw [hεE, ← ENNReal.ofReal_mul (by exact hε.le)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- **Theorem 13 幂规范 $\beta > 2k+1$ 零测度**：
    $\mathcal{H}^{g_\beta}(\{\Lambda \le k/4\}) = 0$（从而 $\mathcal{H}^{g_\beta}(\{\Lambda = k/4\}) = 0$）。 -/
theorem mkMetric_powerGauge_exactLevel_null_of_gt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ : 2 * (k : ℝ) + 1 < β) :
    Measure.mkMetric (interpGauge β) {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} = 0 ∧
    Measure.mkMetric (interpGauge β) {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = 0 := by
  have hb1 : (1 : ℝ) < 2 * (k : ℝ) + 1 := critGauge_base_gt_one k hk
  have hβ1 : 1 < β := lt_trans hb1 hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ1
  have hsub : Tendsto (fun n : ℕ => (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) *
      interpGauge β (ENNReal.ofReal (1 / (Qsel n : ℝ)))) atTop (nhds 0) := by
    have hratio_nn : 0 ≤ (2 * (k : ℝ) + 1) / β := div_nonneg (by positivity) (le_of_lt hβpos)
    have hratio_lt : (2 * (k : ℝ) + 1) / β < 1 := (div_lt_one hβpos).mpr hβ
    have hpow0 : Tendsto (fun n : ℕ => ((2 * (k : ℝ) + 1) / β) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt
    have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 * (k : ℝ) + 1) / β) ^ n)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hpow0
    have hev : ∀ᶠ n : ℕ in atTop,
        (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) * interpGauge β (ENNReal.ofReal (1 / (Qsel n : ℝ))) =
          ENNReal.ofReal (((2 * (k : ℝ) + 1) / β) ^ n) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [interpGauge_at_inv_Qsel hβ1 hn]
      have hcast : (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 * (k : ℝ) + 1) ^ n) := by
        rw [← ENNReal.ofReal_natCast]; push_cast; rfl
      rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv]
    exact hof0.congr' (hev.mono fun _ h => h.symm)
  have hle0 : Measure.mkMetric (interpGauge β)
      {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} = 0 :=
    GaugeNull.mkMetric_levelSet_null_of_subgauge k (interpGauge β) (interpGauge_mono hβ1) hsub
  refine ⟨hle0, measure_mono_null (fun _ hx => le_of_eq hx) hle0⟩

/-- **Theorem 13 幂规范 $1 < \beta < 2k+1$ 非 $\sigma$-有限性**：
    对 $1 < \beta < 2k+1$，精确水平集 $\{\Lambda = k/4\}$ 对 $\mathcal{H}^{g_\beta}$ 测度为 $\top$ 且非 $\sigma$-有限。 -/
theorem mkMetric_powerGauge_exactLevel_not_sigma_finite_of_lt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) (hβlt : β < 2 * (k : ℝ) + 1) :
    Measure.mkMetric (interpGauge β) {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (interpGauge β) (E i) < ⊤ :=
  GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero (critGauge k) (interpGauge β)
    (interpGauge_ratio_tendsto_zero hβ1 hβlt) (mkMetric_critGauge_exactLevel_pos k hk)

/-- **Theorem 16(ii) 幂规范 $\beta > 2$ 零测度**：$\mathcal{H}^{g_\beta}(E_{\mathrm{lim}}(k/4)) = 0$。 -/
theorem mkMetric_powerGauge_unsignedExactLimit_null_of_gt (k : ℕ)
    {β : ℝ} (hβ : 2 < β) :
    Measure.mkMetric (interpGauge β) (unsignedExactLimitSet k) = 0 := by
  have hβ1 : 1 < β := by linarith
  have hβpos : 0 < β := by linarith
  have hsub : Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ≥0∞) *
      interpGauge β (ENNReal.ofReal (1 / (Qsel n : ℝ)))) atTop (nhds 0) := by
    have hratio_nn : 0 ≤ (2 : ℝ) / β := div_nonneg (by norm_num) (le_of_lt hβpos)
    have hratio_lt : (2 : ℝ) / β < 1 := (div_lt_one hβpos).mpr hβ
    have hpow0 : Tendsto (fun n : ℕ => ((2 : ℝ) / β) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt
    have hof0 : Tendsto (fun n : ℕ => ENNReal.ofReal (((2 : ℝ) / β) ^ n)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hpow0
    have hev : ∀ᶠ n : ℕ in atTop,
        ((2 ^ n : ℕ) : ℝ≥0∞) * interpGauge β (ENNReal.ofReal (1 / (Qsel n : ℝ))) =
          ENNReal.ofReal (((2 : ℝ) / β) ^ n) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [interpGauge_at_inv_Qsel hβ1 hn]
      have hcast : ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [← ENNReal.ofReal_natCast]; push_cast; rfl
      rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [zpow_neg, zpow_natCast, div_pow, div_eq_mul_inv]
    exact hof0.congr' (hev.mono fun _ h => h.symm)
  exact GaugeExact.mkMetric_unsignedExactLimit_null_of_subgauge_base2 k
    (interpGauge β) (interpGauge_mono hβ1) hsub

/-- **Theorem 16(ii) 幂规范 $1 < \beta < 2$ 非 $\sigma$-有限性**：
    对 $1 < \beta < 2$，$E_{\mathrm{lim}}(k/4)$ 对 $\mathcal{H}^{g_\beta}$ 测度为 $\top$ 且非 $\sigma$-有限。 -/
theorem mkMetric_powerGauge_unsignedExactLimit_not_sigma_finite_of_lt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) (hβlt : β < 2) :
    Measure.mkMetric (interpGauge β) (unsignedExactLimitSet k) = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, unsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (interpGauge β) (E i) < ⊤ :=
  GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero binaryGauge (interpGauge β)
    (interpGauge_ratio_tendsto_zero hβ1 hβlt) (mkMetric_binaryGauge_unsignedExactLimit_pos k hk)

/-- **Corollary 14(iii) 显式临界规范版**：若 $h_k(r) / g(r) \to 0$（$r \to 0^+$），
    则 $\{\Lambda = k/4\}$ 对 $\mathcal{H}^g$ 测度为 $\top$ 且非 $\sigma$-有限。 -/
theorem mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → critGauge k r ≤ (ε : ℝ≥0∞) * g r) :
    Measure.mkMetric g {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ :=
  GaugeExact.not_countable_union_finite_of_ratio_tendsto_zero (critGauge k) g hratio
    (mkMetric_critGauge_exactLevel_pos k hk)

/-- **Remark 15 相邻能级规范比趋零**：$k \ge 2$ 时 $h_k(r) / h_{k-1}(r) \to 0$（$r \to 0^+$）。 -/
lemma critGauge_adjacent_ratio_tendsto_zero (k : ℕ) (hk : 2 ≤ k) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → critGauge k r ≤ (ε : ℝ≥0∞) * critGauge (k - 1) r := by
  have hb1 : (1 : ℝ) < 2 * ((k - 1 : ℕ) : ℝ) + 1 :=
    critGauge_base_gt_one (k - 1) (by omega)
  have hlt : 2 * ((k - 1 : ℕ) : ℝ) + 1 < 2 * (k : ℝ) + 1 := by
    have : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ k)
    linarith
  exact interpGauge_ratio_tendsto_zero hb1 hlt

/-- **Remark 15 相邻能级分离（上能级规范测下能级为零、下能级规范测上能级非 $\sigma$-有限）**。 -/
theorem critGauge_adjacent_level_separation (k : ℕ) (hk : 2 ≤ k) :
    Measure.mkMetric (critGauge k) {x : ℝ | apprExponent x ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 4)} = 0 ∧
    Measure.mkMetric (critGauge (k - 1)) {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} = ⊤ ∧
    ¬ ∃ E : ℕ → Set ℝ, {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (critGauge (k - 1)) (E i) < ⊤ := by
  have hnull : Measure.mkMetric (critGauge k)
      {x : ℝ | apprExponent x ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 4)} = 0 := by
    have hk' : 1 ≤ k := by omega
    have hlt : ((k - 1 : ℕ) : ℝ) / 4 < (k : ℝ) / 4 := by
      have : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk'
      linarith
    have hsub : {x : ℝ | apprExponent x ≤ ENNReal.ofReal (((k - 1 : ℕ) : ℝ) / 4)} ⊆
        {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} := by
      intro x hx
      exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt)
    exact measure_mono_null hsub (mkMetric_critGauge_strictLevel_null k hk')
  have hsep := mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio k (by omega)
    (critGauge (k - 1)) (critGauge_adjacent_ratio_tendsto_zero k hk)
  exact ⟨hnull, hsep.1, hsep.2⟩

/-- **Theorem 16(ii) 推论（$[0, 1]$ 上的 $\mathcal{H}^{g_2}$ 无穷测度）**。 -/
theorem mkMetric_binaryGauge_unsignedExactLimit_inter_Icc_zero_one_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric binaryGauge (unsignedExactLimitSet k ∩ Set.Icc (0 : ℝ) 1) = ⊤ := by
  have hsub : unsignedExactLimitSet k ∩ Set.Ioo (0 : ℝ) 1 ⊆
      unsignedExactLimitSet k ∩ Set.Icc (0 : ℝ) 1 :=
    Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
  have htop := mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top k hk (by norm_num : (0 : ℝ) < 1)
  exact top_unique (htop ▸ measure_mono hsub)

/-! ## 第六部分：商群度量空间 $\mathbb{R}/\mathbb{Z}$（`UnitAddCircle`）上的原生形式化

本节将 `ℝ` 上的临界规范定理（Theorem 13、Corollary 14(i)(iii)、Remark 15）与无符号精确极限集
普适二进规范定理（Theorem 16(ii)）直接迁移到紧致圆周群 `UnitAddCircle := AddCircle (1 : ℝ)` 上：
1. 利用 `DimHFinite.apprExponent_add_intCast` 将 `apprExponent` 与 `unsignedExactLimitSet k`
   良定义地下降到 `UnitAddCircle`（`circleApprExponent`、`circleExactLevel`、`circleUnsignedExactLimitSet`）；
2. 证明自然投影 `circleProj : ℝ → UnitAddCircle` 全局 $1$-Lipschitz（`mkMetric_circleProj_image_le`）
   且在任意长度 $\le 1/2$ 的区间 `(a, b)` 上为等距嵌入（`mkMetric_le_circleProj_image_of_subset_Ioo`）；
3. 对 `UnitAddCircle` 上任意非空开集 $U$，取 `circleProj ⁻¹' U` 内宽度 $< 1/2$ 的开区间，
   直接证明 Corollary 14(i)（`mkMetric_critGauge_circleExactLevel_inter_open_eq_top`）与
   Theorem 16(ii)（`mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top`）及其全部 $\sigma$-有限性、
   $g_\beta$ 相变与相邻能级分离定理。 -/

/-- 圆周自然投影 $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$。 -/
def circleProj : ℝ → UnitAddCircle := QuotientAddGroup.mk

lemma circleProj_continuous : Continuous circleProj :=
  AddCircle.continuous_mk' (1 : ℝ)

lemma circleProj_surjective : Function.Surjective circleProj :=
  QuotientAddGroup.mk_surjective

lemma apprExponent_eq_of_circleProj_eq {x y : ℝ} (hxy : circleProj x = circleProj y) :
    apprExponent x = apprExponent y := by
  have hmem : x - y ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  have hx : x = y + (m : ℝ) := by
    have hm1 : (m : ℝ) = x - y := by simpa [zsmul_eq_mul, mul_one] using hm
    linarith
  rw [hx]
  exact DimHFinite.apprExponent_add_intCast y m

/-- 圆周 $\mathbb{R}/\mathbb{Z}$ 上的逼近指数 $\Lambda : \mathbb{R}/\mathbb{Z} \to \mathbb{R}_{\ge 0\infty}$。 -/
def circleApprExponent (z : UnitAddCircle) : ℝ≥0∞ :=
  Quotient.liftOn' z apprExponent (fun _ _ hab => by
    apply apprExponent_eq_of_circleProj_eq
    exact Quotient.sound' hab)

@[simp]
lemma circleApprExponent_circleProj (x : ℝ) :
    circleApprExponent (circleProj x) = apprExponent x := rfl

/-- 圆周上的精确能级 $S_k = \{z \in \mathbb{R}/\mathbb{Z} : \Lambda(z) = k/4\}$。 -/
def circleExactLevel (k : ℕ) : Set UnitAddCircle :=
  {z : UnitAddCircle | circleApprExponent z = ENNReal.ofReal ((k : ℝ) / 4)}

/-- 圆周上的严格子水平集 $\{z \in \mathbb{R}/\mathbb{Z} : \Lambda(z) < k/4\}$。 -/
def circleStrictLevel (k : ℕ) : Set UnitAddCircle :=
  {z : UnitAddCircle | circleApprExponent z < ENNReal.ofReal ((k : ℝ) / 4)}

/-- 圆周上的非严格子水平集 $\{z \in \mathbb{R}/\mathbb{Z} : \Lambda(z) \le k/4\}$。 -/
def circleLevelSet (k : ℕ) : Set UnitAddCircle :=
  {z : UnitAddCircle | circleApprExponent z ≤ ENNReal.ofReal ((k : ℝ) / 4)}

/-- 圆周上的无符号精确极限集 $E_{\mathrm{lim}}(k/4) \subset \mathbb{R}/\mathbb{Z}$。 -/
def circleUnsignedExactLimitSet (k : ℕ) : Set UnitAddCircle :=
  circleProj '' unsignedExactLimitSet k

lemma circleProj_mem_circleUnsignedExactLimitSet_iff (k : ℕ) (x : ℝ) :
    circleProj x ∈ circleUnsignedExactLimitSet k ↔ x ∈ unsignedExactLimitSet k := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hmem : y - x ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      QuotientAddGroup.eq_iff_sub_mem.mp hyx
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have hx_eq : x = y + ((-m : ℤ) : ℝ) := by
      have hm1 : (m : ℝ) = y - x := by simpa [zsmul_eq_mul, mul_one] using hm
      push_cast
      linarith
    have hmL : ((-m : ℤ) : ℝ) ∈ Classification.latticeL := ⟨-m, 0, by simp⟩
    have hinv := unsignedExactLimit_add_latticeL k hmL
    have hpre : y ∈ (fun t : ℝ => t + ((-m : ℤ) : ℝ)) ⁻¹' unsignedExactLimitSet k := by
      rw [hinv]; exact hy
    change y + ((-m : ℤ) : ℝ) ∈ unsignedExactLimitSet k at hpre
    rwa [← hx_eq] at hpre
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma circleStrictLevel_eq_image (k : ℕ) :
    circleStrictLevel k = circleProj '' {x : ℝ | apprExponent x < ENNReal.ofReal ((k : ℝ) / 4)} := by
  ext z
  obtain ⟨x, rfl⟩ := circleProj_surjective z
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [circleStrictLevel, Set.mem_ofPred_eq, circleApprExponent_circleProj,
      ← apprExponent_eq_of_circleProj_eq hyx]
    exact hy

lemma circleLevelSet_eq_image (k : ℕ) :
    circleLevelSet k = circleProj '' {x : ℝ | apprExponent x ≤ ENNReal.ofReal ((k : ℝ) / 4)} := by
  ext z
  obtain ⟨x, rfl⟩ := circleProj_surjective z
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [circleLevelSet, Set.mem_ofPred_eq, circleApprExponent_circleProj,
      ← apprExponent_eq_of_circleProj_eq hyx]
    exact hy

lemma circleExactLevel_eq_image (k : ℕ) :
    circleExactLevel k = circleProj '' {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} := by
  ext z
  obtain ⟨x, rfl⟩ := circleProj_surjective z
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [circleExactLevel, Set.mem_ofPred_eq, circleApprExponent_circleProj,
      ← apprExponent_eq_of_circleProj_eq hyx]
    exact hy

lemma edist_circleProj_le (x y : ℝ) :
    edist (circleProj x) (circleProj y) ≤ edist x y := by
  rw [edist_dist, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [dist_eq_norm, Real.dist_eq]
  change ‖((x - y : ℝ) : UnitAddCircle)‖ ≤ |x - y|
  rw [UnitAddCircle.norm_eq]
  simpa using round_le (x - y) 0

lemma ediam_circleProj_image_le (s : Set ℝ) :
    Metric.ediam (circleProj '' s) ≤ Metric.ediam s := by
  rw [Metric.ediam_le_iff]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact le_trans (edist_circleProj_le x y) (Metric.edist_le_ediam_of_mem hx hy)

lemma mkMetric_circleProj_image_le (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m) (A : Set ℝ) :
    Measure.mkMetric m (circleProj '' A) ≤ Measure.mkMetric m A := by
  rw [Measure.mkMetric_apply, Measure.mkMetric_apply]
  refine iSup₂_le fun r hr => le_trans ?_ (le_iSup₂ r hr)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  let t' : ℕ → Set UnitAddCircle := fun n => circleProj '' t n
  have hcov' : circleProj '' A ⊆ ⋃ n, t' n := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨n, ⟨x, hn, rfl⟩⟩
  have hdiam' : ∀ n, Metric.ediam (t' n) ≤ r := fun n =>
    le_trans (ediam_circleProj_image_le (t n)) (hdiam n)
  refine le_trans (iInf_le _ t') (le_trans (iInf_le _ hcov') (le_trans (iInf_le _ hdiam') ?_))
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hne : (t n).Nonempty
  · have hne' : (t' n).Nonempty := hne.image _
    simp only [hne, hne', ciSup_pos]
    exact hm (ediam_circleProj_image_le (t n))
  · have hne' : ¬ (t' n).Nonempty := by
      rintro ⟨_, x, hx, _⟩; exact hne ⟨x, hx⟩
    simp only [hne, hne', ciSup_false, le_refl]

lemma edist_circleProj_eq_of_mem_Ioo {a b x y : ℝ} (hwidth : b - a ≤ 1 / 2)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    edist (circleProj x) (circleProj y) = edist x y := by
  rw [edist_dist, edist_dist]
  congr 1
  rw [dist_eq_norm, Real.dist_eq]
  change ‖((x - y : ℝ) : UnitAddCircle)‖ = |x - y|
  rw [AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero]
  norm_num
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma mkMetric_le_circleProj_image_of_subset_Ioo (m : ℝ≥0∞ → ℝ≥0∞) (hm : Monotone m)
    {a b : ℝ} (hwidth : b - a ≤ 1 / 2) {A : Set ℝ} (hA : A ⊆ Set.Ioo a b) :
    Measure.mkMetric m A ≤ Measure.mkMetric m (circleProj '' A) := by
  rw [Measure.mkMetric_apply, Measure.mkMetric_apply]
  refine iSup₂_le fun r hr => le_trans ?_ (le_iSup₂ r hr)
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  let s : ℕ → Set ℝ := fun n => (circleProj ⁻¹' t n) ∩ Set.Ioo a b
  have hcov_s : A ⊆ ⋃ n, s n := by
    intro x hx
    have hmem : circleProj x ∈ circleProj '' A := ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hmem)
    exact Set.mem_iUnion.mpr ⟨n, hn, hA hx⟩
  have hdiam_s : ∀ n, Metric.ediam (s n) ≤ Metric.ediam (t n) := by
    intro n
    rw [Metric.ediam_le_iff]
    intro x hx y hy
    rw [← edist_circleProj_eq_of_mem_Ioo hwidth hx.2 hy.2]
    exact Metric.edist_le_ediam_of_mem hx.1 hy.1
  have hdiam_r : ∀ n, Metric.ediam (s n) ≤ r := fun n => le_trans (hdiam_s n) (hdiam n)
  refine le_trans (iInf_le _ s) (le_trans (iInf_le _ hcov_s) (le_trans (iInf_le _ hdiam_r) ?_))
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases hne : (s n).Nonempty
  · have hne' : (t n).Nonempty := let ⟨x, hx⟩ := hne; ⟨circleProj x, hx.1⟩
    simp only [hne, hne', ciSup_pos]
    exact hm (hdiam_s n)
  · simp only [hne, ciSup_false, bot_le]

/-- 在 `UnitAddCircle` 上的规范比较引理（覆盖紧致圆周上的任意 $c \ge 0$）。 -/
theorem mkMetric_le_mul_of_eventually_le_circle
    (h g : ℝ≥0∞ → ℝ≥0∞) {δ : ℝ≥0∞} (c : ℝ≥0) (hδ : 0 < δ)
    (hle : ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (c : ℝ≥0∞) * g r) (E : Set UnitAddCircle) :
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
    let t : ℕ → Set UnitAddCircle := fun n =>
      circleProj '' Set.Icc ((e n : ℝ) * d) (((e n : ℝ) + 1) * d)
    have hcov : E ⊆ ⋃ n, t n := by
      intro z _
      obtain ⟨x, rfl⟩ := circleProj_surjective z
      set k : ℤ := Int.floor (x / d)
      refine Set.mem_iUnion.mpr ⟨(Denumerable.eqv ℤ) k, x, ?_, rfl⟩
      simp only [e, Equiv.symm_apply_apply]
      have hk1 : (k : ℝ) ≤ x / d := Int.floor_le (x / d)
      have hk2 : x / d < (k : ℝ) + 1 := Int.lt_floor_add_one (x / d)
      exact ⟨(le_div_iff₀ hd_pos).mp hk1, le_of_lt ((div_lt_iff₀ hd_pos).mp hk2)⟩
    have hed_le_d : ∀ n, Metric.ediam (t n) ≤ ENNReal.ofReal d := fun n => by
      calc Metric.ediam (t n)
          ≤ Metric.ediam (Set.Icc ((e n : ℝ) * d) (((e n : ℝ) + 1) * d)) :=
            ediam_circleProj_image_le _
        _ = ENNReal.ofReal d := by rw [Real.ediam_Icc]; congr 1; ring
    have hdiam : ∀ n, Metric.ediam (t n) ≤ r := fun n => le_trans (hed_le_d n) hd_le_r
    refine le_trans (iInf_le _ t) (le_trans (iInf_le _ hcov) (le_trans (iInf_le _ hdiam) ?_))
    have hzero : ∀ n, (⨆ _ : (t n).Nonempty, h (Metric.ediam (t n))) = 0 := fun n => by
      have h0 : h (Metric.ediam (t n)) = 0 :=
        le_antisymm (hle _ (le_trans (hed_le_d n) hd_le_δ)) zero_le
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
        ⨅ (t : ℕ → Set UnitAddCircle) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r0),
          ∑' n, ⨆ _ : (t n).Nonempty, g (Metric.ediam (t n))) r')
    rw [ENNReal.mul_iSup]
    refine le_trans ?_ (le_iSup (f := fun _ : 0 < r' =>
      (c : ℝ≥0∞) * ⨅ (t : ℕ → Set UnitAddCircle) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r'),
        ∑' n, ⨆ _ : (t n).Nonempty, g (Metric.ediam (t n))) hr'_pos)
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun t => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun hcov => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.coe_ne_top]
    refine le_iInf fun hdiam => ?_
    have hdiam_r : ∀ n, Metric.ediam (t n) ≤ r := fun n => le_trans (hdiam n) hr'_le_r
    refine le_trans (iInf_le _ t) (le_trans (iInf_le _ hcov) (le_trans (iInf_le _ hdiam_r) ?_))
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    by_cases hne : (t n).Nonempty
    · simp [hne, hle (Metric.ediam (t n)) (le_trans (hdiam n) hr'_le_δ)]
    · simp [hne]

lemma mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top_circle
    (h g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (ε : ℝ≥0∞) * g r)
    {E : Set UnitAddCircle} (hfin : Measure.mkMetric g E < ⊤) :
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
  have hcomp := mkMetric_le_mul_of_eventually_le_circle h g ε hδ_pos hle E
  have hMg : Measure.mkMetric g E ≤ (M : ℝ≥0∞) := by
    have h1 : ((Measure.mkMetric g E).toNNReal : ℝ≥0∞) = Measure.mkMetric g E :=
      ENNReal.coe_toNNReal (ne_of_lt hfin)
    dsimp [M]
    rw [h1]
    exact le_self_add
  calc Measure.mkMetric h E
      ≤ (ε : ℝ≥0∞) * Measure.mkMetric g E := hcomp
    _ ≤ (ε : ℝ≥0∞) * (M : ℝ≥0∞) := by gcongr
    _ = ((ε * M : ℝ≥0) : ℝ≥0∞) := rfl
    _ = (η : ℝ≥0∞) := by congr 1; dsimp [ε]; exact div_mul_cancel₀ η (ne_of_gt hM_pos)

theorem not_countable_union_finite_of_ratio_tendsto_zero_circle
    (h g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → h r ≤ (ε : ℝ≥0∞) * g r)
    {S : Set UnitAddCircle} (hpos : 0 < Measure.mkMetric h S) :
    Measure.mkMetric g S = ⊤ ∧
    ¬ ∃ E : ℕ → Set UnitAddCircle, S ⊆ ⋃ i, E i ∧ ∀ i, Measure.mkMetric g (E i) < ⊤ := by
  constructor
  · by_contra hne_top
    have hlt : Measure.mkMetric g S < ⊤ := lt_top_iff_ne_top.mpr hne_top
    exact (ne_of_gt hpos) (mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top_circle h g hratio hlt)
  · rintro ⟨E, hcov, hfin⟩
    have hzero_i : ∀ i : ℕ, Measure.mkMetric h (E i) = 0 :=
      fun i => mkMetric_eq_zero_of_ratio_tendsto_zero_of_lt_top_circle h g hratio (hfin i)
    exact (ne_of_gt hpos) (measure_mono_null hcov (measure_iUnion_null hzero_i))

/-- 从 `UnitAddCircle` 上的非空开集 `U` 中提取宽度 $\le 1/2$ 的开区间 `(a, b) ⊆ circleProj ⁻¹' U`。 -/
lemma exists_Ioo_subset_preimage_of_isOpen_circle {U : Set UnitAddCircle}
    (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    ∃ a b : ℝ, a < b ∧ b - a ≤ 1 / 2 ∧ Set.Ioo a b ⊆ circleProj ⁻¹' U := by
  obtain ⟨z₀, hz₀⟩ := hU_ne
  obtain ⟨x₀, rfl⟩ := circleProj_surjective z₀
  have hpre_open : IsOpen (circleProj ⁻¹' U) := hU_open.preimage circleProj_continuous
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hpre_open x₀ hz₀
  set δ : ℝ := min (r / 2) (1 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  refine ⟨x₀ - δ, x₀ + δ, by linarith, ?_, ?_⟩
  · have : δ ≤ 1 / 4 := min_le_right _ _
    linarith
  · intro x hx
    apply hr_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hδr : δ ≤ r / 2 := min_le_left _ _
    constructor <;> linarith [hx.1, hx.2]

/-- **Theorem 13（圆周 $\mathbb{R}/\mathbb{Z}$ 严格子水平集零测度）**：
    `Measure.mkMetric (critGauge k) (circleStrictLevel k) = 0`。 -/
theorem mkMetric_critGauge_circleStrictLevel_null (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) (circleStrictLevel k) = 0 := by
  rw [circleStrictLevel_eq_image]
  exact le_antisymm
    ((mkMetric_circleProj_image_le (critGauge k) (critGauge_mono k hk) _).trans_eq
      (mkMetric_critGauge_strictLevel_null k hk))
    zero_le

/-- **Corollary 14(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 次临界规范零测度）**：
    若单调函数 $g$ 满足 $(2k+1)^n g(1/Q_n) \to 0$，则 `Measure.mkMetric g (circleLevelSet k) = 0`。 -/
theorem mkMetric_circleLevelSet_null_of_subgauge (k : ℕ)
    (g : ℝ≥0∞ → ℝ≥0∞) (hg : Monotone g)
    (hsub : Tendsto (fun n : ℕ => (((2 * k + 1) ^ n : ℕ) : ℝ≥0∞) *
      g (ENNReal.ofReal (1 / (Qsel n : ℝ)))) atTop (nhds 0)) :
    Measure.mkMetric g (circleLevelSet k) = 0 := by
  rw [circleLevelSet_eq_image]
  exact le_antisymm
    ((mkMetric_circleProj_image_le g hg _).trans_eq
      (GaugeNull.mkMetric_levelSet_null_of_subgauge k g hg hsub))
    zero_le

/-- **Corollary 14(i)（圆周 $\mathbb{R}/\mathbb{Z}$ 任意非空开集/开弧上的 $\mathcal{H}^{h_k}$ 无穷测度）**：
    对任意 $k \ge 1$ 与 `UnitAddCircle` 的任意非空开子集 $U$，
    `Measure.mkMetric (critGauge k) (circleExactLevel k ∩ U) = ⊤`。 -/
theorem mkMetric_critGauge_circleExactLevel_inter_open_eq_top (k : ℕ) (hk : 1 ≤ k)
    {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric (critGauge k) (circleExactLevel k ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ := exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := {x : ℝ | apprExponent x = ENNReal.ofReal ((k : ℝ) / 4)} ∩ Set.Ioo a b
  have hA_img : circleProj '' A ⊆ circleExactLevel k ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩
    exact ⟨hxE, hsub hxI⟩
  have hle : Measure.mkMetric (critGauge k) A ≤
      Measure.mkMetric (critGauge k) (circleExactLevel k ∩ U) :=
    le_trans
      (mkMetric_le_circleProj_image_of_subset_Ioo (critGauge k) (critGauge_mono k hk) hwidth
        Set.inter_subset_right)
      (measure_mono hA_img)
  rw [mkMetric_critGauge_exactLevel_inter_Ioo_eq_top k hk hab] at hle
  exact top_unique hle

/-- **Theorem 13（圆周 $\mathbb{R}/\mathbb{Z}$ 全局无穷测度）**：
    `Measure.mkMetric (critGauge k) (circleExactLevel k) = ⊤`。 -/
theorem mkMetric_critGauge_circleExactLevel_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) (circleExactLevel k) = ⊤ := by
  simpa using mkMetric_critGauge_circleExactLevel_inter_open_eq_top k hk isOpen_univ
    ⟨0, Set.mem_univ _⟩

/-- **Theorem 13（圆周 $\mathbb{R}/\mathbb{Z}$ 全局正测度）**：
    `0 < Measure.mkMetric (critGauge k) (circleExactLevel k)`。 -/
theorem mkMetric_critGauge_circleExactLevel_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Measure.mkMetric (critGauge k) (circleExactLevel k) := by
  rw [mkMetric_critGauge_circleExactLevel_eq_top k hk]
  exact ENNReal.zero_lt_top

/-- **Theorem 13（圆周 $\mathbb{R}/\mathbb{Z}$ $\sigma$-有限可数覆盖分解）**。 -/
theorem critGauge_circleExactLevel_sigma_finite_cover (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set UnitAddCircle,
      circleExactLevel k ⊆ ⋃ i, E i ∧
      circleLevelSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (critGauge k) (E i) < ⊤ := by
  obtain ⟨Eℝ, hE_eq, hE_le, hE_fin⟩ := critGauge_exactLevel_sigma_finite_cover k hk
  refine ⟨fun i => circleProj '' Eℝ i, ?_, ?_, ?_⟩
  · rw [circleExactLevel_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hE_eq hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · rw [circleLevelSet_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hE_le hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · intro i
    exact lt_of_le_of_lt (mkMetric_circleProj_image_le (critGauge k) (critGauge_mono k hk) _)
      (hE_fin i)

/-- **Corollary 14(iii)（圆周 $\mathbb{R}/\mathbb{Z}$ 版）**。 -/
theorem mkMetric_critGauge_circleExactLevel_not_sigma_finite_of_ratio (k : ℕ) (hk : 1 ≤ k)
    (g : ℝ≥0∞ → ℝ≥0∞)
    (hratio : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ r : ℝ≥0∞, r ≤ δ → critGauge k r ≤ (ε : ℝ≥0∞) * g r) :
    Measure.mkMetric g (circleExactLevel k) = ⊤ ∧
    ¬ ∃ E : ℕ → Set UnitAddCircle, circleExactLevel k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric g (E i) < ⊤ :=
  not_countable_union_finite_of_ratio_tendsto_zero_circle (critGauge k) g hratio
    (mkMetric_critGauge_circleExactLevel_pos k hk)

/-- **Theorem 13 幂规范 $\beta > 2k+1$（圆周 $\mathbb{R}/\mathbb{Z}$ 零测度）**。 -/
theorem mkMetric_powerGauge_circleExactLevel_null_of_gt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ : 2 * (k : ℝ) + 1 < β) :
    Measure.mkMetric (interpGauge β) (circleLevelSet k) = 0 ∧
    Measure.mkMetric (interpGauge β) (circleExactLevel k) = 0 := by
  have hb1 : (1 : ℝ) < 2 * (k : ℝ) + 1 := critGauge_base_gt_one k hk
  have hβ1 : 1 < β := lt_trans hb1 hβ
  obtain ⟨hR_le, _⟩ := mkMetric_powerGauge_exactLevel_null_of_gt k hk hβ
  have hC_le : Measure.mkMetric (interpGauge β) (circleLevelSet k) = 0 := by
    rw [circleLevelSet_eq_image]
    exact le_antisymm
      ((mkMetric_circleProj_image_le (interpGauge β) (interpGauge_mono hβ1) _).trans_eq hR_le)
      zero_le
  refine ⟨hC_le, measure_mono_null (fun _ hx => le_of_eq hx) hC_le⟩

/-- **Theorem 13 幂规范 $1 < \beta < 2k+1$（圆周 $\mathbb{R}/\mathbb{Z}$ 非 $\sigma$-有限性）**。 -/
theorem mkMetric_powerGauge_circleExactLevel_not_sigma_finite_of_lt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) (hβlt : β < 2 * (k : ℝ) + 1) :
    Measure.mkMetric (interpGauge β) (circleExactLevel k) = ⊤ ∧
    ¬ ∃ E : ℕ → Set UnitAddCircle, circleExactLevel k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (interpGauge β) (E i) < ⊤ :=
  mkMetric_critGauge_circleExactLevel_not_sigma_finite_of_ratio k hk (interpGauge β)
    (interpGauge_ratio_tendsto_zero hβ1 hβlt)

/-- **Theorem 16(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 上 $E_{\mathrm{lim}}(k/4)$ 在 $h_k$ 下为零测度）**。 -/
theorem critGauge_circleUnsignedExactLimit_null (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric (critGauge k) (circleUnsignedExactLimitSet k) = 0 :=
  le_antisymm
    ((mkMetric_circleProj_image_le (critGauge k) (critGauge_mono k hk) _).trans_eq
      (critGauge_unsignedExactLimit_null k hk))
    zero_le

/-- **Theorem 16(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 上 $E_{\mathrm{lim}}(k/4)$ 的 $\mathcal{H}^{g_2}$-$\sigma$-有限覆盖）**。 -/
theorem binaryGauge_circleUnsignedExactLimit_sigma_finite_cover (k : ℕ) :
    ∃ E : ({N : ℕ // 1 ≤ N} × ℤ × ℤ) → Set UnitAddCircle,
      circleUnsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric binaryGauge (E i) < ⊤ := by
  obtain ⟨Eℝ, hE_sub, hE_fin⟩ := binaryGauge_unsignedExactLimit_sigma_finite_cover k
  refine ⟨fun i => circleProj '' Eℝ i, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hE_sub hx)
    exact Set.mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  · intro i
    exact lt_of_le_of_lt (mkMetric_circleProj_image_le binaryGauge binaryGauge_mono _) (hE_fin i)

/-- **Theorem 16(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 任意非空开集/开弧上的 $\mathcal{H}^{g_2}$ 无穷测度）**。 -/
theorem mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top (k : ℕ) (hk : 1 ≤ k)
    {U : Set UnitAddCircle} (hU_open : IsOpen U) (hU_ne : U.Nonempty) :
    Measure.mkMetric binaryGauge (circleUnsignedExactLimitSet k ∩ U) = ⊤ := by
  obtain ⟨a, b, hab, hwidth, hsub⟩ := exists_Ioo_subset_preimage_of_isOpen_circle hU_open hU_ne
  set A : Set ℝ := unsignedExactLimitSet k ∩ Set.Ioo a b
  have hA_img : circleProj '' A ⊆ circleUnsignedExactLimitSet k ∩ U := by
    rintro _ ⟨x, ⟨hxE, hxI⟩, rfl⟩
    exact ⟨⟨x, hxE, rfl⟩, hsub hxI⟩
  have hle : Measure.mkMetric binaryGauge A ≤
      Measure.mkMetric binaryGauge (circleUnsignedExactLimitSet k ∩ U) :=
    le_trans
      (mkMetric_le_circleProj_image_of_subset_Ioo binaryGauge binaryGauge_mono hwidth
        Set.inter_subset_right)
      (measure_mono hA_img)
  rw [mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top k hk hab] at hle
  exact top_unique hle

/-- **Theorem 16(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 全局 $\mathcal{H}^{g_2}$ 无穷测度）**。 -/
theorem mkMetric_binaryGauge_circleUnsignedExactLimit_eq_top (k : ℕ) (hk : 1 ≤ k) :
    Measure.mkMetric binaryGauge (circleUnsignedExactLimitSet k) = ⊤ := by
  simpa using mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top k hk isOpen_univ
    ⟨0, Set.mem_univ _⟩

/-- **Theorem 16(ii)（圆周 $\mathbb{R}/\mathbb{Z}$ 全局 $\mathcal{H}^{g_2}$ 正测度）**。 -/
theorem mkMetric_binaryGauge_circleUnsignedExactLimit_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < Measure.mkMetric binaryGauge (circleUnsignedExactLimitSet k) := by
  rw [mkMetric_binaryGauge_circleUnsignedExactLimit_eq_top k hk]
  exact ENNReal.zero_lt_top

/-- **Theorem 16(ii) 幂规范 $\beta > 2$（圆周 $\mathbb{R}/\mathbb{Z}$ 零测度）**。 -/
theorem mkMetric_powerGauge_circleUnsignedExactLimit_null_of_gt (k : ℕ)
    {β : ℝ} (hβ : 2 < β) :
    Measure.mkMetric (interpGauge β) (circleUnsignedExactLimitSet k) = 0 :=
  le_antisymm
    ((mkMetric_circleProj_image_le (interpGauge β) (interpGauge_mono (by linarith)) _).trans_eq
      (mkMetric_powerGauge_unsignedExactLimit_null_of_gt k hβ))
    zero_le

/-- **Theorem 16(ii) 幂规范 $1 < \beta < 2$（圆周 $\mathbb{R}/\mathbb{Z}$ 非 $\sigma$-有限性）**。 -/
theorem mkMetric_powerGauge_circleUnsignedExactLimit_not_sigma_finite_of_lt (k : ℕ) (hk : 1 ≤ k)
    {β : ℝ} (hβ1 : 1 < β) (hβlt : β < 2) :
    Measure.mkMetric (interpGauge β) (circleUnsignedExactLimitSet k) = ⊤ ∧
    ¬ ∃ E : ℕ → Set UnitAddCircle, circleUnsignedExactLimitSet k ⊆ ⋃ i, E i ∧
      ∀ i, Measure.mkMetric (interpGauge β) (E i) < ⊤ :=
  not_countable_union_finite_of_ratio_tendsto_zero_circle binaryGauge (interpGauge β)
    (interpGauge_ratio_tendsto_zero hβ1 hβlt)
    (mkMetric_binaryGauge_circleUnsignedExactLimit_pos k hk)

end

end GaugeCircle

/-! ## 公理依赖审计（#print axioms） -/
#print axioms GaugeCircle.critGauge_zero
#print axioms GaugeCircle.critGauge_mono
#print axioms GaugeCircle.critGauge_continuous
#print axioms GaugeCircle.critGauge_at_inv_Qsel
#print axioms GaugeCircle.binaryGauge_zero
#print axioms GaugeCircle.binaryGauge_mono
#print axioms GaugeCircle.binaryGauge_continuous
#print axioms GaugeCircle.binaryGauge_at_inv_Qsel
#print axioms GaugeCircle.mkMetric_critGauge_strictLevel_null
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_pos
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_eq_top
#print axioms GaugeCircle.critGauge_exactLevel_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_Ioo_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_Icc_zero_one_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_inter_eq_top_of_Ioo_subset
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_pos
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Ioo_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_eq_top
#print axioms GaugeCircle.binaryGauge_unsignedExactLimit_sigma_finite_cover
#print axioms GaugeCircle.critGauge_unsignedExactLimit_null
#print axioms GaugeCircle.mkMetric_powerGauge_exactLevel_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_exactLevel_not_sigma_finite_of_lt
#print axioms GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_unsignedExactLimit_not_sigma_finite_of_lt
#print axioms GaugeCircle.critGauge_ge_one
#print axioms GaugeCircle.critGauge_eq_segVal
#print axioms GaugeCircle.binaryGauge_ge_one
#print axioms GaugeCircle.binaryGauge_eq_segVal
#print axioms GaugeCircle.mkMetric_critGauge_exactLevel_not_sigma_finite_of_ratio
#print axioms GaugeCircle.critGauge_adjacent_ratio_tendsto_zero
#print axioms GaugeCircle.critGauge_adjacent_level_separation
#print axioms GaugeCircle.mkMetric_binaryGauge_unsignedExactLimit_inter_Icc_zero_one_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleStrictLevel_null
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_inter_open_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_eq_top
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_pos
#print axioms GaugeCircle.critGauge_circleExactLevel_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_critGauge_circleExactLevel_not_sigma_finite_of_ratio
#print axioms GaugeCircle.mkMetric_powerGauge_circleExactLevel_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_circleExactLevel_not_sigma_finite_of_lt
#print axioms GaugeCircle.critGauge_circleUnsignedExactLimit_null
#print axioms GaugeCircle.binaryGauge_circleUnsignedExactLimit_sigma_finite_cover
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_inter_open_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_eq_top
#print axioms GaugeCircle.mkMetric_binaryGauge_circleUnsignedExactLimit_pos
#print axioms GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_null_of_gt
#print axioms GaugeCircle.mkMetric_powerGauge_circleUnsignedExactLimit_not_sigma_finite_of_lt
#print axioms GaugeCircle.mkMetric_inter_Ioo_eq_top_of_compact_tree
#print axioms GaugeCircle.mkMetric_binCantorTree_pos
#print axioms GaugeCircle.unsignedExactLimit_add_latticeL
#print axioms GaugeCircle.mkMetric_le_mul_of_eventually_le_circle
#print axioms GaugeCircle.not_countable_union_finite_of_ratio_tendsto_zero_circle
#print axioms GaugeCircle.mkMetric_circleLevelSet_null_of_subgauge
