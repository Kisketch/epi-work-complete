import Mathlib
import EpiFormal.WindowThickening

open MeasureTheory Set Filter Finset ENNReal Metric
open scoped NNReal BigOperators Topology MeasureTheory

namespace WindowFrostDirect

noncomputable section

/-!
# 逐窗选层直接组装 Frostman 骨架（L05；E2-Hinter 路线退役后）

本文件是论文 L1027-1055（及 windows 版 L2536-2557）逐窗选层模板的
Frostman 组装骨架：S1-S4（反设 / 开膨胀 / 有限子覆盖）与
S8a / S8b / S8c / S9（分裂界 / 有限和 vs 级数 / 几何级数 / 矛盾）
照抄 CylinderFrostman.lean（E2 frostman_of_count_thresh）同名段落，
仅改名避冲突；删除 Hinter 参数（含全局 M），替换为显式逐窗接口
Hwin：每个有限子覆盖成员 i ∈ F 自带 level（lvl i）
（选层存在性 + 交数上界 + 阈值不等式），主定理结论与 E2 相同
（1 ≤ μH[s] K）。

退役理由（见 verification/frostman_redesign_20261121.md）：
R1 Hinter / 全称集接口在 V = univ 处空真、不可 discharge；
R2 单层 stopped 原子族在数学上就不可能通过任意小窗阈值；
R3 任何保留全局 M 的修补都不可行（计数下界要 M 小、
逐窗阈值要 M 大）。故每窗自选 level、本层常数承担阈值，
计数经顶层总数相消，即本文件 Hwin 的形状。

逐窗接口 discharge 路线（S5 / S6 / S7 在本文件中仅以显式 hypothesis
参数呈现，由以下后续文件分别 discharge，不在本文件证明）：
- S5 选层存在性（Ns ≤ lvl i 与 (Q (lvl i + 1))⁻¹ ≤ diam）→
  WindowSandwich.sandwich_of_tendsto（F3a 选层引理）；
- S6 交数上界（Kc i ≤ 3）→
  CoverCount.meet_card_of_diam_le / CoverCount.window_overlap_le；
- S7 阈值不等式（3 / M (lvl i) ≤ (Q (lvl i + 1) ^ s)⁻¹ 与
  Kc i / M (lvl i) ≤ diam ^ s；计数下界 1 ≤ Σ 同属本家族）→
  WindowMassProd.mass_le_fact_bound（mass_le_prod 乘积界）与
  WindowLogThresh.frostman_ratio_bound（log_inv_le_two_log 对数比较）链。

依赖：仅 Mathlib；不 import E2 主定理所在模块之外的任何新模块。
-/

/-- 0 < s ≤ 1 时次可加性：(a + b)^s ≤ a^s + b^s（Frostman 直径分裂用，直接组装版）。 -/
lemma direct_rpow_add_le_add_rpow {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 0 < s) (hs1 : s ≤ 1) :
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

/-- 开膨胀直径上界（ℝ 半径版，包装 mathlib 的 NNReal 版，直接组装版）。 -/
lemma direct_ediam_thickening_le {A : Set ℝ} {ρ : ℝ} (_hρ : 0 ≤ ρ) :
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

set_option maxHeartbeats 800000 in
/-- Frostman 直接组装核心：紧集 K 上，若每个有限开覆盖的每窗都能选层
（接口 Hwin：每窗自带 level（lvl i）；
由选层 / 交数 / 质量乘积与对数比较链 discharge），则 s 维 Hausdorff 测度 ≥ 1。
骨架 = S1（反设）→ S2（开膨胀）→ S3（有限子覆盖）→ S5/S6/S7（逐窗接口）
→ S8（分裂 / 级数）→ S9（矛盾）。
注：h_thresh 中间层已删（E2 证明未消费；discharge 直接证 Hthresh）。
h_meet 已删（见设计文档 R3）。 -/
theorem frostman_of_window_layer
    {K : Set ℝ} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hK : IsCompact K) (hKne : K.Nonempty)
    (r0R : ℝ) (hr0R : 0 < r0R)
    (Q M : ℕ → ℝ) (Ns : ℕ)
    (Hwin : ∀ (ι : Type) (V : ι → Set ℝ) (F : Finset ι),
      (∀ i, IsOpen (V i)) → K ⊆ ⋃ i ∈ F, V i →
      (∀ i, Bornology.IsBounded (V i)) →
      (∀ i, (V i).Nonempty → 0 < Metric.diam (V i)) →
      (hF : F.Nonempty) →
      (htop : ∀ i, Metric.diam (V i) ≤ 2 * r0R) →
      ∃ (lvl : ι → ℕ) (Kc : ι → ℕ),
        (∀ i ∈ F, (V i).Nonempty → Ns ≤ lvl i ∧ (Q (lvl i + 1))⁻¹ ≤ Metric.diam (V i)) ∧
        (1 : ℝ) ≤ ∑ i ∈ F, ((Kc i : ℝ) / M (lvl i)) ∧
        (∀ i ∈ F, ((Kc i : ℝ) / M (lvl i)) ≤ (Metric.diam (V i)) ^ s))
    : 1 ≤ MeasureTheory.Measure.hausdorffMeasure s K := by
  set r0 : ℝ≥0∞ := ENNReal.ofReal r0R with hr0def
  have hr0 : 0 < r0 := by rw [hr0def]; exact ENNReal.ofReal_pos.mpr hr0R
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_trans ?_ (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
    ⨅ (t : ℕ → Set ℝ) (_ : K ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s) r0 hr0)
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
  -- S2：开膨胀（半径用 r0R/2 封顶，保证加厚集直径落在 F3a 选层范围内）。
  let ρ : ℕ → ℝ := fun i => min (r0R / 2) (((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2)
  have hρ_pos : ∀ i, 0 < ρ i := fun i => by
    have h1 : (0 : ℝ) < r0R / 2 := by linarith [hr0R]
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    have hpos2 : 0 < (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := Real.rpow_pos_of_pos hpos1 (1 / s)
    have h2 : (0 : ℝ) < (((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2) := by linarith
    exact lt_min h1 h2
  have h2ρ_rpow : ∀ i, (2 * ρ i) ^ s ≤ δ0 / (2 : ℝ) ^ (i + 1) := fun i => by
    have hpos1 : 0 < δ0 / (2 : ℝ) ^ (i + 1) := by positivity
    have h1 : 2 * ρ i ≤ (δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s) := by
      have hle : ρ i ≤ (((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) / 2) :=
        min_le_right _ _
      linarith
    calc (2 * ρ i) ^ s
        ≤ (((δ0 / (2 : ℝ) ^ (i + 1)) ^ (1 / s)) ^ s) :=
          Real.rpow_le_rpow (by linarith [hρ_pos i]) h1 (le_of_lt hs0)
      _ = (δ0 / (2 : ℝ) ^ (i + 1)) ^ ((1 / s) * s) :=
          (Real.rpow_mul (le_of_lt hpos1) (1 / s) s).symm
      _ = δ0 / (2 : ℝ) ^ (i + 1) := by rw [one_div_mul_cancel (ne_of_gt hs0), Real.rpow_one]
  let V : ℕ → Set ℝ := fun i => Metric.thickening (ρ i) (t i)
  have hV_open : ∀ i, IsOpen (V i) := fun i => Metric.isOpen_thickening
  have hV_cov : K ⊆ ⋃ i : {i : ℕ // (t i).Nonempty}, V i.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    refine Set.mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, ?_⟩
    exact Metric.self_subset_thickening (hρ_pos i) (t i) hi
  -- S3：有限子覆盖
  obtain ⟨F, hFcov⟩ := hK.elim_finite_subcover
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) (fun i => hV_open i.1) hV_cov
  -- S3b：加厚集有界 + 直径为正（Hinter 正性前提的供给）。
  have hV_bd : ∀ i : {i : ℕ // (t i).Nonempty},
      Bornology.IsBounded (V i.1) := fun i =>
    WindowThickening.isBounded_thickening_of_ediam (le_of_lt (hρ_pos i.1))
      (le_trans (hdiam i.1) le_rfl) ENNReal.ofReal_ne_top
  have hV_pos : ∀ i : {i : ℕ // (t i).Nonempty},
      0 < Metric.diam (V i.1) := fun i =>
    WindowThickening.diam_thickening_pos i.2 (hρ_pos i.1) (hV_bd i)
  -- S2b：加厚集 ediam/直径上界（r0R 封顶；discharge 的 F3a 选层需要直径上界）。
  have hV_ediam_le : ∀ i : {i : ℕ // (t i).Nonempty},
      Metric.ediam (V i.1) ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := fun i => by
    have hcap : 2 * ρ i.1 ≤ r0R := by
      have hle : ρ i.1 ≤ r0R / 2 := min_le_left _ _
      linarith
    calc Metric.ediam (V i.1)
        ≤ Metric.ediam (t i.1) + 2 * ENNReal.ofReal (ρ i.1) :=
          direct_ediam_thickening_le (le_of_lt (hρ_pos i.1))
      _ = Metric.ediam (t i.1) + ENNReal.ofReal (2 * ρ i.1) := by
          have h2 : 2 * ENNReal.ofReal (ρ i.1) = ENNReal.ofReal (2 * ρ i.1) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
          rw [h2]
      _ ≤ ENNReal.ofReal r0R + ENNReal.ofReal r0R := by
          have hle2 : ENNReal.ofReal (2 * ρ i.1) ≤ ENNReal.ofReal r0R :=
            ENNReal.ofReal_le_ofReal hcap
          have hd' : Metric.ediam (t i.1) ≤ ENNReal.ofReal r0R := by
            rw [← hr0def]; exact hdiam i.1
          exact add_le_add hd' hle2
      _ = ENNReal.ofReal r0R + ENNReal.ofReal r0R := rfl
  have hV_diam_le : ∀ i : {i : ℕ // (t i).Nonempty},
      Metric.diam (V i.1) ≤ 2 * r0R := fun i => by
    have hfin : ENNReal.ofReal r0R + ENNReal.ofReal r0R ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    have h := ENNReal.toReal_mono hfin (hV_ediam_le i)
    unfold Metric.diam at h ⊢
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (le_of_lt hr0R)] at h
    linarith
  -- S5 选层存在性由 h_layer 给出；交数上界已并入逐窗质量界
  -- （h_meet、h_thresh 均已删：E2 证明未消费，见设计文档 R3）；
  -- 计数下界 Hcount 与逐窗质量界 Hthresh 直接进入 S9。
  -- S3 族非空（K 非空 + 覆盖）→ Hinter 的 hF 前提。
  have hFne : F.Nonempty := by
    obtain ⟨x, hxK⟩ := hKne
    obtain ⟨i, hiF, _⟩ := Set.mem_iUnion₂.mp (hFcov hxK)
    exact ⟨i, hiF⟩
  obtain ⟨lvl, Kc, h_layer, Hcount, Hthresh⟩ := Hwin _
    (fun i : {i : ℕ // (t i).Nonempty} => V i.1) F (fun i => hV_open i.1) hFcov
    (fun i => hV_bd i) (fun i _ => hV_pos i) hFne (fun i => hV_diam_le i)
  -- S8a：逐点分裂界
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
        exact direct_ediam_thickening_le (le_of_lt (hρ_pos i.1))
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
            direct_rpow_add_le_add_rpow ENNReal.toReal_nonneg (by linarith [hρ_pos i.1]) hs0 hs1
    have htoR_rpow : (Metric.ediam (t i.1)).toReal ^ s = (Metric.ediam (t i.1) ^ s).toReal :=
      ENNReal.toReal_rpow (Metric.ediam (t i.1)) s
    rw [htoR_rpow] at hpow_le
    linarith [h2ρ_rpow i.1]
  -- S8b：有限和 vs 级数
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
  -- S8c：几何级数
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
  -- S9：矛盾
  have htotal_lt : ∑ i ∈ F, Metric.diam (V i.1) ^ s < 1 := by
    calc ∑ i ∈ F, Metric.diam (V i.1) ^ s
        ≤ ∑ i ∈ F, ((Metric.ediam (t i.1) ^ s).toReal + δ0 / (2 : ℝ) ^ (i.1 + 1)) :=
          Finset.sum_le_sum hdiam_bound
      _ = (∑ i ∈ F, (Metric.ediam (t i.1) ^ s).toReal) + ∑ i ∈ F, δ0 / (2 : ℝ) ^ (i.1 + 1) :=
          Finset.sum_add_distrib
      _ ≤ S.toReal + δ0 := add_le_add hsum_t hsum_geom
      _ < 1 := by linarith
  have hle : ∑ i ∈ F, ((Kc i : ℝ) / M (lvl i)) ≤ ∑ i ∈ F, (Metric.diam (V i.1)) ^ s :=
    Finset.sum_le_sum (fun i hi => Hthresh i hi)
  linarith [Hcount, hle, htotal_lt]

end

end WindowFrostDirect
